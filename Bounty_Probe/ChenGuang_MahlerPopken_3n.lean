/-
# Integer complexity of `3 ^ n` (Mahler–Popken)

Source: `FormalConjectures/Mathoverflow/75792.lean`

The *integer complexity* `‖m‖` of `m` is the least number of `1`s needed to write `m`
using `+` and `*` (parentheses free).  The Mahler–Popken inequality says
`3 ^ ‖m‖ ≥ m ^ 3`.  For `m = 3 ^ n` it gives the exact value `‖3 ^ n‖ = 3 n`.

The upper bound is immediate: `n` copies of `3 = 1 + 1 + 1` cost `3 n`.  The lower
bound is the substance.  If `m` is written with `c` ones, then `m ^ 3 ≤ 3 ^ c`, by
induction over the way `m` was built.  Products multiply the two bounds and are
harmless; sums are where the inequality bites, and that case analysis (`a, b ≥ 2`;
`a = 1`; `b = 1`) is isolated below in `cube_add_le`, so that the induction itself
stays a two-line argument.

Everything takes place in `ℕ`: no geometry, topology, analysis or measure theory, and
no axiom beyond the standard three.
-/

import Mathlib.Tactic

namespace ChenGuang.MahlerPopken

/-! ## The construction and the complexity function -/

/-- `Reachable m n` : `m` can be written using exactly `n` copies of `1`,
with `+` and `*` (and arbitrary parentheses). -/
inductive Reachable : ℕ → ℕ → Prop
  | one : Reachable 1 1
  | add {m n a b : ℕ} : Reachable m a → Reachable n b → Reachable (m + n) (a + b)
  | mul {m n a b : ℕ} : Reachable m a → Reachable n b → Reachable (m * n) (a + b)

/-- Every reachable value is positive. -/
theorem Reachable.one_le_fst {m n : ℕ} (h : Reachable m n) : 1 ≤ m := by
  induction h with
  | one => exact le_rfl
  | add _ _ ih₁ ih₂ => exact ih₁.trans (Nat.le_add_right _ _)
  | mul _ _ ih₁ ih₂ =>
      exact ih₁.trans (Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le Nat.zero_lt_one ih₂))

/-- Every construction uses at least one `1`. -/
theorem Reachable.one_le_snd {m n : ℕ} (h : Reachable m n) : 1 ≤ n := by
  induction h with
  | one => exact le_rfl
  | add _ _ ih₁ ih₂ => exact ih₁.trans (Nat.le_add_right _ _)
  | mul _ _ ih₁ ih₂ => exact ih₁.trans (Nat.le_add_right _ _)

/-- Writing `n` with `n` copies of `1` (unary). -/
theorem Reachable.self (n : ℕ) (hn : 0 < n) : Reachable n n :=
  Nat.le_induction .one (fun _ _ ih ↦ .add ih .one) n hn

/-- The integer complexity: fewest `1`s needed to build `n` with `+` and `*`. -/
noncomputable def complexity (n : ℕ) : ℕ := by
  classical
  exact if h : n = 0 then 0
  else Nat.find ⟨n, Reachable.self n (Nat.pos_of_ne_zero h)⟩

theorem Reachable.complexity_le {m n : ℕ} (h : Reachable m n) : complexity m ≤ n := by
  classical
  unfold complexity
  split_ifs with h'
  · subst h'
    exact absurd h (fun hh => Nat.not_succ_le_zero 0 (Reachable.one_le_fst (m := 0) hh))
  exact Nat.find_min' _ h

/-! ## Upper bound `‖3 ^ n‖ ≤ 3 n` -/

/-- `3` costs `3`. -/
theorem reachable_three : Reachable 3 3 := .add .one (.add .one .one)

/-- `3 ^ (n + 1)` costs at most `3 (n + 1)`. -/
theorem Reachable.three_pow (n : ℕ) : Reachable (3 ^ (n + 1)) (3 * (n + 1)) := by
  induction n with
  | zero => simp [reachable_three]
  | succ k ih =>
      rw [pow_succ, Nat.mul_add]
      exact .mul ih reachable_three

theorem complexity_three_pow_le (n : ℕ) : complexity (3 ^ (n + 1)) ≤ 3 * (n + 1) :=
  Reachable.complexity_le (Reachable.three_pow n)

/-! ## Elementary inequalities in `ℕ` -/

/-- Two numbers exceeding `1` grow at least quadratically on the way in: `(a+b)^3`
is dominated by `a^3 b^3`. -/
lemma add_cube_le_mul_cube {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (a + b) ^ 3 ≤ a ^ 3 * b ^ 3 := by
  have h : a + b ≤ a * b := by nlinarith
  calc (a + b) ^ 3 ≤ (a * b) ^ 3 := Nat.pow_le_pow_left h 3
    _ = a ^ 3 * b ^ 3 := by ring

/-- A cube grows by at most a factor of `3` when the argument is increased by `1`,
for arguments at least `3`: `(b + 1) ^ 3 ≤ 3 b ^ 3`. -/
lemma succ_cube_le_three_mul {b : ℕ} (hb : 3 ≤ b) : (b + 1) ^ 3 ≤ 3 * b ^ 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 3 := ⟨b - 3, by omega⟩
  have key : ((k : ℤ) + 4) ^ 3 ≤ 3 * ((k : ℤ) + 3) ^ 3 := by
    have h1 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    have h2 : (0 : ℤ) ≤ (k : ℤ) ^ 2 := sq_nonneg _
    have h3 : (0 : ℤ) ≤ (k : ℤ) ^ 3 := by positivity
    nlinarith
  exact_mod_cast key

/-- A value of at least `2` needs at least two ones: cost `1` never builds anything but
`1` itself. -/
theorem Reachable.two_le_snd {m n : ℕ} (h : Reachable m n) (hm : 2 ≤ m) : 2 ≤ n := by
  induction h with
  | one => omega
  | @add a b na nb h₁ h₂ ih₁ ih₂ =>
      have hna : 1 ≤ na := h₁.one_le_snd
      have hnb : 1 ≤ nb := h₂.one_le_snd
      rcases Nat.lt_or_ge a 2 with ha' | ha'
      · have : 2 ≤ na + nb := by
          calc (2 : ℕ) = 1 + 1 := by norm_num
            _ ≤ na + nb := Nat.add_le_add hna hnb
        exact this
      · exact le_trans (ih₁ ha') (Nat.le_add_right _ _)
  | @mul a b na nb h₁ h₂ ih₁ ih₂ =>
      have ha : 1 ≤ a := h₁.one_le_fst
      rcases Nat.lt_or_ge a 2 with ha' | ha'
      · have hae : a = 1 := by omega
        have hb2 : 2 ≤ b := by subst hae; simpa using hm
        exact le_trans (ih₂ hb2) (Nat.le_add_left _ _)
      · exact le_trans (ih₁ ha') (Nat.le_add_right _ _)

/-! ## The Mahler–Popken lower bound `m ^ 3 ≤ 3 ^ ‖m‖` -/

/-- The sum case of the Mahler–Popken inequality.  Costs add, and the cubic bound is
inherited: if `a ^ 3 ≤ 3 ^ na` and `b ^ 3 ≤ 3 ^ nb`, then `(a + b) ^ 3 ≤ 3 ^ (na + nb)`.

For `a, b ≥ 2` the cube `(a + b) ^ 3` is dominated by `a ^ 3 b ^ 3`, and the two
factors absorb the two bounds separately.  If `a = 1`, then `(1 + b) ^ 3 ≤ 3 b ^ 3`
as soon as `b ≥ 3`, and the spare factor `3` is paid for by `3 ^ na` (with `na ≥ 1`);
the two remaining values `b = 1` and `b = 2` are checked against the small powers
`3 ^ 2 = 9` and `3 ^ 3 = 27`.  The case `b = 1` is the mirror image. -/
theorem cube_add_le {a b na nb : ℕ} (hm : Reachable a na) (hn : Reachable b nb)
    (hcube_a : a ^ 3 ≤ 3 ^ na) (hcube_b : b ^ 3 ≤ 3 ^ nb) : (a + b) ^ 3 ≤ 3 ^ (na + nb) := by
  have ha : 1 ≤ a := hm.one_le_fst
  have hb : 1 ≤ b := hn.one_le_fst
  have hna : 1 ≤ na := hm.one_le_snd
  have hnb : 1 ≤ nb := hn.one_le_snd
  rw [pow_add]
  rcases Nat.lt_or_ge a 2 with ha' | ha2
  · have hae : a = 1 := by omega
    subst hae
    rcases Nat.lt_or_ge b 2 with hb' | hb2
    · have hbe : b = 1 := by omega
      subst hbe
      have h2le : 2 ≤ na + nb := by omega
      have h9 : (3 : ℕ) ^ 2 ≤ 3 ^ (na + nb) := Nat.pow_le_pow_right (by norm_num) h2le
      calc (1 + 1) ^ 3 = 8 := by norm_num
        _ ≤ 3 ^ (na + nb) := le_trans (by norm_num) h9
        _ = 3 ^ na * 3 ^ nb := pow_add 3 na nb
    · rcases Nat.lt_or_ge b 3 with hb3' | hb3
      · have hbe : b = 2 := by omega
        subst hbe
        have hnb2 : 2 ≤ nb := hn.two_le_snd (by norm_num)
        have h3 : 3 ≤ na + nb := by omega
        calc (1 + 2) ^ 3 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ (na + nb) := Nat.pow_le_pow_right (by norm_num) h3
          _ = 3 ^ na * 3 ^ nb := pow_add 3 na nb
      · have hstep : (1 + b) ^ 3 ≤ 3 * b ^ 3 := by
          rw [Nat.add_comm (1) b]
          exact succ_cube_le_three_mul hb3
        have h3na : (3 : ℕ) ≤ 3 ^ na := by
          calc (3 : ℕ) = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ na := Nat.pow_le_pow_right (by norm_num) hna
        exact hstep.trans (Nat.mul_le_mul h3na hcube_b)
  · rcases Nat.lt_or_ge b 2 with hb' | hb2
    · have hbe : b = 1 := by omega
      subst hbe
      rcases Nat.lt_or_ge a 3 with ha3' | ha3
      · have hae : a = 2 := by omega
        subst hae
        have hna2 : 2 ≤ na := hm.two_le_snd (by norm_num)
        have h3 : 3 ≤ na + nb := by omega
        calc (2 + 1) ^ 3 = 3 ^ 3 := by norm_num
          _ ≤ 3 ^ (na + nb) := Nat.pow_le_pow_right (by norm_num) h3
          _ = 3 ^ na * 3 ^ nb := pow_add 3 na nb
      · have hstep : (a + 1) ^ 3 ≤ 3 * a ^ 3 := succ_cube_le_three_mul ha3
        have h3nb : (3 : ℕ) ≤ 3 ^ nb := by
          calc (3 : ℕ) = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ nb := Nat.pow_le_pow_right (by norm_num) hnb
        calc (a + 1) ^ 3 ≤ 3 * a ^ 3 := hstep
          _ = a ^ 3 * 3 := Nat.mul_comm _ _
          _ ≤ 3 ^ na * 3 ^ nb := Nat.mul_le_mul hcube_a h3nb
    · exact (add_cube_le_mul_cube ha2 hb2).trans (Nat.mul_le_mul hcube_a hcube_b)

/-- Mahler–Popken: a number written with `n` ones has cube at most `3 ^ n`. -/
theorem Reachable.pow_three_le {m n : ℕ} (h : Reachable m n) : m ^ 3 ≤ 3 ^ n := by
  induction h with
  | one => norm_num
  | add h₁ h₂ ih₁ ih₂ => exact cube_add_le h₁ h₂ ih₁ ih₂
  | @mul a b na nb h₁ h₂ ih₁ ih₂ =>
      rw [pow_add]
      calc (a * b) ^ 3 = a ^ 3 * b ^ 3 := by ring
        _ ≤ 3 ^ na * 3 ^ nb := Nat.mul_le_mul ih₁ ih₂

/-- The construction using `complexity m` ones really does build `m`. -/
theorem Reachable.complexity_spec {m : ℕ} (hm : 0 < m) : Reachable m (complexity m) := by
  classical
  unfold complexity
  split_ifs with h
  · exact absurd h (by omega)
  · exact Nat.find_spec _

/-! ## Main theorem `‖3 ^ n‖ = 3 n` -/

/-- `3 ^ (n + 1)` is written optimally with `3 (n + 1)` ones. -/
theorem complexity_three_pow_eq (n : ℕ) : complexity (3 ^ (n + 1)) = 3 * (n + 1) := by
  refine le_antisymm (complexity_three_pow_le n) ?_
  have hcube : (3 ^ (n + 1)) ^ 3 ≤ 3 ^ complexity (3 ^ (n + 1)) :=
    (Reachable.complexity_spec (m := 3 ^ (n + 1)) (by positivity)).pow_three_le
  have heq : (3 ^ (n + 1)) ^ 3 = (3 : ℕ) ^ (3 * (n + 1)) := by
    rw [← pow_mul]
    congr 1
    ring
  have hle : (3 : ℕ) ^ (3 * (n + 1)) ≤ 3 ^ complexity (3 ^ (n + 1)) := heq.symm.trans_le hcube
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle

/-- **Mahler–Popken**: `‖3 ^ n‖ = 3 n` for `n ≥ 1`. -/
theorem complexity_three_pow : ∀ n : ℕ, 0 < n → complexity (3 ^ n) = 3 * n := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact complexity_three_pow_eq k

end ChenGuang.MahlerPopken

/-! ## Axiom audit -/

#print axioms ChenGuang.MahlerPopken.complexity_three_pow
