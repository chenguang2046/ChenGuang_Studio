/-
OEIS A248802, Conjecture 1: for every `n`, the least prime factor of
`2 ^ (2 ^ (10 * n + 2) + 2) + 3` is `67`.

Write `E(n) = 2 ^ (10 * n + 2) + 2 = 4 * 1024 ^ n + 2`.  The proof has two halves.

67 divides every term.  `1024 ≡ 1 (mod 33)` makes `E(n) ≡ 6 (mod 66)`, and
`2 ^ 66 ≡ 1 (mod 67)`, so `2 ^ E(n) ≡ 2 ^ 6 = 64 ≡ -3 (mod 67)`.

No smaller prime divides any term.  For an odd prime `p < 67`, write `d` for the
order of `2` modulo `p`.  Then `2 ^ E(n)` depends only on `E(n) mod d`, and
`1024 ^ n mod d` is eventually `T`-periodic, so the infinite family collapses onto
the `T` residues `E(1), ..., E(T)`; a finite table of triples `(p, d, T)` collects
them all and is checked in one `decide` below.  The term `n = 0` is a single value,
`2 ^ 6 + 3 = 67`, and the prime `2` is settled by parity.
-/

import Mathlib.Tactic

set_option maxRecDepth 400000

namespace ChenGuang.OEIS.A248802

/-! ## Reducing an exponent modulo the order of `2` -/

/-- Exponent reduction: `2 ^ e` only depends on `e` modulo the order of `2`. -/
lemma pow_mod_period {p d e : ℕ} (h : 2 ^ d ≡ 1 [MOD p]) :
    2 ^ e ≡ 2 ^ (e % d) [MOD p] := by
  rw [← Nat.div_add_mod e d, Nat.mul_comm d (e / d), pow_add, pow_mul']
  have h1 : (2 ^ d) ^ (e / d) ≡ 1 ^ (e / d) [MOD p] := h.pow _
  simpa using h1.mul (Nat.ModEq.refl (2 ^ (e % d)))

/-- Congruent exponents give congruent powers. -/
lemma pow_exp_modEq {p d x y : ℕ} (hd : 2 ^ d ≡ 1 [MOD p]) (h : x ≡ y [MOD d]) :
    2 ^ x ≡ 2 ^ y [MOD p] := by
  have hx : 2 ^ x ≡ 2 ^ (x % d) [MOD p] := pow_mod_period hd
  have hy : 2 ^ y ≡ 2 ^ (y % d) [MOD p] := pow_mod_period hd
  rw [show x % d = y % d from h] at hx
  exact hx.trans hy.symm

/-- Divisibility transfers along congruences. -/
lemma dvd_add_of_modEq {p a b k : ℕ} (h : a ≡ b [MOD p]) (hk : p ∣ a + k) : p ∣ b + k := by
  have h1 : (a + k) % p = 0 := Nat.mod_eq_zero_of_dvd hk
  have h2 : a % p = b % p := h
  have h3 : (b + k) % p = 0 := by
    rw [Nat.add_mod, ← h2, ← Nat.add_mod]
    exact h1
  exact Nat.dvd_of_mod_eq_zero h3

/-- Shifting the exponent by one period leaves `1024 ^ n` unchanged, for `n ≥ 1`. -/
lemma pow_shift {d T : ℕ} (h : 1024 ^ (1 + T) ≡ 1024 ^ 1 [MOD d]) :
    ∀ k : ℕ, 1 ≤ k → 1024 ^ (k + T) ≡ 1024 ^ k [MOD d] := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 + T = 1 + T + j by omega, pow_add]
  simpa [pow_succ'] using h.mul (Nat.ModEq.refl (1024 ^ j))

/-- Reduction of `1024 ^ n`, for `n ≥ 1`, to the fundamental range `1, ..., T`. -/
lemma pow_reduce {d T : ℕ} (hT : 0 < T) (h : 1024 ^ (1 + T) ≡ 1024 ^ 1 [MOD d]) :
    ∀ n : ℕ, 1 ≤ n → 1024 ^ n ≡ 1024 ^ ((n - 1) % T + 1) [MOD d] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases lt_or_ge n (T + 1) with hlt | hge
    · have hnm : n - 1 < T := by omega
      have hfix : (n - 1) % T + 1 = n := by
        rw [Nat.mod_eq_of_lt hnm]
        omega
      rw [hfix]
    · have hstep : 1024 ^ n ≡ 1024 ^ (n - T) [MOD d] := by
        have hnT : 1 ≤ n - T := by omega
        calc 1024 ^ n = 1024 ^ (n - T + T) := by congr 1; omega
          _ ≡ 1024 ^ (n - T) [MOD d] := pow_shift h (n - T) hnT
      have hred : (n - 1) % T = (n - T - 1) % T := by
        have : n - 1 = (n - T - 1) + T := by omega
        rw [this, Nat.add_mod_right]
      rw [hred]
      exact hstep.trans (ih (n - T) (by omega) (by omega))

/-- The core reduction: if none of the `T` fundamental residues is divisible by `p`,
no term of the family is. -/
lemma not_dvd_of_period {p d T : ℕ} (hord : 2 ^ d ≡ 1 [MOD p]) (hT : 0 < T)
    (hper : 1024 ^ (1 + T) ≡ 1024 ^ 1 [MOD d])
    (hchk : ∀ r, 1 ≤ r → r ≤ T → ¬ p ∣ 2 ^ ((4 * 1024 ^ r + 2) % d) + 3)
    {n : ℕ} (hn : 1 ≤ n) : ¬ p ∣ 2 ^ (4 * 1024 ^ n + 2) + 3 := by
  set r := (n - 1) % T + 1 with hr
  have hr1 : 1 ≤ r := by omega
  have hrT : r ≤ T := by
    have hlt : (n - 1) % T < T := Nat.mod_lt _ hT
    omega
  have hred : 1024 ^ n ≡ 1024 ^ r [MOD d] := by
    rw [hr]
    exact pow_reduce hT hper n hn
  have hE : 4 * 1024 ^ n + 2 ≡ 4 * 1024 ^ r + 2 [MOD d] :=
    ((Nat.ModEq.refl 4).mul hred).add (Nat.ModEq.refl 2)
  have h1 : 2 ^ (4 * 1024 ^ n + 2) ≡ 2 ^ (4 * 1024 ^ r + 2) [MOD p] := pow_exp_modEq hord hE
  have h2 : 2 ^ (4 * 1024 ^ r + 2) ≡ 2 ^ ((4 * 1024 ^ r + 2) % d) [MOD p] := pow_mod_period hord
  intro hdvd
  exact hchk r hr1 hrT (dvd_add_of_modEq (h1.trans h2) hdvd)

/-- `2 ^ (10 * n + 2) = 4 * 1024 ^ n`. -/
lemma two_pow_ten_mul (n : ℕ) : 2 ^ (10 * n + 2) = 4 * 1024 ^ n := by
  rw [pow_add, pow_mul, show (2 : ℕ) ^ 10 = 1024 by norm_num, pow_two]
  ring

/-! ## The finite order table for odd primes below `67` -/

/-- The odd primes `p < 67`, with `d = ord_p(2)` and `T` a period of `1024` modulo `d`. -/
def orderTable : List (ℕ × ℕ × ℕ) :=
  [(3, 2, 1), (5, 4, 1), (7, 3, 1), (11, 10, 2), (13, 12, 1), (17, 8, 1),
   (19, 18, 3), (23, 11, 1), (29, 28, 3), (31, 5, 2), (37, 36, 3), (41, 20, 2),
   (43, 14, 3), (47, 23, 11), (53, 52, 6), (59, 58, 14), (61, 60, 2)]

/-- Every entry carries a genuine order of `2` and a positive period of `1024`. -/
lemma orderTable_spec : ∀ e ∈ orderTable, 2 ^ e.2.1 ≡ 1 [MOD e.1]
    ∧ 1024 ^ (1 + e.2.2) ≡ 1024 ^ 1 [MOD e.2.1] ∧ 0 < e.2.2 := by
  decide

/-- The finite check: on the fundamental residues no entry divides the corresponding
term, and the case `n = 0` is the single value `2 ^ 6 + 3`. -/
lemma orderTable_check : ∀ e ∈ orderTable, ∀ r ∈ Finset.Icc 1 e.2.2,
    ¬ e.1 ∣ 2 ^ ((4 * 1024 ^ r + 2) % e.2.1) + 3 := by
  decide

/-- The table covers every odd prime below `67`. -/
lemma orderTable_cover : ∀ p ∈ Finset.range 67, p.Prime → p ≠ 2 → ∃ e ∈ orderTable, e.1 = p := by
  decide

/-! ## The two halves of the argument -/

/-- Every term is odd, so `2` never divides. -/
lemma not_dvd_two (n : ℕ) : ¬ 2 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  rw [two_pow_ten_mul]
  have hk : 0 < 4 * 1024 ^ n + 2 := by positivity
  have h1 : 2 ^ (4 * 1024 ^ n + 2) % 2 = 0 := by
    rw [Nat.pow_mod, show (2 : ℕ) % 2 = 0 from rfl, Nat.zero_pow hk, Nat.zero_mod]
  intro hd
  have h0 : (2 ^ (4 * 1024 ^ n + 2) + 3) % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
  rw [Nat.add_mod, h1] at h0
  norm_num at h0

/-- No prime `p < 67`, `p ≠ 2`, divides any term. -/
lemma not_dvd_of_lt (n p : ℕ) (hp : p.Prime) (hlt : p < 67) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  rw [two_pow_ten_mul]
  obtain ⟨e, he, hpe⟩ := orderTable_cover p (Finset.mem_range.mpr hlt) hp hp2
  obtain ⟨hord, hper, hT⟩ := orderTable_spec e he
  rw [← hpe]
  match n with
  | 0 =>
    -- the single value `2 ^ 6 + 3 = 67`
    have hprime : (67 : ℕ).Prime := by norm_num
    have hval : 2 ^ (4 * 1024 ^ 0 + 2) + 3 = 67 := by norm_num
    rw [hval]
    intro hdvd
    rcases (Nat.dvd_prime hprime).mp hdvd with h1 | h1
    · exact hp.ne_one (hpe ▸ h1)
    · exact absurd (hpe ▸ h1) (by omega)
  | k + 1 =>
    exact not_dvd_of_period hord hT hper
      (fun r h1 h2 => orderTable_check e he r (Finset.mem_Icc.mpr ⟨h1, h2⟩)) (n := k + 1) (by omega)

/-- `67` divides every term. -/
lemma dvd_67 (n : ℕ) : 67 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  rw [two_pow_ten_mul]
  have h1024 : 1024 ^ n ≡ 1 [MOD 33] := by
    have h : (1024 : ℕ) ≡ 1 [MOD 33] := by norm_num
    simpa using h.pow n
  have hge1 : 1 ≤ 1024 ^ n := by
    have h : 0 < 1024 ^ n := by positivity
    omega
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hge1).mp h1024.symm
  have h66 : 66 ∣ 4 * (1024 ^ n - 1) := ⟨2 * k, by rw [hk]; ring⟩
  have h6le : 6 ≤ 4 * 1024 ^ n + 2 := by
    have h4 : 4 * 1 ≤ 4 * 1024 ^ n := Nat.mul_le_mul_left 4 hge1
    omega
  have hE6 : 6 ≡ 4 * 1024 ^ n + 2 [MOD 66] := by
    rw [Nat.modEq_iff_dvd' h6le]
    have hsub : 4 * 1024 ^ n + 2 - 6 = 4 * (1024 ^ n - 1) := by
      rw [Nat.mul_sub 4 (1024 ^ n) 1]
      omega
    rw [hsub]
    exact h66
  have hpow : 2 ^ 6 ≡ 2 ^ (4 * 1024 ^ n + 2) [MOD 67] :=
    pow_exp_modEq (p := 67) (d := 66) (by norm_num) hE6
  have h67 : 67 ∣ 2 ^ 6 + 3 := by norm_num
  exact dvd_add_of_modEq hpow h67

/-- **A248802, Conjecture 1**: the least prime factor is `67`. -/
theorem minFac_eq (n : ℕ) : (2 ^ (2 ^ (10 * n + 2) + 2) + 3).minFac = 67 := by
  set N := 2 ^ (2 ^ (10 * n + 2) + 2) + 3 with hN
  have hN1 : N ≠ 1 := by
    rw [hN]
    have h : 0 < 2 ^ (2 ^ (10 * n + 2) + 2) := by positivity
    omega
  have h67 : 67 ∣ N := by rw [hN]; exact dvd_67 n
  have hle : N.minFac ≤ 67 := Nat.minFac_le_of_dvd (by norm_num) h67
  have hp : N.minFac.Prime := Nat.minFac_prime hN1
  have hp2 : N.minFac ≠ 2 := by
    intro h2
    exact not_dvd_two n (hN ▸ h2 ▸ Nat.minFac_dvd N)
  by_contra hne
  have hlt : N.minFac < 67 := lt_of_le_of_ne hle hne
  exact not_dvd_of_lt n N.minFac hp hlt hp2 (hN ▸ Nat.minFac_dvd N)

end ChenGuang.OEIS.A248802

/-! ## Axiom audit -/

#print axioms ChenGuang.OEIS.A248802.minFac_eq
