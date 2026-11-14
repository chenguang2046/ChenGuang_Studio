/-
# OEIS A113250: the odd-indexed terms are perfect squares

Source: `FormalConjectures/OEIS/113250.lean`

The sequence `a` is the member `p = 16` of the family

  `a (n+4) = -4 a (n+3) + 4 p a (n+1) + p ^ 2 a n`,  `(a 0, a 1, a 2, a 3) = (-1, 4, 32, 64)`,

and the claim is that `a (2n+1)` is always a perfect square.

The squares come from a companion sequence `y`, the solution of the second-order
recurrence `y (n+2) = -4 y (n+1) - p y n` with `(y 0, y 1) = (-2, 8 - p)`.  The
argument has three steps.

1. *Squares of `y` obey the recurrence of `a`.*  For `u = y(n+1)` and `v = y(n)` the
   next companion term is `-4u - pv`, and the identity `sq_recurrence` shows that its
   square is `(16 - p) u^2 + (p^2 - 16p) v^2 + p^3` times the square one step before.
   So `y ^ 2` follows a three-lag recurrence with coefficients `16 - p`,
   `p^2 - 16p`, `p^3`.
2. *Along one parity class, the four-step recurrence of `a` collapses to that same
   three-lag recurrence*: eliminating the term of the other parity from three
   consecutive instances of the recurrence (`three_lag_of_four_step`).
3. *Three initial values agree.*  `a 1 = (y 0)^2`, `a 3 = (y 1)^2` and `a 5 = (y 2)^2`,
   so by induction on the index the two sequences `a(2n+1)` and `(y n)^2` coincide.

The statement is the one recorded for A113250 in formal-conjectures.
-/

import Mathlib.Tactic

namespace ChenGuang.OEIS.A113250

/-- The sequence A113250. -/
def a : ℕ → ℤ
  | 0 => -1
  | 1 => 4
  | 2 => 32
  | 3 => 64
  | n + 4 => -4 * a (n + 3) + 64 * a (n + 1) + 256 * a n

/-- The companion sequence, `y (n+2) = -4 y (n+1) - p y n`. -/
def y (p : ℤ) : ℕ → ℤ
  | 0 => -2
  | 1 => 8 - p
  | n + 2 => -4 * y p (n + 1) - p * y p n

/-- *Step 1, the polynomial identity.*  If `u = y(n+1)` and `v = y(n)`, then the
square of the next companion term `-4u - pv` is a fixed combination of `u^2`, `v^2`
and the square two steps back.  This is the only computation in the proof. -/
private lemma sq_recurrence (p u v : ℤ) :
    (-4 * (-4 * u - p * v) - p * u) ^ 2 =
      (16 - p) * (-4 * u - p * v) ^ 2 + (p ^ 2 - 16 * p) * u ^ 2 + p ^ 3 * v ^ 2 := by
  ring

/-- *Step 1.*  The squares of the companion sequence satisfy the three-lag recurrence
with coefficients `16 - p`, `p^2 - 16p`, `p^3`. -/
private lemma sq_y_recurrence (p : ℤ) (n : ℕ) :
    y p (n + 3) ^ 2 =
      (16 - p) * y p (n + 2) ^ 2 + (p ^ 2 - 16 * p) * y p (n + 1) ^ 2 + p ^ 3 * y p n ^ 2 := by
  have h3 : y p (n + 3) = -4 * y p (n + 2) - p * y p (n + 1) := by
    rw [show n + 3 = n + 1 + 2 by omega]
    rfl
  rw [h3]
  exact sq_recurrence p (y p (n + 1)) (y p n)

/-- *Step 2.*  A sequence satisfying the four-step recurrence of the family satisfies,
on each parity class, a three-lag recurrence: the terms of the other parity cancel.
Explicitly, `f(k+6)` is a combination of `f(k+4)`, `f(k+2)` and `f k`. -/
private lemma three_lag_of_four_step {f : ℕ → ℤ} {p : ℤ}
    (h : ∀ k : ℕ, f (k + 4) = -4 * f (k + 3) + 4 * p * f (k + 1) + p ^ 2 * f k) (k : ℕ) :
    f (k + 6) = (16 - p) * f (k + 4) + (p ^ 2 - 16 * p) * f (k + 2) + p ^ 3 * f k := by
  have h1 := h (k + 2)
  have h2 := h (k + 1)
  have h3 := h k
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3
  linear_combination h1 - 4 * h2 + p * h3

/-- *Step 3.*  Three consecutive agreements propagate: if `f 1`, `f 3`, `f 5` are the
squares of `y 0`, `y 1`, `y 2`, then `f (2n+1)` is the square of `y n` for all `n`.

The induction keeps the three consecutive values in step, since each application of
the three-lag recurrence advances the window by one. -/
private theorem odd_terms_eq_sq {f : ℕ → ℤ} {p : ℤ}
    (h : ∀ k : ℕ, f (k + 4) = -4 * f (k + 3) + 4 * p * f (k + 1) + p ^ 2 * f k)
    (h1 : f 1 = y p 0 ^ 2) (h3 : f 3 = y p 1 ^ 2) (h5 : f 5 = y p 2 ^ 2) (n : ℕ) :
    f (2 * n + 1) = y p n ^ 2 := by
  have key : ∀ n : ℕ,
      f (2 * n + 1) = y p n ^ 2 ∧ f (2 * n + 3) = y p (n + 1) ^ 2 ∧
        f (2 * n + 5) = y p (n + 2) ^ 2 := by
    intro n
    induction n with
    | zero => exact ⟨h1, h3, h5⟩
    | succ n ih =>
      obtain ⟨e1, e3, e5⟩ := ih
      have hstep : f (2 * n + 7) = (16 - p) * f (2 * n + 5) +
          (p ^ 2 - 16 * p) * f (2 * n + 3) + p ^ 3 * f (2 * n + 1) := by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using three_lag_of_four_step h (2 * n + 1)
      rw [e1, e3, e5] at hstep
      have h7 : f (2 * n + 7) = y p (n + 3) ^ 2 := by
        rw [hstep]
        exact (sq_y_recurrence p n).symm
      simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
        Nat.reduceAdd] using ⟨e3, e5, h7⟩
  exact (key n).1

/-- **A113250**: every odd-indexed term of the sequence is a perfect square. -/
theorem odd_terms_are_squares : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  have h : a (2 * n + 1) = y 16 n ^ 2 :=
    odd_terms_eq_sq (p := 16) (fun k => by norm_num [a]) (by norm_num [a, y])
      (by norm_num [a, y]) (by norm_num [a, y]) n
  rw [h]
  exact ⟨y 16 n, by ring⟩

end ChenGuang.OEIS.A113250

/-! ## Axiom audit -/

#print axioms ChenGuang.OEIS.A113250.odd_terms_are_squares
