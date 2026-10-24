import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Slice 007: Trivial zeros of the Riemann zeta function

For every positive integer n,

  zeta(-2 * n) = 0.

mathlib provides `riemannZeta_neg_two_mul_nat_add_one`, which states
`riemannZeta (-2 * (k + 1)) = 0` for every natural number k; every negative
even integer -2 * n with n positive is of this form with k = n - 1.
-/

theorem riemannZeta_trivial_zero (n : Nat) (hn : n ≠ 0) :
    riemannZeta (-2 * n) = 0 := by
  have hk : ∃ k : Nat, n = k + 1 := by
    refine ⟨n - 1, ?_⟩
    omega
  rcases hk with ⟨k, rfl⟩
  simpa [Nat.cast_add] using riemannZeta_neg_two_mul_nat_add_one k

#print axioms riemannZeta_trivial_zero
