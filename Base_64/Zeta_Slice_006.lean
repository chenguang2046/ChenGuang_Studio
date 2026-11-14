import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Slice 006: Euler formula for zeta at positive even integers

For every positive integer n,

  zeta(2n) = (-1)^(n+1) * B_{2n} * (2 pi)^(2n) / (2 * (2n)!)

where B_{2n} is the 2n-th Bernoulli number.

mathlib provides `riemannZeta_two_mul_nat`, which states

  zeta(2k) = (-1)^(k+1) * 2^(2k-1) * pi^(2k) * bernoulli(2k) / (2k)!

The two formulas agree because (2 pi)^(2n) / 2 = 2^(2n-1) * pi^(2n).
-/

theorem zeta_even_euler (n : Nat) (hn : n ≠ 0) :
    riemannZeta (2 * n) =
      (-1 : Complex) ^ (n + 1) * bernoulli (2 * n) * (2 * Real.pi : Complex) ^ (2 * n) /
        (2 * Nat.factorial (2 * n)) := by
  rw [riemannZeta_two_mul_nat hn, mul_pow]
  have hpow : (2 : Complex) ^ (2 * n) = 2 * (2 : Complex) ^ (2 * n - 1) := by
    conv_lhs =>
      arg 2
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)]
    rw [pow_succ]
    ring
  rw [hpow]
  field_simp
