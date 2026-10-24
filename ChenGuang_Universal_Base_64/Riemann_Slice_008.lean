import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Slice 008: The value of the Riemann zeta function at s = 0

  zeta(0) = -1/2.

This is the classical special value obtained from the analytic continuation;
mathlib states it directly as `riemannZeta_zero`.
-/

theorem riemannZeta_at_zero :
    riemannZeta 0 = (-1 / 2 : Complex) := by
  exact riemannZeta_zero

#print axioms riemannZeta_at_zero
