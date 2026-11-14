import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Slice 009: The Riemann zeta functional equation (symmetric structure)

Verified by directly invoking mathlib's own theorems (no new analytic facts
are invented, no zero-distribution computation is touched):

1. The completed zeta function `completedRiemannZeta` (the xi function) is
   symmetric under s |-> 1 - s, for every complex s:
       completedRiemannZeta (1 - s) = completedRiemannZeta s
   This is `completedRiemannZeta_one_sub` (RiemannZeta.lean), the functional
   equation in its cleanest symmetric form.

2. The classical functional equation for the un-completed zeta, valid away
   from poles (s is not a non-positive integer and s != 1):
       zeta (1 - s) = 2 * (2 * pi)^(-s) * Gamma s * cos (pi * s / 2) * zeta s
   This is `riemannZeta_one_sub` (RiemannZeta.lean), the standard textbook
   reflection identity zeta(s) <-> zeta(1-s).
-/

open Complex

/-- Completed zeta symmetry: xi(1 - s) = xi s for every complex s. -/
theorem completed_zeta_symmetric (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  exact completedRiemannZeta_one_sub s

/-- The regularised completed zeta also satisfies xi0(1 - s) = xi0 s. -/
theorem completed_zeta_zero_symmetric (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  exact completedRiemannZeta₀_one_sub s

/-- Classical Riemann zeta functional equation (textbook reflection form):
    zeta(1 - s) = 2 * (2 * pi)^(-s) * Gamma s * cos(pi * s / 2) * zeta s. -/
theorem zeta_functional_equation (s : ℂ)
    (hs : ∀ n : ℕ, s ≠ -↑n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) =
      2 * (2 * ↑Real.pi) ^ (-s) * Gamma s * cos (↑Real.pi * s / 2) * riemannZeta s := by
  exact riemannZeta_one_sub hs hs'

/-- The completed-zeta symmetry is an involution: reflecting twice returns. -/
theorem completed_zeta_double_reflection (s : ℂ) :
    completedRiemannZeta (1 - (1 - s)) = completedRiemannZeta s := by
  rw [completedRiemannZeta_one_sub, completedRiemannZeta_one_sub]

#print axioms completed_zeta_symmetric
#print axioms completed_zeta_zero_symmetric
#print axioms zeta_functional_equation
#print axioms completed_zeta_double_reflection
