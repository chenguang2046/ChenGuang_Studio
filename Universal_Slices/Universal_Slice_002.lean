/-
Universal_Slice_002: The Gamma factor pi^(-s/2) * Gamma(s/2)
(验证 Gamma 因子的解析与亚纯性质)

Content:
  1. gammaFactor: definition of the Gamma factor pi^(-s/2) * Gamma(s/2).
  2. gammaFactor_ne_zero_of_re_pos: zero-free in the right half-plane.
  3. gammaReflection: Euler reflection formula
     Gamma z * Gamma (1 - z) = pi / sin (pi * z).
  4. gamma_differentiableAt: Gamma is differentiable away from
     the nonpositive integers.
  5. gamma_not_continuousAt_neg_nat: Gamma is discontinuous at negative
     integers (simple poles).
  6. inv_gamma_differentiable: the reciprocal 1/Gamma is entire.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

noncomputable section

open Complex
open scoped Real
open scoped Topology
open scoped BigOperators

namespace UniversalSlice002

/-- The Gamma factor pi^(-s/2) * Gamma(s/2) occurring in the functional
    equation of the Riemann zeta function. -/
noncomputable def gammaFactor (s : ℂ) : ℂ := (π : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)

/-- The Gamma factor has no zeros in the right half-plane Re(s/2) > 0. -/
theorem gammaFactor_ne_zero_of_re_pos {s : ℂ} (hs : 0 < (s / 2).re) : gammaFactor s ≠ 0 := by
  unfold gammaFactor
  apply mul_ne_zero
  · exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · exact Complex.Gamma_ne_zero_of_re_pos hs

/-- Euler's reflection formula for the complex Gamma function. -/
theorem gammaReflection (z : ℂ) :
    Complex.Gamma z * Complex.Gamma (1 - z) = (π : ℂ) / Complex.sin (π * z) := by
  exact Complex.Gamma_mul_Gamma_one_sub z

/-- Gamma is differentiable (hence analytic) at every point that is not a
    nonpositive integer. -/
theorem gamma_differentiableAt (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) :
    DifferentiableAt ℂ Complex.Gamma s :=
  Complex.differentiableAt_Gamma s hs

/-- Gamma is discontinuous at every negative integer: the poles of the
    Gamma factor. -/
theorem gamma_not_continuousAt_neg_nat (n : ℕ) :
    ¬ ContinuousAt Complex.Gamma (-(n : ℂ)) :=
  Complex.not_continuousAt_Gamma_neg_nat n

/-- The reciprocal 1/Gamma is differentiable everywhere (an entire function). -/
theorem inv_gamma_differentiable :
    Differentiable ℂ (fun w : ℂ => (Complex.Gamma w)⁻¹) :=
  Complex.differentiable_one_div_Gamma

end UniversalSlice002
