import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Slice 004: Gamma reflection formula

For any complex number z which is not an integer,
the reflection formula states

  Gamma(z) * Gamma(1 - z) = pi / sin(pi * z).

mathlib provides the unconditional statement
`Complex.Gamma_mul_Gamma_one_sub`, which is exactly the identity
(in particular it holds for all non-integer z).
-/

theorem gamma_reflection (z : Complex) :
    Complex.Gamma z * Complex.Gamma (1 - z) =
      (Real.pi : Complex) / Complex.sin ((Real.pi : Complex) * z) := by
  exact Complex.Gamma_mul_Gamma_one_sub z
