import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Universal Slice 017: Functional equations of the Gamma function

This slice verifies the functional equation Gamma (s + 1) = s * Gamma s,
the connection with factorials Gamma (n + 1) = n!, the value Gamma 1 = 1,
and positivity and nonvanishing on the real positive axis.
-/

noncomputable section

namespace UniversalSlice017

open Complex

-- Complex functional equation: Gamma (s + 1) = s * Gamma s for s ≠ 0.
theorem gamma_add_one_complex (s : ℂ) (hs : s ≠ 0) :
    Gamma (s + 1) = s * Gamma s :=
  Complex.Gamma_add_one s hs

-- Complex value at 1.
theorem gamma_one_complex : Gamma (1 : ℂ) = 1 :=
  Complex.Gamma_one

-- Complex factorial relation: Gamma (n + 1) = n!.
theorem gamma_nat_eq_factorial_complex (n : ℕ) :
    Gamma (n + 1 : ℂ) = (n.factorial : ℂ) :=
  Complex.Gamma_nat_eq_factorial n

-- Real functional equation.
theorem gamma_add_one_real (s : ℝ) (hs : s ≠ 0) :
    Real.Gamma (s + 1) = s * Real.Gamma s :=
  Real.Gamma_add_one hs

-- Real value at 1.
theorem gamma_one_real : Real.Gamma 1 = 1 :=
  Real.Gamma_one

-- Real factorial relation.
theorem gamma_nat_eq_factorial_real (n : ℕ) :
    Real.Gamma (n + 1) = (n.factorial : ℝ) :=
  Real.Gamma_nat_eq_factorial n

-- Positivity on the positive real axis.
theorem gamma_pos_of_pos (s : ℝ) (hs : 0 < s) : 0 < Real.Gamma s :=
  Real.Gamma_pos_of_pos hs

-- Nonvanishing away from the nonpositive integers.
theorem gamma_ne_zero_real {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : Real.Gamma s ≠ 0 :=
  Real.Gamma_ne_zero hs

end UniversalSlice017
