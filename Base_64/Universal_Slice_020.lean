import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# Eisenstein series of weight 2: baseline verification

mathlib's `NumberTheory.ModularForms.EisensteinSeries` provides, at the level of
weight `2` and level `1`, the raw sums `e2Summand`, the conditionally summed
series `G2`, its normalisation `E2 = (1 / (2 ζ(2))) • G2`, and the defect
function `D2` which measures the failure of the weight-`2` transformation law.

This file verifies, by direct reference to the corresponding mathlib lemmas, the
most basic facts of this layer:

* the constant term `e2Summand 0 z = 2 ζ(2)`;
* the defining conditional sums of `G2` and the normalisation `E2`;
* the basic properties of the defect `D2` (identity, cocycle rule, vanishing on `T`);
* the invariance of `E2` under the translation `T` and the defect term in the full
  `SL(2, ℤ)` action, which prevents `E2` from being a modular form.

For completeness we also record that mathlib goes beyond weight `2`: normalised
Eisenstein series of weight `k ≥ 3` are available as modular forms
(`ModularForm.E`, with the instances `E₄` and `E₆`).

No new analytic content is developed; every statement below is a direct
consequence of an existing mathlib lemma.
-/


open UpperHalfPlane

open ModularForm EisensteinSeries Matrix.SpecialLinearGroup Filter Complex MatrixGroups
  SummationFilter Real

open scoped MatrixGroups

namespace UniversalSlice020

/-! ## The summands of the weight-2 series -/

/-- The `m = 0` summand of the weight-2 Eisenstein series equals `2 ζ(2)`
for every point `z` of the upper half plane. -/
lemma e2Summand_const_term (z : ℍ) : EisensteinSeries.e2Summand 0 z = 2 * riemannZeta 2 :=
  EisensteinSeries.e2Summand_zero_eq_two_riemannZeta_two z

/-- The sequence of summands is summable for every fixed `m` and `z`. -/
lemma e2Summand_summable (m : ℤ) (z : ℍ) :
    Summable (fun n : ℤ => eisSummand 2 ![m, n] z) :=
  EisensteinSeries.e2Summand_summable m z

/-! ## The series `G2` and its normalisation `E2` -/

/-- `G2` is defined as the conditional sum of `e2Summand m` over the symmetric
interval `[-N, N]`. -/
lemma G2_definition (z : ℍ) :
    EisensteinSeries.G2 z = ∑'[symmetricIcc ℤ] m, EisensteinSeries.e2Summand m z :=
  rfl

/-- The normalised weight-2 series: `E2 = (1 / (2 ζ(2))) • G2`. -/
lemma E2_definition (z : ℍ) :
    EisensteinSeries.E2 z = (1 / (2 * riemannZeta 2)) • EisensteinSeries.G2 z :=
  rfl

/-! ## The defect function `D2` -/

/-- The defect vanishes at the identity. -/
lemma D2_one : EisensteinSeries.D2 (1 : SL(2, ℤ)) = 0 :=
  EisensteinSeries.D2_one

/-- The defect satisfies the cocycle rule of the weight-2 action. -/
lemma D2_cocycle (A B : SL(2, ℤ)) :
    EisensteinSeries.D2 (A * B) =
      (EisensteinSeries.D2 A) ∣[(2 : ℤ)] B + EisensteinSeries.D2 B :=
  EisensteinSeries.D2_mul A B

/-- The defect vanishes on the translation `T`. -/
lemma D2_T : EisensteinSeries.D2 ModularGroup.T = 0 :=
  EisensteinSeries.D2_T

/-! ## Transformation of `E2` under `SL(2, ℤ)` -/

/-- `E2` is invariant under the translation `T`. -/
lemma E2_T_invariant :
    EisensteinSeries.E2 ∣[(2 : ℤ)] ModularGroup.T = EisensteinSeries.E2 :=
  EisensteinSeries.E2_T_transform

/-- The full action of `γ ∈ SL(2, ℤ)` on `E2` carries the defect term
`(1 / (2 ζ(2))) • D2 γ`; this is precisely the obstruction to `E2` being a
modular form. -/
lemma E2_slash_action (γ : SL(2, ℤ)) :
    EisensteinSeries.E2 ∣[(2 : ℤ)] γ =
      EisensteinSeries.E2 - (1 / (2 * riemannZeta 2)) • EisensteinSeries.D2 γ :=
  EisensteinSeries.E2_slash_action γ

/-! ## Recorded baseline beyond weight 2 -/

-- mathlib additionally provides normalised Eisenstein series of weight `k ≥ 3`
-- and level 1 as modular forms: `ModularForm.E`, with instances `E₄` (weight 4)
-- and `E₆` (weight 6). This is recorded here for completeness; the weight-2
-- verification above is the scope of this file.

end UniversalSlice020

#print axioms UniversalSlice020.e2Summand_const_term
#print axioms UniversalSlice020.e2Summand_summable
#print axioms UniversalSlice020.G2_definition
#print axioms UniversalSlice020.E2_definition
#print axioms UniversalSlice020.D2_one
#print axioms UniversalSlice020.D2_cocycle
#print axioms UniversalSlice020.D2_T
#print axioms UniversalSlice020.E2_T_invariant
#print axioms UniversalSlice020.E2_slash_action
