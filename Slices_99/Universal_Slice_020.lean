import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-! # Universal_Slice_020 — E₂ / G₂ 与斜杠作用（ChenGuang Studio，30 行精简版） -/
open UpperHalfPlane ModularForm EisensteinSeries Matrix.SpecialLinearGroup Filter Complex MatrixGroups SummationFilter Real
open scoped MatrixGroups

namespace UniversalSlice020

lemma e2Summand_const_term (z : ℍ) : EisensteinSeries.e2Summand 0 z = 2 * riemannZeta 2 := EisensteinSeries.e2Summand_zero_eq_two_riemannZeta_two z
lemma e2Summand_summable (m : ℤ) (z : ℍ) : Summable (fun n : ℤ => EisensteinSeries.eisSummand 2 ![m, n] z) := EisensteinSeries.e2Summand_summable m z
lemma G2_definition (z : ℍ) : EisensteinSeries.G2 z = ∑'[symmetricIcc ℤ] m, EisensteinSeries.e2Summand m z := rfl
lemma E2_definition (z : ℍ) : EisensteinSeries.E2 z = (1 / (2 * riemannZeta 2)) • EisensteinSeries.G2 z := rfl
lemma D2_one : EisensteinSeries.D2 (1 : SL(2, ℤ)) = 0 := EisensteinSeries.D2_one
lemma D2_cocycle (A B : SL(2, ℤ)) : EisensteinSeries.D2 (A * B) = (EisensteinSeries.D2 A) ∣[(2 : ℤ)] B + EisensteinSeries.D2 B := EisensteinSeries.D2_mul A B
lemma D2_T : EisensteinSeries.D2 ModularGroup.T = 0 := EisensteinSeries.D2_T
lemma E2_T_invariant : EisensteinSeries.E2 ∣[(2 : ℤ)] ModularGroup.T = EisensteinSeries.E2 := EisensteinSeries.E2_T_transform
lemma E2_slash_action (γ : SL(2, ℤ)) : EisensteinSeries.E2 ∣[(2 : ℤ)] γ = EisensteinSeries.E2 - (1 / (2 * riemannZeta 2)) • EisensteinSeries.D2 γ := EisensteinSeries.E2_slash_action γ

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
