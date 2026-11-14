import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
BSD_Ext_Slice_004 : Basic facts about modular forms.

Uses mathlib's `ModularForm`, `CuspForm` structures and the
`ModularFormClass` level-one facts: negative weight level-one
modular forms vanish, and weight-zero level-one modular forms are
constant.
-/

open scoped MatrixGroups
open ModularForm ModularFormClass

namespace BSDExtSlice004

-- A level-one modular form of negative weight is zero.
theorem levelOne_neg_weight_eq_zero {k : ℤ} (hk : k < 0)
    (f : ModularForm 𝒮ℒ k) : ⇑f = 0 :=
  ModularFormClass.levelOne_neg_weight_eq_zero hk f

-- A level-one modular form of weight zero is constant.
theorem levelOne_weight_zero_const (f : ModularForm 𝒮ℒ 0) :
    ∃ c : ℂ, ⇑f = Function.const UpperHalfPlane c :=
  ModularFormClass.levelOne_weight_zero_const f

-- Extensionality for modular forms (functions agreeing pointwise coincide).
theorem ext_of_fun_eq {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    {f g : ModularForm Γ k} (h : ∀ τ : UpperHalfPlane, f τ = g τ) : f = g :=
  ModularForm.ext h

-- Extensionality for cusp forms.
theorem cusp_ext_of_fun_eq {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    {f g : CuspForm Γ k} (h : ∀ τ : UpperHalfPlane, f τ = g τ) : f = g :=
  CuspForm.ext h

-- The constant modular form of weight 0 evaluates to its constant.
theorem const_apply_value {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (x : ℂ) (τ : UpperHalfPlane) : (ModularForm.const x : ModularForm Γ 0) τ = x :=
  ModularForm.const_apply x τ

end BSDExtSlice004


#print axioms BSDExtSlice004.levelOne_neg_weight_eq_zero
#print axioms BSDExtSlice004.levelOne_weight_zero_const
#print axioms BSDExtSlice004.ext_of_fun_eq
#print axioms BSDExtSlice004.cusp_ext_of_fun_eq
#print axioms BSDExtSlice004.const_apply_value
