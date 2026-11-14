import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

/-!
# Universal Slice 018: Further properties of spaces of modular forms

This slice verifies that constant functions of weight zero are modular
forms, and that the space of cusp forms embeds into the space of modular
forms as a linear subspace, linearly equivalent to the cusp form submodule.

References:
`ModularForm.const`, `ModularForm.const_apply`,
`CuspForm.toModularFormₗ`, `CuspForm.toModularFormₗ_injective`,
`ModularForm.cuspFormSubmodule`, `CuspForm.equivCuspFormSubmodule`,
`ModularForm.IsCuspForm`, `ModularForm.mem_cuspFormSubmodule_iff`.
-/

noncomputable section

namespace UniversalSlice018

open ModularForm
open scoped UpperHalfPlane

/-- The constant function with value x is a modular form of weight 0. -/
noncomputable def const_zero_weight_def (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    (x : ℂ) : ModularForm Γ 0 :=
  ModularForm.const x

/-- Its pointwise value is the constant x. -/
theorem const_apply_def (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] (x : ℂ) (τ : ℍ) :
    (ModularForm.const x : ModularForm Γ 0) τ = x :=
  ModularForm.const_apply x τ

/-- The inclusion of cusp forms into modular forms is injective. -/
theorem cusp_to_modular_injective_def (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    (k : ℤ) :
    Function.Injective (CuspForm.toModularFormₗ : CuspForm Γ k → ModularForm Γ k) :=
  CuspForm.toModularFormₗ_injective

/-- The cusp form submodule is linearly equivalent to the type of cusp forms. -/
noncomputable def cusp_equiv_submodule_def (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    (k : ℤ) : CuspForm Γ k ≃ₗ[ℂ] ModularForm.cuspFormSubmodule Γ k :=
  CuspForm.equivCuspFormSubmodule Γ k

/-- Membership in the cusp form submodule is exactly the predicate IsCuspForm. -/
theorem mem_cusp_submodule_iff_def (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    {f : ModularForm Γ 0} :
    f ∈ ModularForm.cuspFormSubmodule Γ 0 ↔ ModularForm.IsCuspForm f :=
  ModularForm.mem_cuspFormSubmodule_iff

end UniversalSlice018
