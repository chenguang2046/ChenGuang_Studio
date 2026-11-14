import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

/-!
# Universal Slice 011: Closure properties of modular form spaces

The `NumberTheory.ModularForms` directory of mathlib does not currently contain a
Hecke operator definition, so we follow the documented degradation route and verify
basic closure properties of modular form spaces:  the space `SlashInvariantForm Γ k`
is an additive commutative group (closed under pointwise addition) and, over a
subgroup with determinant one, a complex module (closed under scalar
multiplication); and the weight-`k` slash action is multiplicative in the weight:
`(f * g) ∣[k₁+k₂] A = (f ∣[k₁] A) * (g ∣[k₂] A)` for every `A : SL(2, ℤ)`.

References:
`SlashInvariantForm.instAdd`, `SlashInvariantForm.instModuleComplex`,
`SlashInvariantForm.slash_action_eqn`, `ModularForm.mul_slash_SL2`.
-/

namespace Slice011

/-- The space `SlashInvariantForm Γ k` carries an additive commutative group
structure, hence is closed under pointwise addition, negation and subtraction. -/
theorem addCommGroup_instance (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    Nonempty (AddCommGroup (SlashInvariantForm Γ k)) :=
  ⟨inferInstance⟩

/-- Over a subgroup with determinant one, the space `SlashInvariantForm Γ k`
carries a complex module structure, hence is closed under scalar multiplication. -/
theorem module_instance (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] (k : ℤ) :
    Nonempty (Module ℂ (SlashInvariantForm Γ k)) :=
  ⟨inferInstance⟩

/-- The sum of two slash-invariant forms of weight `k` is again invariant under the
same subgroup: for every `γ ∈ Γ`, applying the weight-`k` slash action to the sum
leaves it unchanged. -/
theorem add_slash_invariant (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (f g : SlashInvariantForm Γ k) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Γ) :
    SlashAction.map k γ ((f + g : SlashInvariantForm Γ k) : UpperHalfPlane → ℂ) =
      ((f + g : SlashInvariantForm Γ k) : UpperHalfPlane → ℂ) :=
  SlashInvariantForm.slash_action_eqn (f := f + g) γ hγ

/-- The slash action is multiplicative in the weight: transforming the pointwise
product of two functions with weight `k₁ + k₂` equals the product of the individual
transforms with weights `k₁` and `k₂`. -/
theorem mul_slash_weight_add (k₁ k₂ : ℤ) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (f g : UpperHalfPlane → ℂ) :
    SlashAction.map (k₁ + k₂) A (f * g) = SlashAction.map k₁ A f * SlashAction.map k₂ A g :=
  ModularForm.mul_slash_SL2 k₁ k₂ A f g

end Slice011
