import Slices_99.Challenge_104_Gamma0_Dimension
import Mathlib.NumberTheory.ModularForms.NormTrace

open scoped BigOperators MatrixGroups
open Challenge104Gamma0Dimension

noncomputable section

namespace Probe104

-- P1: Gamma0GL N ≤ 𝒮ℒ
example (N : ℕ) : Gamma0GL N ≤ 𝒮ℒ := by
  change (gamma0_N N).map (mapGL ℝ) ≤ (⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)
  exact Subgroup.map_le_map (mapGL ℝ) (le_top : gamma0_N N ≤ ⊤)

-- P2: relIndex 实例
example (N : ℕ) [NeZero N] : (Gamma0GL N).IsFiniteRelIndex 𝒮ℒ := by
  infer_instance

-- P3: HasDetPlusMinusOne 𝒮ℒ
example : Subgroup.HasDetPlusMinusOne 𝒮ℒ := by
  infer_instance

-- P4: Module ℂ (CuspForm (Gamma0GL N) k)
example (N : ℕ) [NeZero N] (k : ℤ) : Module ℂ (CuspForm (Gamma0GL N) k) := by
  infer_instance

-- P5: norm 应用于 CuspForm → ModularForm 𝒮ℒ (k*relIndex)
example (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma0GL N) k) :
    ModularForm 𝒮ℒ (k * Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ)) :=
  ModularForm.norm 𝒮ℒ f

-- P6: CuspForm.trace
example (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma0GL N) k) : CuspForm 𝒮ℒ k :=
  CuspForm.trace 𝒮ℒ f

-- P7: isZero_of_neg_weight 应用到 ModularForm
example (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) (f : ModularForm (Gamma0GL N) k) : f = 0 :=
  ModularForm.isZero_of_neg_weight hk f

-- P8: toModularFormₗ
example (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma0GL N) k) : ModularForm (Gamma0GL N) k :=
  CuspForm.toModularFormₗ f

-- P9: k<0 时 CuspForm 是 Subsingleton
example (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) :
    Subsingleton (CuspForm (Gamma0GL N) k) := by
  refine ⟨fun f g => ?_⟩
  apply CuspForm.toModularFormₗ_injective
  rw [ModularForm.isZero_of_neg_weight hk (CuspForm.toModularFormₗ f),
    ModularForm.isZero_of_neg_weight hk (CuspForm.toModularFormₗ g)]

-- P10: k<0 时有限维（infer_instance 是否自动）
example (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) :
    FiniteDimensional ℂ (CuspForm (Gamma0GL N) k) := by
  infer_instance

end Probe104

end
