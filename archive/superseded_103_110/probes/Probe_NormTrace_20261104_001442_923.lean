import Slices_99.Challenge_104_Gamma0_Dimension
import Mathlib.NumberTheory.ModularForms.NormTrace

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup
open Challenge021Gamma0NIndex Challenge104Gamma0Dimension

noncomputable section

namespace Probe104b

-- Q1: Gamma0GL N ≤ 𝒮ℒ
example (N : ℕ) : Gamma0GL N ≤ 𝒮ℒ := by
  change (gamma0_N N).map (mapGL ℝ) ≤ (⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)
  exact Subgroup.map_le_map (mapGL ℝ) (le_top : gamma0_N N ≤ ⊤)

-- Q2: relIndex 实例
example (N : ℕ) [NeZero N] : (Gamma0GL N).IsFiniteRelIndex 𝒮ℒ := by
  infer_instance

-- Q3: HasDetPlusMinusOne 𝒮ℒ
example : Subgroup.HasDetPlusMinusOne 𝒮ℒ := by
  infer_instance

-- Q4: norm 的类型（weight 提升）
example (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma0GL N) k) :
    ModularForm 𝒮ℒ (k * Nat.card (𝒮ℒ ⧸ (Gamma0GL N).subgroupOf 𝒮ℒ)) :=
  ModularForm.norm 𝒮ℒ f

-- Q5: norm_ne_zero 可用（CuspForm 输入）
example (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma0GL N) k) (hf : f ≠ 0) :
    ModularForm.norm 𝒮ℒ f ≠ 0 := by
  apply ModularForm.norm_ne_zero
  exact DFunLike.ne_iff.mp hf

-- Q6: qExpansion_mul 对 𝒮ℒ 可用（任意 Γ 泛化）
example (k : ℤ) (f g : ModularForm 𝒮ℒ k) :
    qExpansion 1 (f * g) = qExpansion 1 f * qExpansion 1 g := by
  rw [ModularForm.qExpansion_mul (𝒢 := 𝒮ℒ) (h := 1) (by norm_num : (0 : ℝ) < 1)]

-- Q7: sturm_bound_levelOne 可用
example (k : ℤ) (f : ModularForm 𝒮ℒ k)
    (h : (↑(k.toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 :=
  ModularForm.sturm_bound_levelOne h

-- Q8: PowerSeries.order_mul
example (p q : PowerSeries ℂ) : (p * q).order = p.order + q.order := by
  rw [PowerSeries.order_mul]

-- Q9: qExpansionAddHom 加法性
example (k : ℤ) (f g : ModularForm 𝒮ℒ k) :
    qExpansion 1 (f + g) = qExpansion 1 f + qExpansion 1 g := by
  exact ModularForm.qExpansionAddHom (h := 1) (by norm_num : (0 : ℝ) < 1) f g

-- Q10: coeff 线性（PowerSeries.coeff）
example (i : ℕ) (a : ℂ) (p q : PowerSeries ℂ) :
    PowerSeries.coeff ℂ i (a • p + q) = a • PowerSeries.coeff ℂ i p + PowerSeries.coeff ℂ i q := by
  simp [Pi.add_apply, Pi.smul_apply]

end Probe104b

end
