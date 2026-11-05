import Slices_99.Challenge_104_Gamma0_Dimension
import Mathlib.NumberTheory.ModularForms.NormTrace

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open Challenge021Gamma0NIndex Challenge104Gamma0Dimension

noncomputable section

namespace Probe104c

-- Q1: Gamma0GL N ≤ 𝒮ℒ
example (N : ℕ) : Gamma0GL N ≤ 𝒮ℒ := by
  rw [MonoidHom.range_eq_map]
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
  exact fun hz => hf (DFunLike.coe_injective hz)

-- Q6: qExpansion_mul 对 𝒮ℒ 可用（任意 Γ 泛化）
example (k : ℤ) (f g : ModularForm 𝒮ℒ k) :
    qExpansion 1 (f * g) = qExpansion 1 f * qExpansion 1 g := by
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g]

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
  exact ModularForm.qExpansionAddHom one_pos one_mem_strictPeriods_SL k (f + g)

-- Q10: coeff 线性（PowerSeries.coeff）
example (i : ℕ) (a : ℂ) (p q : PowerSeries ℂ) :
    PowerSeries.coeff i (a • p + q) = a • PowerSeries.coeff i p + PowerSeries.coeff i q := by
  simp [Pi.add_apply, Pi.smul_apply]

-- Q11: qExpansion_smul 对 𝒮ℒ
example (k : ℤ) (a : ℂ) (f : ModularForm 𝒮ℒ k) :
    qExpansion 1 (a • f) = a • qExpansion 1 f := by
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL a f]

end Probe104c

end
