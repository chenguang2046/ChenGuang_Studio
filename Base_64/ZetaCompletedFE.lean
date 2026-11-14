import Mathlib
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Filter Complex
open scoped Topology

namespace ZetaCompletedFE

-- =====================================================================
-- 定理 A：completedRiemannZeta 满足函数方程
--   completedRiemannZeta (1 - s) = completedRiemannZeta s
-- =====================================================================

theorem completedRiemannZeta_functional_equation (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

-- =====================================================================
-- 预备：completedRiemannZeta₀ 是整函数，在 0、1 处解析
-- 分解式：Λ s = Λ₀ s - 1/s - 1/(1-s)
-- =====================================================================

lemma completedZeta₀_analyticAt_zero : AnalyticAt ℂ completedRiemannZeta₀ 0 :=
  (differentiable_completedZeta₀).analyticAt 0

lemma completedZeta₀_analyticAt_one : AnalyticAt ℂ completedRiemannZeta₀ 1 :=
  (differentiable_completedZeta₀).analyticAt 1

lemma analyticAt_inv_one_sub_zero : AnalyticAt ℂ (fun z : ℂ => (1 - z)⁻¹) 0 := by
  have hsub : AnalyticAt ℂ (fun z : ℂ => 1 - z) 0 :=
    (analyticAt_const (v := (1 : ℂ)) (x := (0 : ℂ))).sub analyticAt_id
  have h0 : (fun z : ℂ => 1 - z) 0 ≠ 0 := by norm_num
  exact hsub.inv h0

lemma analyticAt_inv_z_one : AnalyticAt ℂ (fun z : ℂ => z⁻¹) 1 := by
  have h0 : id (1 : ℂ) ≠ 0 := by norm_num
  exact analyticAt_id.inv h0

lemma meromorphicAt_inv_z_zero : MeromorphicAt (fun z : ℂ => z⁻¹) 0 :=
  (MeromorphicAt.id (0 : ℂ)).inv

lemma completedRiemannZeta_decomp_zero :
    (fun z : ℂ => completedRiemannZeta z) =ᶠ[𝓝[≠] 0]
      (fun z => completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) := by
  filter_upwards with z
  rw [completedRiemannZeta_eq]

lemma completedRiemannZeta_decomp_one :
    (fun z : ℂ => completedRiemannZeta z) =ᶠ[𝓝[≠] 1]
      (fun z => completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) := by
  filter_upwards with z
  rw [completedRiemannZeta_eq]

-- =====================================================================
-- 定理 B：completedRiemannZeta 在 s = 0 处亚纯，且为单极点
-- =====================================================================

theorem meromorphicAt_completedRiemannZeta_zero :
    MeromorphicAt completedRiemannZeta 0 := by
  have hΛ₀ : MeromorphicAt (fun z : ℂ => completedRiemannZeta₀ z) 0 :=
    completedZeta₀_analyticAt_zero.meromorphicAt
  have h₁ : MeromorphicAt (fun z : ℂ => 1 / z) 0 := by
    simpa [one_div] using meromorphicAt_inv_z_zero
  have h₂ : MeromorphicAt (fun z : ℂ => 1 / (1 - z)) 0 := by
    simpa [one_div] using analyticAt_inv_one_sub_zero.meromorphicAt
  exact MeromorphicAt.congr (hΛ₀.sub h₁ |>.sub h₂) completedRiemannZeta_decomp_zero.symm

theorem completedRiemannZeta_simple_pole_zero :
    meromorphicOrderAt completedRiemannZeta 0 = ((-1 : ℤ) : WithTop ℤ) := by
  let D : ℂ → ℂ := fun z => completedRiemannZeta₀ z - (1 - z)⁻¹
  have hD_an : AnalyticAt ℂ D 0 := by
    dsimp [D]
    exact completedZeta₀_analyticAt_zero.sub analyticAt_inv_one_sub_zero
  have hD_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt D 0 :=
    hD_an.meromorphicOrderAt_nonneg
  have hlt0 : ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) :=
    WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < (0 : ℤ))
  have hlt : ((-1 : ℤ) : WithTop ℤ) < meromorphicOrderAt D 0 :=
    lt_of_lt_of_le hlt0 hD_nonneg
  have h₁ : meromorphicOrderAt (fun z : ℂ => -1 / z) 0 = ((-1 : ℤ) : WithTop ℤ) := by
    have hzpow : meromorphicOrderAt (fun z : ℂ => (z - 0) ^ (-1 : ℤ)) 0 =
        ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_zpow_id_sub_const (𝕜 := ℂ) (x := 0) (n := (-1 : ℤ))
    have hzpow' : meromorphicOrderAt (fun z : ℂ => z⁻¹) 0 = ((-1 : ℤ) : WithTop ℤ) := by
      simpa using hzpow
    calc
      meromorphicOrderAt (fun z : ℂ => -1 / z) 0
          = meromorphicOrderAt (fun z : ℂ => -z⁻¹) 0 := by
              apply meromorphicOrderAt_congr
              filter_upwards with z
              simp [div_eq_mul_inv]
      _ = meromorphicOrderAt (fun z : ℂ => z⁻¹) 0 := by
              exact (meromorphicOrderAt_neg (𝕜 := ℂ) (E := ℂ) (x := 0)
                (f := fun z : ℂ => z⁻¹)).symm
      _ = ((-1 : ℤ) : WithTop ℤ) := hzpow'
  have hlt' : meromorphicOrderAt (fun z : ℂ => -1 / z) 0 < meromorphicOrderAt D 0 := by
    simpa [h₁] using hlt
  have hsum0 : meromorphicOrderAt ((fun z : ℂ => -1 / z) + D) 0 =
      meromorphicOrderAt (fun z : ℂ => -1 / z) 0 :=
    meromorphicOrderAt_add_eq_left_of_lt (f₁ := fun z : ℂ => -1 / z) (f₂ := D)
      (hD_an.meromorphicAt) hlt'
  have hsum : meromorphicOrderAt (fun z : ℂ => -1 / z + D z) 0 =
      ((-1 : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt ((fun z : ℂ => -1 / z) + D) 0 = ((-1 : ℤ) : WithTop ℤ)
    rw [hsum0, h₁]
  have hfg : (fun z : ℂ => -1 / z + D z) =ᶠ[𝓝[≠] 0] completedRiemannZeta := by
    filter_upwards with z
    rw [completedRiemannZeta_eq]
    simp [D, div_eq_mul_inv]
    ring_nf
  rw [← meromorphicOrderAt_congr hfg]
  exact hsum

-- =====================================================================
-- 定理 C：completedRiemannZeta 在 s = 1 处亚纯，且为单极点
-- =====================================================================

theorem meromorphicAt_completedRiemannZeta_one :
    MeromorphicAt completedRiemannZeta 1 := by
  have hΛ₀ : MeromorphicAt (fun z : ℂ => completedRiemannZeta₀ z) 1 :=
    completedZeta₀_analyticAt_one.meromorphicAt
  have h₁ : MeromorphicAt (fun z : ℂ => 1 / z) 1 := by
    simpa [one_div] using analyticAt_inv_z_one.meromorphicAt
  have h₂ : MeromorphicAt (fun z : ℂ => 1 / (1 - z)) 1 := by
    have hsub : MeromorphicAt (fun z : ℂ => 1 - z) 1 :=
      (MeromorphicAt.const (1 : ℂ) 1).sub (MeromorphicAt.id 1)
    have hinv : MeromorphicAt (fun z : ℂ => (1 - z)⁻¹) 1 := hsub.inv
    simpa [one_div] using hinv
  exact MeromorphicAt.congr (hΛ₀.sub h₁ |>.sub h₂) completedRiemannZeta_decomp_one.symm

theorem completedRiemannZeta_simple_pole_one :
    meromorphicOrderAt completedRiemannZeta 1 = ((-1 : ℤ) : WithTop ℤ) := by
  let E : ℂ → ℂ := fun z => completedRiemannZeta₀ z - z⁻¹
  have hE_an : AnalyticAt ℂ E 1 := by
    dsimp [E]
    exact completedZeta₀_analyticAt_one.sub analyticAt_inv_z_one
  have hE_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt E 1 :=
    hE_an.meromorphicOrderAt_nonneg
  have hlt0 : ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) :=
    WithTop.coe_lt_coe.mpr (by norm_num : (-1 : ℤ) < (0 : ℤ))
  have hlt : ((-1 : ℤ) : WithTop ℤ) < meromorphicOrderAt E 1 :=
    lt_of_lt_of_le hlt0 hE_nonneg
  have h₁ : meromorphicOrderAt (fun z : ℂ => -1 / (1 - z)) 1 = ((-1 : ℤ) : WithTop ℤ) := by
    have hzpow : meromorphicOrderAt (fun z : ℂ => (z - 1) ^ (-1 : ℤ)) 1 =
        ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_zpow_id_sub_const (𝕜 := ℂ) (x := 1) (n := (-1 : ℤ))
    have hzpow' : meromorphicOrderAt (fun z : ℂ => (z - 1)⁻¹) 1 = ((-1 : ℤ) : WithTop ℤ) := by
      simpa using hzpow
    calc
      meromorphicOrderAt (fun z : ℂ => -1 / (1 - z)) 1
          = meromorphicOrderAt (fun z : ℂ => (z - 1)⁻¹) 1 := by
              apply meromorphicOrderAt_congr
              filter_upwards with z
              rw [div_eq_mul_inv]
              rw [show (1 - z)⁻¹ = (-(z - 1))⁻¹ by
                rw [show 1 - z = -(z - 1) by ring]]
              rw [inv_neg]
              simp
      _ = ((-1 : ℤ) : WithTop ℤ) := hzpow'
  have hlt' : meromorphicOrderAt (fun z : ℂ => -1 / (1 - z)) 1 < meromorphicOrderAt E 1 := by
    simpa [h₁] using hlt
  have hsum0 : meromorphicOrderAt ((fun z : ℂ => -1 / (1 - z)) + E) 1 =
      meromorphicOrderAt (fun z : ℂ => -1 / (1 - z)) 1 :=
    meromorphicOrderAt_add_eq_left_of_lt (f₁ := fun z : ℂ => -1 / (1 - z)) (f₂ := E)
      (hE_an.meromorphicAt) hlt'
  have hsum : meromorphicOrderAt (fun z : ℂ => -1 / (1 - z) + E z) 1 =
      ((-1 : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt ((fun z : ℂ => -1 / (1 - z)) + E) 1 = ((-1 : ℤ) : WithTop ℤ)
    rw [hsum0, h₁]
  have hfg : (fun z : ℂ => -1 / (1 - z) + E z) =ᶠ[𝓝[≠] 1] completedRiemannZeta := by
    filter_upwards with z
    rw [completedRiemannZeta_eq]
    simp [E, div_eq_mul_inv]
    ring_nf
  rw [← meromorphicOrderAt_congr hfg]
  exact hsum

-- =====================================================================
-- 定理 D：留数——s = 0 处留数为 -1（s = 1 处留数为 1，mathlib 已证）
-- =====================================================================

theorem completedRiemannZeta_residue_zero :
    Tendsto (fun z : ℂ => z * completedRiemannZeta z) (𝓝[≠] 0) (𝓝 (-1)) := by
  have hdecomp : (fun z : ℂ => z * completedRiemannZeta z) =ᶠ[𝓝[≠] 0]
      fun z => z * completedRiemannZeta₀ z - 1 - z / (1 - z) := by
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards with z
    intro hz
    have hz0 : z ≠ 0 := by simpa using hz
    rw [completedRiemannZeta_eq]
    rw [mul_sub, mul_sub]
    simp [div_eq_mul_inv, mul_inv_cancel₀ hz0]
  have hz₀ : Tendsto (fun z : ℂ => z * completedRiemannZeta₀ z) (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt completedRiemannZeta₀ 0 :=
      (differentiable_completedZeta₀).continuous.continuousAt
    have hmain : Tendsto (fun z : ℂ => z * completedRiemannZeta₀ z) (𝓝 0) (𝓝 0) := by
      simpa using ((Filter.tendsto_id (x := 𝓝 (0 : ℂ))).mul hc.tendsto)
    exact tendsto_nhdsWithin_of_tendsto_nhds hmain
  have hc1 : ContinuousAt (fun z : ℂ => (1 - z)⁻¹) 0 := by
    apply ContinuousAt.inv₀
    · exact continuousAt_const.sub continuousAt_id
    · norm_num
  have hz1 : Tendsto (fun z : ℂ => z / (1 - z)) (𝓝[≠] 0) (𝓝 0) := by
    have hmain : Tendsto (fun z : ℂ => z * (1 - z)⁻¹) (𝓝 0) (𝓝 0) := by
      simpa using ((Filter.tendsto_id (x := 𝓝 (0 : ℂ))).mul hc1.tendsto)
    exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa [div_eq_mul_inv] using hmain)
  refine (Filter.Tendsto.congr' hdecomp.symm) ?_
  have hmid : Tendsto (fun z : ℂ => z * completedRiemannZeta₀ z - 1) (𝓝[≠] 0) (𝓝 (0 - 1)) :=
    hz₀.sub tendsto_const_nhds
  have hfin : Tendsto (fun z : ℂ => (z * completedRiemannZeta₀ z - 1) - z / (1 - z))
      (𝓝[≠] 0) (𝓝 ((0 - 1) - 0)) :=
    hmid.sub hz1
  simpa using hfin

-- =====================================================================
-- 汇总命题
-- =====================================================================

theorem completedRiemannZeta_functional_equation_and_poles :
    (∀ s : ℂ, completedRiemannZeta (1 - s) = completedRiemannZeta s) ∧
    meromorphicOrderAt completedRiemannZeta 0 = ((-1 : ℤ) : WithTop ℤ) ∧
    meromorphicOrderAt completedRiemannZeta 1 = ((-1 : ℤ) : WithTop ℤ) ∧
    MeromorphicAt completedRiemannZeta 0 ∧ MeromorphicAt completedRiemannZeta 1 := by
  exact ⟨completedRiemannZeta_functional_equation, completedRiemannZeta_simple_pole_zero,
    completedRiemannZeta_simple_pole_one, meromorphicAt_completedRiemannZeta_zero,
    meromorphicAt_completedRiemannZeta_one⟩

end ZetaCompletedFE

-- 公理审计
#print axioms ZetaCompletedFE.completedRiemannZeta_functional_equation
#print axioms ZetaCompletedFE.completedRiemannZeta_simple_pole_zero
#print axioms ZetaCompletedFE.completedRiemannZeta_simple_pole_one
#print axioms ZetaCompletedFE.meromorphicAt_completedRiemannZeta_zero
#print axioms ZetaCompletedFE.meromorphicAt_completedRiemannZeta_one
#print axioms ZetaCompletedFE.completedRiemannZeta_residue_zero
#print axioms ZetaCompletedFE.completedRiemannZeta_functional_equation_and_poles

