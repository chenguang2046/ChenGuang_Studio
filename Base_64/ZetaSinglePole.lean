import Mathlib

open Complex Filter
open scoped Topology

noncomputable section

namespace ZetaSinglePole

-- s ↦ s / (1 - s) 在 s = 1 处亚纯
lemma meromorphicAt_self_div_one_sub_one :
    MeromorphicAt (fun s : ℂ => s / (1 - s)) 1 := by
  have hid : MeromorphicAt (fun s : ℂ => s) 1 := by
    exact MeromorphicAt.id (1 : ℂ)
  have hsub : AnalyticAt ℂ (fun s : ℂ => 1 - s) 1 :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 1).sub analyticAt_id
  have hsubM : MeromorphicAt (fun s : ℂ => 1 - s) 1 := hsub.meromorphicAt
  have hinv : MeromorphicAt (fun s : ℂ => (1 - s)⁻¹) 1 := hsubM.inv
  exact MeromorphicAt.mul hid hinv

-- 分子 s ↦ s * completedRiemannZeta₀ s - 1 - s / (1 - s) 在 s = 1 处亚纯
lemma meromorphicAt_num :
    MeromorphicAt (fun s : ℂ => s * completedRiemannZeta₀ s - 1 - s / (1 - s)) 1 := by
  have hA : AnalyticAt ℂ (fun s : ℂ => s * completedRiemannZeta₀ s) 1 :=
    AnalyticAt.mul analyticAt_id ((Differentiable.analyticAt differentiable_completedZeta₀) 1)
  have hA' : MeromorphicAt (fun s : ℂ => s * completedRiemannZeta₀ s) 1 := hA.meromorphicAt
  have hC : MeromorphicAt (fun _ : ℂ => (-1 : ℂ)) 1 := MeromorphicAt.const (-1) 1
  have hB : MeromorphicAt (fun s : ℂ => s / (1 - s)) 1 := meromorphicAt_self_div_one_sub_one
  have h1 : MeromorphicAt (fun s : ℂ => s * completedRiemannZeta₀ s + (-1 : ℂ)) 1 :=
    MeromorphicAt.add hA' hC
  have h2 : MeromorphicAt (fun s : ℂ => -(s / (1 - s))) 1 := hB.neg
  exact MeromorphicAt.add h1 h2

-- Gamma 在 3/2 处解析（3/2 的实部 > 0，非极点）
lemma analyticAt_Gamma_three_half : AnalyticAt ℂ Gamma (3 / 2 : ℂ) := by
  have hInv : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) (3 / 2 : ℂ) :=
    Differentiable.analyticAt Complex.differentiable_one_div_Gamma (3 / 2 : ℂ)
  have hGamma0 : Gamma (3 / 2 : ℂ) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
  have h := hInv.inv (by
    simpa using hGamma0)
  convert h using 1
  ext s
  exact (inv_inv (Gamma s)).symm

-- s ↦ π ^ (-s / 2) 在 s = 1 处解析（π ≠ 0，cpow 可微）
lemma analyticAt_pi_cpow_half :
    AnalyticAt ℂ (fun s : ℂ => (↑Real.pi : ℂ) ^ (-s / 2)) 1 := by
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards with z
  exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)

-- s ↦ s / 2 + 1 在 s = 1 处解析
lemma analyticAt_half_add_one : AnalyticAt ℂ (fun s : ℂ => s / 2 + 1) 1 := by
  have h1 : AnalyticAt ℂ (fun s : ℂ => s / 2) 1 :=
    AnalyticAt.mul analyticAt_id
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ((2 : ℂ)⁻¹)) 1)
  have h2 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 1 :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 1)
  exact AnalyticAt.add h1 h2

-- 分母 s ↦ 2 * π ^ (-s / 2) * Gamma (s / 2 + 1) 在 s = 1 处亚纯
lemma meromorphicAt_denom :
    MeromorphicAt (fun s : ℂ => 2 * (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2 + 1)) 1 := by
  have hD1 : AnalyticAt ℂ (fun s : ℂ => (2 : ℂ) * (↑Real.pi : ℂ) ^ (-s / 2)) 1 :=
    AnalyticAt.mul (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) 1)
      analyticAt_pi_cpow_half
  have hGc : AnalyticAt ℂ (fun s : ℂ => Gamma (s / 2 + 1)) 1 := by
    have hG' : AnalyticAt ℂ Gamma (1 / 2 + 1) := by
      convert analyticAt_Gamma_three_half using 1
      ring
    exact AnalyticAt.comp hG' analyticAt_half_add_one
  exact (AnalyticAt.mul hD1 hGc).meromorphicAt

-- 主结论 1：riemannZeta 在 s = 1 处亚纯（分解自 completedRiemannZeta₀，分母含 1/(1-s) 因子）
lemma meromorphicAt_riemannZeta_one : MeromorphicAt riemannZeta 1 := by
  have hdiv : MeromorphicAt
      (fun s : ℂ => (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) /
        (2 * (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2 + 1))) 1 :=
    MeromorphicAt.div meromorphicAt_num meromorphicAt_denom
  refine hdiv.congr ?_
  filter_upwards with s
  simpa using (riemannZeta_eq_mul_completedRiemannZeta₀ s).symm

-- 主结论 2：留数为 1（(s - 1) * riemannZeta s 在 s → 1（去心邻域）时极限为 1）
lemma residue_one :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) :=
  riemannZeta_residue_one

end ZetaSinglePole

end

#print axioms ZetaSinglePole.meromorphicAt_riemannZeta_one
#print axioms ZetaSinglePole.residue_one
#print axioms ZetaSinglePole.meromorphicAt_self_div_one_sub_one
#print axioms ZetaSinglePole.analyticAt_Gamma_three_half
