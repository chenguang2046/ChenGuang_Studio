import Mathlib

open Complex
open scoped Topology
open Set

noncomputable section

/-- φ(s) = √π · Γ(s-1/2) / Γ(s) · ζ(2s-1) / ζ(2s) -/
def phi (s : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s - (1 / 2 : ℂ)) / Complex.Gamma s *
    riemannZeta (2 * s - 1) / riemannZeta (2 * s)

/-- (φ'/φ)(s) = logDeriv phi s -/
def logPhi (s : ℂ) : ℂ :=
  logDeriv phi s

/-- 左端集合（按用户指示：亚纯性失效点集）: {r | logPhi 在 1/2+ir 处非亚纯} -/
def poleSet : Set ℝ :=
  {r : ℝ | ¬ MeromorphicAt (fun s : ℂ => logPhi s) (1 / 2 + (r : ℂ) * Complex.I)}

/-- 右端集合: {r | ζ(1+2ir) = 0} -/
def zetaZeroSet : Set ℝ :=
  {r : ℝ | riemannZeta (1 + (2 * r : ℂ) * Complex.I) = 0}

/-! ## Gamma 处处亚纯 -/
/-- 1/Γ 处处可微（mathlib: differentiable_one_div_Gamma），故处处解析，从而亚纯；inv_iff 回到 Γ -/
lemma gamma_meromorphicAt (x : ℂ) : MeromorphicAt (fun s : ℂ => Complex.Gamma s) x := by
  have h1 : MeromorphicAt (fun s : ℂ => (Complex.Gamma s)⁻¹) x := by
    have hdiff : DifferentiableOn ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) univ :=
      Complex.differentiable_one_div_Gamma.differentiableOn
    have han : AnalyticOnNhd ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) univ :=
      hdiff.analyticOnNhd isOpen_univ
    exact han.meromorphicOn x (by simp)
  exact (MeromorphicAt.inv_iff.mp h1)

/-! ## Riemann zeta 处处亚纯 -/
/-- ζ 在 s≠1 处解析（mathlib: analyticOn_riemannZeta） -/
lemma zeta_meromorphicAt_of_ne_one {x : ℂ} (hx : x ≠ 1) : MeromorphicAt riemannZeta x := by
  exact analyticOn_riemannZeta.meromorphicOn x hx

/-- ζ 在极点 s=1 处亚纯：用分解式 ζ = (s·CR₀ - 1 - s/(1-s)) / (2·π^(-s/2)·Γ(s/2+1)) 与闭包 -/
lemma zeta_meromorphicAt_one : MeromorphicAt riemannZeta 1 := by
  have hM : MeromorphicAt (fun s : ℂ => s * completedRiemannZeta₀ s - 1 - s / (1 - s)) 1 := by
    have h1 : MeromorphicAt (fun s : ℂ => s * completedRiemannZeta₀ s) 1 := by
      have hCR : Differentiable ℂ completedRiemannZeta₀ := by
        change Differentiable ℂ (HurwitzZeta.completedHurwitzZetaEven₀ (0 : UnitAddCircle))
        exact HurwitzZeta.differentiable_completedHurwitzZetaEven₀ (0 : UnitAddCircle)
      have hCRan : AnalyticAt ℂ completedRiemannZeta₀ 1 :=
        (hCR.differentiableOn.analyticOnNhd isOpen_univ) 1 (by simp)
      exact (analyticAt_id.meromorphicAt).mul hCRan.meromorphicAt
    have h2 : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) 1 := MeromorphicAt.const (1 : ℂ) 1
    have h3 : MeromorphicAt (fun s : ℂ => s / (1 - s)) 1 := by
      have hA : AnalyticAt ℂ (fun s : ℂ => (1 : ℂ) - s) 1 := analyticAt_const.sub analyticAt_id
      have hInv : MeromorphicAt (fun s : ℂ => ((1 : ℂ) - s)⁻¹) 1 := MeromorphicAt.inv hA.meromorphicAt
      exact (analyticAt_id.meromorphicAt).mul hInv
    exact (h1.sub h2).sub h3
  have hD : MeromorphicAt
      (fun s : ℂ => (2 : ℂ) * (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2 + 1)) 1 := by
    have hc2 : MeromorphicAt (fun _ : ℂ => (2 : ℂ)) 1 := MeromorphicAt.const (2 : ℂ) 1
    have hpi : MeromorphicAt (fun s : ℂ => (↑Real.pi : ℂ) ^ (-s / 2)) 1 := by
      have han : AnalyticAt ℂ (fun s : ℂ => (↑Real.pi : ℂ) ^ (-s / 2)) 1 := by
        refine AnalyticAt.cpow analyticAt_const (analyticAt_id.neg.div_const (c := (2 : ℂ))) ?_
        exact ofReal_mem_slitPlane.mpr Real.pi_pos
      exact han.meromorphicAt
    have hG : MeromorphicAt (fun s : ℂ => Gamma (s / 2 + 1)) 1 := by
      have hg : AnalyticAt ℂ (fun s : ℂ => s / 2 + 1) 1 :=
        (analyticAt_id.div_const (c := (2 : ℂ))).add analyticAt_const
      exact MeromorphicAt.comp_analyticAt (f := fun s : ℂ => Gamma s)
        (g := fun s : ℂ => s / 2 + 1) (gamma_meromorphicAt (1 / 2 + 1)) hg
    exact (hc2.mul hpi).mul hG
  have hdiv : MeromorphicAt
      (fun s : ℂ => (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) /
        (2 * (↑Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2 + 1))) 1 :=
    MeromorphicAt.div hM hD
  convert hdiv using 1
  funext s
  exact riemannZeta_eq_mul_completedRiemannZeta₀ s

/-- ζ 处处亚纯（s=1 用 zeta_meromorphicAt_one，其余用解析性） -/
lemma zeta_meromorphicAt (x : ℂ) : MeromorphicAt riemannZeta x := by
  by_cases hx : x = 1
  · subst hx
    exact zeta_meromorphicAt_one
  · exact zeta_meromorphicAt_of_ne_one hx

/-! ## φ 处处亚纯，从而 logPhi 处处亚纯 -/
lemma phi_meromorphicAt (x : ℂ) : MeromorphicAt phi x := by
  unfold phi
  have hc : MeromorphicAt (fun _ : ℂ => (Real.sqrt Real.pi : ℂ)) x := MeromorphicAt.const _ x
  have hΓ1 : MeromorphicAt (fun s : ℂ => Complex.Gamma (s - (1 / 2 : ℂ))) x := by
    exact MeromorphicAt.comp_analyticAt (f := fun s : ℂ => Complex.Gamma s)
      (g := fun s : ℂ => s - (1 / 2 : ℂ))
      (gamma_meromorphicAt (x - (1 / 2 : ℂ))) (analyticAt_id.sub analyticAt_const)
  have hΓ2 : MeromorphicAt (fun s : ℂ => Complex.Gamma s) x := gamma_meromorphicAt x
  have hz1 : MeromorphicAt (fun s : ℂ => riemannZeta (2 * s - 1)) x := by
    exact MeromorphicAt.comp_analyticAt (f := riemannZeta) (g := fun s : ℂ => 2 * s - 1)
      (zeta_meromorphicAt (2 * x - 1)) ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
  have hz2 : MeromorphicAt (fun s : ℂ => riemannZeta (2 * s)) x := by
    exact MeromorphicAt.comp_analyticAt (f := riemannZeta) (g := fun s : ℂ => 2 * s)
      (zeta_meromorphicAt (2 * x)) (analyticAt_const.mul analyticAt_id)
  convert (((hc.mul hΓ1).div hΓ2).mul hz1).div hz2 using 1

/-! ## 主定理 -/
/-- 左端集合为空：logPhi 处处亚纯 -/
lemma poleSet_empty : poleSet = ∅ := by
  ext r
  constructor
  · intro hp
    exact hp (by
      have hφ : MeromorphicAt phi (1 / 2 + (r : ℂ) * Complex.I) := phi_meromorphicAt _
      simpa [logPhi] using MeromorphicAt.logDeriv hφ)
  · intro h
    exact False.elim h

/-- 右端集合为空：ζ 在 Re s ≥ 1 无零点（mathlib: riemannZeta_ne_zero_of_one_le_re） -/
lemma zetaZeroSet_empty : zetaZeroSet = ∅ := by
  ext r
  constructor
  · intro hz
    have hre : 1 ≤ (1 + (2 * r : ℂ) * Complex.I).re := by
      simp
    exact False.elim (riemannZeta_ne_zero_of_one_le_re hre hz)
  · intro h
    exact False.elim h

/-- 命题：(φ'/φ)(1/2+ir) 的亚纯失效点集恰好等于 {r | ζ(1+2ir)=0}（两边均为空集） -/
theorem phi_poles_eq_zeta_zeros : poleSet = zetaZeroSet := by
  rw [poleSet_empty, zetaZeroSet_empty]

end
