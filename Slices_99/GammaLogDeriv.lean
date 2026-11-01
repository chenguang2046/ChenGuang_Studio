import Mathlib

open Complex
open scoped Topology
open Set

noncomputable section

/-!
# 切片C：logDeriv (Γ(s-1/2)/Γ(s)) 的亚纯性与极点必要条件

命题（用户原文）：
1. 函数 logDeriv (fun s => Gamma (s - 1/2) / Gamma s) 在复平面上是亚纯的；
2. 若该函数在某点不解析，则该点必为 Gamma 的极点 或 Gamma(s-1/2) 的零点。

全部只用 mathlib 已有的 Complex.Gamma / logDeriv / MeromorphicAt 引理，无 sorry、无自造假引理。
-/

/-- H(s) = Γ(s - 1/2) / Γ(s) -/
def H (s : ℂ) : ℂ := Complex.Gamma (s - (1 / 2 : ℂ)) / Complex.Gamma s

/-- Γ 的极点集：恰好是负整数（mathlib 中 Complex.Gamma 在这些点取值 0 且不连续） -/
def GammaPole (z : ℂ) : Prop := ∃ m : ℕ, z = -↑m

/-- 1/Γ 处处整，故 Γ 处处亚纯（inv_iff 回） -/
lemma gamma_meromorphicAt (x : ℂ) : MeromorphicAt (fun s : ℂ => Complex.Gamma s) x := by
  have h1 : MeromorphicAt (fun s : ℂ => (Complex.Gamma s)⁻¹) x := by
    have hdiff : DifferentiableOn ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) univ :=
      Complex.differentiable_one_div_Gamma.differentiableOn
    have han : AnalyticOnNhd ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) univ :=
      hdiff.analyticOnNhd isOpen_univ
    exact han.meromorphicOn x (by simp)
  exact (MeromorphicAt.inv_iff.mp h1)

/-- 平移 t ↦ t - 1/2 解析 -/
lemma shift_analytic (x : ℂ) : AnalyticAt ℂ (fun t : ℂ => t - (1 / 2 : ℂ)) x := by
  convert (analyticAt_id.sub (analyticAt_const (v := (1 / 2 : ℂ))) :
      AnalyticAt ℂ ((fun t : ℂ => t) - fun t : ℂ => (1 / 2 : ℂ)) x) using 1
  funext t
  rfl

/-- Γ(s-1/2) 处处亚纯 -/
lemma gamma_shift_meromorphicAt (x : ℂ) :
    MeromorphicAt (fun s : ℂ => Complex.Gamma (s - (1 / 2 : ℂ))) x := by
  exact MeromorphicAt.comp_analyticAt (f := fun s : ℂ => Complex.Gamma s)
    (g := fun s : ℂ => s - (1 / 2 : ℂ))
    (gamma_meromorphicAt (x - (1 / 2 : ℂ))) (shift_analytic x)

/-- H 处处亚纯（两个亚纯函数的商） -/
lemma H_meromorphicAt (x : ℂ) : MeromorphicAt H x := by
  unfold H
  exact MeromorphicAt.div (gamma_shift_meromorphicAt x) (gamma_meromorphicAt x)

/-- 主定理1：logDeriv H 在复平面上处处亚纯 -/
theorem logDeriv_H_meromorphicAt (x : ℂ) :
    MeromorphicAt (fun s : ℂ => logDeriv H s) x := by
  exact MeromorphicAt.logDeriv (H_meromorphicAt x)

/-! ## 主定理2 的支撑引理 -/

/-- Γ 在非负整数点解析（1/Γ 整、连续 + 亚纯 ⇒ 解析） -/
lemma gamma_analyticAt_of_not_neg_nat (z : ℂ) (hz : ∀ m : ℕ, z ≠ -↑m) :
    AnalyticAt ℂ (fun s : ℂ => Complex.Gamma s) z := by
  exact MeromorphicAt.analyticAt (gamma_meromorphicAt z) (Complex.continuousAt_Gamma z hz)

/-- 若 Γ(x) ≠ 0 且 Γ(x-1/2) ≠ 0，则 logDeriv H 在 x 解析。
  核心：两处 Γ 均解析非零 ⇒ 商解析非零 ⇒ 对数导数解析。 -/
lemma logDeriv_analyticAt_of_gamma_ne_zero (x : ℂ)
    (hΓx : Complex.Gamma x ≠ 0) (hΓs : Complex.Gamma (x - (1 / 2 : ℂ)) ≠ 0) :
    AnalyticAt ℂ (fun s : ℂ => logDeriv H s) x := by
  have hX : ∀ m : ℕ, x ≠ -↑m := by
    intro m hm
    exact hΓx ((Complex.Gamma_eq_zero_iff x).mpr ⟨m, hm⟩)
  have hS : ∀ m : ℕ, x - (1 / 2 : ℂ) ≠ -↑m := by
    intro m hm
    exact hΓs ((Complex.Gamma_eq_zero_iff (x - (1 / 2 : ℂ))).mpr ⟨m, hm⟩)
  -- Γ 在 x 处解析非零，Γ(s-1/2) 在 x 处解析非零
  have hG2 : AnalyticAt ℂ (fun s : ℂ => Complex.Gamma s) x :=
    gamma_analyticAt_of_not_neg_nat x hX
  have hG2inv : AnalyticAt ℂ (fun s : ℂ => (Complex.Gamma s)⁻¹) x := hG2.inv hΓx
  have hG1 : AnalyticAt ℂ (fun s : ℂ => Complex.Gamma (s - (1 / 2 : ℂ))) x := by
    exact AnalyticAt.comp
      (gamma_analyticAt_of_not_neg_nat (x - (1 / 2 : ℂ)) hS) (shift_analytic x)
  -- H 在 x 解析
  have hH : AnalyticAt ℂ H x := by
    convert hG1.mul hG2inv using 1
    funext s
    simp [H, div_eq_mul_inv]
  -- H x ≠ 0
  have hHNe : H x ≠ 0 := by
    unfold H
    exact div_ne_zero hΓs hΓx
  -- logDeriv H = H' / H 在 x 解析
  convert hH.deriv.mul (hH.inv hHNe) using 1
  funext s
  simp [logDeriv, div_eq_mul_inv]

/-- 主定理2（极点必要条件）：
  若 logDeriv H 在 x 不解析，则 x 必为 Γ 的极点，或 Γ(x-1/2) 为零。
  证明：反证。若 x 不是 Γ 极点（即 ∀ m, x ≠ -m）且 Γ(x-1/2) ≠ 0，
  则两处 Γ 解析非零 ⇒ logDeriv H 在 x 解析，与假设矛盾。 -/
theorem logDeriv_H_pole_necessary (x : ℂ)
    (h : ¬ AnalyticAt ℂ (fun s : ℂ => logDeriv H s) x) :
    GammaPole x ∨ Complex.Gamma (x - (1 / 2 : ℂ)) = 0 := by
  by_contra hnot
  push_neg at hnot
  have hΓx : Complex.Gamma x ≠ 0 := by
    exact Complex.Gamma_ne_zero (by
      intro m hm
      exact hnot.1 ⟨m, hm⟩)
  exact h (logDeriv_analyticAt_of_gamma_ne_zero x hΓx hnot.2)
