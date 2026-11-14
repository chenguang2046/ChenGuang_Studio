import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Meromorphic.Order

open Complex Filter Function
open scoped Topology

noncomputable section

namespace HurwitzZeta

/-! ## 辅助引理 -/

/-- `Gammaℝ` 在 `s = 1` 的某个邻域内非零 -/
private lemma gamma_ne_one_nhds : ∀ᶠ z in 𝓝 (1 : ℂ), Gammaℝ z ≠ 0 := by
  have h : ∀ᶠ z in 𝓝 (1 : ℂ), (Gammaℝ z)⁻¹ ≠ 0 :=
    (differentiable_Gammaℝ_inv.continuous.continuousAt).eventually_ne (by simp [Gammaℝ_one])
  exact h.mono (fun z hz hγ0 => hz (by simp [hγ0]))

/-- 去掉 `1 / (s - 1) / Gammaℝ s` 这一一阶极点项后，`hurwitzZetaEven` 的余部是整函数 -/
private lemma differentiable_hurwitzZetaEven_sub_one_div_global (a : UnitAddCircle) :
    Differentiable ℂ (fun s ↦ hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s) := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact differentiableAt_hurwitzZetaEven_sub_one_div a
  · refine (differentiableAt_hurwitzZetaEven a hs).sub ?_
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    have h1 : DifferentiableAt ℂ (fun s => (s - 1)⁻¹ * (Gammaℝ s)⁻¹) s :=
      (DifferentiableAt.inv (DifferentiableAt.sub differentiableAt_id (differentiableAt_const (1 : ℂ))) hs1).mul
        differentiable_Gammaℝ_inv.differentiableAt
    have heq : (fun s => 1 / (s - 1) / Gammaℝ s) =ᶠ[𝓝 s]
        (fun s => (s - 1)⁻¹ * (Gammaℝ s)⁻¹) := by
      filter_upwards with t
      simp [div_eq_mul_inv]
    exact (DifferentiableAt.congr_of_eventuallyEq h1 heq)

/-! ## 单极点：存在解析非零的 `g`，使得 `hurwitzZeta a z = g z / (z - 1)` -/

lemma simple_pole_hurwitzZeta (a : UnitAddCircle) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] 1, hurwitzZeta a z = g z / (z - 1) := by
  let g : ℂ → ℂ := fun s ↦
    (Gammaℝ s)⁻¹ + (s - 1) *
      (hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s + hurwitzZetaOdd a s)
  refine ⟨g, ?_, ?_, ?_⟩
  · -- g 在 1 解析（实为整函数）
    apply Differentiable.analyticAt
    have hR : Differentiable ℂ (fun s ↦ hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s) :=
      differentiable_hurwitzZetaEven_sub_one_div_global a
    have hsum : Differentiable ℂ (fun s ↦
        hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s + hurwitzZetaOdd a s) :=
      hR.add (differentiable_hurwitzZetaOdd a)
    have hmul : Differentiable ℂ (fun s ↦
        (s - 1) * (hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s + hurwitzZetaOdd a s)) :=
      (Differentiable.sub differentiable_id (differentiable_const (1 : ℂ))).mul hsum
    exact differentiable_Gammaℝ_inv.add hmul
  · -- g 1 = 1 ≠ 0
    simp [g, Gammaℝ_one]
  · -- 在 punctured 邻域内 `hurwitzZeta a z = g z / (z - 1)`
    have hγ' : ∀ᶠ z in 𝓝[≠] 1, Gammaℝ z ≠ 0 := by
      apply eventually_nhdsWithin_iff.2
      filter_upwards [gamma_ne_one_nhds] with z hγ
      exact fun _ => hγ
    have hne1 : ∀ᶠ z in 𝓝[≠] (1 : ℂ), z ≠ 1 := by
      apply eventually_nhdsWithin_iff.2
      exact Eventually.of_forall (fun z hz => hz)
    filter_upwards [hne1, hγ'] with z hz1 hγ
    dsimp [g, hurwitzZeta]
    field_simp [sub_ne_zero.mpr hz1, hγ]
    ring

/-- `hurwitzZeta a` 在 `s = 1` 亚纯（由 punctured 邻域分解直接推出） -/
lemma meromorphicAt_hurwitzZeta_one (a : UnitAddCircle) : MeromorphicAt (hurwitzZeta a) 1 := by
  rcases simple_pole_hurwitzZeta a with ⟨g, hg_an, hg1, hg_eq⟩
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  refine ⟨-1, g, hg_an, ?_⟩
  filter_upwards [hg_eq] with z hz
  rw [hz]
  rw [zpow_neg, zpow_one, smul_eq_mul, div_eq_mul_inv]
  rw [mul_comm]

/-- 极点阶为 1：`meromorphicOrderAt (hurwitzZeta a) 1 = -1` -/
lemma meromorphicOrderAt_hurwitzZeta_one' (a : UnitAddCircle) :
    meromorphicOrderAt (hurwitzZeta a) 1 = (-1 : ℤ) := by
  rcases simple_pole_hurwitzZeta a with ⟨g, hg_an, hg1, hg_eq⟩
  refine (meromorphicOrderAt_eq_int_iff (n := -1) ?_).2 ?_
  · exact meromorphicAt_hurwitzZeta_one a
  · refine ⟨g, hg_an, hg1, ?_⟩
    filter_upwards [hg_eq] with z hz
    rw [hz]
    rw [zpow_neg, zpow_one, smul_eq_mul, div_eq_mul_inv]
    rw [mul_comm]

/-! ## 主定理 -/

/-- 命题 1+2：`hurwitzZeta a s` 在 `s = 1` 处有单极点，且留数为 1 -/
theorem hurwitzZeta_simple_pole_main (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * hurwitzZeta a s) (𝓝[≠] 1) (𝓝 1) ∧
    MeromorphicAt (hurwitzZeta a) 1 ∧
    meromorphicOrderAt (hurwitzZeta a) 1 = (-1 : ℤ) ∧
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] 1, hurwitzZeta a z = g z / (z - 1) :=
  ⟨hurwitzZeta_residue_one a, meromorphicAt_hurwitzZeta_one a,
    meromorphicOrderAt_hurwitzZeta_one' a, simple_pole_hurwitzZeta a⟩

/-- 命题 3：`hurwitzZeta 0 s` 退化为 `riemannZeta s` -/
theorem hurwitzZeta_zero_eq_riemannZeta_main : hurwitzZeta 0 = riemannZeta :=
  hurwitzZeta_zero

end HurwitzZeta
