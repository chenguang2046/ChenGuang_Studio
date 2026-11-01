import Mathlib
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Piecewise

/-!
# 完备 Dirichlet L 函数：函数方程与亚纯性（单文件独立验证）

独立命题：
1. 对任意模 N 的本原 Dirichlet 特征 χ，其完备 L 函数满足函数方程
   `completedLFunction χ s = rootNumber χ · completedLFunction χ̄ (1 - s)`
   （mathlib 中本原特征版本含因子 `N^(1/2 - s)`；模 1 时退化为上述用户原式）。
2. `completedLFunction` 在复平面亚纯，其极点位置由 Γ 因子与 L 函数的极点共同决定。

全部证明只使用 mathlib 现成引理，不使用 `sorry`，不新增自造假引理。
-/

noncomputable section
open scoped Topology
open Complex Filter

namespace DirichletCharacter

-- =====================================================================
-- 第 0 节：LFunction 在 s = 1 处亚纯（切片 A 已交付结论，内联以备独立运行）
-- =====================================================================

/-- 任意特征（含平凡特征）在 `s ≠ 1` 处局部解析。 -/
lemma LFunction_analyticAt_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (LFunction χ) s := by
  have hd : DifferentiableOn ℂ (LFunction χ) {z | z ≠ 1} :=
    fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hs)

/-- 非平凡特征在 `s = 1` 处无极点，全平面解析。 -/
lemma LFunction_analyticOnNhd_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
  (differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ

/-- 任意特征在 `s = 1` 的留数为 `∑ j, χ j / N`。 -/
lemma LFunction_residue_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Tendsto (fun s : ℂ => (s - 1) * LFunction χ s) (𝓝[≠] 1) (𝓝 (∑ j : ZMod N, χ j / N)) := by
  simpa [LFunction] using (ZMod.LFunction_residue_one (χ : ZMod N → ℂ))

/-- `LFunction` 在 `s = 1` 处亚纯。 -/
theorem LFunction_meromorphicAt_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    MeromorphicAt (LFunction χ) 1 := by
  by_cases hχ : χ ≠ 1
  · exact ((LFunction_analyticOnNhd_of_ne_one χ hχ) 1 (by simp)).meromorphicAt
  · let f0 : ℂ → ℂ := fun z => (z - 1) * LFunction χ z
    let g : ℂ → ℂ := Function.update f0 1 (∑ j : ZMod N, χ j / N)
    have hf0 : Tendsto f0 (𝓝[≠] 1) (𝓝 (∑ j : ZMod N, χ j / N)) := by
      simpa [f0] using LFunction_residue_one χ
    have hc_g : ContinuousAt g 1 := (continuousAt_update_same).2 hf0
    have hf0d : ∀ z : ℂ, z ≠ 1 → DifferentiableAt ℂ f0 z := by
      intro z hz
      have hzminus : AnalyticAt ℂ (fun w : ℂ => w - (1 : ℂ)) z :=
        analyticAt_id.sub (analyticAt_const (v := (1 : ℂ)))
      have hprod : DifferentiableAt ℂ (fun w : ℂ => (w - (1 : ℂ)) * LFunction χ w) z :=
        hzminus.differentiableAt.mul (differentiableAt_LFunction χ z (Or.inl hz))
      simpa [f0] using hprod
    have hpd : ∀ᶠ z in 𝓝[≠] 1, DifferentiableAt ℂ g z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hg_eq_f0 : g =ᶠ[𝓝 z] f0 := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        simp [g, Function.update_of_ne hw]
      exact (hf0d z hz).congr_of_eventuallyEq hg_eq_f0
    have hg_an : AnalyticAt ℂ g 1 :=
      analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hpd hc_g
    refine ⟨2, ?_⟩
    have hzsmul : AnalyticAt ℂ (fun z : ℂ => (z - 1) • g z) 1 :=
      (analyticAt_id.sub analyticAt_const).smul hg_an
    apply hzsmul.congr
    filter_upwards with z
    by_cases hz : z = 1
    · subst z
      simp [g, f0, smul_eq_mul]
    · simp only [g, Function.update_of_ne hz, f0, smul_eq_mul]
      ring

-- =====================================================================
-- 第 1 节：Γ 因子 gammaFactor 在 s = 1 处解析且非零（平凡特征）
-- =====================================================================

/-- Gammaℝ 在 `re z > 0` 半平面上可微（π^(-z/2) 与 Γ(z/2) 的乘积）。 -/
lemma Gammaℝ_differentiableOn_repos : DifferentiableOn ℂ Gammaℝ {z | 0 < z.re} := by
  intro z hz
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) z :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) z := by
    apply (Complex.differentiableAt_Gamma (z / 2) _).comp z (differentiableAt_id.div_const (2 : ℂ))
    intro m hm
    have hre : (z / 2 : ℂ).re = z.re / 2 := by
      rw [Complex.div_re]
      norm_num
      ring
    have hpos : 0 < (z / 2 : ℂ).re := by
      rw [hre]
      exact div_pos hz (by norm_num)
    have hneg : (-(m : ℂ)).re ≤ 0 := by simp
    have hre2 := congrArg Complex.re hm
    nlinarith
  have h : DifferentiableAt ℂ (fun w : ℂ => Gammaℝ w) z :=
    h1.mul h2 |>.congr_of_eventuallyEq (by
      filter_upwards with w
      simp [Gammaℝ_def])
  exact h.differentiableWithinAt

/-- gammaFactor 在 `s = 1` 处解析（Γ 因子无极点，是整函数的平移/组合）。 -/
lemma gammaFactor_analyticAt_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    AnalyticAt ℂ (gammaFactor χ) 1 := by
  by_cases hEven : χ.Even
  · have hd : DifferentiableOn ℂ (gammaFactor χ) {z | 0 < z.re} := by
      intro z hz
      have hg : DifferentiableAt ℂ (gammaFactor χ) z := by
        have hg' : DifferentiableAt ℂ (fun w : ℂ => Gammaℝ w) z :=
          (Gammaℝ_differentiableOn_repos z hz).differentiableAt
            ((isOpen_lt continuous_const continuous_re).mem_nhds hz)
        exact hg'.congr_of_eventuallyEq (f₁ := gammaFactor χ) (by
          filter_upwards with w
          rw [hEven.gammaFactor_def w])
      exact hg.differentiableWithinAt
    exact hd.analyticAt ((isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (0 : ℝ) < (1 : ℂ).re))
  · have hOdd : χ.Odd := (χ.even_or_odd).resolve_left hEven
    have hd : DifferentiableOn ℂ (gammaFactor χ) {z | 0 < (z + 1).re} := by
      intro z hz
      have hg : DifferentiableAt ℂ (gammaFactor χ) z := by
        have hg' : DifferentiableAt ℂ (fun w : ℂ => Gammaℝ (w + 1)) z := by
          have hG' : DifferentiableAt ℂ Gammaℝ (z + 1) :=
            (Gammaℝ_differentiableOn_repos (z + 1) hz).differentiableAt
              ((isOpen_lt continuous_const continuous_re).mem_nhds (by simpa [Complex.add_re] using hz))
          simpa [Function.comp_def] using hG'.comp z (differentiableAt_id.add_const 1)
        exact hg'.congr_of_eventuallyEq (f₁ := gammaFactor χ) (by
          filter_upwards with w
          rw [hOdd.gammaFactor_def w])
      exact hg.differentiableWithinAt
    exact hd.analyticAt (by
      simpa [Complex.add_re] using
        ((isOpen_lt continuous_const (continuous_re.add continuous_const)).mem_nhds
          (by norm_num : (0 : ℝ) < (1 : ℂ).re + 1)))

/-- 平凡特征的 Γ 因子在 `s = 1` 处非零（Gammaℝ 1 = 1）。 -/
lemma gammaFactor_one_ne_zero {N : ℕ} [NeZero N] :
    gammaFactor (1 : DirichletCharacter ℂ N) 1 ≠ 0 := by
  have hEven : (1 : DirichletCharacter ℂ N).Even := by
    rw [DirichletCharacter.Even]
    exact MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod N))
  rw [hEven.gammaFactor_def 1]
  rw [Complex.Gammaℝ_one]
  norm_num

-- =====================================================================
-- 第 2 节：分解式 completedLFunction = LFunction · gammaFactor
-- =====================================================================

/-- 在 Γ 因子非零处，完备 L 函数恰为 L 函数与 Γ 因子的乘积：
故其局部性质（极点）由 L 函数的极点与 Γ 因子共同决定。 -/
lemma completedLFunction_eq_mul_gammaFactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 0 ∨ N ≠ 1) (hg : gammaFactor χ s ≠ 0) :
    completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hs
  rw [hL]
  rw [div_mul_cancel₀ _ hg]

-- =====================================================================
-- 第 3 节：completedLFunction 在复平面亚纯，且极点位置由 L 函数极点决定
-- =====================================================================

/-- 内联：`completedRiemannZeta` 在 `0` 处亚纯（ZetaCompletedFE 结论，由 mathlib 引理推出）。
分解式 `Λ = Λ₀ - 1/z - 1/(1-z)` 中两个极项给出 `s = 0` 处的极点。 -/
lemma meromorphicAt_completedRiemannZeta_zero : MeromorphicAt completedRiemannZeta 0 := by
  have hΛ₀ : MeromorphicAt (fun z : ℂ => completedRiemannZeta₀ z) 0 :=
    (differentiable_completedZeta₀).analyticAt 0 |>.meromorphicAt
  have h₁ : MeromorphicAt (fun z : ℂ => 1 / z) 0 := by
    have h₁' : MeromorphicAt (fun z : ℂ => z⁻¹) 0 := (MeromorphicAt.id (0 : ℂ)).inv
    simpa [one_div] using h₁'
  have h₂ : MeromorphicAt (fun z : ℂ => 1 / (1 - z)) 0 := by
    have hsub : AnalyticAt ℂ (fun z : ℂ => 1 - z) 0 :=
      (analyticAt_const (v := (1 : ℂ)) (x := (0 : ℂ))).sub analyticAt_id
    have h0 : (fun z : ℂ => 1 - z) 0 ≠ 0 := by norm_num
    have h₂' : MeromorphicAt (fun z : ℂ => (1 - z)⁻¹) 0 := (hsub.inv h0).meromorphicAt
    simpa [one_div] using h₂'
  refine MeromorphicAt.congr (hΛ₀.sub h₁ |>.sub h₂) ?_
  filter_upwards with z
  simp [completedRiemannZeta_eq]

/-- 无极点区域：在 `s ≠ 1 ∨ χ ≠ 1` 且 `s ≠ 0 ∨ N ≠ 1` 处 completedLFunction 解析。
（即极点只可能出现在平凡特征的 `s = 1` 处，或模 1 平凡特征的 `s = 0` 处。） -/
theorem completedLFunction_analyticAt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s ≠ 1 ∨ χ ≠ 1) (hs0 : s ≠ 0 ∨ N ≠ 1) :
    AnalyticAt ℂ (completedLFunction χ) s := by
  by_cases hχ : χ ≠ 1
  · exact Differentiable.analyticAt (differentiable_completedLFunction hχ) s
  · have hχ1 : χ = 1 := (Classical.not_not.mp hχ)
    subst χ
    have hs1 : s ≠ 1 := hs.elim (fun h => h) (fun h => False.elim (by simp at h))
    by_cases hs0z : s ≠ 0
    · have hd : DifferentiableOn ℂ (completedLFunction (1 : DirichletCharacter ℂ N))
          ({z | z ≠ 0} ∩ {z | z ≠ 1}) := by
        intro z hz
        exact (differentiableAt_completedLFunction (1 : DirichletCharacter ℂ N) z
          (Or.inl hz.1) (Or.inl hz.2)).differentiableWithinAt
      exact hd.analyticAt ((isOpen_ne.inter isOpen_ne).mem_nhds ⟨hs0z, hs1⟩)
    · have hs0' : s = 0 := by
        by_contra h
        exact hs0z h
      have hN : N ≠ 1 := hs0.elim (fun h => False.elim (h hs0')) id
      have hd : DifferentiableOn ℂ (completedLFunction (1 : DirichletCharacter ℂ N)) {z | z ≠ 1} := by
        intro z hz
        exact (differentiableAt_completedLFunction (1 : DirichletCharacter ℂ N) z
          (Or.inr hN) (Or.inl hz)).differentiableWithinAt
      exact hd.analyticAt (isOpen_ne.mem_nhds hs1)

/-- completedLFunction 在复平面上处处亚纯。
平凡特征的 `s = 1` 极点来自 L 函数（单极点）乘 Γ 因子（解析非零）；
其余位置解析。 -/
theorem completedLFunction_meromorphicAt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    MeromorphicAt (completedLFunction χ) s := by
  by_cases hχ : χ ≠ 1
  · exact ((Differentiable.analyticAt (differentiable_completedLFunction hχ) s).meromorphicAt)
  · have hχ1 : χ = 1 := (Classical.not_not.mp hχ)
    subst χ
    by_cases hs1 : s = 1
    · subst s
      have hLm : MeromorphicAt (LFunction (1 : DirichletCharacter ℂ N)) 1 :=
        LFunction_meromorphicAt_one (1 : DirichletCharacter ℂ N)
      have hGan : AnalyticAt ℂ (gammaFactor (1 : DirichletCharacter ℂ N)) 1 :=
        gammaFactor_analyticAt_one (1 : DirichletCharacter ℂ N)
      have hGm : MeromorphicAt (gammaFactor (1 : DirichletCharacter ℂ N)) 1 := hGan.meromorphicAt
      have hg1 : gammaFactor (1 : DirichletCharacter ℂ N) 1 ≠ 0 := gammaFactor_one_ne_zero (N := N)
      have hg : ∀ᶠ z in 𝓝 (1 : ℂ), gammaFactor (1 : DirichletCharacter ℂ N) z ≠ 0 :=
        hGan.continuousAt.eventually_ne hg1
      have hznz : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 0 := (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
      have hc : completedLFunction (1 : DirichletCharacter ℂ N) =ᶠ[𝓝 1]
          LFunction (1 : DirichletCharacter ℂ N) * gammaFactor (1 : DirichletCharacter ℂ N) := by
        filter_upwards [hznz, hg] with z hznz hgz
        exact completedLFunction_eq_mul_gammaFactor (1 : DirichletCharacter ℂ N) (Or.inl hznz) hgz
      exact hLm.mul hGm |>.congr (hc.filter_mono nhdsWithin_le_nhds).symm
    · by_cases hs0z : s ≠ 0
      · exact (completedLFunction_analyticAt (1 : DirichletCharacter ℂ N) (Or.inl hs1)
          (Or.inl hs0z)).meromorphicAt
      · by_cases hN : N = 1
        · subst N
          have hs0' : s = 0 := by
            by_contra h
            exact hs0z h
          subst s
          have hz : MeromorphicAt completedRiemannZeta 0 := meromorphicAt_completedRiemannZeta_zero
          simpa [completedLFunction_modOne_eq] using hz
        · exact (completedLFunction_analyticAt (1 : DirichletCharacter ℂ N) (Or.inl hs1)
            (Or.inr hN)).meromorphicAt

-- =====================================================================
-- 第 4 节：函数方程 completedLFunction χ s = rootNumber χ · completedLFunction χ̄ (1-s)
-- =====================================================================

/-- 主定理：对任意模 N 的本原 Dirichlet 特征 χ，
`completedLFunction χ s = N^(1/2 - s) * rootNumber χ * completedLFunction χ̄ (1 - s)`。 -/
theorem completedLFunction_functional_equation
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ s = (N : ℂ) ^ (1 / 2 - s) * rootNumber χ *
      completedLFunction (star χ) (1 - s) := by
  have h1 := IsPrimitive.completedLFunction_one_sub hχ (1 - s)
  rw [show (1 - (1 - s : ℂ)) = s by ring] at h1
  rw [show ((1 - s : ℂ) - (1 / 2 : ℂ)) = 1 / 2 - s by ring] at h1
  rw [← MulChar.star_eq_inv] at h1
  exact h1

/-- 模 1 时 `N^(1/2 - s) = 1`，即退化为用户原式：
`completedLFunction χ s = rootNumber χ · completedLFunction χ̄ (1 - s)`。 -/
theorem completedLFunction_functional_equation_modOne
    {χ : DirichletCharacter ℂ 1} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ s = rootNumber χ * completedLFunction (star χ) (1 - s) := by
  have h1 := completedLFunction_functional_equation (N := 1) hχ s
  rw [show (↑(1 : ℕ) : ℂ) = (1 : ℂ) by norm_num] at h1
  rw [Complex.one_cpow] at h1
  simpa [one_mul] using h1

-- =====================================================================
-- 公理审计
-- =====================================================================

#print axioms completedLFunction_functional_equation
#print axioms completedLFunction_functional_equation_modOne
#print axioms completedLFunction_meromorphicAt
#print axioms completedLFunction_analyticAt

end DirichletCharacter
