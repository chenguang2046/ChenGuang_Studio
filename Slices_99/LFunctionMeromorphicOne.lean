import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Meromorphic.Basic

/-!
# DirichletCharacter.LFunction 在 s = 1 处的亚纯性

切片 A 任务：用 Lean 4 + mathlib 形式化验证
`DirichletCharacter.LFunction` 在 `s = 1` 处亚纯（`MeromorphicAt`），
并给出其在 `s = 1` 附近解析延拓的具体条件。

不使用 `sorry`。证明依据：
- `LFunction_eq_LSeries`：在 `1 < s.re` 半平面与朴素 Dirichlet 级数一致（解析延拓的级数来源）；
- `differentiableAt_LFunction` / `differentiable_LFunction`：非平凡特征处处可微，平凡特征在 `s ≠ 1` 可微；
- `ZMod.LFunction_residue_one`：任意特征在 `s = 1` 的留数为 `∑ j, χ j / N`（平凡特征时为 `1`，单极点来源）；
- `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`：可去奇点定理，
  把 `s = 1` 处的留数行为提升为局部解析结构，从而构造 `MeromorphicAt` 见证。
-/

noncomputable section
open scoped Topology
open Complex Filter

namespace DirichletCharacter

/-- 解析延拓的条件之一：在 `1 < s.re` 半平面，`LFunction` 与朴素 Dirichlet 级数一致。 -/
lemma LFunction_eq_LSeries_of_one_lt_re {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LSeries (fun x => χ ↑x) s :=
  LFunction_eq_LSeries χ hs

/-- 解析延拓的条件之二：任意特征（含平凡特征）在 `s ≠ 1` 处局部解析。 -/
lemma LFunction_analyticAt_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (LFunction χ) s := by
  have hd : DifferentiableOn ℂ (LFunction χ) {z | z ≠ 1} :=
    fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hs)

/-- 解析延拓的条件之三：非平凡特征在 `s = 1` 处无极点，全平面解析。 -/
lemma LFunction_analyticOnNhd_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
  (differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ

/-- 解析延拓的条件之四：任意特征在 `s = 1` 的留数为 `∑ j, χ j / N`。
（对平凡特征，`∑ j, χ j / N = φ(N)/N`，即 `s = 1` 为单极点。） -/
lemma LFunction_residue_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Tendsto (fun s : ℂ => (s - 1) * LFunction χ s) (𝓝[≠] 1) (𝓝 (∑ j : ZMod N, χ j / N)) := by
  simpa [LFunction] using (ZMod.LFunction_residue_one (χ : ZMod N → ℂ))

/-- 主定理：`DirichletCharacter.LFunction` 在 `s = 1` 处亚纯。 -/
theorem LFunction_meromorphicAt_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    MeromorphicAt (LFunction χ) 1 := by
  by_cases hχ : χ ≠ 1
  · -- 非平凡特征：全平面解析（尤其 s=1 处解析）⇒ 亚纯
    exact ((LFunction_analyticOnNhd_of_ne_one χ hχ) 1 (by simp)).meromorphicAt
  · -- 平凡特征：s=1 有单极点（留数 ∑χ/N）。用 residue + 可去奇点定理构造 MeromorphicAt 见证
    let f0 : ℂ → ℂ := fun z => (z - 1) * LFunction χ z
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

/-- 综合：`LFunction` 在 `s = 1` 附近解析延拓的具体条件清单。 -/
theorem LFunction_analytic_continuation {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (∀ s : ℂ, 1 < s.re → LFunction χ s = LSeries (fun x => χ ↑x) s) ∧
      (∀ s : ℂ, s ≠ 1 → AnalyticAt ℂ (LFunction χ) s) ∧
      MeromorphicAt (LFunction χ) 1 ∧
      Tendsto (fun s : ℂ => (s - 1) * LFunction χ s) (𝓝[≠] 1) (𝓝 (∑ j : ZMod N, χ j / N)) :=
  ⟨fun _s hs => LFunction_eq_LSeries χ hs,
    fun _s hs => LFunction_analyticAt_of_ne_one χ hs,
    LFunction_meromorphicAt_one χ,
    LFunction_residue_one χ⟩

end DirichletCharacter
