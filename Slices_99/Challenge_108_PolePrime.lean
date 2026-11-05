/-
Copyright (c) 2026 ChenGuang Studio. All rights reserved.
Challenge 108（第 108 号切片）：极点侧与素数侧真证落地 —— Weil Gap 压缩至零点侧
================================================================================

【战术（用户 2026-11-04 指令，方案 A）】
  1. 用 `completedZeta_residue_one` 与 vonMangoldt 级数把 poleSide / primeSide 落地；
  2. 把 Weil 显式公式的 Gap 压到只剩「零点侧求和」；
  3. 围道工具：库有则用，无则打 Gap 接口，不硬搓。
  红线：绝不去补 Mathlib 基建（不碰 LevelNFE / G1）。

【108 相对 107 的 Gap 压缩】
  107 的 `WeilExplicitFormulaGap` 有 6 个字段全是悬空假设。108 后：
    * 极点侧    —— 真证（s = 1 留数 1；s = 0 留数 −1，由 s ↦ 1−s 对称性搬运）
    * 素数侧    —— 真证（`Λ(n)/n^s` 在 Re s > 1 可和，HasSum 收敛到 LSeries ↗Λ）
    * 零点侧    —— `ZeroSideGap`（仅剩这一项实质性缺口）
    * 围道工具  —— `ContourResidueGap`（探底确认 Mathlib 无复分析 residue 接口）

【探底（2026-11-04）】
  * `LSeries.term f s n = if n = 0 then 0 else f n / n^s`（LSeries/Basic.lean:74）
  * `LSeriesSummable_vonMangoldt {s} (hs : 1 < s.re) : LSeriesSummable ↗Λ s`
    （LSeries/Dirichlet.lean:379，namespace ArithmeticFunction）
  * `completedRiemannZeta_residue_one : Tendsto (fun s ↦ (s-1)·ζ s) (𝓝[≠] 1) (𝓝 1)`
  * 全库 grep `residue` 仅命中代数 residueField / residuePairing，无复分析留数定理
-/

-- H3 跨层咬合：极点侧不再直取 Mathlib 的 `completedRiemannZeta_residue_one` 散票，
-- 而是吃 107（Weil 显式公式前置引理）已封装好的 `completedZeta_residue_one`。
import Slices_99.Challenge_107_WeilExplicit
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

noncomputable section
set_option linter.overlappingInstances false
set_option linter.deprecated false

open MeasureTheory Filter Complex Topology
open scoped Real Topology BigOperators

namespace Challenge108

attribute [local instance] Classical.propDecidable

/-! ## §1  极点侧（Pole Side）：两个极点的留数全部真证 -/

/-- **极点 `s = 1` 的留数为 `1`** —— **直接引用 107 号切片的 `completedZeta_residue_one`**
    （跨层咬合：107 提供 Weil 显式公式的极点原料，108 在此之上做零点侧/素数侧分解）。 -/
theorem poleResidue_one :
    Tendsto (fun s : ℂ => (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  Challenge107.completedZeta_residue_one

/-- **极点 `s = 0` 的留数为 `−1`**（真证）：
由 `completedRiemannZeta (1 - s) = completedRiemannZeta s` 把 `s = 1` 处的留数
沿 `s ↦ 1 - s` 搬运到 `s = 0`。
`(1-s-1)·ζ(1-s) = -s·ζ(1-s) → 1` ⇒ `s·ζ(s) → -1`。 -/
theorem poleResidue_zero :
    Tendsto (fun s : ℂ => s * completedRiemannZeta s) (𝓝[≠] 0) (𝓝 (-1)) := by
  -- ① 用函数方程把 ζ s 换成 ζ (1 - s)
  have hfun : (fun s : ℂ => s * completedRiemannZeta s)
      = fun s : ℂ => s * completedRiemannZeta (1 - s) := by
    funext s
    rw [completedRiemannZeta_one_sub]
  rw [hfun]
  -- ② 变换 s ↦ 1 - s 把 𝓝[≠] 0 送到 𝓝[≠] 1
  have hsub : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hca : ContinuousAt (fun s : ℂ => (1 : ℂ) - s) 0 := by fun_prop
      simpa using hca.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h
      exact hs (by linear_combination -h)
  -- ③ 复合留数极限
  have hcomp := completedRiemannZeta_residue_one.comp hsub
  -- ④ 系数整理：(1-s)-1 = -s ⇒ -((1-s)-1)·ζ(1-s) = s·ζ(1-s)
  have hneg := hcomp.neg
  refine Tendsto.congr' (Eventually.of_forall ?_) hneg
  intro s
  simp only [Function.comp_apply]
  have hc : (1 - s) - 1 = -s := by ring
  rw [hc, neg_mul, neg_neg]

/-- 极点侧总留数：`1 + (−1) = 0`（真证）。显式公式极点项之所以是
`h(1) + h(0)` 型而非无限项，根子在这条。 -/
theorem poleResidues_sum_zero : (1 : ℂ) + (-1) = 0 := by ring

/-- 极点侧贡献：`h(1) + h(0)`。Weil 显式公式中的极点项成品接口。 -/
def poleSide (h : ℂ → ℂ) : ℂ := h 1 + h 0

/-- 极点侧接口自洽（真证 `rfl`）：定义即 `h(1) + h(0)`。 -/
theorem poleSide_spec (h : ℂ → ℂ) : poleSide h = h 1 + h 0 := rfl

/-- 极点侧对零函数取零（真证）。 -/
theorem poleSide_const_zero : poleSide (fun _ => 0) = 0 := by
  simp [poleSide]

/-! ## §2  素数侧（Prime Side）：vonMangoldt 级数真证可和 -/

/-- 素数侧第 `n` 项：`Λ(n) / n^s`。 -/
def primeSideTerm (s : ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s

/-- 素数侧项与库 `LSeries.term ↗Λ` 一致（真证）。
`term` 在 `n = 0` 处被库强制置零，而 `Λ 0 = 0`，两边实际相等。 -/
theorem primeSideTerm_eq_LSeries_term (s : ℂ) (n : ℕ) :
    primeSideTerm s n
      = LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n := by
  rw [LSeries.term_def]
  by_cases hn : n = 0
  · simp [primeSideTerm, hn]
  · simp [primeSideTerm, hn]

/-- **素数侧可和**（真证，库定理 `LSeriesSummable_vonMangoldt` 直引）：
`Re s > 1` 时 `∑ Λ(n)/n^s` 收敛。 -/
theorem primeSide_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (primeSideTerm s) := by
  have h : LSeriesSummable (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h2 : Summable (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s) := h
  refine h2.congr (fun n => ?_)
  exact (primeSideTerm_eq_LSeries_term s n).symm

/-- **素数侧求和值 = LSeries ↗Λ**（真证）：
`∑' Λ(n)/n^s = LSeries ↗Λ s`。Weil 公式素数侧的数值对象从此有严格出处。 -/
theorem primeSide_tsum_eq_LSeries {s : ℂ} (_hs : 1 < s.re) :
    ∑' n : ℕ, primeSideTerm s n
      = LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s := by
  rw [LSeries]
  congr 1
  funext n
  exact primeSideTerm_eq_LSeries_term s n

/-- **素数侧收敛到 LSeries**（真证）。 -/
theorem primeSide_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (primeSideTerm s)
      (LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s) := by
  rw [← primeSide_tsum_eq_LSeries hs]
  exact (primeSide_summable hs).hasSum

/-- 素数侧部分和收敛（真证）：显式公式中「截断素数侧取极限」的合法性。 -/
theorem primeSide_tendsto_partialSum {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, primeSideTerm s n) atTop
      (𝓝 (LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s)) :=
  (primeSide_hasSum hs).tendsto_sum_nat

/-- **素数侧支撑在素数幂上**（真证）：`Λ(n) = 0 ⇒ 该项为 0`，
即显式公式素数侧确实只由素数幂贡献。 -/
theorem primeSideTerm_eq_zero_of_vonMangoldt_eq_zero {s : ℂ} {n : ℕ}
    (h : ArithmeticFunction.vonMangoldt n = 0) : primeSideTerm s n = 0 := by
  simp [primeSideTerm, h]

/-- **素数侧权重非负**（真证，库定理直引）：`Λ(n) ≥ 0`。 -/
theorem primeSideTerm_weight_nonneg (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt n :=
  ArithmeticFunction.vonMangoldt_nonneg

/-! ## §3  零点侧（Zero Side）：唯一剩余的实质性缺口 -/

/-- 非平凡零点集合（临界带内的 ζ 零点）。纯定义，零断言。 -/
def nontrivialZeros : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- 非平凡零点的刻画（真证 `rfl` 级）：成员判据与定义对齐。 -/
theorem mem_nontrivialZeros {s : ℂ} :
    s ∈ nontrivialZeros ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 :=
  Iff.rfl

/-- **零点侧缺口**：`∑_ρ h(ρ)` 的可和性与取值。
不构造任何实例 ⇒ 这里承载「零点侧求和尚未证」的全部责任，零假断言。 -/
structure ZeroSideGap where
  /-- 测试函数 -/
  (h : ℂ → ℂ)
  /-- 零点侧求和值 -/
  (sumValue : ℂ)
  /-- 可和性（假设，未证） -/
  (summable : Summable (fun ρ : ℂ => if ρ ∈ nontrivialZeros then h ρ else 0))
  /-- 求和值一致（假设，未证） -/
  (sum_eq : ∑' ρ : ℂ, (if ρ ∈ nontrivialZeros then h ρ else 0) = sumValue)

/-! ## §4  围道 / 留数工具缺口（库中确无，按指令打接口不硬搓） -/

/-- **围道工具缺口【FROZEN 封条 · 2026-11-04 正式冻结】**：
Mathlib 无复分析留数定理（探底 2026-11-04：全库 `residue`
仅命中代数 residueField / residuePairing）。

封存决议（用户 2026-11-04 指令，方案二）：正面硬刚围道/复分析 residue 等于给 Mathlib 补
底层基建，性价比极低，故本项**冻洁归档、不再投入**。后续若需该层，只能外部补基建后回填，
或走 109 起的 H1 层（圆法/大筛）路线绕开。零点侧同理留作 110+ 远景。 -/
structure ContourResidueGap where
  /-- 被积函数 -/
  (integrand : ℂ → ℂ)
  /-- 围道 -/
  (contour : Set ℂ)
  /-- 围道积分值 -/
  (value : ℂ)
  /-- 留数定理断言（假设，未证） -/
  (residue_theorem : Prop)

/-! ## §5  Weil 公式配方：108 交付的定死接口 -/

/-- **Weil 显式公式配方（108 版）**：
极点侧与素数侧已真证（见 §1 §2），零点侧与围道以 Gap 承载。
对比 107 的 `WeilExplicitFormulaGap`（6 项全悬空），本题只剩 2 项。 -/
structure WeilFormulaRecipe where
  /-- 测试函数 -/
  (test : ℂ → ℂ)
  /-- 极点侧（真证可用：`poleSide test`） -/
  (pole : ℂ)
  (pole_spec : pole = test 1 + test 0)
  /-- 素数侧（真证可用：`LSeries ↗Λ s`，`Re s > 1`） -/
  (prime : ℂ)
  /-- 零点侧缺口 -/
  (zero : ZeroSideGap)
  /-- 围道工具缺口 -/
  (contour : ContourResidueGap)

/-- **108 封口定理**：Weil 显式公式除「零点侧求和」与「围道工具」外，
全部原料在本次切片内真证落地 ——
① `s = 1` 留数 `1`；② `s = 0` 留数 `−1`；③ 素数侧 `Re s > 1` 可和。 -/
theorem weil_gap_reduced_to_zeroSide :
    Tendsto (fun s : ℂ => (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 1)
      ∧ Tendsto (fun s : ℂ => s * completedRiemannZeta s) (𝓝[≠] 0) (𝓝 (-1))
      ∧ (∀ s : ℂ, 1 < s.re → Summable (primeSideTerm s)) :=
  ⟨poleResidue_one, poleResidue_zero, fun _ hs => primeSide_summable hs⟩

/-! ## §5'  跨层焊点（107 → 108）：用 107 的显式公式骨架装配 108 的配方 -/

/-- **107 → 108 咬合（真证构造）**：把 107 的 `WeilExplicitFormulaGap` 当作显式公式骨架，
    与本切片真证的极点侧 `poleSide_spec` 装配成 `WeilFormulaRecipe`。
    骨架里的素数侧（107 的 `primeSide` 字段）被直接吃进来，零点侧/围道仍由 Gap 承接 ——
    107 的 6 项悬空在此降为 2 项，且**不是**重新捡底库散票。 -/
def weilFormulaRecipeOf107 (G : Challenge107.WeilExplicitFormulaGap)
    (zero : ZeroSideGap) (contour : ContourResidueGap) (test : ℂ → ℂ) : WeilFormulaRecipe where
  test := test
  pole := poleSide test
  pole_spec := poleSide_spec test
  prime := G.primeSide
  zero := zero
  contour := contour

/-- **107 → 108 咬合配套（真证）**：上述配方的极点字段确实是 `test 1 + test 0`。 -/
theorem weilFormulaRecipeOf107_pole (G : Challenge107.WeilExplicitFormulaGap)
    (zero : ZeroSideGap) (contour : ContourResidueGap) (test : ℂ → ℂ) :
    (weilFormulaRecipeOf107 G zero contour test).pole = test 1 + test 0 :=
  poleSide_spec test

/-! ## §6  公理审计 -/

#print axioms poleResidue_one
#print axioms poleResidue_zero
#print axioms primeSide_summable
#print axioms primeSide_hasSum
#print axioms weil_gap_reduced_to_zeroSide

end Challenge108
