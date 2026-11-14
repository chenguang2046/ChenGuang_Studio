import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# 独立命题：Dirichlet 级数（LSeries）在 Re(s) > 1 上的收敛性与解析性

命题（本文件完整验证，无 sorry，无自造假引理）：
1. LSeries（Dirichlet 级数）在其收敛半平面 Re(s) > 1 上绝对收敛。
   —— 一般表述：系数有界（∀ n ≠ 0, ‖f n‖ ≤ m）时，∀ s, 1 < s.re → LSeriesSummable f s。
   —— 特例：系数为常数 1。
2. 在上述区域内解析（holomorphic）。
3. 系数为常数 1 时，LSeries 退化为 riemannZeta（在 Re(s) > 1 上逐点相等）。

标注：
- 【现成】= 直接调用 mathlib 现成定理（注释注明来源文件）；
- 【自证】= 本文件自行完成的推导（组合现成组件或逐项比较级数）。
-/

noncomputable section

open Complex

/-! ## 1. 绝对收敛 -/

/-- 【现成】有界系数 → Re(s) > 1 时 LSeries 绝对收敛。
    直接引用 `LSeriesSummable_of_bounded_of_one_lt_re`
    （Mathlib/NumberTheory/LSeries/Basic.lean:393）。 -/
theorem bounded_LSeriesSummable_of_one_lt_re {f : ℕ → ℂ} {m : ℝ}
    (h : ∀ n ≠ 0, ‖f n‖ ≤ m) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f s :=
  LSeriesSummable_of_bounded_of_one_lt_re h hs

/-- 【自证】常数系数 1 特例：Re(s) > 1 时 ∑ 1 / n^s 绝对收敛。
    即上述现成定理在 m = 1 时的特化。 -/
theorem const_one_LSeriesSummable_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun _ => (1 : ℂ)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => by simp) hs

/-- 【现成】常数系数 1 的绝对收敛横坐标 ≤ 1。
    直接引用 `LSeries.abscissaOfAbsConv_le_of_le_const`
    （Mathlib/NumberTheory/LSeries/Convergence.lean:108）。 -/
lemma abscissaOfAbsConv_const_one_le :
    LSeries.abscissaOfAbsConv (fun _ => (1 : ℂ)) ≤ 1 := by
  exact LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, by intro n hn; simp⟩

/-! ## 2. 解析性 -/

/-- 【现成】一般情形：LSeries 在绝对收敛开半平面 {s | abscissaOfAbsConv f < s.re}
    上解析。直接引用 `LSeries_analyticOn`（Mathlib/NumberTheory/LSeries/Deriv.lean:161）。 -/
theorem LSeries_analyticOn_halfPlane (f : ℕ → ℂ) :
    AnalyticOn ℂ (LSeries f) {s | LSeries.abscissaOfAbsConv f < s.re} :=
  LSeries_analyticOn f

/-- 【自证】常数系数 1：LSeries (fun _ => 1) 在 Re(s) > 1 上解析。
    证明：由现成定理 `LSeries_analyticOn` 给出的解析域
    {s | abscissaOfAbsConv f < s.re}，配合现成横坐标界 abscissaOfAbsConv ≤ 1
    （上一节引理），自证集合包含 {s | 1 < s.re} ⊆ 解析域。 -/
theorem LSeries_analyticOn_const_one :
    AnalyticOn ℂ (LSeries (fun _ => (1 : ℂ))) {s | 1 < s.re} := by
  refine (LSeries_analyticOn (fun _ => (1 : ℂ))).mono ?_
  intro s hs
  have hsE : ((1 : ℝ) : EReal) < (s.re : EReal) := by exact_mod_cast hs
  exact lt_of_le_of_lt abscissaOfAbsConv_const_one_le hsE

/-! ## 3. 退化：常数系数 1 的 LSeries = riemannZeta（Re(s) > 1 上逐点相等） -/

/-- 【现成 + 自证】系数为常数 1 时 LSeries 退化为 riemannZeta。
    - 右侧展开 `riemannZeta s = ∑' n, 1 / n^s` 调用现成定理
      `zeta_eq_tsum_one_div_nat_cpow`（Mathlib/NumberTheory/LSeries/RiemannZeta.lean:207）；
    - 左侧按定义展开为 ∑' term，并与右侧逐项比较（自证：
      n = 0 时两边均为 0（Re(s) > 1 使 s ≠ 0），n ≠ 0 时系数为 1）。 -/
theorem LSeries_const_one_eq_riemannZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun _ => (1 : ℂ)) s = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  change (∑' n : ℕ, LSeries.term (fun _ => (1 : ℂ)) s n) = ∑' n : ℕ, 1 / (n : ℂ) ^ s
  refine tsum_congr fun n => ?_
  rw [LSeries.term_of_ne_zero' (Complex.ne_zero_of_one_lt_re hs)]

/-! ## 公理审计 -/

#print axioms bounded_LSeriesSummable_of_one_lt_re
#print axioms const_one_LSeriesSummable_of_one_lt_re
#print axioms LSeries_analyticOn_const_one
#print axioms LSeries_const_one_eq_riemannZeta_of_one_lt_re
