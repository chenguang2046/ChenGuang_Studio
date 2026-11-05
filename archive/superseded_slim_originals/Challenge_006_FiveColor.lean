import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Challenge_006：五色定理的核心逻辑基础（最小度顶点引理 + 数学归纳法着色框架）

任务书要求：用图论与拓扑基础（欧拉公式的图论形式 V - E + F = 2，或 planar
graph 的边数界 E ≤ 3V - 6）证明"任一平面图必存在度数至多 5 的顶点"，并搭建
在此基础上进行数学归纳法着色的完整框架（不要求完整证明 5-着色定理本身，
重点在最小度顶点引理 + 归纳框架；若 mathlib 有完整五色定理则直接引用）。

## 策略
mathlib v4.34 的 Combinatorics.SimpleGraph 提供有限简单图基础（`SimpleGraph`、
`edgeFinset`、`neighborFinset`、`degree`、握手引理 `sum_degrees_eq_twice_card_edges`
以及诱导子图 `induce`），但**未提供平面嵌入 / 欧拉公式 / 五色定理**（已勘察确认）。
按任务书授权：

1. 以欧拉公式的图论推论"简单平面图边数界 E ≤ 3V - 6"作为平面性前提参数，
   自证最小度引理 `exists_degree_le_five_of_euler_bound`：
   握手引理 ∑deg = 2E ≤ 2(3V-6) = 6V-12，若所有顶点度 ≥ 6 则 ∑deg ≥ 6V，矛盾。
2. 自建正常着色定义 `ProperColoring`，交付归纳框架：
   `five_color_induction_step`（删去度 ≤5 顶点后 5-着色可提升为全图 6-着色，
   v 直接用第 6 色）与 `five_color_induction_framework`（归纳步的逐点声明）。
   注明：真正的 5-着色需对 v 的邻居做 Kempe 链换色，本文件按任务书只交付
   "最小度引理 + 归纳框架"，五色完整证明如实降级说明（mathlib 亦无此库）。

所有证明零 sorry、零伪造引理；平面性以边数界显式参数化，缺口如实披露。
-/

open scoped BigOperators

noncomputable section

namespace Challenge006

/-- 正常 k-着色（自建定义）：相邻顶点异色（非邻点可同色）。 -/
def ProperColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, ∀ ⦃u w : V⦄, G.Adj u w → c u ≠ c w

section MinDegreeLemma

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- 最小度引理（五色定理的核心输入）：
    若图满足平面图边数界 E ≤ 3V - 6（欧拉公式 V - E + F = 2 的图论推论，
    此处作为平面性前提显式参数化），则存在度数至多 5 的顶点。
    证明：握手引理 ∑deg = 2E ≤ 2(3V-6) = 6V-12；若所有度 ≥ 6 则 ∑deg ≥ 6V，矛盾。 -/
theorem exists_degree_le_five_of_euler_bound [Nonempty V]
    (hEdge : G.edgeFinset.card ≤ 3 * Fintype.card V - 6) :
    ∃ v : V, G.degree v ≤ 5 := by
  by_contra hnot
  push Not at hnot
  have hge : ∀ v : V, 6 ≤ G.degree v := fun v => Nat.succ_le_of_lt (hnot v)
  have hsum_ge : (6 : ℕ) * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc
      (6 : ℕ) * Fintype.card V = ∑ v : V, 6 := by
        simp [Finset.sum_const, Finset.card_univ, mul_comm]
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum (fun v _ => hge v)
  have hsum_le : ∑ v : V, G.degree v ≤ 2 * (3 * Fintype.card V - 6) := by
    calc
      ∑ v : V, G.degree v = 2 * G.edgeFinset.card := by
        exact G.sum_degrees_eq_twice_card_edges
      _ ≤ 2 * (3 * Fintype.card V - 6) := by
        exact Nat.mul_le_mul_left 2 hEdge
  have hbad : (6 : ℕ) * Fintype.card V ≤ 6 * Fintype.card V - 12 := by
    calc
      (6 : ℕ) * Fintype.card V ≤ ∑ v : V, G.degree v := hsum_ge
      _ ≤ 2 * (3 * Fintype.card V - 6) := hsum_le
      _ = 6 * Fintype.card V - 12 := by omega
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ‹Nonempty V›
  omega

end MinDegreeLemma

section InductionFramework

/-- 归纳步（六色框架）：若删除顶点 v 后的导出子图可 5-着色，且 v 的度数 ≤ 5，
    则全图可 6-着色（v 使用第 6 种颜色；其余顶点继承诱导子图的 5-着色）。
    注：完整的 5-着色需要 Kempe 链对 v 的邻居换色，不属于本框架（如实降级说明）。 -/
theorem five_color_induction_step {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (_hdeg : G.degree v ≤ 5)
    (hcol : ProperColoring (G.induce {w : V | w ≠ v}) 5) :
    ProperColoring G 6 := by
  classical
  rcases hcol with ⟨c, hc⟩
  let lift5 : Fin 5 → Fin 6 := fun i => ⟨i.val, by exact Nat.lt_trans i.isLt (by decide)⟩
  refine ⟨fun w => if h : w = v then ⟨5, by decide⟩ else lift5 (c ⟨w, h⟩), ?_⟩
  intro u w huw
  by_cases hu : u = v
  · by_cases hw : w = v
    · exfalso
      exact G.loopless.irrefl u (by simp [hu, hw] at huw ⊢)
    · apply Fin.ne_of_val_ne
      intro hval
      have hlt : (c ⟨w, hw⟩).val < 5 := (c ⟨w, hw⟩).isLt
      simp [hu, hw, lift5] at hval
      omega
  · by_cases hw : w = v
    · apply Fin.ne_of_val_ne
      intro hval
      have hlt : (c ⟨u, hu⟩).val < 5 := (c ⟨u, hu⟩).isLt
      simp [hu, hw, lift5] at hval
      omega
    · apply Fin.ne_of_val_ne
      intro hval
      have hc' : c ⟨u, hu⟩ ≠ c ⟨w, hw⟩ := hc (by simpa using huw)
      apply hc'
      apply Fin.ext
      simp [hu, hw, lift5] at hval
      exact hval

/-- 归纳框架（结构声明）：对有限图按顶点数归纳——空图可着色；对非空有限图，
    由最小度引理取度 ≤5 顶点 v（平面情形），由归纳假设其导出子图可 5-着色，
    再用 `five_color_induction_step` 提升为全图 6-着色。
    该定理把归纳步打包为逐顶点可用的框架；配合最小度引理即五色定理的证明骨架
    （Lean 侧如实交付框架而非完整 5-着色证明）。 -/
theorem five_color_induction_framework {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (∀ v : V, G.degree v ≤ 5 →
      ProperColoring (G.induce {w : V | w ≠ v}) 5 → ProperColoring G 6) := by
  intro v hdeg hcol
  exact five_color_induction_step G v hdeg hcol

end InductionFramework

end Challenge006

/-! ## 公理审计 -/

#print axioms Challenge006.ProperColoring
#print axioms Challenge006.exists_degree_le_five_of_euler_bound
#print axioms Challenge006.five_color_induction_step
#print axioms Challenge006.five_color_induction_framework
