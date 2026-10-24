import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Challenge 014 — 欧拉路径定理

连通图存在欧拉路径（遍历每条边恰一次的 trail）当且仅当奇度顶点数为 0 或 2。

mathlib（`SimpleGraph.Walk.IsEulerian`）已完整证明**必要性**方向：
- `IsEulerian.card_odd_degree`：欧拉遍历 ⟹ 奇度顶点数为 0 或 2；
- `IsEulerian.connected_of_forall_not_isIsolated`：欧拉遍历且无孤立点 ⟹ 连通；
- `IsEulerian.even_degree_iff`：非端点度偶 / 端点度奇。

**充分方向**（奇度顶点 0 或 2 ⟹ 存在欧拉路径）mathlib 在
`Mathlib/Combinatorics/SimpleGraph/Trails.lean` 的 TODO 中明确标注尚未收录
（需要 Hierholzer 构造算法），本文件如实记录该地基缺失，不硬钻不凑数。

本文件 4 个切片：必要方向核心、连通性、端点奇偶、握手引理支撑。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace SimpleGraph

namespace Challenge014

variable {V : Type*} (G : SimpleGraph V)

open SimpleGraph.Walk

/-- **切片 1 · 欧拉路径的必要条件（核心）**：若图存在欧拉遍历
（每条边恰好走一次），则奇度顶点数为 0（回路情形）或 2（开路径情形）。
直接包装 mathlib `IsEulerian.card_odd_degree`。 -/
theorem eulerian_exists_odd_degree_eq_zero_or_two [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v : V} {p : G.Walk u v} (ht : p.IsEulerian) :
    Fintype.card { v | Odd (G.degree v) } = 0 ∨
      Fintype.card { v | Odd (G.degree v) } = 2 :=
  ht.card_odd_degree

/-- **切片 2 · 欧拉遍历的连通性**：若欧拉遍历经过每个非孤立顶点
（即图无孤立点），则图连通。
包装 mathlib `IsEulerian.connected_of_forall_not_isIsolated`。 -/
theorem eulerian_connected_of_no_isolated [DecidableEq V] {u v : V} {p : G.Walk u v}
    (ht : p.IsEulerian) (hG : ∀ v, ¬G.IsIsolated v) : G.Connected :=
  ht.connected_of_forall_not_isIsolated hG

/-- **切片 3a · 非端点度数为偶**：欧拉遍历 `u → v` 中，
既非起点又非终点的顶点其度数为偶。 -/
theorem eulerian_nonendpoint_even_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v x : V} {p : G.Walk u v} (ht : p.IsEulerian)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    Even (G.degree x) := by
  rw [ht.even_degree_iff]
  intro _
  exact ⟨hxu, hxv⟩

/-- **切片 3b · 端点度数为奇**：开欧拉路径（`u ≠ v`）的两个端点
度数为奇（每个端点贡献奇次出入）。由 `even_degree_iff` 推出。 -/
theorem eulerian_endpoint_odd_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v : V} {p : G.Walk u v} (ht : p.IsEulerian)
    (huv : u ≠ v) :
    Odd (G.degree u) ∧ Odd (G.degree v) := by
  constructor
  · rw [← Nat.not_even_iff_odd, ht.even_degree_iff]
    intro h
    exact (h huv).1 rfl
  · rw [← Nat.not_even_iff_odd, ht.even_degree_iff]
    intro h
    exact (h huv).2 rfl

/-- **切片 4 · 握手引理支撑**：奇度顶点数必为偶数
（度数和 = 2·边数 在 ZMod 2 下取模），是欧拉定理组合论基础。
包装 mathlib `even_card_odd_degree_vertices`。 -/
theorem odd_degree_vertices_card_even [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] :
    Even (Finset.card (Finset.univ.filter fun v : V => Odd (G.degree v))) := by
  simpa using (even_card_odd_degree_vertices (G := G))

end Challenge014

end SimpleGraph

/-! # 公理审计 -/
#print axioms SimpleGraph.Challenge014.eulerian_exists_odd_degree_eq_zero_or_two
#print axioms SimpleGraph.Challenge014.eulerian_connected_of_no_isolated
#print axioms SimpleGraph.Challenge014.eulerian_nonendpoint_even_degree
#print axioms SimpleGraph.Challenge014.eulerian_endpoint_odd_degree
#print axioms SimpleGraph.Challenge014.odd_degree_vertices_card_even
