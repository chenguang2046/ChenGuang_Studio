import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Challenge 014.5 — 握手引理：奇度顶点数必为偶数

从 Challenge_014_Eulerian.lean 拆分（台账 id 85 / no 014.5）。
本文件仅包含切片 4：`odd_degree_vertices_card_even`
（包装 mathlib `even_card_odd_degree_vertices`）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace SimpleGraph

namespace Challenge014

variable {V : Type*} (G : SimpleGraph V)

open SimpleGraph.Walk

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
#print axioms SimpleGraph.Challenge014.odd_degree_vertices_card_even
