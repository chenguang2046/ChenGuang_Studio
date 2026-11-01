import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Challenge 014.3 — 非端点度数为偶

从 Challenge_014_Eulerian.lean 拆分（台账 id 83 / no 014.3）。
本文件仅包含切片 3a：`eulerian_nonendpoint_even_degree`
（由 `IsEulerian.even_degree_iff` 推出）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace SimpleGraph

namespace Challenge014

variable {V : Type*} (G : SimpleGraph V)

open SimpleGraph.Walk

/-- **切片 3a · 非端点度数为偶**：欧拉遍历 `u → v` 中，
既非起点又非终点的顶点其度数为偶。 -/
theorem eulerian_nonendpoint_even_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v x : V} {p : G.Walk u v} (ht : p.IsEulerian)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    Even (G.degree x) := by
  rw [ht.even_degree_iff]
  intro _
  exact ⟨hxu, hxv⟩

end Challenge014

end SimpleGraph

/-! # 公理审计 -/
#print axioms SimpleGraph.Challenge014.eulerian_nonendpoint_even_degree
