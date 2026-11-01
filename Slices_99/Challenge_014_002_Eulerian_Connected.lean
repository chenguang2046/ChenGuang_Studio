import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Challenge 014.2 — 欧拉遍历的连通性

从 Challenge_014_Eulerian.lean 拆分（台账 id 82 / no 014.2）。
本文件仅包含切片 2：`eulerian_connected_of_no_isolated`
（包装 mathlib `IsEulerian.connected_of_forall_not_isIsolated`）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace SimpleGraph

namespace Challenge014

variable {V : Type*} (G : SimpleGraph V)

open SimpleGraph.Walk

/-- **切片 2 · 欧拉遍历的连通性**：若欧拉遍历经过每个非孤立顶点
（即图无孤立点），则图连通。
包装 mathlib `IsEulerian.connected_of_forall_not_isIsolated`。 -/
theorem eulerian_connected_of_no_isolated [DecidableEq V] {u v : V} {p : G.Walk u v}
    (ht : p.IsEulerian) (hG : ∀ v, ¬G.IsIsolated v) : G.Connected :=
  ht.connected_of_forall_not_isIsolated hG

end Challenge014

end SimpleGraph

/-! # 公理审计 -/
#print axioms SimpleGraph.Challenge014.eulerian_connected_of_no_isolated
