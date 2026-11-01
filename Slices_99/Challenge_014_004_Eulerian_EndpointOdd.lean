import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Challenge 014.4 — 端点度数为奇

从 Challenge_014_Eulerian.lean 拆分（台账 id 84 / no 014.4）。
本文件仅包含切片 3b：`eulerian_endpoint_odd_degree`
（开欧拉路径 `u ≠ v` 的两个端点度数为奇，由 `even_degree_iff` 推出）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace SimpleGraph

namespace Challenge014

variable {V : Type*} (G : SimpleGraph V)

open SimpleGraph.Walk

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

end Challenge014

end SimpleGraph

/-! # 公理审计 -/
#print axioms SimpleGraph.Challenge014.eulerian_endpoint_odd_degree
