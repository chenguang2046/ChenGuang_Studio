import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Challenge 014.1 — 欧拉路径的必要条件（核心）

从 Challenge_014_Eulerian.lean 拆分（台账 id 81 / no 014.1）。
连通图存在欧拉路径（遍历每条边恰一次的 trail）当且仅当奇度顶点数为 0 或 2；
本文件包含必要方向核心：`eulerian_exists_odd_degree_eq_zero_or_two`
（包装 mathlib `IsEulerian.card_odd_degree`）。

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

end Challenge014

end SimpleGraph

/-! # 公理审计 -/
#print axioms SimpleGraph.Challenge014.eulerian_exists_odd_degree_eq_zero_or_two
