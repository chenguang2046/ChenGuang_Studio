import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Field.Defs

/-!
# Challenge 013.4 — 有限整环必为域（对照）

从 Challenge_013_Wedderburn.lean 拆分（台账 id 80 / no 013.4）。
本文件仅包含切片 4：`finite_domain_isField`（`Finite.isDomain_to_isField` 的直接包装）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace Challenge013

universe u

section Wedderburn

/-- **切片 4 · 对照定理**：有限整环必为域（Wedderburn 的较弱版本，
不需除环假设，`Finite.isDomain_to_isField` 的直接包装）。 -/
theorem finite_domain_isField (D : Type u) [Ring D] [IsDomain D] [Finite D] : IsField D := by
  exact Finite.isDomain_to_isField D

end Wedderburn

end Challenge013

/-! # 公理审计 -/
#print axioms Challenge013.finite_domain_isField
