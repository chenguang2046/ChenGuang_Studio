import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Field.Defs

/-!
# Challenge 013.2 — 有限除环乘法交换

从 Challenge_013_Wedderburn.lean 拆分（台账 id 78 / no 013.2）。
mathlib 实例 `littleWedderburn` 在 `[DivisionRing D] [Finite D]` 下提供 `Field D`。
本文件仅包含切片 2：`finite_divisionRing_mul_comm`（域的交换律推论）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace Challenge013

universe u

section Wedderburn

variable (D : Type u) [DivisionRing D] [Finite D]

/-- **切片 2 · 交换性推论**：有限除环的乘法交换。 -/
theorem finite_divisionRing_mul_comm (x y : D) : x * y = y * x := by
  simpa using (inferInstance : Field D).mul_comm x y

end Wedderburn

end Challenge013

/-! # 公理审计 -/
#print axioms Challenge013.finite_divisionRing_mul_comm
