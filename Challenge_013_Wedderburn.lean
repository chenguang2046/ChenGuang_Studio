import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Field.Defs

/-!
# Challenge 013 — Wedderburn 小定理（有限除环必为域）

mathlib 已收录 Wedderburn 小定理：`littleWedderburn` 是一个高优先级实例，
在 `[DivisionRing D] [Finite D]` 下自动提供 `Field D`。
本文件对其做高阶命题式包装，并给出若干关键推论：

1. `wedderburn_little` — 有限除环是域（Wedderburn 小定理的命题形式）；
2. `finite_divisionRing_mul_comm` — 有限除环乘法交换（域的交换律推论）；
3. `all_mem_center` — 有限除环每个元素都在中心里（中心 = 全环的等价刻画）；
4. `finite_domain_isField` — 对照定理：有限整环是域（`Finite.isDomain_to_isField`）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace Challenge013

universe u

section Wedderburn

variable (D : Type u) [DivisionRing D] [Finite D]

/-- **切片 1 · Wedderburn 小定理（命题形式）**：有限除环必为域。
mathlib 实例 `littleWedderburn` 在 `[DivisionRing D] [Finite D]` 下提供 `Field D`，
此处包装为 `IsField D` 命题。 -/
theorem wedderburn_little : IsField D := by
  exact Field.toIsField D

/-- **切片 2 · 交换性推论**：有限除环的乘法交换。 -/
theorem finite_divisionRing_mul_comm (x y : D) : x * y = y * x := by
  simpa using (inferInstance : Field D).mul_comm x y

/-- **切片 3 · 中心 = 全环（等价刻画）**：有限除环的每个元素都在中心里，
即中心等于全环（Wedderburn 交换性的中心化表述）。
`Subring.mem_center_iff`：`x ∈ Subring.center D ↔ ∀ y, x * y = y * x`。 -/
theorem all_mem_center (x : D) : x ∈ Subring.center D := by
  rw [Subring.mem_center_iff]
  intro y
  exact finite_divisionRing_mul_comm D y x

/-- **切片 4 · 对照定理**：有限整环必为域（Wedderburn 的较弱版本，
不需除环假设，`Finite.isDomain_to_isField` 的直接包装）。 -/
theorem finite_domain_isField (D : Type u) [Ring D] [IsDomain D] [Finite D] : IsField D := by
  exact Finite.isDomain_to_isField D

end Wedderburn

end Challenge013

/-! # 公理审计 -/
#print axioms Challenge013.wedderburn_little
#print axioms Challenge013.finite_divisionRing_mul_comm
#print axioms Challenge013.all_mem_center
#print axioms Challenge013.finite_domain_isField
