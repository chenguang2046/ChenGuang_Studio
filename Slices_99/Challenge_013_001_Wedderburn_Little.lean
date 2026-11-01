import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Field.Defs

/-!
# Challenge 013.1 — Wedderburn 小定理（有限除环必为域）

从 Challenge_013_Wedderburn.lean 拆分（台账 id 77 / no 013.1）。
mathlib 已收录 Wedderburn 小定理：`littleWedderburn` 是一个高优先级实例，
在 `[DivisionRing D] [Finite D]` 下自动提供 `Field D`。
本文件仅包含切片 1：`wedderburn_little`（Wedderburn 小定理的命题形式）。

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

end Wedderburn

end Challenge013

/-! # 公理审计 -/
#print axioms Challenge013.wedderburn_little
