import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Field.Defs
import ChenGuang_99_Slices.Challenge_013_002_Wedderburn_MulComm

/-!
# Challenge 013.3 — 有限除环中心 = 全环

从 Challenge_013_Wedderburn.lean 拆分（台账 id 79 / no 013.3）。
本文件仅包含切片 3：`all_mem_center`（中心 = 全环的等价刻画）。
证明原样引用同 namespace 的 `finite_divisionRing_mul_comm`
（定义于 Challenge_013_002_Wedderburn_MulComm.lean，见其 import）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace Challenge013

universe u

section Wedderburn

variable (D : Type u) [DivisionRing D] [Finite D]

/-- **切片 3 · 中心 = 全环（等价刻画）**：有限除环的每个元素都在中心里，
即中心等于全环（Wedderburn 交换性的中心化表述）。
`Subring.mem_center_iff`：`x ∈ Subring.center D ↔ ∀ y, x * y = y * x`。 -/
theorem all_mem_center (x : D) : x ∈ Subring.center D := by
  rw [Subring.mem_center_iff]
  intro y
  exact finite_divisionRing_mul_comm D y x

end Wedderburn

end Challenge013

/-! # 公理审计 -/
#print axioms Challenge013.all_mem_center
