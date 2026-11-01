/-
Challenge_016_001_Group_Lagrange.lean
从 Challenge_016_Group_Theorems.lean 拆分（台账 id 89 / no 016.1）
经典群论定理切片 1/3：拉格朗日定理（子群阶整除群阶）。
mathlib 现成定理包装，无占位未完成记号。
-/
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Basic

namespace Challenge016

universe u

/-- 拉格朗日定理：有限群的子群阶整除群阶。
    来自 mathlib `Subgroup.index_mul_card`。 -/
theorem lagrange_card_dvd {G : Type u} [Group G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G := by
  rw [← Subgroup.index_mul_card H]
  simpa [mul_comm] using dvd_mul_right (a := Nat.card H) (b := H.index)

end Challenge016

/-! # 公理审计 -/
#print axioms Challenge016.lagrange_card_dvd
