/-
Challenge_016_003_Group_Cauchy.lean
从 Challenge_016_Group_Theorems.lean 拆分（台账 id 91 / no 016.3）
经典群论定理切片 3/3：Cauchy 定理（p 阶元存在）。
mathlib 现成定理包装，无占位未完成记号。
-/
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Basic

namespace Challenge016

universe u

/-- Cauchy 定理：若素数 p 整除有限群阶，则存在阶恰为 p 的元素。
    来自 mathlib `exists_prime_orderOf_dvd_card'`。 -/
theorem cauchy_prime_order {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hdvd : p ∣ Nat.card G) : ∃ x : G, orderOf x = p :=
  exists_prime_orderOf_dvd_card' p hdvd

end Challenge016

/-! # 公理审计 -/
#print axioms Challenge016.cauchy_prime_order
