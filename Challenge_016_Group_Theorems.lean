/-
Challenge_016_Group_Theorems.lean
经典群论定理切片 3 片（累计 88 -> 91）
1. lagrange_card_dvd   : 拉格朗日定理（子群阶整除群阶）
2. cayley_embedding    : 凯莱定理（群嵌入置换群）
3. cauchy_prime_order  : Cauchy 定理（p 阶元存在）
全部为 mathlib 现成定理包装或纯逻辑手搓，无占位未完成记号。
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

/-- 凯莱定理：每个群可以嵌入其自身上的置换群（左正则表示）。 -/
theorem cayley_embedding {G : Type u} [Group G] : Nonempty (G ↪ Equiv.Perm G) := by
  let f : G → Equiv.Perm G := fun a =>
    { toFun := fun b => a * b
      invFun := fun b => a⁻¹ * b
      left_inv := by
        intro b
        simp
      right_inv := by
        intro b
        simp }
  refine ⟨⟨f, ?_⟩⟩
  intro a b h
  simpa [f] using congrFun (congrArg Equiv.toFun h) 1

/-- Cauchy 定理：若素数 p 整除有限群阶，则存在阶恰为 p 的元素。
    来自 mathlib `exists_prime_orderOf_dvd_card'`。 -/
theorem cauchy_prime_order {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hdvd : p ∣ Nat.card G) : ∃ x : G, orderOf x = p :=
  exists_prime_orderOf_dvd_card' p hdvd

end Challenge016

/-! # 公理审计 -/
#print axioms Challenge016.lagrange_card_dvd
#print axioms Challenge016.cayley_embedding
#print axioms Challenge016.cauchy_prime_order
