/-
Challenge_016_002_Group_Cayley.lean
从 Challenge_016_Group_Theorems.lean 拆分（台账 id 90 / no 016.2）
经典群论定理切片 2/3：凯莱定理（群嵌入置换群）。
纯逻辑手搓，无占位未完成记号。
-/
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Basic

namespace Challenge016

universe u

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

end Challenge016

/-! # 公理审计 -/
#print axioms Challenge016.cayley_embedding
