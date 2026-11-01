/-
Challenge_018_002_Foundational_RealUncountable.lean
从 Challenge_018_Foundational.lean 拆分（台账 id 99 / no 018.2）
底层基础定理切片 2/2：实数不可数（康托对角线思想）。
实数不可数为 mathlib `not_countable_real` 包装，无占位未完成记号。
-/
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.Real.Cardinality

namespace Challenge018

/-- 实数不可数：全体实数不是可数集。
    来自 mathlib `not_countable_real`。 -/
theorem real_uncountable : ¬(Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real

end Challenge018

/-! # 公理审计 -/
#print axioms Challenge018.real_uncountable
