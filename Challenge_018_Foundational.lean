/-
Challenge_018_Foundational.lean
底层基础定理切片 2 片（累计 97 -> 99）
1. nat_well_ordering: 良序原理 / 最小数原理（自然数）
2. real_uncountable : 实数不可数（康托对角线思想）
良序为手搓（Nat.find），实数不可数为 mathlib `not_countable_real` 包装。
无占位未完成记号。
-/
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.Real.Cardinality

namespace Challenge018

/-- 良序原理（最小数原理）：自然数的非空可判子集必有最小元。
    手搓：利用 `Nat.find`。 -/
theorem nat_well_ordering {P : ℕ → Prop} [DecidablePred P] (h : ∃ n, P n) :
    ∃ m, P m ∧ ∀ k < m, ¬ P k :=
  ⟨Nat.find h, Nat.find_spec h, fun _k hk => Nat.find_min h hk⟩

/-- 实数不可数：全体实数不是可数集。
    来自 mathlib `not_countable_real`。 -/
theorem real_uncountable : ¬(Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real

end Challenge018

/-! # 公理审计 -/
#print axioms Challenge018.nat_well_ordering
#print axioms Challenge018.real_uncountable
