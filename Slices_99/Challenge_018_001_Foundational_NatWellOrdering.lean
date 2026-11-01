/-
Challenge_018_001_Foundational_NatWellOrdering.lean
从 Challenge_018_Foundational.lean 拆分（台账 id 98 / no 018.1）
底层基础定理切片 1/2：良序原理 / 最小数原理（自然数）。
良序为手搓（Nat.find），无占位未完成记号。
-/
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.Real.Cardinality

namespace Challenge018

/-- 良序原理（最小数原理）：自然数的非空可判子集必有最小元。
    手搓：利用 `Nat.find`。 -/
theorem nat_well_ordering {P : ℕ → Prop} [DecidablePred P] (h : ∃ n, P n) :
    ∃ m, P m ∧ ∀ k < m, ¬ P k :=
  ⟨Nat.find h, Nat.find_spec h, fun _k hk => Nat.find_min h hk⟩

end Challenge018

/-! # 公理审计 -/
#print axioms Challenge018.nat_well_ordering
