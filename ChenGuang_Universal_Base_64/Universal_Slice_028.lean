import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Universal Slice 028: Completeness of the real numbers

Pure textbook statement: the least-upper-bound (completeness) principle for
the real numbers, expressed through the supremum of a nonempty bounded-above set.
-/

namespace UniversalSlice028

/-- The supremum of a nonempty bounded-above set is its least upper bound. -/
theorem isLUB_sSup {s : Set ℝ} (hne : s.Nonempty) (hb : BddAbove s) : IsLUB s (sSup s) :=
  isLUB_csSup hne hb

/-- Every element of a bounded-above set is bounded by its supremum. -/
theorem le_sSup {s : Set ℝ} (hb : BddAbove s) {a : ℝ} (ha : a ∈ s) : a ≤ sSup s :=
  le_csSup hb ha

/-- If every element of s is at most a, then the supremum is at most a. -/
theorem sSup_le {s : Set ℝ} (hne : s.Nonempty) {a : ℝ} (ha : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  csSup_le hne ha

end UniversalSlice028

#print axioms UniversalSlice028.isLUB_sSup
#print axioms UniversalSlice028.le_sSup
#print axioms UniversalSlice028.sSup_le
