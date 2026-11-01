import Mathlib.Data.Nat.Prime.Defs

/-!
# Universal Slice 029: De Morgan's laws

Pure textbook statement: the propositional forms of De Morgan's laws,
complement of a disjunction and complement of a conjunction.
-/

namespace UniversalSlice029

/-- De Morgan for disjunction: not (p or q) iff (not p) and (not q). -/
theorem deMorgan_or (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  not_or

/-- De Morgan for conjunction: not (p and q) iff (not p) or (not q). -/
theorem deMorgan_and (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  classical
  constructor
  · intro h
    by_cases hp : p
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  · intro h hpq
    rcases h with hp | hq
    · exact hp hpq.1
    · exact hq hpq.2

end UniversalSlice029

#print axioms UniversalSlice029.deMorgan_or
#print axioms UniversalSlice029.deMorgan_and
