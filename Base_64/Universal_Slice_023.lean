import Mathlib.Data.Nat.Prime.Defs

/-!
# Universal Slice 023: Mathematical induction on natural numbers

Pure textbook statement: the induction principle for the natural numbers,
applied directly through the eliminator `Nat.rec`, together with a concrete
induction proof.
-/

namespace UniversalSlice023

/-- The induction principle: from a base case and an induction step, conclude the
statement for every natural number. -/
theorem induction_principle (P : ℕ → Prop) (h0 : P 0) (hS : ∀ n : ℕ, P n → P (n + 1)) : ∀ n : ℕ, P n :=
  fun n => Nat.rec h0 hS n

/-- A concrete application of induction: n + 0 = n for every natural number n. -/
theorem add_zero_induction : ∀ n : ℕ, n + 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      Nat.succ n + 0 = Nat.succ (n + 0) := Nat.succ_add n 0
      _ = Nat.succ n := by rw [ih]

end UniversalSlice023

#print axioms UniversalSlice023.induction_principle
#print axioms UniversalSlice023.add_zero_induction
