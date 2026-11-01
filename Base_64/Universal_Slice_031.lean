import Mathlib.Data.Set.Finite.Basic

/-!
# Universal Slice 031: Infinite sets and equinumerosity with the naturals

Pure textbook statement: an infinite type admits injective maps from the
natural numbers, and every injective image of an infinite type is infinite.
-/

namespace UniversalSlice031

/-- The natural numbers form an infinite type. -/
theorem infinite_nat : Infinite ℕ :=
  inferInstance

/-- A type is infinite iff its universal set is infinite. -/
theorem infinite_univ_iff {α : Type*} : Set.Infinite (Set.univ : Set α) ↔ Infinite α :=
  Set.infinite_univ_iff

/-- The universal set of an infinite type is infinite. -/
theorem infinite_univ {α : Type*} [Infinite α] : Set.Infinite (Set.univ : Set α) :=
  Set.infinite_univ

/-- The range of an injective map out of an infinite type is infinite. -/
theorem infinite_range_of_injective {α β : Type*} [Infinite α] {f : α → β} (hf : Function.Injective f) :
    Set.Infinite (Set.range f) :=
  Set.infinite_range_of_injective hf

/-- An injective embedding of the naturals into a set witnesses its infinity. -/
theorem infinite_of_injective_forall_mem {β : Type*} (s : Set β) (f : ℕ → β) (hf : Function.Injective f)
    (hsub : ∀ n : ℕ, f n ∈ s) : s.Infinite :=
  Set.infinite_of_injective_forall_mem hf hsub

end UniversalSlice031

#print axioms UniversalSlice031.infinite_nat
#print axioms UniversalSlice031.infinite_univ_iff
#print axioms UniversalSlice031.infinite_univ
#print axioms UniversalSlice031.infinite_range_of_injective
#print axioms UniversalSlice031.infinite_of_injective_forall_mem
