import Mathlib.Logic.Function.Basic

/-!
# Universal Slice 030: Injective, surjective and bijective functions

Pure textbook statement: bijectivity is equivalent to injectivity together
with surjectivity, to the existence of a two-sided inverse, and to the
property that every value has a unique preimage.
-/

namespace UniversalSlice030

/-- Bijective iff injective and surjective. -/
theorem bijective_iff_inj_surj {α β : Type*} (f : α → β) :
    Function.Injective f ∧ Function.Surjective f ↔ Function.Bijective f := by
  rfl

/-- The identity function is bijective. -/
theorem bijective_id {α : Type*} : Function.Bijective (@id α) :=
  Function.bijective_id

/-- Bijective iff the function has a two-sided inverse. -/
theorem bijective_iff_has_inverse {α β : Type*} (f : α → β) :
    Function.Bijective f ↔ ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  Function.bijective_iff_has_inverse

/-- Bijective iff every value has a unique preimage. -/
theorem bijective_iff_existsUnique {α β : Type*} (f : α → β) :
    Function.Bijective f ↔ ∀ b : β, ∃! a : α, f a = b :=
  Function.bijective_iff_existsUnique f

end UniversalSlice030

#print axioms UniversalSlice030.bijective_iff_inj_surj
#print axioms UniversalSlice030.bijective_id
#print axioms UniversalSlice030.bijective_iff_has_inverse
#print axioms UniversalSlice030.bijective_iff_existsUnique
