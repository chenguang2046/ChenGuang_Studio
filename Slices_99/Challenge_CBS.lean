/-
Challenge 1: Cantor-Bernstein-Schroeder theorem
================================================

Statement (CBS): if there is an injection `A → B` and an injection `B → A`,
then there exists a bijection `A → B`.

Mathlib status: the theorem is available in the standard library as
`Function.Embedding.schroeder_bernstein` (Mathlib/SetTheory/Cardinal/SchroederBernstein.lean).
The three results below are direct references to (or one-line corollaries of) that theorem
and the cardinal order machinery in `SetTheory.Cardinal.Order`.

Academic note: the proof of `Function.Embedding.schroeder_bernstein` is a fixed-point
construction (`Set.FixedPoints.lfp`) on the complete lattice of subsets of `A`; the
bijection is defined as `s.piecewise f (invFun g)`. No `sorry`, no invented lemmas.
-/
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.SetTheory.Cardinal.Order

open scoped Cardinal

namespace GoldbachChallenge

open Function

universe u

/-- **CBS theorem (function form)**: injections in both directions yield a bijection.
Directly invokes the library theorem `Function.Embedding.schroeder_bernstein`. -/
theorem schroeder_bernstein {α β : Type u} {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h :=
  Function.Embedding.schroeder_bernstein hf hg

/-- **CBS theorem (cardinal form)**: the two injections give `#α ≤ #β` and `#β ≤ #α`,
hence `#α = #β` by antisymmetry of the partial order on cardinals. -/
theorem mk_eq_of_injective {α β : Type u} {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    #α = #β :=
  le_antisymm (Cardinal.mk_le_of_injective hf) (Cardinal.mk_le_of_injective hg)

/-- **CBS theorem (embedding form)**: embeddings in both directions yield an equivalence.
Directly invokes the library theorem `Function.Embedding.antisymm`. -/
theorem equiv_of_embeddings {α β : Type u} (e₁ : α ↪ β) (e₂ : β ↪ α) :
    Nonempty (α ≃ β) :=
  Function.Embedding.antisymm e₁ e₂

end GoldbachChallenge
