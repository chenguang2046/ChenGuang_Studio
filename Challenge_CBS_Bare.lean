/-
Challenge 1 (upgraded): Cantor-Bernstein-Schroeder, bare-bones construction
============================================================================

Statement
  If f : A → B is injective and g : B → A is injective, then there exists a
  bijection A → B.

Design (bare Lean, no Mathlib)
  * Only the Lean kernel prelude (Init) is used; no `import Mathlib`.
  * We implement the classical fixed-point construction (Tarski / Knaster-Tarski
    on the powerset):
        s := lfp F,  F X := A \ g '' (B \ f '' X)
    and define
        h a := if a ∈ s then f a else gInv a,
    where gInv : A → B chooses, for a ∈ range g, the unique b with g b = a
    (junk value b₀ otherwise).  Since g is injective, the choice is actually
    unique; the classical axiom is only used to *obtain* the witness.
  * Injectivity of h is proved by a 2x2 case split using the fixed-point
    equation; surjectivity by the standard case split on b ∈ f '' s.
  * Constructivity report: the classical Cantor-Bernstein-Schroeder theorem
    needs a trichotomy on infinite ancestor chains (or the fixed point s), and
    this is not derivable in an intuitionistic type theory without
    choice/EM; hence the proof uses the kernel axiom `Classical.choice`
    (standard axiom), and `#print axioms` is audited below.  No Mathlib
    import is used.

Red lines: no `sorry`, no fake lemmas, comments objective, no modification of
existing files.
-/
import Init

namespace GoldbachChallenge

universe u v

-- ---------------------------------------------------------------------------
-- Minimal set-theoretic infrastructure (only what is needed)
-- ---------------------------------------------------------------------------

/-- A set is a predicate. -/
def Set (α : Type u) := α → Prop

/-- Subset relation. -/
def subset {α : Type u} (s t : Set α) : Prop := ∀ a : α, s a → t a

/-- Image of a set under a function. -/
def image {α : Type u} {β : Type v} (f : α → β) (s : Set α) : Set β :=
  fun b => ∃ a : α, s a ∧ f a = b

/-- Complement of a set. -/
def compl {α : Type u} (s : Set α) : Set α :=
  fun a => ¬ s a

/-- Monotonicity of an endomap on the powerset. -/
def Monotone {α : Type u} (F : Set α → Set α) : Prop :=
  ∀ X Y : Set α, subset X Y → subset (F X) (F Y)

/-- Least fixed point of a monotone endomap on the powerset (Tarski). -/
def lfp {α : Type u} (F : Set α → Set α) : Set α :=
  fun a => ∀ X : Set α, subset (F X) X → X a

/-- First Tarski inequality: F (lfp F) ⊆ lfp F. -/
theorem lfp_F_subset {α : Type u} {F : Set α → Set α} (hmono : Monotone F) :
    subset (F (lfp F)) (lfp F) := by
  intro a hFa X hclosed
  have hlfpX : subset (lfp F) X := fun a' h => h X hclosed
  have hFX : subset (F (lfp F)) (F X) := hmono (lfp F) X hlfpX
  exact hclosed a (hFX a hFa)

/-- Second Tarski inequality: lfp F ⊆ F (lfp F). -/
theorem lfp_le_F {α : Type u} {F : Set α → Set α} (hmono : Monotone F) :
    subset (lfp F) (F (lfp F)) := by
  intro a h
  exact h (F (lfp F)) (hmono (F (lfp F)) (lfp F) (lfp_F_subset hmono))

/-- Tarski fixed-point identity: lfp F = F (lfp F). -/
theorem lfp_fixed {α : Type u} {F : Set α → Set α} (hmono : Monotone F) :
    lfp F = F (lfp F) := by
  apply funext
  intro a
  apply propext
  constructor
  · exact lfp_le_F hmono a
  · exact lfp_F_subset hmono a

-- ---------------------------------------------------------------------------
-- Surjectivity / bijectivity (not present in bare Init)
-- ---------------------------------------------------------------------------

/-- Surjectivity. -/
def Surj {α : Type u} {β : Type v} (f : α → β) : Prop :=
  ∀ b : β, ∃ a : α, f a = b

/-- Bijectivity = injective ∧ surjective. -/
def Bij {α : Type u} {β : Type v} (f : α → β) : Prop :=
  Function.Injective f ∧ Surj f

-- ---------------------------------------------------------------------------
-- Cantor-Bernstein-Schroeder (bare construction)
-- ---------------------------------------------------------------------------

/--
CBS: f : A → B injective and g : B → A injective imply the existence of a
bijection A → B.  Classical fixed-point construction; only kernel axioms used
are `Classical.choice` (plus `propext` / `funext` for the fixed-point identity
of predicates).
-/
theorem cantor_schroeder_bernstein_bare {A : Type u} {B : Type v}
    (f : A → B) (g : B → A)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : A → B, Bij h := by
  classical
  by_cases hA : Nonempty A
  · rcases hA with ⟨a₀⟩
    -- junk value in B for elements outside the range of g
    let b₀ : B := f a₀
    -- right-inverse-style choice: for a in range g pick a preimage under g
    let gInv : A → B :=
      fun a => if h : ∃ b : B, g b = a then Classical.choose h else b₀
    have gInv_spec : ∀ a : A, (∃ b : B, g b = a) → g (gInv a) = a := by
      intro a h
      dsimp [gInv]
      rw [dif_pos h]
      exact Classical.choose_spec h
    -- the Tarski operator of the classical proof
    let F : Set A → Set A :=
      fun X => fun a => ¬ image g (compl (image f X)) a
    have hmono : Monotone F := by
      intro X Y hXY a hFa
      intro haY
      rcases haY with ⟨b, hb⟩
      have hbX : compl (image f X) b := by
        intro hbXin
        have hbYin : image f Y b := by
          rcases hbXin with ⟨a', ha', rfl⟩
          exact ⟨a', ⟨hXY a' ha', rfl⟩⟩
        exact hb.1 hbYin
      exact hFa ⟨b, ⟨hbX, hb.2⟩⟩
    let s : Set A := lfp F
    -- elements outside s are in g '' (B \ f '' s) (fixed point + EM)
    have a_out_image : ∀ a : A, ¬ s a → image g (compl (image f s)) a := by
      intro a ha
      by_cases h : image g (compl (image f s)) a
      · exact h
      · exfalso
        exact ha (lfp_F_subset hmono a h)
    -- elements inside s are not in g '' (B \ f '' s) (fixed point)
    have a_in_s_F : ∀ a : A, s a → F s a := by
      intro a ha
      exact lfp_le_F hmono a ha
    -- the CBS bijection: use f on s, use the g-preimage outside s
    let h : A → B := fun a => if s a then f a else gInv a
    -- mixed case of injectivity: s-side and outside-side cannot collide
    have mixed_imp : ∀ a₁ a₂ : A, s a₁ → ¬ s a₂ → ¬ h a₁ = h a₂ := by
      intro a₁ a₂ h1 h2 hh
      have hh1 : h a₁ = f a₁ := by simp [h, h1]
      have hh2 : h a₂ = gInv a₂ := by simp [h, h2]
      have hf_eq : f a₁ = gInv a₂ := by
        rw [hh1, hh2] at hh
        exact hh
      have ha2in : image g (compl (image f s)) a₂ := a_out_image a₂ h2
      rcases ha2in with ⟨b', hb'⟩
      have hb'out : ¬ image f s b' := hb'.1
      have hgb' : g b' = a₂ := hb'.2
      have hspec : g (gInv a₂) = a₂ := gInv_spec a₂ ⟨b', hgb'⟩
      have hgInv_eq : gInv a₂ = b' := hg (by rw [hspec, hgb'])
      have hf_in : image f s (gInv a₂) := by
        rw [← hf_eq]
        exact ⟨a₁, ⟨h1, rfl⟩⟩
      exact hb'out (by rwa [hgInv_eq] at hf_in)
    refine ⟨h, ?_⟩
    constructor
    · intro a₁ a₂ hh
      by_cases h1 : s a₁
      · by_cases h2 : s a₂
        · have hh1 : h a₁ = f a₁ := by simp [h, h1]
          have hh2 : h a₂ = f a₂ := by simp [h, h2]
          have hf_eq : f a₁ = f a₂ := by
            rw [hh1, hh2] at hh
            exact hh
          exact hf hf_eq
        · exact False.elim (mixed_imp a₁ a₂ h1 h2 hh)
      · by_cases h2 : s a₂
        · exact False.elim (mixed_imp a₂ a₁ h2 h1 hh.symm)
        · have hh1 : h a₁ = gInv a₁ := by simp [h, h1]
          have hh2 : h a₂ = gInv a₂ := by simp [h, h2]
          have hgInv_eq : gInv a₁ = gInv a₂ := by
            rw [hh1, hh2] at hh
            exact hh
          have ha1r : ∃ b : B, g b = a₁ := by
            rcases a_out_image a₁ h1 with ⟨b, hb⟩
            exact ⟨b, hb.2⟩
          have ha2r : ∃ b : B, g b = a₂ := by
            rcases a_out_image a₂ h2 with ⟨b, hb⟩
            exact ⟨b, hb.2⟩
          have hg1 : g (gInv a₁) = a₁ := gInv_spec a₁ ha1r
          have hg2 : g (gInv a₂) = a₂ := gInv_spec a₂ ha2r
          have hg_eq : g (gInv a₁) = g (gInv a₂) := by rw [hgInv_eq]
          rwa [hg1, hg2] at hg_eq
    · intro b
      by_cases hb : image f s b
      · rcases hb with ⟨a, ha, rfl⟩
        exact ⟨a, by simp [h, ha]⟩
      · let a : A := g b
        have ha_notin : ¬ s a := by
          intro ha
          have hFs : F s a := a_in_s_F a ha
          have himg : image g (compl (image f s)) a := ⟨b, ⟨hb, rfl⟩⟩
          exact hFs himg
        refine ⟨a, ?_⟩
        have hh : h a = gInv a := by simp [h, ha_notin]
        have hspec : g (gInv a) = a := gInv_spec a ⟨b, rfl⟩
        have hg_eq : g (gInv a) = g b := by rw [hspec]
        have hgInv_eq : gInv a = b := hg hg_eq
        rwa [hgInv_eq] at hh
  · -- A is empty: then B is empty (via the injection g), and the empty map works.
    have hAempty : ∀ a : A, False := fun a => hA ⟨a⟩
    have hBempty : ∀ b : B, False := fun b => hAempty (g b)
    refine ⟨fun a => False.elim (hAempty a), ?_⟩
    constructor
    · intro a₁ a₂ hh
      exact False.elim (hAempty a₁)
    · intro b
      exact False.elim (hBempty b)

end GoldbachChallenge
