/-
Challenge 3: Rouché's theorem, polynomial version
==================================================

Statement: if `|g| < |f|` on the boundary of a closed contour, then `f` and `f + g`
have the same number of zeros inside.

Mathlib status: a full complex-analysis Rouché theorem is **not present** in
mathlib v4.34 (whole-tree search found no Rouché / argument-principle theorem).
Per the task rule "report the gap honestly and degrade", we prove the finite
polynomial instance instead:

  * the boundary core lemma (norm form): the strict triangle inequality shows
    that `‖u‖ < ‖v‖` forces `u + v ≠ 0`;
  * the finite counting instance: for `f = X³ - X` and `g = X`, both `f` and
    `f + g = X³` have exactly `3` roots counted with multiplicity (this is
    exactly the Rouché conclusion "same number of zeros" for this pair).

In mathlib v4.34 the absolute value on `ℂ` is the norm `‖·‖`; the dedicated
name `Complex.abs` lives in other files and is not exported by the polynomial
API, so the statements below use the equivalent norm form.
No `sorry`, no invented lemmas.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Norm

namespace GoldbachChallenge

open Polynomial

/-- Boundary core lemma (norm form of the strict triangle-inequality argument):
if `‖u‖ < ‖v‖` and `v ≠ 0`, then `u + v ≠ 0`.  In Rouché's setting this is the
local step preventing `f + g` from vanishing where the dominant term does not. -/
theorem rouche_boundary_core {u v : ℂ} (hlt : ‖u‖ < ‖v‖) (hv0 : v ≠ 0) :
    u + v ≠ 0 := by
  intro h0
  have hle : ‖v‖ ≤ ‖u + v‖ + ‖u‖ := by
    have h1 : ‖(u + v) + (-u)‖ ≤ ‖u + v‖ + ‖-u‖ := norm_add_le (u + v) (-u)
    rw [show (u + v) + (-u) = v by ring] at h1
    rwa [norm_neg] at h1
  have hnorm0 : ‖u + v‖ = 0 := by simp [h0]
  linarith

/-- The polynomial `f = X³ - X` of the finite instance. -/
noncomputable def fR : ℂ[X] :=
  X ^ 3 - X

/-- `fR = (X - 0) · (X - 1) · (X - (-1))`, so its roots (with multiplicity)
are exactly `0, 1, -1` and their count is `3`. -/
theorem fR_roots_card : fR.roots.card = 3 := by
  have hfac : fR = (({0, 1, -1} : Multiset ℂ).map (fun a : ℂ => X - C a)).prod := by
    unfold fR
    simp
    ring_nf
  rw [hfac, roots_multiset_prod_X_sub_C]
  norm_num

/-- Finite instance of the Rouché conclusion: `fR = X³ - X` and `fR + X = X³`
both have exactly `3` roots counted with multiplicity. -/
theorem rouche_finite_example : fR.roots.card = (fR + X).roots.card := by
  have h1 : fR.roots.card = 3 := fR_roots_card
  have h2 : (fR + X).roots.card = 3 := by
    have h : fR + X = X ^ 3 := by
      unfold fR
      ring
    rw [h]
    have hfac3 :
        (X : ℂ[X]) ^ 3 = (({0, 0, 0} : Multiset ℂ).map (fun a : ℂ => X - C a)).prod := by
      simp
      ring_nf
    rw [hfac3, roots_multiset_prod_X_sub_C]
    norm_num
  rw [h1, h2]

end GoldbachChallenge
