/-
Challenge 3 (upgraded): Rouché's theorem, global complex-analysis version
==========================================================================

Goal (textbook global Rouché): if `f`, `g` are analytic on a domain and
`|g(z)| < |f(z)|` for every `z` on a simple closed contour, then `f` and `f + g`
have the same number of zeros (counted with multiplicity) inside the contour.

Mathlib v4.34 reconnaissance (files actually surveyed)
------------------------------------------------------
* `Mathlib.Analysis.Complex.CauchyIntegral` -- circle integrals and Cauchy's
  formula:
  - `DiffContOnCl.circleIntegral_sub_inv_smul` (Cauchy integral formula)
  - `circleIntegral_eq_zero_of_differentiable_on_off_countable` (vanishing off
    countably many singularities)
  - `DifferentiableOn.analyticOnNhd` / `DifferentiableOn.hasFPowerSeriesOnBall`
    (differentiable implies analytic, local power series)
* `Mathlib.Analysis.Analytic.Order` -- vanishing order at a point:
  - `analyticOrderAt`, `analyticOrderAt_eq_zero`, `analyticOrderAt_add_eq_left_of_lt`
* `Mathlib.Analysis.Analytic.IsolatedZeros` -- isolated zeros
  (`AnalyticAt.locally_ne_zero`, `eq_pow_order_mul_iterate_dslope`)
* `Mathlib.Algebra.Polynomial.Splits` -- `Splits.natDegree_eq_card_roots`,
  `splits_iff_card_roots`
* `Mathlib.Analysis.Complex.Polynomial.Basic` -- `Complex.isAlgClosed`: every
  `ℂ[X]` polynomial splits (`IsAlgClosed.splits`)

Honest gap report: what the *global* theorem needs but mathlib v4.34 lacks
---------------------------------------------------------------------------
1. Residue theorem / argument principle.  A whole-tree search for
   `Rouché` / `argument principle` / `winding number` / zero-counting integrals
   returns 0 hits: there is no theorem of the form
   `(2πi)⁻¹ ∮ f'(z)/f(z) dz = #zeros − #poles`.
2. Winding numbers and their homotopy invariance (no `windingNumber` API).
3. Log-derivative integration: no API to split `∮ f'/f` into local
   contributions `order · 2πi` at each zero.  The natural building block
   `circleIntegral_eq_zero_of_differentiable_on_off_countable` exists, but the
   decomposition theorem itself is absent.
4. Homotopy `f_t = f + t·g` with uniform `|g| < |f|` on the boundary, and
   continuity of the zero-counting integral under `t`.
5. Asymptotic leading-term control for polynomials: the classical reduction
   `|g| < |f|` on a sufficiently large circle  ⇒  `natDegree (f+g) = natDegree f`
   is not in the library either; it is stated as an explicit hypothesis below.

Deliverable (degraded, per the task rule "report the gap and degrade")
----------------------------------------------------------------------
A. Boundary norm-control lemmas, extending the earlier `rouche_boundary_core`
   (the strict-triangle-inequality step): the dominant term `f` and the
   perturbed term `f + g` do not vanish on the boundary where `‖g‖ < ‖f‖`.
B. Local multiplicity statements for analytic functions (`analyticOrderAt`),
   including the *local Rouché mechanism*: if the vanishing order of `g` at
   `z₀` strictly exceeds that of `f`, then `f + g` has the same order as `f`.
C. Finite zero-counting version for complex polynomials: because ℂ is
   algebraically closed, `roots.card = natDegree` for every nonzero polynomial;
   hence if a perturbation leaves the degree unchanged, the number of roots
   counted with multiplicity is unchanged.  The explicit instance
   `fR = X³ − X`, `g = X` (from `Challenge_Rouche.lean`) is verified again
   through the generic lemma, including the degree computation.

No `sorry`, no invented lemmas; the comments record only objective facts about
the library state and the mathematical argument.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace GoldbachChallenge

open Polynomial

/-! ## A. Boundary norm control (global Rouché's local step) -/

/-- Boundary core lemma (norm form of the strict triangle-inequality argument):
if `‖u‖ < ‖v‖` and `v ≠ 0`, then `u + v ≠ 0`.  In Rouché's setting this is the
local step preventing `f + g` from vanishing where the dominant term does not.
(Re-used verbatim from `Challenge_Rouche.lean`, where the project does not
produce importable `.olean` artefacts for sibling slices.) -/
theorem rouche_boundary_core {u v : ℂ} (hlt : ‖u‖ < ‖v‖) (_hv0 : v ≠ 0) :
    u + v ≠ 0 := by
  intro h0
  have hle : ‖v‖ ≤ ‖u + v‖ + ‖u‖ := by
    have h1 : ‖(u + v) + (-u)‖ ≤ ‖u + v‖ + ‖-u‖ := norm_add_le (u + v) (-u)
    rw [show (u + v) + (-u) = v by ring] at h1
    rwa [norm_neg] at h1
  have hnorm0 : ‖u + v‖ = 0 := by simp [h0]
  linarith

/-- In Rouché's setting the dominant term does not vanish on the boundary:
`‖g z‖ < ‖f z‖` forces `f z ≠ 0` (otherwise the strict inequality would read
`‖g z‖ < 0`, contradicting non-negativity of the norm). -/
theorem rouche_dominant_nonzero {f g : ℂ → ℂ} {z : ℂ} (hlt : ‖g z‖ < ‖f z‖) :
    f z ≠ 0 := by
  intro hz0
  have hlt0 : ‖g z‖ < 0 := by simpa [hz0] using hlt
  have hnonneg : 0 ≤ ‖g z‖ := norm_nonneg (g z)
  linarith

/-- In Rouché's setting the perturbed function does not vanish on the boundary:
`‖g z‖ < ‖f z‖` forces `(f + g) z ≠ 0`; this is the strict triangle-inequality
step `rouche_boundary_core` applied pointwise. -/
theorem rouche_perturbed_nonzero {f g : ℂ → ℂ} {z : ℂ} (hlt : ‖g z‖ < ‖f z‖) :
    (f + g) z ≠ 0 := by
  simpa [Pi.add_apply, add_comm] using
    rouche_boundary_core (u := g z) (v := f z) hlt (rouche_dominant_nonzero hlt)

/-- Circle-boundary version of the Rouché hypothesis: if `‖g z‖ < ‖f z‖` for
every `z` with `‖z - c‖ = R`, then neither `f` nor `f + g` vanishes anywhere on
that circle. -/
theorem rouche_circle_boundary_nonzero {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (h : ∀ z : ℂ, ‖z - c‖ = R → ‖g z‖ < ‖f z‖) :
    ∀ z : ℂ, ‖z - c‖ = R → f z ≠ 0 ∧ (f + g) z ≠ 0 := by
  intro z hz
  exact ⟨rouche_dominant_nonzero (h z hz), rouche_perturbed_nonzero (h z hz)⟩

/-! ## B. Local multiplicity of analytic functions (`analyticOrderAt`) -/

/-- A non-vanishing value has vanishing order zero: if `f z₀ ≠ 0`, then
`analyticOrderAt f z₀ = 0`. -/
theorem rouche_order_zero_of_nonzero {f : ℂ → ℂ} {z₀ : ℂ} (hfz0 : f z₀ ≠ 0) :
    analyticOrderAt f z₀ = 0 :=
  (analyticOrderAt_eq_zero (𝕜 := ℂ) (E := ℂ)).mpr (Or.inr hfz0)

/-- Local Rouché mechanism for analytic functions: if the vanishing order of `g`
at `z₀` is strictly larger than that of `f`, then `f + g` has the same vanishing
order as `f` at `z₀` (the lower-order term dominates the sum).  This is the
pointwise content used by the homotopy argument of the global theorem; the
global counting step that aggregates these local orders through
`(2πi)⁻¹ ∮ f'/f` is the missing library component listed as gap 1-3. -/
theorem rouche_order_add_left_of_lt {f g : ℂ → ℂ} {z₀ : ℂ}
    (hfg : analyticOrderAt f z₀ < analyticOrderAt g z₀) :
    analyticOrderAt (f + g) z₀ = analyticOrderAt f z₀ :=
  analyticOrderAt_add_eq_left_of_lt (𝕜 := ℂ) (E := ℂ) hfg

/-! ## C. Finite zero counting for complex polynomials -/

/-- The polynomial `f = X³ - X` of the finite instance (same definition as in
`Challenge_Rouche.lean`). -/
noncomputable def fR : ℂ[X] :=
  X ^ 3 - X

/-- Every nonzero polynomial over ℂ has exactly `natDegree` roots counted with
multiplicity: ℂ is algebraically closed (`Complex.isAlgClosed`), hence every
polynomial splits (`IsAlgClosed.splits`), and `Splits.natDegree_eq_card_roots`
equates the root count with the degree. -/
theorem rouche_poly_splits_card {p : ℂ[X]} (_hp : p ≠ 0) : p.roots.card = p.natDegree :=
  (IsAlgClosed.splits p).natDegree_eq_card_roots.symm

/-- Polynomial (finite) counting version of Rouché: if a perturbation `q` leaves
the degree of `p` unchanged, then `p` and `p + q` have the same number of complex
roots counted with multiplicity.  In the classical Rouché setting the degree
equality follows from `|q| < |p|` on a sufficiently large circle by a
leading-term argument; that asymptotic reduction is not present in mathlib and
is therefore an explicit hypothesis (see gap 5 in the header). -/
theorem rouche_poly_card_eq_of_natDegree_eq {p q : ℂ[X]} (hp : p ≠ 0)
    (hpq : p + q ≠ 0) (hdeg : (p + q).natDegree = p.natDegree) :
    (p + q).roots.card = p.roots.card := by
  calc
    (p + q).roots.card = (p + q).natDegree := rouche_poly_splits_card hpq
    _ = p.natDegree := hdeg
    _ = p.roots.card := (rouche_poly_splits_card hp).symm

/-- Explicit instance, re-verified through the generic lemma: `fR = X³ - X` and
`g = X` satisfy the polynomial Rouché conclusion `roots.card` equal to `3`.
The degree computation is the finite analogue of the leading-term argument on a
large circle. -/
theorem rouche_global_instance : (fR + X).roots.card = fR.roots.card := by
  have hsum : fR + X = X ^ 3 := by
    unfold fR
    ring
  have hpq0 : fR + X ≠ 0 := by
    rw [hsum]
    exact pow_ne_zero 3 (X_ne_zero (R := ℂ))
  have hp0 : fR ≠ 0 := by
    unfold fR
    intro h
    have hsub : (X : ℂ[X]) ^ 3 = X := sub_eq_zero.mp h
    have hd := congrArg (fun p : ℂ[X] => p.natDegree) hsub
    simp at hd
  have hdeg_fR : fR.natDegree = 3 := by
    unfold fR
    rw [show X ^ 3 - X = X ^ 3 + (-X : ℂ[X]) by ring]
    rw [natDegree_add_eq_left_of_degree_lt]
    · rw [natDegree_X_pow]
    · rw [degree_neg, degree_X, degree_X_pow]
      norm_num
  have hdeg : (fR + X).natDegree = fR.natDegree := by
    rw [hsum, hdeg_fR]
    exact natDegree_X_pow (R := ℂ) (n := 3)
  exact rouche_poly_card_eq_of_natDegree_eq (p := fR) (q := X) hp0 hpq0 hdeg

end GoldbachChallenge
