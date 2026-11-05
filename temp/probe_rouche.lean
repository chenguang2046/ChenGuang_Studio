/-
Rouché's theorem, discrete polynomial version
===============================================

Mathlib v4.34 does not contain a full complex-analysis Rouché theorem
(whole-tree search found no Rouché / argument-principle theorem).  Per the
task rule "report the gap honestly and degrade", this file completes the
polynomial / discrete version:

  * the core counting theorem `poly_rouche_discrete`: if `q` has strictly
    smaller degree than `p` (the polynomial analogue of the boundary
    condition `|g| < |f|`), then `p` and `p + q` have the same number of
    roots counted with multiplicity;
  * the finite instance `rouche_instance_cubic`: `f = X³ - X` and
    `g = X` (`deg g = 1 < 3 = deg f`), both have exactly 3 roots.

The boundary core lemma `rouche_boundary_core` (strict triangle inequality:
`‖u‖ < ‖v‖` forces `u + v ≠ 0`) lives in `Challenge_Rouche.lean` and is
reproduced here so that this file is self-contained for the counting part.

No `sorry`, no invented lemmas.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Norm

open Polynomial

namespace RoucheDiscrete

/-- Boundary core lemma (norm form of the strict triangle-inequality argument):
if `‖u‖ < ‖v‖` and `v ≠ 0`, then `u + v ≠ 0`.  In Rouché's setting this is the
local step preventing `f + g` from vanishing where the dominant term does not. -/
theorem rouche_boundary_core {u v : ℂ} (hlt : ‖u‖ < ‖v‖) (_hv0 : v ≠ 0) :
    u + v ≠ 0 := by
  intro h0
  have hle : ‖v‖ ≤ ‖u + v‖ + ‖u‖ := by
    have h1 : ‖(u + v) + (-u)‖ ≤ ‖u + v‖ + ‖-u‖ := norm_add_le (u + v) (-u)
    rw [show (u + v) + (-u) = v by ring] at h1
    rwa [norm_neg] at h1
  have hnorm0 : ‖u + v‖ = 0 := by simp [h0]
  linarith

/-- Discrete Rouché (polynomial version): a strictly lower-degree perturbation
`q` does not change the number of roots (counted with multiplicity) of a
nonzero polynomial `p` over an algebraically closed field.  Here `ℂ` is
algebraically closed, so every polynomial splits and
`roots.card = natDegree`. -/
theorem poly_rouche_discrete {p q : ℂ[X]} (_hp : p ≠ 0) (hpq : p + q ≠ 0)
    (hdeg : q.natDegree < p.natDegree) :
    (p + q).roots.card = p.roots.card := by
  by_cases hq0 : q = 0
  · subst hq0
    simp
  · have hd : q.degree < p.degree := by
      exact (natDegree_lt_natDegree_iff (p := q) (q := p) hq0).mp hdeg
    have hnd : (p + q).natDegree = p.natDegree :=
      natDegree_add_eq_left_of_degree_lt (p := p) (q := q) hd
    calc
      (p + q).roots.card = (p + q).natDegree :=
        (IsAlgClosed.splits (p + q)).natDegree_eq_card_roots.symm
      _ = p.natDegree := hnd
      _ = p.roots.card := (IsAlgClosed.splits p).natDegree_eq_card_roots

/-- Finite instance: `f = X³ - X` and `g = X`.  Since `deg g = 1 < 3 = deg f`,
the discrete Rouché theorem applies and `f + g = X³` has the same number of
roots as `f` (namely 3, counted with multiplicity). -/
theorem rouche_instance_cubic :
    ((X ^ 3 - X : ℂ[X]) + X).roots.card = (X ^ 3 - X : ℂ[X]).roots.card := by
  apply poly_rouche_discrete
  · -- p = X³ - X ≠ 0
    intro h
    have hsub : (X : ℂ[X]) ^ 3 = X := sub_eq_zero.mp h
    have hd := congrArg (fun r : ℂ[X] => r.natDegree) hsub
    simp at hd
  · -- (X³ - X) + X = X³ ≠ 0
    intro h
    have hcube : (X : ℂ[X]) ^ 3 = 0 := by
      have h' : (X ^ 3 - X : ℂ[X]) + X = 0 := h
      rw [show (X ^ 3 - X : ℂ[X]) + X = X ^ 3 by ring] at h'
      exact h'
    exact (pow_ne_zero 3 (X_ne_zero (R := ℂ))) hcube
  · -- deg g = 1 < 3 = deg f
    have hnd : (X ^ 3 - X : ℂ[X]).natDegree = 3 := by
      rw [sub_eq_add_neg]
      have hdeg_lt : (-X : ℂ[X]).degree < (X ^ 3 : ℂ[X]).degree := by
        rw [degree_neg, degree_X, degree_X_pow]
        norm_num
      rw [natDegree_add_eq_left_of_degree_lt hdeg_lt]
      rw [natDegree_X_pow]
    rw [hnd]
    rw [natDegree_X]
    norm_num

/-- The same conclusion restated in the direction of the Rouché statement:
`f` and `f + g` have the same number of zeros. -/
theorem rouche_finite_same_zeros :
    (X ^ 3 - X : ℂ[X]).roots.card = ((X ^ 3 - X : ℂ[X]) + X).roots.card :=
  rouche_instance_cubic.symm

end RoucheDiscrete

#print axioms RoucheDiscrete.poly_rouche_discrete
#print axioms RoucheDiscrete.rouche_instance_cubic
#print axioms RoucheDiscrete.rouche_finite_same_zeros
#print axioms RoucheDiscrete.rouche_boundary_core
