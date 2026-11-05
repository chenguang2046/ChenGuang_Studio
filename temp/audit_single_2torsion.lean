/-
Challenge 2 (upgraded): explicit structure of the 2-torsion points of an elliptic curve,
fully generalised to an arbitrary field.

=============================================================================
Statement. Let F be a field of characteristic different from 2, and let
W : y^2 = x^3 + a·x + b be a short Weierstrass curve over F whose discriminant
Δ is nonzero (so W is nonsingular).  Then the 2-torsion points (i.e. the points
P with P + P = O) are exactly O together with the points (x, 0) whose
x-coordinate is a root of the cubic x^3 + a·x + b = 0.  In particular there is
an explicit bijection

    { P ∈ W.Point | P + P = O }  ≃  { x ∈ F | x^3 + a·x + b = 0 } ⊕ {O},

and the 2-torsion points form an additive subgroup of W.Point.

=============================================================================
Method.  We reuse the existing mathlib machinery:
  * WeierstrassCurve.twoTorsionPolynomial        (Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean)
  * WeierstrassCurve.eval_toPoly_twoTorsionPolynomial
  * WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_of_add_self
  * WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_iff
    (Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean)
For the short form a₁ = a₂ = a₃ = 0, a₄ = a, a₆ = b the 2-torsion polynomial
evaluates to 4·(x³ + a·x + b), so in characteristic ≠ 2 the root condition is
exactly x³ + a·x + b = 0.  The characteristic assumption is used through
`NeZero (2 : F)`; note that mathlib's `isRoot_twoTorsionPolynomial_iff` already
requires it together with Δ ≠ 0, so the generalisation is faithful and no
invented lemmas are needed.

No `sorry`, no fabricated lemmas.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Group.Subgroup.Basic

set_option maxHeartbeats 800000

namespace GoldbachChallenge

open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F]

/-- The short Weierstrass curve `y² = x³ + a·x + b`, i.e. `a₁ = a₂ = a₃ = 0`,
`a₄ = a`, `a₆ = b`. -/
noncomputable def shortW (a b : F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

/-- On the short form, the 2-torsion polynomial evaluates to `4 · (x³ + a·x + b)`. -/
lemma eval_twoTorsion_short (a b x : F) :
    (shortW a b).twoTorsionPolynomial.toPoly.eval x = 4 * (x ^ 3 + a * x + b) := by
  rw [eval_toPoly_twoTorsionPolynomial]
  simp [shortW, b₂, b₄, b₆]
  ring

/-- For `char F ≠ 2`, `x` is a root of the 2-torsion polynomial of the short form
iff `x³ + a·x + b = 0` (the factor `4` is nonzero in characteristic `≠ 2`). -/
lemma twoTorsionPolynomial_IsRoot_iff (h2 : NeZero (2 : F)) (a b x : F) :
    (shortW a b).twoTorsionPolynomial.toPoly.IsRoot x ↔ x ^ 3 + a * x + b = 0 := by
  rw [IsRoot.def, eval_twoTorsion_short]
  have h4n : (4 : F) ≠ 0 := by
    have hm : (2 : F) * 2 ≠ 0 := mul_ne_zero (NeZero.ne (2 : F)) (NeZero.ne (2 : F))
    rw [show (4 : F) = (2 : F) * 2 by norm_num]
    exact hm
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left h4n
  · intro h
    rw [h]
    simp

/-- For `char F ≠ 2` and `Δ ≠ 0`, a nonsingular affine point `(x, y)` of the short
form is 2-torsion (`P + P = 0`) iff `x³ + a·x + b = 0`. -/
theorem twoTorsion_iff_root {a b x y : F} (h2 : NeZero (2 : F))
    (hΔ : (shortW a b).Δ ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular (shortW a b) x y) :
    (WeierstrassCurve.Affine.Point.some x y hns +
        WeierstrassCurve.Affine.Point.some x y hns = 0) ↔
      x ^ 3 + a * x + b = 0 := by
  constructor
  · intro hP0
    have hIsRoot := WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_of_add_self hns hP0
    exact (twoTorsionPolynomial_IsRoot_iff h2 a b x).mp hIsRoot
  · intro hroot
    have hEq : WeierstrassCurve.Affine.Equation (shortW a b) x y := hns.1
    rw [equation_iff] at hEq
    have hEq' : y ^ 2 = x ^ 3 + a * x + b := by
      simpa [shortW] using hEq
    have hy2 : y ^ 2 = 0 := by
      rw [hEq', hroot]
    have hy : y = 0 := (sq_eq_zero_iff.mp hy2)
    have hy0 : y = WeierstrassCurve.Affine.negY (shortW a b) x y := by
      subst y
      simp [shortW, negY]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy0

/-- In characteristic `≠ 2`, every 2-torsion point of the short form has
`y`-coordinate `0`. -/
lemma twoTorsion_y_eq_zero {a b x y : F} (h2 : NeZero (2 : F))
    (hΔ : (shortW a b).Δ ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular (shortW a b) x y)
    (hP0 : WeierstrassCurve.Affine.Point.some x y hns +
        WeierstrassCurve.Affine.Point.some x y hns = 0) : y = 0 := by
  have hroot : x ^ 3 + a * x + b = 0 := (twoTorsion_iff_root h2 hΔ hns).mp hP0
  have hEq : WeierstrassCurve.Affine.Equation (shortW a b) x y := hns.1
  rw [equation_iff] at hEq
  have hEq' : y ^ 2 = x ^ 3 + a * x + b := by
    simpa [shortW] using hEq
  have hy2 : y ^ 2 = 0 := by
    rw [hEq', hroot]
  exact (sq_eq_zero_iff.mp hy2)

/-- For `Δ ≠ 0`, a root of `x³ + a·x + b` gives a nonsingular point `(x, 0)` of the
short form. -/
lemma nonsingular_of_root {a b x : F} (hΔ : (shortW a b).Δ ≠ 0)
    (hroot : x ^ 3 + a * x + b = 0) :
    WeierstrassCurve.Affine.Nonsingular (shortW a b) x 0 := by
  have hEq : WeierstrassCurve.Affine.Equation (shortW a b) x 0 := by
    rw [equation_iff]
    simp [shortW, hroot]
  exact (equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq

/-- For `char F ≠ 2` and `Δ ≠ 0`, the point `(x, 0)` with `x` a root of
`x³ + a·x + b` is 2-torsion. -/
lemma root_point_twoTorsion {a b x : F} (h2 : NeZero (2 : F))
    (hΔ : (shortW a b).Δ ≠ 0) (hroot : x ^ 3 + a * x + b = 0) :
    WeierstrassCurve.Affine.Point.some x 0 (nonsingular_of_root hΔ hroot) +
      WeierstrassCurve.Affine.Point.some x 0 (nonsingular_of_root hΔ hroot) = 0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [shortW, negY]

/-- The set of roots of `x³ + a·x + b = 0` in `F`. -/
def rootSet (a b : F) : Set F := {x : F | x ^ 3 + a * x + b = 0}

/-- The set of 2-torsion points of a Weierstrass curve. -/
def twoTorsionSet (W : WeierstrassCurve F) : Set (WeierstrassCurve.Affine.Point W) :=
  {P : WeierstrassCurve.Affine.Point W | P + P = 0}

/-- Roots of `x³ + a·x + b` give 2-torsion points of the short form. -/
theorem rootSet_mem_twoTorsion {a b : F} (h2 : NeZero (2 : F))
    (hΔ : (shortW a b).Δ ≠ 0) (x : F) (hx : x ∈ rootSet a b) :
    WeierstrassCurve.Affine.Point.some x 0 (nonsingular_of_root hΔ (by simpa [rootSet] using hx)) ∈
      twoTorsionSet (shortW a b) := by
  rw [twoTorsionSet]
  exact root_point_twoTorsion h2 hΔ (by simpa [rootSet] using hx)

/-- Every 2-torsion point of the short form has its `x`-coordinate in the root set
and `y`-coordinate `0`. -/
theorem twoTorsion_mem_rootSet {a b x y : F} (h2 : NeZero (2 : F))
    (hΔ : (shortW a b).Δ ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular (shortW a b) x y)
    (hP0 : WeierstrassCurve.Affine.Point.some x y hns +
        WeierstrassCurve.Affine.Point.some x y hns = 0) :
    x ∈ rootSet a b ∧ y = 0 := by
  constructor
  · exact (twoTorsion_iff_root h2 hΔ hns).mp hP0
  · exact twoTorsion_y_eq_zero h2 hΔ hns hP0

/-- The zero point is 2-torsion. -/
theorem twoTorsion_zero (W : WeierstrassCurve F) :
    (0 : WeierstrassCurve.Affine.Point W) ∈ twoTorsionSet W := by
  simp [twoTorsionSet]

/-- The sum of two 2-torsion points is 2-torsion. -/
theorem twoTorsion_add {W : WeierstrassCurve F} {P Q : WeierstrassCurve.Affine.Point W}
    (hP : P ∈ twoTorsionSet W) (hQ : Q ∈ twoTorsionSet W) :
    P + Q ∈ twoTorsionSet W := by
  change P + P = 0 at hP
  change Q + Q = 0 at hQ
  change (P + Q) + (P + Q) = 0
  calc
    (P + Q) + (P + Q) = (P + P) + (Q + Q) := by abel
    _ = 0 := by simp [hP, hQ]

/-- The negative of a 2-torsion point is 2-torsion. -/
theorem twoTorsion_neg {W : WeierstrassCurve F} {P : WeierstrassCurve.Affine.Point W}
    (hP : P ∈ twoTorsionSet W) : -P ∈ twoTorsionSet W := by
  change P + P = 0 at hP
  change (-P) + (-P) = 0
  calc
    (-P) + (-P) = -(P + P) := by abel
    _ = 0 := by simp [hP]

/-- The 2-torsion points form an additive subgroup of `W.Point`. -/
def twoTorsionSubgroup (W : WeierstrassCurve F) :
    AddSubgroup (WeierstrassCurve.Affine.Point W) where
  carrier := twoTorsionSet W
  zero_mem' := twoTorsion_zero W
  add_mem' := twoTorsion_add
  neg_mem' := twoTorsion_neg

/-- The type of roots of `x³ + a·x + b = 0`. -/
def rootSub (a b : F) := {x : F // x ∈ rootSet a b}

/-- The type of 2-torsion points of `W`. -/
def twoTorSub (W : WeierstrassCurve F) := {P : WeierstrassCurve.Affine.Point W // P ∈ twoTorsionSet W}

/-- Explicit bijection between 2-torsion points of the short form and
`{roots of x³ + a·x + b} ⊕ {O}` (characteristic `≠ 2`, `Δ ≠ 0`). -/
noncomputable def twoTorSub_equiv_rootSub_plus_O (a b : F) (h2 : NeZero (2 : F))
    (hΔ : (shortW a b).Δ ≠ 0) : twoTorSub (shortW a b) ≃ rootSub a b ⊕ PUnit := by
  let W := shortW a b
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  · intro P
    rcases P with ⟨Pp, hP0⟩
    rcases Pp with _ | ⟨x, y, hns⟩
    · exact Sum.inr PUnit.unit
    · exact Sum.inl ⟨x, (twoTorsion_iff_root h2 hΔ hns).mp hP0⟩
  · intro e
    cases e with
    | inl r =>
        exact ⟨WeierstrassCurve.Affine.Point.some r.1 0 (nonsingular_of_root hΔ r.2),
          root_point_twoTorsion h2 hΔ r.2⟩
    | inr _ => exact ⟨0, twoTorsion_zero W⟩
  · intro P
    rcases P with ⟨Pp, hP0⟩
    rcases Pp with _ | ⟨x, y, hns⟩
    · apply Subtype.ext
      rfl
    · have hy : y = 0 := twoTorsion_y_eq_zero h2 hΔ hns hP0
      subst y
      apply Subtype.ext
      apply congrArg
        (fun h : WeierstrassCurve.Affine.Nonsingular (shortW a b) x 0 =>
          WeierstrassCurve.Affine.Point.some x 0 h)
      exact Subsingleton.elim hns
        (nonsingular_of_root hΔ ((twoTorsion_iff_root h2 hΔ hns).mp hP0))
  · intro e
    cases e with
    | inl r =>
        apply congrArg Sum.inl
        apply Subtype.ext
        rfl
    | inr u =>
        cases u
        rfl

end GoldbachChallenge

-- ===== 公理审计（仅审计用，不进入交付文件） =====
#print axioms GoldbachChallenge.twoTorsion_iff_root
#print axioms GoldbachChallenge.twoTorsion_add
#print axioms GoldbachChallenge.twoTorsion_neg
#print axioms GoldbachChallenge.twoTorsion_zero
#print axioms GoldbachChallenge.twoTorSub_equiv_rootSub_plus_O
