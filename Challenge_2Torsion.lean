/-
Challenge 2: explicit structure of the 2-torsion points of an elliptic curve
=============================================================================

Statement: on a short Weierstrass curve `y² = x³ + a·x + b` over a field `F` of
characteristic `≠ 2` with nonzero discriminant `Δ`, the 2-torsion points (i.e.
`P + P = 0`) are exactly `O` together with the points `(x, 0)` whose `x`-coordinate
is a root of `x³ + a·x + b = 0`.

Mathlib status: the 2-torsion polynomial machinery exists as
`WeierstrassCurve.twoTorsionPolynomial`, `WeierstrassCurve.eval_toPoly_twoTorsionPolynomial`,
`WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_of_add_self` and
`WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_iff`
(see `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` and `.../Affine/Point.lean`).
For the short form the polynomial evaluates to `4 · (x³ + a·x + b)`, so the equivalence
with `x³ + a·x + b = 0` follows (characteristic `≠ 2` makes the factor `4` nonzero).

The explicit instance below (over `ℚ`, curve `y² = x³ - x`) exhibits the four
2-torsion points `O, (0,0), (1,0), (-1,0)` and shows they exhaust all of them.
No `sorry`, no invented lemmas.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

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

/-- For `char F ≠ 2` and `Δ ≠ 0`, a nonsingular affine point `(x, y)` is 2-torsion
(`P + P = 0`) iff `x³ + a·x + b = 0`; in that case necessarily `y = 0`. -/
theorem twoTorsion_iff_root {a b x y : F} (h2 : NeZero (2 : F))
    (hΔ : (shortW a b).Δ ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular (shortW a b) x y) :
    (WeierstrassCurve.Affine.Point.some x y hns +
        WeierstrassCurve.Affine.Point.some x y hns = 0) ↔
      x ^ 3 + a * x + b = 0 := by
  constructor
  · intro hP0
    have hIsRoot := WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_of_add_self hns hP0
    rw [IsRoot.def, eval_twoTorsion_short] at hIsRoot
    have h2n : (2 : F) ≠ 0 := NeZero.ne (2 : F)
    have h4n : (4 : F) ≠ 0 := by
      have hm : (2 : F) * 2 ≠ 0 := mul_ne_zero h2n h2n
      rw [show (4 : F) = (2 : F) * 2 by norm_num]
      exact hm
    exact (mul_eq_zero.mp hIsRoot).resolve_left h4n
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

section ShortCurveQ

/-- Discriminant of `y² = x³ - x` over `ℚ` is nonzero (equal to `8` in mathlib's
`b`-coefficient convention `Δ = b₂²·b₈ - 8·b₄³ - 27·b₆² + 9·b₂·b₄·b₆`). -/
lemma shortQ_Δ_ne_zero : (shortW (-1 : ℚ) 0).Δ ≠ 0 := by
  norm_num [shortW, Δ, b₂, b₄, b₆, b₈]

/-- `(0, 0)` is a nonsingular point of `y² = x³ - x`. -/
lemma shortQ_ns0 : WeierstrassCurve.Affine.Nonsingular (shortW (-1 : ℚ) 0) 0 0 := by
  rw [nonsingular_iff', equation_iff]
  norm_num [shortW]

/-- `(1, 0)` is a nonsingular point of `y² = x³ - x`. -/
lemma shortQ_ns1 : WeierstrassCurve.Affine.Nonsingular (shortW (-1 : ℚ) 0) 1 0 := by
  rw [nonsingular_iff', equation_iff]
  norm_num [shortW]

/-- `(-1, 0)` is a nonsingular point of `y² = x³ - x`. -/
lemma shortQ_nsNeg1 : WeierstrassCurve.Affine.Nonsingular (shortW (-1 : ℚ) 0) (-1) 0 := by
  rw [nonsingular_iff', equation_iff]
  norm_num [shortW]

/-- On `y² = x³ - x`, the `x`-coordinate of any 2-torsion point is one of `0, 1, -1`. -/
theorem twoTorsion_x_coord_shortQ (x y : ℚ)
    (hns : WeierstrassCurve.Affine.Nonsingular (shortW (-1 : ℚ) 0) x y)
    (hP0 : WeierstrassCurve.Affine.Point.some x y hns +
        WeierstrassCurve.Affine.Point.some x y hns = 0) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hroot : x ^ 3 + (-1) * x + 0 = 0 :=
    (twoTorsion_iff_root (F := ℚ) (a := -1) (b := 0) (x := x) (y := y)
      (h2 := inferInstance) shortQ_Δ_ne_zero hns).mp hP0
  have hfac : x ^ 3 + (-1) * x + 0 = x * (x - 1) * (x + 1) := by
    ring
  rw [hfac] at hroot
  rcases mul_eq_zero.mp hroot with hx0 | hx2
  · rcases mul_eq_zero.mp hx0 with hx0' | hx1
    · exact Or.inl hx0'
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

/-- Explicit structure on `y² = x³ - x` over `ℚ`: the 2-torsion points are exactly
`O, (0, 0), (1, 0), (-1, 0)`. -/
theorem twoTorsion_set_shortQ :
    ∀ P : WeierstrassCurve.Affine.Point (shortW (-1 : ℚ) 0), P + P = 0 →
      P = 0 ∨ P = WeierstrassCurve.Affine.Point.some 0 0 shortQ_ns0 ∨
        P = WeierstrassCurve.Affine.Point.some 1 0 shortQ_ns1 ∨
          P = WeierstrassCurve.Affine.Point.some (-1) 0 shortQ_nsNeg1 := by
  intro P hP0
  cases P with
  | zero => exact Or.inl rfl
  | some x y hns =>
      right
      have hx := twoTorsion_x_coord_shortQ x y hns hP0
      have hroot : x ^ 3 + (-1) * x + 0 = 0 :=
        (twoTorsion_iff_root (F := ℚ) (a := -1) (b := 0) (x := x) (y := y)
          (h2 := inferInstance) shortQ_Δ_ne_zero hns).mp hP0
      have hy : y = 0 := by
        have hEq : WeierstrassCurve.Affine.Equation (shortW (-1 : ℚ) 0) x y := hns.1
        rw [equation_iff] at hEq
        have hEq' : y ^ 2 = x ^ 3 + (-1) * x + 0 := by
          simpa [shortW] using hEq
        have hy2 : y ^ 2 = 0 := by
          rw [hEq', hroot]
        exact (sq_eq_zero_iff.mp hy2)
      rcases hx with hx0 | hx1 | hx2
      · exact Or.inl (by simp [hy, hx0])
      · exact Or.inr (Or.inl (by simp [hy, hx1]))
      · exact Or.inr (Or.inr (by simp [hy, hx2]))

end ShortCurveQ

end GoldbachChallenge
