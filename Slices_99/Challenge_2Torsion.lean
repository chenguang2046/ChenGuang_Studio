import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace GoldbachChallenge

open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F]

noncomputable def shortW (a b : F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

lemma eval_twoTorsion_short (a b x : F) :
    (shortW a b).twoTorsionPolynomial.toPoly.eval x = 4 * (x ^ 3 + a * x + b) := by
  rw [eval_toPoly_twoTorsionPolynomial]
  simp [shortW, b₂, b₄, b₆]
  ring

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

lemma shortQ_Δ_ne_zero : (shortW (-1 : ℚ) 0).Δ ≠ 0 := by
  norm_num [shortW, Δ, b₂, b₄, b₆, b₈]

lemma shortQ_ns0 : WeierstrassCurve.Affine.Nonsingular (shortW (-1 : ℚ) 0) 0 0 := by
  rw [nonsingular_iff', equation_iff]
  norm_num [shortW]

lemma shortQ_ns1 : WeierstrassCurve.Affine.Nonsingular (shortW (-1 : ℚ) 0) 1 0 := by
  rw [nonsingular_iff', equation_iff]
  norm_num [shortW]

lemma shortQ_nsNeg1 : WeierstrassCurve.Affine.Nonsingular (shortW (-1 : ℚ) 0) (-1) 0 := by
  rw [nonsingular_iff', equation_iff]
  norm_num [shortW]

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
