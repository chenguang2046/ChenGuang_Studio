import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Group.Subgroup.Basic

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

#check add_eq_zero_iff_eq_neg
#check add_self_of_Y_eq
#check add_self_of_Y_ne
#check some_ne_zero
#check negY
#check equation_iff
#check equation_iff_nonsingular_of_Δ_ne_zero
#check nonsingular_iff'
#check isRoot_twoTorsionPolynomial_iff
#check isRoot_twoTorsionPolynomial_of_add_self
#check AddSubgroup
#check Polynomial.card_roots_le_natDegree
#check Polynomial.roots_card_le_natDegree
#check sq_eq_zero_iff

noncomputable def shortW (a b : F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

#check shortW
#check (shortW (-1 : F) 0).Δ
