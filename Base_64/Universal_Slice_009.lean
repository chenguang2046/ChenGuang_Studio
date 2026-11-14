import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Universal Slice 009: The Weierstrass elliptic curve point group

We verify that the type `W.Point` of nonsingular affine points on a Weierstrass
curve `W : WeierstrassCurve.Affine F` over a field `F` carries an additive
commutative group structure whose binary operation is the chord-and-tangent
addition law.  All four group axioms (identity, associativity, commutativity,
inverse) follow from the `AddCommGroup` instance provided by mathlib.

References:
`WeierstrassCurve.Affine.Point`, `WeierstrassCurve.Affine.Point.instAddCommGroup`,
`add_zero`, `zero_add`, `add_assoc`, `add_comm`, `add_neg_cancel`.
-/

open WeierstrassCurve

namespace Slice009

variable {F : Type} [Field F] [DecidableEq F]

namespace PointGroup

variable (W : WeierstrassCurve.Affine F)

/-- Left identity: `0 + P = P` for every nonsingular point `P`. -/
theorem left_identity (P : W.Point) : (0 : W.Point) + P = P := by
  exact zero_add P

/-- Right identity: `P + 0 = P` for every nonsingular point `P`. -/
theorem right_identity (P : W.Point) : P + (0 : W.Point) = P := by
  exact add_zero P

/-- Associativity of the point addition law. -/
theorem addition_assoc (P Q R : W.Point) : (P + Q) + R = P + (Q + R) := by
  exact add_assoc P Q R

/-- Commutativity of the point addition law. -/
theorem addition_comm (P Q : W.Point) : P + Q = Q + P := by
  exact add_comm P Q

/-- Inverse law: `P + (-P) = 0` for every nonsingular point `P`. -/
theorem negation_cancel (P : W.Point) : P + (-P) = (0 : W.Point) := by
  exact add_neg_cancel P

end PointGroup

end Slice009
