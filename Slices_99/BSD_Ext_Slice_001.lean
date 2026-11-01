import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
BSD_Ext_Slice_001 : Weierstrass curve basic quantities.

Pure algebraic properties of the standard quantities b2, b4, b6, b8,
c4, c6 and discriminant Delta of a Weierstrass curve over the rationals.
All statements are direct consequences of the definitions in mathlib.
-/

open WeierstrassCurve

namespace BSDExtSlice001

-- Concrete curve E : y^2 = x^3 + x + 1 over Q
def E : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 1
  a₆ := 1

theorem E_b₂ : E.b₂ = 0 := by
  simp [E, b₂]

theorem E_b₄ : E.b₄ = 2 := by
  simp [E, b₄]

theorem E_b₆ : E.b₆ = 4 := by
  simp [E, b₆]

theorem E_b₈ : E.b₈ = -1 := by
  simp [E, b₈]

theorem E_c₄ : E.c₄ = -48 := by
  simp [E, c₄, b₂, b₄]
  norm_num

theorem E_c₆ : E.c₆ = -864 := by
  simp [E, c₆, b₂, b₄, b₆]
  norm_num

theorem E_Δ : E.Δ = -496 := by
  simp [E, Δ, b₂, b₄, b₆, b₈]
  norm_num

-- Basic relation among the b-quantities, valid for any curve.
theorem b_relation_any (W : WeierstrassCurve ℚ) :
    4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 :=
  W.b_relation

-- Fundamental relation 1728 * Delta = c4^3 - c6^2, valid for any curve.
theorem c_relation_any (W : WeierstrassCurve ℚ) :
    1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 :=
  W.c_relation

-- Instantiated on the concrete curve E.
theorem E_b_relation : 4 * E.b₈ = E.b₂ * E.b₆ - E.b₄ ^ 2 :=
  E.b_relation

theorem E_c_relation : 1728 * E.Δ = E.c₄ ^ 3 - E.c₆ ^ 2 :=
  E.c_relation

end BSDExtSlice001


#print axioms BSDExtSlice001.E_b₂
#print axioms BSDExtSlice001.E_c₄
#print axioms BSDExtSlice001.E_c₆
#print axioms BSDExtSlice001.E_Δ
#print axioms BSDExtSlice001.b_relation_any
#print axioms BSDExtSlice001.c_relation_any
