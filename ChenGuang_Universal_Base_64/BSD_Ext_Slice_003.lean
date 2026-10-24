import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-!
BSD_Ext_Slice_003 : Models of elliptic curves by j-invariant.

Uses mathlib's `WeierstrassCurve.ofJ0`, `ofJ1728`, `ofJNe0Or1728`
and the lemma `ofJ_j` stating that `ofJ j` has j-invariant `j`.
-/

open WeierstrassCurve

namespace BSDExtSlice003

-- The curve y^2 + y = x^3 has j = 0 (over a field where 3 is a unit).
theorem ofJ0_c₄_value : (ofJ0 ℚ).c₄ = 0 := by
  simp [ofJ0_c₄]

theorem ofJ0_Δ_value : (ofJ0 ℚ).Δ = -27 := by
  simp [ofJ0_Δ]

-- The curve y^2 = x^3 + x has j = 1728 (over a field where 2 is a unit).
theorem ofJ1728_c₄_value : (ofJ1728 ℚ).c₄ = -48 := by
  simp [ofJ1728_c₄]

theorem ofJ1728_Δ_value : (ofJ1728 ℚ).Δ = -64 := by
  simp [ofJ1728_Δ]

-- Generic model with j-invariant j for j not 0 or 1728.
theorem ofJNe0Or1728_c₄_value (j : ℚ) :
    (ofJNe0Or1728 j).c₄ = j * (j - 1728) ^ 3 := by
  simp [ofJNe0Or1728_c₄]

theorem ofJNe0Or1728_Δ_value (j : ℚ) :
    (ofJNe0Or1728 j).Δ = j ^ 2 * (j - 1728) ^ 9 := by
  simp [ofJNe0Or1728_Δ]

-- j-invariant of ofJ j equals j.
theorem ofJ_j_value (j : ℚ) : (ofJ j).j = j :=
  ofJ_j j

end BSDExtSlice003


#print axioms BSDExtSlice003.ofJ0_c₄_value
#print axioms BSDExtSlice003.ofJ1728_Δ_value
#print axioms BSDExtSlice003.ofJNe0Or1728_c₄_value
#print axioms BSDExtSlice003.ofJ_j_value
