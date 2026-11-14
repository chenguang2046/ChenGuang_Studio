import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-!
BSD_Ext_Slice_002 : Short Weierstrass normal form and the j-invariant.

Uses mathlib's `WeierstrassCurve.IsShortNF` and the formulae for
`Delta` and `j` in short Weierstrass form.
-/

open WeierstrassCurve

namespace BSDExtSlice002

-- Concrete short curve E : y^2 = x^3 + 2*x + 3 over Q.
def E : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 2
  a₆ := 3

-- E is in short Weierstrass normal form.
instance E_IsShortNF : E.IsShortNF where
  a₁ := rfl
  a₂ := rfl
  a₃ := rfl

-- In short form: b4 = 2*a4, b6 = 4*a6, b8 = -a4^2.
theorem E_b₄_of_short : E.b₄ = 2 * E.a₄ := E.b₄_of_isShortNF
theorem E_b₆_of_short : E.b₆ = 4 * E.a₆ := E.b₆_of_isShortNF
theorem E_b₈_of_short : E.b₈ = -E.a₄ ^ 2 := E.b₈_of_isShortNF

-- Discriminant in short form: Delta = -16 * (4 a4^3 + 27 a6^2).
theorem E_Δ_of_short :
    E.Δ = -16 * (4 * E.a₄ ^ 3 + 27 * E.a₆ ^ 2) :=
  E.Δ_of_isShortNF

-- E is elliptic (its discriminant is nonzero).
instance E_IsElliptic : E.IsElliptic := ⟨by
  rw [E_Δ_of_short]
  norm_num [E]
⟩

-- j-invariant in short form.
theorem E_j_of_short :
    E.j = 6912 * E.a₄ ^ 3 / (4 * E.a₄ ^ 3 + 27 * E.a₆ ^ 2) :=
  E.j_of_isShortNF

-- Concrete computation for E : a4 = 2, a6 = 3.
theorem E_Δ_value : E.Δ = -4400 := by
  rw [E_Δ_of_short]
  norm_num [E]

-- Concrete j for E.
theorem E_j_value :
    E.j = 6912 * 8 / (32 + 243) := by
  rw [E_j_of_short]
  norm_num [E]

end BSDExtSlice002


#print axioms BSDExtSlice002.E_b₄_of_short
#print axioms BSDExtSlice002.E_Δ_of_short
#print axioms BSDExtSlice002.E_j_of_short
#print axioms BSDExtSlice002.E_Δ_value
#print axioms BSDExtSlice002.E_j_value
