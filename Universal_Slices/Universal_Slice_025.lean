import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Universal Slice 025: The Cauchy-Schwarz inequality

Pure textbook statement: in an inner product space over the reals, the absolute
value of the inner product is bounded by the product of the norms.
-/

namespace UniversalSlice025

open scoped InnerProductSpace

/-- Cauchy-Schwarz inequality with norms: ||<x, y>|| <= ||x|| * ||y||. -/
theorem cauchySchwarz_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    ‖inner ℝ x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_inner_le_norm x y

/-- Cauchy-Schwarz inequality, squared real form: <x, y>^2 <= <x, x> * <y, y>. -/
theorem cauchySchwarz_real {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F) :
    inner ℝ x y * inner ℝ x y ≤ inner ℝ x x * inner ℝ y y :=
  real_inner_mul_inner_self_le x y

end UniversalSlice025

#print axioms UniversalSlice025.cauchySchwarz_norm
#print axioms UniversalSlice025.cauchySchwarz_real
