import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Universal Slice 027: Convergence inside the radius of convergence

Pure textbook statement: for a geometric power series the series converges,
is summable and has the closed sum (1 - r)^-1 whenever |r| < 1.
-/

namespace UniversalSlice027

open scoped BigOperators

/-- The geometric power series converges for |r| < 1 with sum (1 - r)^-1. -/
theorem hasSum_geometric_abs (r : ℝ) (h : |r| < 1) :
    HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  hasSum_geometric_of_abs_lt_one h

/-- The same series is summable for |r| < 1. -/
theorem summable_geometric_abs (r : ℝ) (h : |r| < 1) : Summable (fun n : ℕ ↦ r ^ n) :=
  summable_geometric_of_abs_lt_one h

/-- The sum of the series equals the closed form (1 - r)^-1. -/
theorem tsum_geometric_abs (r : ℝ) (h : |r| < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_abs_lt_one h

end UniversalSlice027

#print axioms UniversalSlice027.hasSum_geometric_abs
#print axioms UniversalSlice027.summable_geometric_abs
#print axioms UniversalSlice027.tsum_geometric_abs
