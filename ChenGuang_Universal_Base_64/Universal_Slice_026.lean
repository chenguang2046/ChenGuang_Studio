import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Universal Slice 026: Convergence of geometric series and its sum

Pure textbook statement: the finite geometric sum formula and the convergence
of the infinite geometric series when the ratio is in [0, 1).
-/

namespace UniversalSlice026

open Finset

open scoped BigOperators

/-- Finite geometric sum: sum_{i < n} x^i = (x^n - 1) / (x - 1) for x != 1. -/
theorem geom_sum_finite (x : ℝ) (h : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1) :=
  geom_sum_eq h n

/-- Infinite geometric series: if 0 <= r < 1 then the series converges to (1 - r)^-1. -/
theorem hasSum_geometric (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  hasSum_geometric_of_lt_one h0 h1

/-- Summability version for 0 <= r < 1. -/
theorem summable_geometric (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ ↦ r ^ n) :=
  summable_geometric_of_lt_one h0 h1

end UniversalSlice026

#print axioms UniversalSlice026.geom_sum_finite
#print axioms UniversalSlice026.hasSum_geometric
#print axioms UniversalSlice026.summable_geometric
