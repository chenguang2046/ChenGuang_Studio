import Mathlib.NumberTheory.Chebyshev

/-!
# Universal Slice 015: Prime counting function and Chebyshev bounds

This slice records classical control relations between the prime counting
function pi and the Chebyshev theta and psi functions, giving explicit
upper and lower bounds for pi.

References:
`Chebyshev.theta_le_pi_mul_log`, `Chebyshev.psi_le_primeCounting_mul_log`,
`Chebyshev.pi_ge`, `Chebyshev.pi_le_log4_mul_div`,
`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.psi_ge`,
`Chebyshev.psi_le_const_mul_self`, `Chebyshev.psi_le_primeCounting_mul_log'`.
-/

noncomputable section

namespace UniversalSlice015

open scoped Nat.Prime

/-- theta is bounded above by pi times log n. -/
theorem theta_le_pi_mul_log_def (n : ℕ) :
    Chebyshev.theta n ≤ (Nat.primeCounting n) * Real.log n :=
  Chebyshev.theta_le_pi_mul_log n

/-- psi is bounded above by pi times log n. -/
theorem psi_le_pi_mul_log_def (n : ℕ) :
    Chebyshev.psi n ≤ (Nat.primeCounting n) * Real.log n :=
  Chebyshev.psi_le_primeCounting_mul_log n

/-- Lower bound on pi: pi n is at least (n * log 2 - log (n+1)) / log n. -/
theorem pi_ge_def (n : ℕ) :
    (n * Real.log 2 - Real.log (n + 1)) / Real.log n ≤ Nat.primeCounting n :=
  Chebyshev.pi_ge n

/-- Upper bound on pi: pi of floor x is at most log 4 * x / log (sqrt x) + sqrt x. -/
theorem pi_le_log4_mul_div_def {x : ℝ} (hx : 1 < x) :
    Nat.primeCounting ⌊x⌋₊ ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x :=
  Chebyshev.pi_le_log4_mul_div hx

/-- Upper bound on theta: theta x <= log 4 * x for nonnegative x. -/
theorem theta_le_log4_mul_x_def {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.theta x ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

/-- Lower bound on psi. -/
theorem psi_ge_def (n : ℕ) :
    n * Real.log 2 - Real.log (n + 1) ≤ Chebyshev.psi n :=
  Chebyshev.psi_ge n

/-- Upper bound on psi with an explicit constant. -/
theorem psi_le_const_mul_self_def {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
  Chebyshev.psi_le_const_mul_self hx

/-- Relation between psi and pi on the reals: psi x <= pi (floor x) * log x. -/
theorem psi_le_pi_mul_log_floor_def (x : ℝ) :
    Chebyshev.psi x ≤ (Nat.primeCounting ⌊x⌋₊) * Real.log x :=
  Chebyshev.psi_le_primeCounting_mul_log' x

end UniversalSlice015
