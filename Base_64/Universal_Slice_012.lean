import Mathlib.NumberTheory.Chebyshev

/-!
# Universal Slice 012: Classical control of the Chebyshev functions

We formalize the finite-range version of the classical estimate
`θ(x) ≤ ψ(x) ≤ θ(x) + 2√x log x` for all `x ≥ 1`:  the left inequality is
`Chebyshev.theta_le_psi`, and the right one follows from
`Chebyshev.psi_sub_theta_le`.  We also record the absolute bound
`|ψ(x) - θ(x)| ≤ 2√x log x` and the elementary linear upper bound
`θ(x) ≤ log 4 · x`.

References:
`Chebyshev.theta_le_psi`, `Chebyshev.psi_sub_theta_le`,
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`, `Chebyshev.theta_le_log4_mul_x`.
-/

open Real

namespace Slice012

/-- Finite-range control: for `x ≥ 1`, `θ x ≤ ψ x ≤ θ x + 2√x log x`. -/
theorem theta_le_psi_le_theta_add_two_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.theta x ≤ Chebyshev.psi x ∧
      Chebyshev.psi x ≤ Chebyshev.theta x + 2 * Real.sqrt x * log x := by
  constructor
  · exact Chebyshev.theta_le_psi x
  · have h := Chebyshev.psi_sub_theta_le (x := x) hx
    linarith

/-- Absolute finite-range bound: `|ψ x - θ x| ≤ 2√x log x` for `x ≥ 1`. -/
theorem abs_psi_sub_theta_le_two_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * log x :=
  Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx

/-- Elementary linear upper bound: `θ x ≤ log 4 * x` for `x ≥ 0`. -/
theorem theta_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.theta x ≤ log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

end Slice012
