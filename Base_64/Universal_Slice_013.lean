import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Universal Slice 013: The Euler–Mascheroni constant via the harmonic series

We record mathlib's definition of the Euler–Mascheroni constant
`Real.eulerMascheroniConstant = limUnder atTop Real.eulerMascheroniSeq`, where
`Real.eulerMascheroniSeq n = harmonic n - log (n + 1)`, and verify that the
classical defining sequence `harmonic n - log n` tends to `γ` as `n → ∞`, together
with the classical bounds `1/2 < γ < 2/3` and the strict sandwich inequalities for
every term of the defining sequences.

References:
`Real.eulerMascheroniConstant`, `Real.eulerMascheroniSeq`,
`Real.tendsto_eulerMascheroniSeq`, `Real.tendsto_harmonic_sub_log`,
`Real.one_half_lt_eulerMascheroniConstant`,
`Real.eulerMascheroniConstant_lt_two_thirds`,
`Real.eulerMascheroniSeq_lt_eulerMascheroniConstant`.
-/

open Filter
open Real
open scoped Topology

namespace Slice013

/-- The defining sequence `eulerMascheroniSeq n = harmonic n - log (n + 1)` tends
to the Euler–Mascheroni constant. -/
theorem tendsto_eulerMascheroniSeq :
    Tendsto Real.eulerMascheroniSeq atTop (𝓝 Real.eulerMascheroniConstant) :=
  Real.tendsto_eulerMascheroniSeq

/-- The classical definition via the harmonic series: the difference
`harmonic n - log n` tends to the Euler–Mascheroni constant as `n → ∞`. -/
theorem tendsto_harmonic_sub_log :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) - log (n : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log

/-- Classical bounds: `1/2 < γ < 2/3`. -/
theorem gamma_bounds :
    (1 / 2 : ℝ) < Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant < (2 / 3 : ℝ) := by
  constructor
  · exact Real.one_half_lt_eulerMascheroniConstant
  · exact Real.eulerMascheroniConstant_lt_two_thirds

/-- Every term of the lower defining sequence is a strict lower bound for `γ`. -/
theorem eulerMascheroniSeq_lt_gamma (n : ℕ) :
    Real.eulerMascheroniSeq n < Real.eulerMascheroniConstant :=
  Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n

end Slice013
