import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

/-!
# Universal Slice 016: Power series and zeros of analytic functions

This slice verifies that analytic functions admit local power series
expansions, that evaluating such a series at zero recovers the constant
term, and the principle of isolated zeros for analytic functions.

References:
`AnalyticAt` (definition), `HasFPowerSeriesAt`,
`HasSum.hasSum_at_zero`, `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`,
`AnalyticAt.frequently_zero_iff_eventually_zero`,
`AnalyticAt.frequently_eq_iff_eventually_eq`.
-/

noncomputable section

namespace UniversalSlice016

open Filter
open scoped Topology

/-- Every analytic function has a power series expansion at each point. -/
theorem analytic_has_fpower_series_def {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt f p z₀ :=
  hf

/-- Evaluating a power series at zero recovers the constant term. -/
theorem has_sum_at_zero_def (a : ℕ → ℂ) :
    HasSum (fun n : ℕ => (0 : ℂ) ^ n • a n) (a 0) :=
  HasSum.hasSum_at_zero a

/-- Principle of isolated zeros (local form): an analytic function is either
identically zero in a neighbourhood of the point, or nonzero on a punctured
neighbourhood of the point. -/
theorem isolated_zeros_local_def {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) :=
  hf.eventually_eq_zero_or_eventually_ne_zero

/-- If the zeros of an analytic function accumulate at a point, then the
function is identically zero in a neighbourhood of that point. -/
theorem zeros_accumulate_def {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    (∃ᶠ z in 𝓝[≠] w, f z = 0) ↔ (∀ᶠ z in 𝓝 w, f z = 0) :=
  hf.frequently_zero_iff_eventually_zero

/-- Two analytic functions agreeing on a set with an accumulation point
coincide in a neighbourhood of that point. -/
theorem analytic_agree_def {f g : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hg : AnalyticAt ℂ g z₀) :
    (∃ᶠ z in 𝓝[≠] z₀, f z = g z) ↔ (∀ᶠ z in 𝓝 z₀, f z = g z) :=
  hf.frequently_eq_iff_eventually_eq hg

end UniversalSlice016
