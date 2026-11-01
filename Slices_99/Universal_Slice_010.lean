import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Universal Slice 010: Basic properties of removable singularities

In the current mathlib build the `Analysis.Complex` library does not yet contain a
definition of the residue of a meromorphic function, so we follow the documented
degradation route and formalize the adjacent basic facts about simple singularities:
Riemann's removable singularity theorem.  If a complex-differentiable function on a
punctured neighbourhood of a point `c` is continuous at `c`, then it is analytic at
`c`; and if it is bounded on the punctured neighbourhood, then it has a limit at `c`.

References:
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`,
`Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under`.
-/

open Filter
open scoped Topology

namespace Slice010

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Riemann's removable singularity theorem (continuous version): if `f : ℂ → E`
is complex differentiable in a punctured neighbourhood of `c` and continuous at
`c`, then `f` is analytic at `c`. -/
theorem removable_of_continuous {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z) (hc : ContinuousAt f c) :
    AnalyticAt ℂ f c :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc

/-- Bounded version: if `f : ℂ → E` is complex differentiable in a punctured
neighbourhood of `c` and bounded there, then `f` has a limit at `c` (the
limiting value is `limUnder (𝓝[≠] c) f`). -/
theorem exists_limit_of_differentiable_on_punctured_nhds_of_bounded {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖) :
    Tendsto f (𝓝[≠] c) (𝓝 ((𝓝[≠] c).limUnder f)) :=
  Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hb

end Slice010
