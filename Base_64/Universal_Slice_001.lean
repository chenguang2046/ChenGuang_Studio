/-
Universal_Slice_001: The Euler product for completely multiplicative functions
(完全乘性函数的狄利克雷级数等于素数处欧拉乘积，含有限代数截断)

Content:
  1. finiteEulerProduct_completelyMultiplicative:
     for every N, the truncated Euler product over primes < N
     equals the Dirichlet series summed over N-smooth numbers.
  2. eulerProduct_completelyMultiplicative_tprod / _tendsto:
     the full Dirichlet series of a completely multiplicative summable f
     equals the Euler product over all primes (infinite / limit form).
  3. riemannZeta_eulerProduct_completelyMultiplicative:
     the classical instance f(n) = n^(-s) (completely multiplicative),
     yielding zeta(s) = prod_p (1 - p^(-s))^(-1) for Re s > 1.
-/
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

noncomputable section

open scoped BigOperators
open scoped Topology
open Filter

namespace UniversalSlice001

/-! ## 1. Finite algebraic truncation -/

/-- For every natural number N, the truncated Euler product over primes below N
    equals the Dirichlet series sum over N-smooth numbers (numbers whose prime
    factors are all below N). -/
theorem finiteEulerProduct_completelyMultiplicative {f : ℕ →* ℂ} (hsum : Summable f) (N : ℕ) :
    (∏ p ∈ N.primesBelow, (1 - f p)⁻¹) = ∑' m : N.smoothNumbers, f m := by
  exact EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hsum N

/-! ## 2. Completely multiplicative functions: infinite forms -/

/-- The Dirichlet series of a completely multiplicative, summable function f
    equals the Euler product over all primes. -/
theorem eulerProduct_completelyMultiplicative_tprod {f : ℕ →*₀ ℂ}
    (hsum : Summable fun n : ℕ => ‖f n‖) :
    (∏' p : Nat.Primes, (1 - f p)⁻¹) = ∑' n : ℕ, f n := by
  exact EulerProduct.eulerProduct_completely_multiplicative_tprod hsum

/-- The finite partial products over primes below n converge to the full
    Dirichlet series of the completely multiplicative function f. -/
theorem eulerProduct_completelyMultiplicative_tendsto {f : ℕ →*₀ ℂ}
    (hsum : Summable fun n : ℕ => ‖f n‖) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ n.primesBelow, (1 - f p)⁻¹) atTop (𝓝 (∑' n : ℕ, f n)) := by
  exact EulerProduct.eulerProduct_completely_multiplicative hsum

/-! ## 3. Classical instance: the Riemann zeta function -/

/-- For Re s > 1, the completely multiplicative function n ↦ n^(-s) gives
    zeta(s) = prod_p (1 - p^(-s))^(-1). -/
theorem riemannZeta_eulerProduct_completelyMultiplicative {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

end UniversalSlice001
