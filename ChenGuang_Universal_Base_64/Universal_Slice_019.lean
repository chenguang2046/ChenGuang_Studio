import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Stirling's Formula for the Factorial (real asymptotics)

This file records, in textbook style, the asymptotic facts on the factorial
sequence `n ↦ n!` that are available in `Mathlib.Analysis.SpecialFunctions.Stirling`:

* the Stirling sequence `stirlingSeq n = n! / (√(2n) (n/e)^n)` converges to `√π`;
* the asymptotic equivalence `n! ~ √(2πn) (n/e)^n` as `n → ∞`;
* the effective (global) lower bounds of Robbins type, valid for every natural `n`.

All statements below are direct corollaries of the theorems already proved in
mathlib; no new analytic argument is developed here.
-/


open scoped Topology Real Nat Asymptotics

open Nat hiding log log_pow

open Finset Filter Real

namespace UniversalSlice019

/-! ## The Stirling sequence and its limit -/

/-- The Stirling sequence `stirlingSeq n = n! / (√(2n) (n/e)^n)` tends to `√π`.
This is Stirling's formula in limit form. -/
lemma stirlingSeq_limit_sqrt_pi :
    Tendsto Stirling.stirlingSeq atTop (𝓝 (Real.sqrt Real.pi)) :=
  Stirling.tendsto_stirlingSeq_sqrt_pi

/-- The terms of the Stirling sequence are positive for every positive index. -/
lemma stirlingSeq_pos (n : ℕ) : 0 < Stirling.stirlingSeq (n + 1) :=
  Stirling.stirlingSeq'_pos n

/-- Boundary values of the Stirling sequence. -/
lemma stirlingSeq_zero : Stirling.stirlingSeq 0 = 0 :=
  Stirling.stirlingSeq_zero

lemma stirlingSeq_one : Stirling.stirlingSeq 1 = Real.exp 1 / Real.sqrt 2 :=
  Stirling.stirlingSeq_one

/-! ## Asymptotic equivalence -/

/-- **Stirling's formula in asymptotic form**: `n! ~ √(2πn) (n/e)^n` as `n → ∞`. -/
lemma factorial_equiv_stirling :
    (fun n : ℕ => n ! : ℕ → ℝ) ~[atTop]
      fun n : ℕ => Real.sqrt (2 * n * Real.pi) * (n / Real.exp 1) ^ n :=
  Stirling.factorial_isEquivalent_stirling

/-! ## Global (effective) bounds -/

/-- The Stirling sequence is bounded below by `√π` for all positive `n`. -/
lemma sqrt_pi_le_stirlingSeq {n : ℕ} (hn : n ≠ 0) : Real.sqrt Real.pi ≤ Stirling.stirlingSeq n :=
  Stirling.sqrt_pi_le_stirlingSeq hn

/-- Robbins-type lower bound: `√(2πn) (n/e)^n ≤ n!` holds for every natural `n`
(in particular also for small `n`, where the asymptotic form is not applicable). -/
lemma le_factorial_stirling (n : ℕ) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n ≤ n ! :=
  Stirling.le_factorial_stirling n

/-- Logarithmic form of the lower bound, valid for positive `n`. -/
lemma le_log_factorial_stirling {n : ℕ} (hn : n ≠ 0) :
    n * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2 ≤ Real.log n ! :=
  Stirling.le_log_factorial_stirling hn

end UniversalSlice019

#print axioms UniversalSlice019.stirlingSeq_limit_sqrt_pi
#print axioms UniversalSlice019.stirlingSeq_pos
#print axioms UniversalSlice019.stirlingSeq_zero
#print axioms UniversalSlice019.stirlingSeq_one
#print axioms UniversalSlice019.factorial_equiv_stirling
#print axioms UniversalSlice019.sqrt_pi_le_stirlingSeq
#print axioms UniversalSlice019.le_factorial_stirling
#print axioms UniversalSlice019.le_log_factorial_stirling
