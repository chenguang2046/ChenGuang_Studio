import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Real.Sqrt

/-! # Challenge_011 — Hasse 界与好约化欧拉因子（ChenGuang Studio） -/
open Polynomial
noncomputable section
namespace Challenge011

/-- 好约化局部欧拉因子的教科书形式：`1 - a·T + q·T²`（`q = p`）。 -/
def eulerFactorPolynomial (q a : ℤ) : ℤ[X] := 1 - C a * X + C q * X ^ 2

/-- Hasse 界 `|a| ≤ 2√p` 与整式判据 `a² ≤ 4p` 等价。 -/
theorem hasse_sq_iff_abs {p : ℕ} {a : ℤ} (hp : 0 ≤ (p : ℝ)) :
    |(a : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) ↔ (a : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by
  have hnn : (0 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by positivity
  have hsq : (2 * Real.sqrt (p : ℝ)) ^ 2 = 4 * (p : ℝ) := by rw [mul_pow, Real.sq_sqrt hp]; norm_num
  constructor
  · intro h
    have h2 : (a : ℝ) ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [hsq] at h2; exact_mod_cast h2
  · intro h
    have hc : (a : ℝ) ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 := by rw [hsq]; exact_mod_cast h
    calc |(a : ℝ)| = Real.sqrt ((a : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((2 * Real.sqrt (p : ℝ)) ^ 2) := Real.sqrt_le_sqrt hc
      _ = 2 * Real.sqrt (p : ℝ) := Real.sqrt_sq hnn

/-- 判别式 `a² < 4p` ⇒ 欧拉因子无实根。 -/
theorem eulerFactor_no_real_root {p : ℕ} {a : ℤ} (_hp : 0 < p) (h : (a : ℤ) ^ 2 < 4 * (p : ℤ)) :
    ∀ x : ℝ, 1 - (a : ℝ) * x + (p : ℝ) * x ^ 2 ≠ 0 := by
  intro x hx
  have hc : (a : ℝ) ^ 2 < 4 * (p : ℝ) := by exact_mod_cast h
  nlinarith [sq_nonneg (2 * (p : ℝ) * x - (a : ℝ))]

/-- `E : y² = x³ + a·x + b` 在 `𝔽_p` 上的仿射点计数。 -/
def countAffinePoints (p a b : ℕ) : ℕ :=
  (Finset.range p).sum fun x => ((Finset.range p).filter fun y =>
    (y * y) % p = (x * x * x + a * x + b) % p).card

/-- Hasse 界在有限实例上的判定。 -/
def hasseOk (p a b : ℕ) : Prop :=
  let N := countAffinePoints p a b + 1
  ((p + 1 : ℤ) - (N : ℤ)) ^ 2 ≤ 4 * (p : ℤ)

instance hasseOkDecidable (p a b : ℕ) : Decidable (hasseOk p a b) := by unfold hasseOk; infer_instance

theorem hasse_finite_p5 : hasseOk 5 1 1 := by decide
theorem hasse_finite_p7 : hasseOk 7 1 1 := by decide
theorem hasse_finite_p11 : hasseOk 11 1 1 := by decide
theorem hasse_finite_p13 : hasseOk 13 1 1 := by decide

end Challenge011
