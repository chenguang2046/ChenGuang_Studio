/-
# Prime Number Theorem (PNT) — Formalized Prerequisites (mathlib v4.34.0)

Background. The analytic prime number theorem asserts ψ(x) / x → 1
(x → ∞), where ψ(x) = Σ_{n ≤ x} Λ(n).

## Findings (mathlib v4.34.0)

1. mathlib **没有** PNT 主定理：
   - 全局检索不到 `PrimeNumberTheorem` / `primeNumberTheorem`；
   - 检索不到 ψ~x、θ~x、π~x/log x 的任何渐近（Tendsto / IsEquivalent）陈述；
   - 也检索不到 Newman / Ikehara / Tauberian / Perron 公式等 PNT 证明工具。
2. 等价陈述（θ(x)~x 或 π(x)~x/log x）在 mathlib 中**同样缺失**，
   且三者互为等价、难度相同（均需 Newman 型证明），不存在"地基更好"的退路。
3. mathlib already provides the PNT **prerequisites** (all called and verified in this file):
   - `ArithmeticFunction.vonMangoldt`：Λ 的定义（vonMangoldt_apply）
   - `Chebyshev.psi` / `Chebyshev.theta`：ψ、θ 定义
   - Chebyshev 型上下界与 ψ−θ 小阶估计
   - `riemannZeta_ne_zero_of_one_le_re`：ζ 在 Re s ≥ 1 无零点（PNT 关键部件）

## Scope

This file formalizes the prerequisite components for the Prime Number
Theorem that are available in mathlib v4.34.0. The main assertion
ψ(x) ~ x (equivalently θ(x) ~ x or π(x) ~ x/log x) is **out of scope**:
mathlib currently ships no PNT theorem and no Newman/Tauberian/Perron
tooling, so a full proof cannot be derived here without new axioms.

Delivered here: a verified formalization of the PNT prerequisites, all
stated by calling existing mathlib theorems; no self-proven claims, no
`sorry`.

-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Filter Asymptotics
open scoped BigOperators

namespace PrimeNumberTheorem

/-! ## 1. ψ 的定义：ψ(x) = Σ_{n ≤ x} Λ(n) （调用 Chebyshev.psi_eq_sum_Icc） -/

/-- ψ(x) = Σ_{n ∈ [0, ⌊x⌋]} Λ(n)，其中 Λ = ArithmeticFunction.vonMangoldt。 -/
theorem pnt_prereq_psi_def (x : ℝ) :
    Chebyshev.psi x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
  simpa using (Chebyshev.psi_eq_sum_Icc x)

/-- Λ(p) = log p 对素数 p 成立（调用 ArithmeticFunction.vonMangoldt_apply_prime）。 -/
theorem pnt_prereq_lambda_on_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.vonMangoldt p = Real.log p :=
  ArithmeticFunction.vonMangoldt_apply_prime hp

/-! ## 2. Chebyshev 型上下界（PNT 的经典前置估计，全部调用） -/

/-- θ(x) ≤ log 4 · x （Chebyshev 上界，调用 Chebyshev.theta_le_log4_mul_x）。 -/
theorem pnt_prereq_theta_upper {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.theta x ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

/-- ψ(x) ≤ (log 4 + 4) · x （Chebyshev 上界，调用 Chebyshev.psi_le_const_mul_self）。 -/
theorem pnt_prereq_psi_upper {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
  Chebyshev.psi_le_const_mul_self hx

/-- ψ(n) ≥ n·log 2 − log(n+1) （Chebyshev 下界，调用 Chebyshev.psi_ge）。 -/
theorem pnt_prereq_psi_lower (n : ℕ) :
    n * Real.log 2 - Real.log (n + 1) ≤ Chebyshev.psi n :=
  Chebyshev.psi_ge n

/-! ## 3. ψ 与 θ 之差（小阶估计，调用） -/

/-- ψ(x) − θ(x) ≤ 2·√x·log x （调用 Chebyshev.psi_sub_theta_le）。 -/
theorem pnt_prereq_psi_theta_gap {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
  Chebyshev.psi_sub_theta_le hx

/-- ψ − θ = O(√x)（调用 Chebyshev.isBigO_psi_sub_theta_sqrt）。 -/
theorem pnt_prereq_psi_theta_gap_isBigO :
    IsBigO atTop (Chebyshev.psi - Chebyshev.theta : ℝ → ℝ) Real.sqrt :=
  Chebyshev.isBigO_psi_sub_theta_sqrt

/-! ## 4. ζ 在 Re s ≥ 1 无零点（PNT 关键前置部件，调用） -/

/-- riemannZeta s ≠ 0 对一切 Re s ≥ 1 成立（调用 riemannZeta_ne_zero_of_one_le_re）。 -/
theorem pnt_prereq_zeta_nozeros {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-! ## 5. 主命题

PNT 解析形式 ψ(x) ~ x 的完整证明需要：
  (a) −ζ'(s)/ζ(s) 的 Dirichlet 级数与 ψ 的 Mellin/Perron 关系；
  (b) Newman / Ikehara 型 Tauberian 引理；
  (c) 围道积分估计。
mathlib 目前仅有第 4 节的 ζ 无零点部件，缺少 (a)(b)(c) 的现成定理，
且这些引理本身即重大结果。故主命题在本库范围内保持未证明：不加公理、不留
sorry、不伪造证明。

等价陈述 θ(x)~x、π(x)~x/log x 亦同此结论。 -/

end PrimeNumberTheorem

/-! ## 公理审计 -/

#print axioms PrimeNumberTheorem.pnt_prereq_psi_def
#print axioms PrimeNumberTheorem.pnt_prereq_lambda_on_prime
#print axioms PrimeNumberTheorem.pnt_prereq_theta_upper
#print axioms PrimeNumberTheorem.pnt_prereq_psi_upper
#print axioms PrimeNumberTheorem.pnt_prereq_psi_lower
#print axioms PrimeNumberTheorem.pnt_prereq_psi_theta_gap
#print axioms PrimeNumberTheorem.pnt_prereq_psi_theta_gap_isBigO
#print axioms PrimeNumberTheorem.pnt_prereq_zeta_nozeros
