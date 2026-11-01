/-
Challenge_011 — Hasse-Weil 局部欧拉因子结构（椭圆曲线局部验证）
目标：验证椭圆曲线 E 在素数 p 处的局部欧拉因子 1 - a_p·p^(-s) + p^(1-2s) 的代数性质，
      或证明 Hasse 界 |a_p| ≤ 2√p 的有限实例/基础推论。
方法（双轨）：
  (1) mathlib v4.34 已定义 Weierstrass 曲线的完整局部 L 结构：
      WeierstrassCurve.localPolynomial（好约化时为 1 - a·T + q·T²）、
      localEulerFactor、LFunction、LSeries。本文件以 #check 引用展示真实结构。
  (2) 自建最外围局部代数验证（不依赖虚构引理）：
      A. Hasse 界绝对值形式 |a| ≤ 2√p 与平方形式 a² ≤ 4p 等价（代数引理）；
      B. 严格 Hasse 界 a² < 4p 蕴含好约化局部多项式 1 - a·x + p·x² 无实根
         （判别式 Δ = a² - 4p < 0，根为复共轭对，对应欧拉因子的代数结构）；
      C. 有限实例：椭圆曲线 E : y² = x³ + x + 1（判别式 -16·31，p = 5,7,11,13
         均好约化），用 decide 遍历有限域验证
         a_p = p+1 - |E(𝔽_p)| 满足 (p+1-N)² ≤ 4p，即 Hasse 界 |a_p| ≤ 2√p。
  只做最外围局部代数，绝不触碰 BSD 秩与 Sha 群。
零 sorry，公理审计见文件尾。
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Real.Sqrt

open scoped Polynomial
open Polynomial

noncomputable section

namespace Challenge011

/-! 第一部分：mathlib 现成的 Weierstrass 曲线局部 L 结构（真实引用） -/

#check WeierstrassCurve.localPolynomial
#check WeierstrassCurve.localEulerFactor
#check WeierstrassCurve.LFunction
#check WeierstrassCurve.LSeries

/-! 第二部分：好约化局部欧拉因子的代数性质（自建） -/

/-- 好约化局部欧拉因子的教科书形式：1 - a·T + q·T²（q = p = 剩余域基数）。 -/
def eulerFactorPolynomial (q a : ℤ) : ℤ[X] :=
  1 - C a * X + C q * X ^ 2

-- 性质 A：|a| ≤ 2√p（实数） ⟺ a² ≤ 4p（整数平方形式）
theorem hasse_sq_iff_abs {p : ℕ} {a : ℤ} (hp : 0 ≤ (p : ℝ)) :
    |(a : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) ↔ (a : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by
  have hpos : 0 ≤ 2 * Real.sqrt (p : ℝ) := by positivity
  have habs : |2 * Real.sqrt (p : ℝ)| = 2 * Real.sqrt (p : ℝ) := abs_of_nonneg hpos
  constructor
  · intro h
    have h2 : |(a : ℝ)| ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 := by
      apply sq_le_sq.mpr
      simpa [habs] using h
    have h2' : (a : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
      rw [sq_abs] at h2
      have hm : (2 * Real.sqrt (p : ℝ)) ^ 2 = 4 * (p : ℝ) := by
        rw [mul_pow, Real.sq_sqrt hp]
        norm_num
      simpa [hm] using h2
    exact_mod_cast h2'
  · intro h
    have hc : (a : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by exact_mod_cast h
    have hm : 4 * (p : ℝ) = (2 * Real.sqrt (p : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hp]
      norm_num
    have h2 : |(a : ℝ)| ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 := by
      rw [sq_abs, ← hm]
      exact hc
    have hs : Real.sqrt (|(a : ℝ)| ^ 2) ≤ Real.sqrt ((2 * Real.sqrt (p : ℝ)) ^ 2) :=
      Real.sqrt_le_sqrt h2
    -- sqrt(|a|²) = |a|；sqrt((2√p)²) = |2√p| = 2√p（非负）
    simpa [Real.sqrt_sq_eq_abs, habs] using hs

-- 性质 B：严格 Hasse 界 a² < 4p 蕴含好约化局部多项式无实根
--（判别式 Δ = a² - 4q < 0，两根为复共轭对：Hasse 界的最外围代数推论）
theorem eulerFactor_no_real_root {p : ℕ} {a : ℤ} (_hp : 0 < p)
    (h : (a : ℤ) ^ 2 < 4 * (p : ℤ)) :
    ∀ x : ℝ, 1 - (a : ℝ) * x + (p : ℝ) * x ^ 2 ≠ 0 := by
  intro x
  by_contra hx
  -- hx : 1 - a·x + p·x² ≠ 0 的否定，即假设 x 是实根
  have hroot : 1 - (a : ℝ) * x + (p : ℝ) * x ^ 2 = 0 := by simpa using hx
  have hx'' : (p : ℝ) * x ^ 2 = (a : ℝ) * x - 1 := by linarith
  -- 从根等式推出 (2px - a)² = a² - 4p < 0，与平方非负矛盾
  have hsq : (2 * (p : ℝ) * x - (a : ℝ)) ^ 2 = (a : ℝ) ^ 2 - 4 * (p : ℝ) := by
    have hpq : (2 * (p : ℝ) * x - (a : ℝ)) ^ 2 =
        4 * (p : ℝ) * ((p : ℝ) * x ^ 2) - 4 * (p : ℝ) * (a : ℝ) * x + (a : ℝ) ^ 2 := by
      ring
    rw [hx''] at hpq
    rw [hpq]
    ring
  have hc : (a : ℝ) ^ 2 < 4 * (p : ℝ) := by exact_mod_cast h
  have hge : 0 ≤ (2 * (p : ℝ) * x - (a : ℝ)) ^ 2 := sq_nonneg _
  rw [hsq] at hge
  linarith

/-! 第三部分：Hasse 界有限实例（自建，native_decide 遍历有限域验证） -/

/-- E : y² = x³ + a·x + b 在 𝔽_p 上的仿射点计数（每个 x 累加 y 解个数）。 -/
def countAffinePoints (p a b : ℕ) : ℕ :=
  ((Finset.range p).sum fun x =>
    ((Finset.range p).filter fun y =>
      (y * y) % p = (x * x * x + a * x + b) % p).card)

/-- Hasse 界可判定检查：N = 全点计数（仿射 + 无穷远点 1），a_p = p+1 - N 满足
    (a_p)² ≤ 4p（⟺ |a_p| ≤ 2√p，Hasse 界标准形式）。 -/
def hasseOk (p a b : ℕ) : Prop :=
  let N := countAffinePoints p a b + 1
  ((p + 1 : ℤ) - (N : ℤ)) ^ 2 ≤ 4 * (p : ℤ)

instance hasseOkDecidable (p a b : ℕ) : Decidable (hasseOk p a b) := by
  unfold hasseOk
  infer_instance

-- E : y² = x³ + x + 1，判别式 Δ = -16·(4 + 27) = -16·31；
-- p = 5, 7, 11, 13 均不整除 31，故 E 在这些 p 处好约化。
theorem hasse_finite_p5 : hasseOk 5 1 1 := by decide
theorem hasse_finite_p7 : hasseOk 7 1 1 := by decide
theorem hasse_finite_p11 : hasseOk 11 1 1 := by decide
theorem hasse_finite_p13 : hasseOk 13 1 1 := by decide

end Challenge011

-- 公理审计
#print axioms Challenge011.hasse_sq_iff_abs
#print axioms Challenge011.eulerFactor_no_real_root
#print axioms Challenge011.hasse_finite_p5
#print axioms Challenge011.hasse_finite_p13
