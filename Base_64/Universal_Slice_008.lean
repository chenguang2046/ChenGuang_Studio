import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Universal Slice 008

黎曼可积函数在区间上的加法与数乘性质。

mathlib 的区间积分 `∫ x in a..b, f x ∂μ` 基于黎曼意义下的
`IntervalIntegrable`。本文调用：

* `IntervalIntegrable.add`：可积函数的和仍可积；
* `IntervalIntegrable.const_mul`：可积函数的常数倍仍可积；
* `intervalIntegral.integral_add`：积分对加法线性；
* `intervalIntegral.integral_const_mul`：积分对数乘线性。
-/

namespace UniversalSlice008

open MeasureTheory

variable {f g : ℝ → ℝ} {μ : Measure ℝ} {a b c d : ℝ}

/-- 加法封闭性：若 `f`、`g` 在 `[a, b]` 上（黎曼）可积，则 `f + g` 也可积。 -/
theorem integrable_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable (fun x => f x + g x) μ a b :=
  hf.add hg

/-- 数乘封闭性：若 `f` 在 `[a, b]` 上可积，则 `c * f` 也可积。 -/
theorem integrable_const_mul (c : ℝ) (hf : IntervalIntegrable f μ a b) :
    IntervalIntegrable (fun x => c * f x) μ a b :=
  hf.const_mul c

/-- 区间积分对加法线性：`∫ (f + g) = ∫ f + ∫ g`。 -/
theorem integral_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, (f x + g x) ∂μ = ∫ x in a..b, f x ∂μ + ∫ x in a..b, g x ∂μ :=
  intervalIntegral.integral_add hf hg

/-- 区间积分对数乘线性：`∫ (c * f) = c * ∫ f`。 -/
theorem integral_const_mul (c : ℝ) :
    ∫ x in a..b, c * f x ∂μ = c * ∫ x in a..b, f x ∂μ :=
  intervalIntegral.integral_const_mul c f

/-- 线性组合的积分等于积分的线性组合。 -/
theorem integral_linear_combination (hf : IntervalIntegrable f μ a b)
    (hg : IntervalIntegrable g μ a b) :
    ∫ x in a..b, (c * f x + d * g x) ∂μ
      = c * ∫ x in a..b, f x ∂μ + d * ∫ x in a..b, g x ∂μ := by
  calc
    ∫ x in a..b, (c * f x + d * g x) ∂μ
        = ∫ x in a..b, c * f x ∂μ + ∫ x in a..b, d * g x ∂μ :=
          intervalIntegral.integral_add (hf.const_mul c) (hg.const_mul d)
    _ = c * ∫ x in a..b, f x ∂μ + d * ∫ x in a..b, g x ∂μ := by
          rw [intervalIntegral.integral_const_mul c f,
            intervalIntegral.integral_const_mul d g]

end UniversalSlice008
