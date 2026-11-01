import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Universal Slice 007

指数和 `e^(2π i n α)` 的复数定义及其模长为 1 的证明。

定义 `expSum n α = exp (2 * π * i * n * α)`（其中 `n : ℤ`，`α : ℝ`），
并证明 `‖expSum n α‖ = 1`，即该复数落在单位圆上。

引用的 mathlib 定理：
* `Complex.norm_exp`：`‖exp z‖ = Real.exp z.re`；
* `Complex.exp_mul_I`（经由 `Complex.norm_exp` 的理论基础）；
* `Real.exp_zero`。
-/

namespace UniversalSlice007

/-- 指数和：`e^(2π i n α) = exp (2 * π * i * n * α)`。 -/
noncomputable def expSum (n : ℤ) (α : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (n : ℝ) * α : ℝ) : ℂ) * Complex.I)

/-- 指数和的模长为 1，即位于复平面单位圆上。 -/
theorem expSum_norm_eq_one (n : ℤ) (α : ℝ) : ‖expSum n α‖ = 1 := by
  unfold expSum
  rw [Complex.norm_exp]
  have hre : (((2 * Real.pi * (n : ℝ) * α : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

end UniversalSlice007
