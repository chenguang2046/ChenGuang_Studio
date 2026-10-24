import Mathlib.NumberTheory.LSeries.Basic

/-!
# Universal Slice 004

一般狄利克雷级数在 `Re(s) > 1` 时的绝对收敛性。

设 `f : ℕ → ℂ` 为系数序列，`L(f, s) = ∑ n, f n / n ^ s` 为一般狄利克雷级数。
mathlib 中 `LSeriesSummable f s` 即断言项级数 `∑ n, term f s n` 绝对可和，
其中 `term f s n` 为级数通项。本文调用 mathlib 现成的收敛判据：

* `LSeriesSummable_of_bounded_of_one_lt_re`：有界系数 + `1 < Re(s)` 绝对收敛；
* `LSeriesSummable_of_bounded_of_one_lt_real`：实参数版本；
* `LSeriesSummable_of_isBigO_rpow`：系数按 `n ^ (x - 1)` 增长 + `x < Re(s)` 绝对收敛。
-/

namespace UniversalSlice004

/-- 有界系数判据：若 `‖f n‖ ≤ m` 对一切 `n ≠ 0` 成立，且 `1 < Re(s)`，
则一般狄利克雷级数 `L(f, s)` 在 `s` 处绝对收敛。 -/
theorem abs_convergence_of_bounded_coefficients {f : ℕ → ℂ} {m : ℝ} {s : ℂ}
    (hb : ∀ n ≠ 0, ‖f n‖ ≤ m) (hs : 1 < s.re) :
    Summable (LSeries.term f s) := by
  simpa [LSeriesSummable] using
    (LSeriesSummable_of_bounded_of_one_lt_re hb hs : LSeriesSummable f s)

/-- 实参数版本：若 `s : ℝ` 满足 `1 < s`，则 `L(f, s)` 绝对收敛。 -/
theorem abs_convergence_of_bounded_coefficients_real {f : ℕ → ℂ} {m : ℝ} {s : ℝ}
    (hb : ∀ n ≠ 0, ‖f n‖ ≤ m) (hs : 1 < s) :
    Summable (LSeries.term f (s : ℂ)) := by
  simpa [LSeriesSummable] using
    (LSeriesSummable_of_bounded_of_one_lt_real hb hs : LSeriesSummable f (s : ℂ))

/-- 多项式增长判据：若 `f n = O(n ^ (x - 1))` 且 `x < Re(s)`，
则一般狄利克雷级数 `L(f, s)` 在 `s` 处绝对收敛。 -/
theorem abs_convergence_of_polynomial_growth {f : ℕ → ℂ} {x : ℝ} {s : ℂ}
    (hs : x < s.re)
    (h : Asymptotics.IsBigO Filter.atTop f (fun n : ℕ => (n : ℝ) ^ (x - 1))) :
    Summable (LSeries.term f s) := by
  simpa [LSeriesSummable] using
    (LSeriesSummable_of_isBigO_rpow hs h : LSeriesSummable f s)

end UniversalSlice004
