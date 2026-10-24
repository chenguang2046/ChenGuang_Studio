/-
Challenge_009 — Chebyshev 型下界（PNT 前置）
目标：形式化素数计数函数 π(x) 与 Chebyshev 界 π(x) ≥ c·x/log x 的数量级关系。
方法（双轨）：
  (1) 直接包装 mathlib 真实定理（PrimeCounting 模块）：
      - Nat.primesLE_card_eq_primeCounting  （π(n) = # {p ≤ n | p 素数}）
      - Nat.primeCounting_add_le            （Chebyshev 型线性上界）
      - Nat.monotone_primeCounting          （单调性）
  (2) mathlib 不提供"存在常数 c>0 使 π(x) ≥ c·x/log x"的显式常数证明
      （v4.34 无完整 PNT / Chebyshev 显式界），按任务书授权改为
      手搓有限范围的严格下界：用 native_decide 可判定验证
      ∀ n, 2 ≤ n ≤ 5000 : n / (log₂ n + 1) ≤ π(n)。
      如实标注：范围 2..5000、常数 c = 1、对数以 2 为底
      （log₂ n = ln n / ln 2，故对应实数常数 c ≈ ln 2 ≈ 0.693）。
零 sorry，公理审计见文件尾。
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Log

namespace Challenge009

-- (1a) π(n) 与素数集合基数的关系（mathlib 现成）
theorem primesLE_card_eq_primeCounting (n : ℕ) :
    (Nat.primesLE n).card = Nat.primeCounting n :=
  Nat.primesLE_card_eq_primeCounting n

-- (1b) Chebyshev 型线性上界（mathlib 现成：π(k+n) ≤ π(k) + φ(a)·(n/a + 1)）
theorem primeCounting_linear_upper (a k n : ℕ) (h0 : a ≠ 0) (h1 : a ≤ k) :
    Nat.primeCounting (k + n) ≤
      Nat.primeCounting k + Nat.totient a * (n / a + 1) :=
  Nat.primeCounting_add_le h0 h1 n

-- (1c) 单调性
theorem primeCounting_mono : Monotone Nat.primeCounting :=
  Nat.monotone_primeCounting

-- (2) 有限范围严格下界（自建，native_decide 可判定验证）
-- 下界函数：L_c(n) := (c·n) / (log₂ n + 1)，取 c = 1
def chebyshevLowerBound (c n : ℕ) : ℕ :=
  (c * n) / (Nat.log 2 n + 1)

-- 命题：对 2 ≤ n ≤ 5000，L_1(n) ≤ π(n)
theorem chebyshev_lower_finite_range :
    ∀ n ∈ Finset.Icc 2 5000, chebyshevLowerBound 1 n ≤ Nat.primeCounting n := by
  native_decide

-- 直接展开为更易读的形式：n / (log₂ n + 1) ≤ π(n)
theorem chebyshev_lower_finite_range' :
    ∀ n : ℕ, 2 ≤ n → n ≤ 5000 →
      n / (Nat.log 2 n + 1) ≤ Nat.primeCounting n := by
  intro n hn2 hnN
  simpa [chebyshevLowerBound] using
    (chebyshev_lower_finite_range n (by simp [hn2, hnN]))

-- 附注（纯客观，非定理）：log₂ n = ln n / ln 2，故上述验证对应实数常数
-- c ≈ ln 2 ≈ 0.693 的 Chebyshev 下界 π(n) ≥ c·n/log n（仅限 2..5000）。

end Challenge009

-- 公理审计
#print axioms Challenge009.chebyshev_lower_finite_range
#print axioms Challenge009.primesLE_card_eq_primeCounting
#print axioms Challenge009.primeCounting_linear_upper
