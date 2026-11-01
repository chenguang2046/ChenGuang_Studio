import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.Complex.Basic

/-!
# Universal Slice 006

算术函数的局部因子经有限乘积构建全局函数值。

对乘性算术函数 `f : ArithmeticFunction R`（满足 `f 1 = 1` 且对互素
整数 `m, n` 有 `f (m * n) = f m * f n`），其全局值可由局部因子（素因子
处的取值）经有限乘积恢复。本文实例化 `R = ℂ`，调用：

* `ArithmeticFunction.IsMultiplicative.map_prod`：互素因子序列的乘积；
* `ArithmeticFunction.IsMultiplicative.map_prod_of_prime`：素因子集合乘积；
* `ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors`：素因子子集乘积；
* `ArithmeticFunction.IsMultiplicative.prod_primeFactors`：无平方数由素因子局部值乘积给出。
-/

namespace UniversalSlice006

open scoped BigOperators Function

/-- 局部因子乘积：对两两互素的因子序列 `g i`，有
`f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i)`。 -/
theorem local_factors_prod {ι : Type*} (g : ι → ℕ)
    {f : ArithmeticFunction ℂ} (hf : ArithmeticFunction.IsMultiplicative f)
    (s : Finset ι) (hs : (s : Set ι).Pairwise (Nat.Coprime on g)) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) :=
  ArithmeticFunction.IsMultiplicative.map_prod g hf s hs

/-- 素因子局部值乘积：对素因子集合 `t`，有
`f (∏ p ∈ t, p) = ∏ p ∈ t, f p`。 -/
theorem local_factors_prod_of_prime {f : ArithmeticFunction ℂ}
    (hf : ArithmeticFunction.IsMultiplicative f) (t : Finset ℕ)
    (ht : ∀ p ∈ t, p.Prime) :
    f (∏ p ∈ t, p) = ∏ p ∈ t, f p :=
  ArithmeticFunction.IsMultiplicative.map_prod_of_prime hf t ht

/-- 素因子子集版本：对 `t ⊆ l.primeFactors`，有
`f (∏ p ∈ t, p) = ∏ p ∈ t, f p`。 -/
theorem local_factors_prod_of_subset_primeFactors {f : ArithmeticFunction ℂ}
    (hf : ArithmeticFunction.IsMultiplicative f) (l : ℕ) (t : Finset ℕ)
    (ht : t ⊆ l.primeFactors) :
    f (∏ p ∈ t, p) = ∏ p ∈ t, f p :=
  ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors hf l t ht

/-- 无平方数的全局值：若 `l` 无平方因子，则
`∏ p ∈ l.primeFactors, f p = f l`，即全局值由素因子局部值乘积给出。 -/
theorem prod_primeFactors_eq_value {f : ArithmeticFunction ℂ}
    (hf : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ p ∈ l.primeFactors, f p = f l :=
  ArithmeticFunction.IsMultiplicative.prod_primeFactors hf hl

end UniversalSlice006
