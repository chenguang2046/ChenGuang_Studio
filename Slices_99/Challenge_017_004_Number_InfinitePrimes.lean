/-
Challenge_017_004_Number_InfinitePrimes.lean
从 Challenge_017_Number_Theorems.lean 拆分（台账 id 95 / no 017.4）
经典数论定理切片 4/6：素数无穷。
mathlib 现成定理包装，无占位未完成记号。
-/
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Int.GCD

open scoped Nat

namespace Challenge017

/-- 素数无穷：对任意 n，存在不小于 n 的素数。
    来自 mathlib `Nat.exists_infinite_primes`。 -/
theorem infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes n

end Challenge017

/-! # 公理审计 -/
#print axioms Challenge017.infinite_primes
