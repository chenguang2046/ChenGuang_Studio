/-
Challenge_017_002_Number_EulerTotient.lean
从 Challenge_017_Number_Theorems.lean 拆分（台账 id 93 / no 017.2）
经典数论定理切片 2/6：欧拉 totient 定理。
mathlib 现成定理包装，无占位未完成记号。
-/
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Int.GCD

open scoped Nat

namespace Challenge017

/-- 欧拉 totient 定理：与 n 互素的 x 满足 x^φ(n) ≡ 1 (mod n)。
    来自 mathlib `Nat.ModEq.pow_totient`。 -/
theorem euler_totient (x n : ℕ) (h : Nat.Coprime x n) :
    x ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

end Challenge017

/-! # 公理审计 -/
#print axioms Challenge017.euler_totient
