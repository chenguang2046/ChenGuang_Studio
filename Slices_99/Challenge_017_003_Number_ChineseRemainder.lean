/-
Challenge_017_003_Number_ChineseRemainder.lean
从 Challenge_017_Number_Theorems.lean 拆分（台账 id 94 / no 017.3）
经典数论定理切片 3/6：中国剩余定理（环同构）。
mathlib 现成定理包装，无占位未完成记号。
-/
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Int.GCD

open scoped Nat

namespace Challenge017

/-- 中国剩余定理：互素模数 m,n 的剩余环同构于乘积。
    来自 mathlib `ZMod.chineseRemainder`。 -/
theorem chinese_remainder (m n : ℕ) (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

end Challenge017

/-! # 公理审计 -/
#print axioms Challenge017.chinese_remainder
