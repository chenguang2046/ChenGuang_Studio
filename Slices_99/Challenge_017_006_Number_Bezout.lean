/-
Challenge_017_006_Number_Bezout.lean
从 Challenge_017_Number_Theorems.lean 拆分（台账 id 97 / no 017.6）
经典数论定理切片 6/6：贝祖引理（gcd 线性组合）。
mathlib 现成定理包装，无占位未完成记号。
-/
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Int.GCD

open scoped Nat

namespace Challenge017

/-- 贝祖引理：gcd(x,y) 是 x 与 y 的整系数线性组合。
    来自 mathlib `Nat.gcd_eq_gcd_ab`。 -/
theorem bezout_lemma (x y : ℕ) : ∃ a b : ℤ, (Nat.gcd x y : ℤ) = x * a + y * b :=
  ⟨x.gcdA y, x.gcdB y, Nat.gcd_eq_gcd_ab x y⟩

end Challenge017

/-! # 公理审计 -/
#print axioms Challenge017.bezout_lemma
