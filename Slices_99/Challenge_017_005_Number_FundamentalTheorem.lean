/-
Challenge_017_005_Number_FundamentalTheorem.lean
从 Challenge_017_Number_Theorems.lean 拆分（台账 id 96 / no 017.5）
经典数论定理切片 5/6：算术基本定理（唯一分解）。
mathlib 现成定理包装，无占位未完成记号。
-/
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Int.GCD

open scoped Nat

namespace Challenge017

/-- 算术基本定理：非零自然数被其素因子分解唯一确定（factorization 单射）。
    来自 mathlib `Nat.eq_of_factorization_eq`。 -/
theorem fundamental_theorem_of_arithmetic {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization = b.factorization) : a = b :=
  Nat.factorization_inj ha hb h

end Challenge017

/-! # 公理审计 -/
#print axioms Challenge017.fundamental_theorem_of_arithmetic
