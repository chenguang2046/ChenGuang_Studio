/-
Challenge_017_001_Number_FermatLittle.lean
从 Challenge_017_Number_Theorems.lean 拆分（台账 id 92 / no 017.1）
经典数论定理切片 1/6：费马小定理。
mathlib 现成定理包装，无占位未完成记号。
-/
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Int.GCD

open scoped Nat

namespace Challenge017

/-- 费马小定理：对素数 p，任意整数 a 满足 a^p ≡ a (mod p)。
    来自 mathlib `ZMod.pow_card`。 -/
theorem fermat_little (p : ℕ) [Fact p.Prime] (a : ℕ) : a ^ p ≡ a [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [Nat.cast_pow]
  exact ZMod.pow_card (p := p) (x := (a : ZMod p))

end Challenge017

/-! # 公理审计 -/
#print axioms Challenge017.fermat_little
