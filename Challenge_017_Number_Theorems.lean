/-
Challenge_017_Number_Theorems.lean
经典数论定理切片 6 片（累计 91 -> 97）
1. fermat_little                    : 费马小定理
2. euler_totient                    : 欧拉 totient 定理
3. chinese_remainder                : 中国剩余定理（环同构）
4. infinite_primes                  : 素数无穷
5. fundamental_theorem_of_arithmetic: 算术基本定理（唯一分解）
6. bezout_lemma                     : 贝祖引理（gcd 线性组合）
全部为 mathlib 现成定理包装，无占位未完成记号。
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

/-- 欧拉 totient 定理：与 n 互素的 x 满足 x^φ(n) ≡ 1 (mod n)。
    来自 mathlib `Nat.ModEq.pow_totient`。 -/
theorem euler_totient (x n : ℕ) (h : Nat.Coprime x n) :
    x ^ Nat.totient n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

/-- 中国剩余定理：互素模数 m,n 的剩余环同构于乘积。
    来自 mathlib `ZMod.chineseRemainder`。 -/
theorem chinese_remainder (m n : ℕ) (h : Nat.Coprime m n) :
    Nonempty (ZMod (m * n) ≃+* ZMod m × ZMod n) :=
  ⟨ZMod.chineseRemainder h⟩

/-- 素数无穷：对任意 n，存在不小于 n 的素数。
    来自 mathlib `Nat.exists_infinite_primes`。 -/
theorem infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes n

/-- 算术基本定理：非零自然数被其素因子分解唯一确定（factorization 单射）。
    来自 mathlib `Nat.eq_of_factorization_eq`。 -/
theorem fundamental_theorem_of_arithmetic {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization = b.factorization) : a = b :=
  Nat.factorization_inj ha hb h

/-- 贝祖引理：gcd(x,y) 是 x 与 y 的整系数线性组合。
    来自 mathlib `Nat.gcd_eq_gcd_ab`。 -/
theorem bezout_lemma (x y : ℕ) : ∃ a b : ℤ, (Nat.gcd x y : ℤ) = x * a + y * b :=
  ⟨x.gcdA y, x.gcdB y, Nat.gcd_eq_gcd_ab x y⟩

end Challenge017

/-! # 公理审计 -/
#print axioms Challenge017.fermat_little
#print axioms Challenge017.euler_totient
#print axioms Challenge017.chinese_remainder
#print axioms Challenge017.infinite_primes
#print axioms Challenge017.fundamental_theorem_of_arithmetic
#print axioms Challenge017.bezout_lemma
