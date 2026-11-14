import Mathlib

/-!
# 哥德巴赫猜想：形式化与数值验证

哥德巴赫猜想（Goldbach's conjecture）：每个大于 2 的偶数都可以表示为两个质数之和。

本文件包含两部分：
1. `GoldbachConjecture`：猜想本身的形式化陈述（未证明命题，因为该猜想至今仍是开放问题）；
2. `verifyGoldbach`：数值验证函数，检查范围 [4, N] 内所有偶数是否都满足
   哥德巴赫性质，若找到反例则返回该反例。
-/

namespace Goldbach

/-- 哥德巴赫猜想的形式化陈述：任意偶数 n > 2，存在质数 p, q 使得 n = p + q。 -/
def GoldbachConjecture : Prop :=
  ∀ n : Nat, 2 < n → Even n → ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- 返回不超过 N 的所有质数。 -/
def primesUpTo (N : Nat) : List Nat :=
  (List.range (N + 1)).filter fun k => 2 ≤ k ∧ Nat.Prime k

/-- 数值验证：若 [4, N] 内存在不满足哥德巴赫性质的偶数，返回 `some m`（第一个反例）；全部满足则返回 `none`。 -/
def verifyGoldbach (N : Nat) : Option Nat := Id.run do
  let half := N / 2
  let primesAll := primesUpTo N
  let mut isPrime : Array Bool := Array.replicate (N + 1) false
  for p in primesAll do
    isPrime := isPrime.set! p true
  let primesHalf := primesAll.filter fun p => p ≤ half
  for e in List.range (half + 1) do
    let m := 2 * e
    if 4 ≤ m then
      if not (primesHalf.any fun p => isPrime[m - p]!) then
        return some m
  return none

/-- 对单个偶数 m 返回一组具体的质数分解 (p, q)。 -/
def goldbachPair (primes : List Nat) (isPrime : Array Bool) (m : Nat) : Option (Nat × Nat) :=
  (primes.find? fun p => isPrime[m - p]!).map fun p => (p, m - p)

end Goldbach

-- 抽查：若干偶数的具体质数分解
#eval Id.run do
  let N := 100000
  let primes := Goldbach.primesUpTo N
  let mut isPrime : Array Bool := Array.replicate (N + 1) false
  for p in primes do
    isPrime := isPrime.set! p true
  let samples := [4, 10, 28, 100, 1000, 10000, 99998, 100000].filterMap
    (fun m => (Goldbach.goldbachPair primes isPrime m).map fun (p, q) => (m, p, q))
  samples

-- 数值验证 10 万以内所有偶数
#eval Goldbach.verifyGoldbach 100000
