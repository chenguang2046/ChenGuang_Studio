import Slices_99.Challenge_021C_Index_Main

set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup QuotientGroup

namespace Challenge021Gamma0NIndex

def universalIndex (N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) * (p + 1))

theorem universalIndex_one : universalIndex 1 = 1 := by
  simp [universalIndex]

theorem universalIndex_prime (p : ℕ) [Fact p.Prime] : universalIndex p = p + 1 := by
  have hp : p.Prime := Fact.out
  rw [universalIndex, hp.primeFactors, Finset.prod_singleton, hp.factorization_self]
  norm_num

theorem universalIndex_primePow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    universalIndex (p ^ k) = p ^ k + p ^ (k - 1) := by
  have hp : p.Prime := Fact.out
  rw [universalIndex, Nat.primeFactors_pow (k := k) p (Nat.Prime.ne_zero hp), hp.primeFactors,
    Finset.prod_singleton]
  rw [Nat.factorization_pow_self hp]
  calc
    p ^ (k - 1) * (p + 1) = p ^ (k - 1) * p + p ^ (k - 1) := by ring
    _ = p ^ ((k - 1) + 1) + p ^ (k - 1) := by rw [pow_succ]
    _ = p ^ k + p ^ (k - 1) := by rw [Nat.sub_add_cancel hk]

end Challenge021Gamma0NIndex
