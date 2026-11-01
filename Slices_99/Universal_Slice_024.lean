import Mathlib.Data.Nat.Choose.Sum

/-!
# Universal Slice 024: Binomial coefficients and the binomial theorem

Pure textbook statement: Pascal's identity for binomial coefficients, and the
binomial theorem in a commutative semiring.
-/

namespace UniversalSlice024

open Finset

/-- Pascal's identity: C(n+1, k+1) = C(n, k) + C(n, k+1). -/
theorem pascal_identity (n k : ℕ) : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ' n k

/-- Pascal's identity, succ form: C(succ n, succ k) = C(n, k) + C(n, succ k). -/
theorem pascal_identity_succ (n k : ℕ) : Nat.choose (Nat.succ n) (Nat.succ k) = Nat.choose n k + Nat.choose n (Nat.succ k) :=
  Nat.choose_succ_succ n k

/-- The binomial theorem in a commutative semiring:
(x + y)^n = sum over m of (choose n m) * x^m * y^(n-m). -/
theorem binomial_theorem {R : Type*} [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m :=
  add_pow x y n

end UniversalSlice024

#print axioms UniversalSlice024.pascal_identity
#print axioms UniversalSlice024.pascal_identity_succ
#print axioms UniversalSlice024.binomial_theorem
