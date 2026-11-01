import Mathlib.Data.Nat.Prime.Infinite

/-!
# Universal Slice 021: There are infinitely many prime numbers

Pure textbook statement: Euclid's theorem on the infinitude of primes,
expressed through the library theorem `Nat.exists_infinite_primes`.
-/

namespace UniversalSlice021

/-- For every natural number n there is a prime p with n <= p. -/
theorem prime_unbounded (n : ℕ) : ∃ p : ℕ, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes n

/-- Consequently, for every natural number n there is a prime strictly greater than n. -/
theorem prime_gt (n : ℕ) : ∃ p : ℕ, n < p ∧ Nat.Prime p := by
  obtain ⟨p, hp_le, hp⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, Nat.lt_of_succ_le hp_le, hp⟩

end UniversalSlice021

#print axioms UniversalSlice021.prime_unbounded
#print axioms UniversalSlice021.prime_gt
