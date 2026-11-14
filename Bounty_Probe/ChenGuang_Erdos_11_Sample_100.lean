/-
# Erdős Problem 11 — a finite sample up to `100`

Erdős Problem 11 asks whether every integer `n > 1` that is not divisible by `4` can be
written as `n = k + 2 ^ l` with `k` squarefree.  The general question is open; what is
recorded here is a finite sample of it: for every `n ≤ 100` with `4 ∤ n` and `n > 1` we
exhibit an explicit pair `(k, l)`.

The witnesses are chosen so that squarefreeness is *seen*, not computed: in every case
`k` is a prime, or a product of two distinct primes, or `1`.  Two one-line lemmas cover
the first two shapes, and the identity `n = k + 2 ^ l` is a numeral computation.  The
sample is then closed by `interval_cases`, so the whole certificate is a single table of
witnesses — one branch per `n`, in increasing order from `2` to `100` — rather than a
chain of auxiliary facts.  The branches with `4 ∣ n` are vacuous and are discharged by
the divisibility hypothesis alone.

Odd numbers are never divisible by `4`, so the sample certifies the odd case as well
(the corollary `odd_le_100`).
-/

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace ChenGuang.Erdos11.Sample100

/-! ## Two shapes of squarefree numbers -/

/-- A prime is squarefree. -/
theorem squarefree_of_prime {p : ℕ} (hp : p.Prime) : Squarefree p := hp.squarefree

/-- A product of two distinct primes is squarefree. -/
theorem squarefree_of_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Squarefree (p * q) :=
  (Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hne)).mpr
    ⟨hp.squarefree, hq.squarefree⟩

/-! ## The sample -/

/-- **Erdős Problem 11, sampled up to `100`**: every `n ≤ 100` with `4 ∤ n` and `n > 1`
is a squarefree number plus a power of two. -/
theorem not_four_dvd_le_100 (n : ℕ) (hn : n ≤ 100) (hfour : ¬ 4 ∣ n) (hgt : 1 < n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  interval_cases n
  · exact ⟨1, 0, squarefree_one, by norm_num⟩
  · exact ⟨2, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨3, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨5, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨5, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨7, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨2, 3, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨7, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨11, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨13, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨13, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨13, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨17, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨17, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨19, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨3 * 7, 0, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨19, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨23, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨2 * 11, 2, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨23, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨13, 4, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨29, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨29, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨31, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨2, 5, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨31, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨29, 3, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨37, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨37, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨37, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨41, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨41, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨43, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨2 * 19, 3, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨43, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨47, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨2 * 23, 2, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨47, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨37, 4, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨53, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨53, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨53, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨3 * 19, 0, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨43, 4, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨59, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨61, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨61, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨61, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨2, 6, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨59, 3, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨67, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨3 * 23, 0, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨67, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨71, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨73, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨73, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨73, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨7 * 11, 0, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨71, 3, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨79, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨2 * 37, 3, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨79, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨83, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨5 * 17, 0, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨83, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨73, 4, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨89, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨89, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨89, 2, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨3 * 31, 0, squarefree_of_two_primes (by norm_num) (by norm_num) (by norm_num), by norm_num⟩
  · exact ⟨79, 4, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour
  · exact ⟨89, 3, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨97, 0, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact ⟨97, 1, squarefree_of_prime (by norm_num), by norm_num⟩
  · exact absurd (by norm_num) hfour

/-! ## The odd case -/

/-- For odd `n > 1` the sample applies, since an odd number is never divisible by `4`. -/
theorem odd_le_100 (n : ℕ) (hn : Odd n) (hgt : 1 < n) (hle : n ≤ 100) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  refine not_four_dvd_le_100 n hle ?_ hgt
  rintro ⟨m, hm⟩
  obtain ⟨j, hj⟩ := hn
  rw [hj] at hm
  omega

end ChenGuang.Erdos11.Sample100

/-! ## Axiom audit -/

#print axioms ChenGuang.Erdos11.Sample100.not_four_dvd_le_100
#print axioms ChenGuang.Erdos11.Sample100.odd_le_100
