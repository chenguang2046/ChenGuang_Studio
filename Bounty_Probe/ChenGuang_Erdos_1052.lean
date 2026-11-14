/-
# Erdős Problem 1052: unitary perfect numbers are even

A divisor `d` of `n` is a *unitary divisor* if `d` is coprime to `n / d`; it is proper
if `d < n`, and `n` is *unitary perfect* when it is the sum of its proper unitary
divisors.

The question of Erdős is whether there are only finitely many unitary perfect numbers.
The first step, proved here, is that all of them are even.  The argument is elementary:

* the unitary divisors of `n` are exactly the numbers `∏ p ^ v_p(n)` taken over the
  subsets of `n.primeFactors`, so `σ*(n) = ∏ (1 + p ^ v_p(n))`;
* for odd `n` every factor `1 + p ^ a` is even, whence `2 ^ ω(n) ∣ σ*(n)`;
* a unitary perfect odd `n` satisfies `σ*(n) = 2 n`, which is even to the first power,
  so `ω(n) ≤ 1` and `n = p ^ a`;
* then `1 + p ^ a = 2 p ^ a` is impossible.

Reference: <https://www.erdosproblems.com/1052>
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ChenGuang.Erdos1052

open Finset

/-! ## Unitary divisors and the unitary sigma -/

/-- The proper unitary divisors of `n`: divisors `d < n` coprime to `n / d`. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- `n` is unitary perfect when it is the sum of its proper unitary divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- The unitary divisors of `n`, including `n` itself. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The unitary divisor sum `σ*(n)`, including the term `n`. -/
def unitarySigma (n : ℕ) : ℕ := ∑ d ∈ unitaryDivisors n, d

/-- The product `∏ p ∈ S, p ^ v_p(n)`. -/
def unitaryPart (n : ℕ) (S : Finset ℕ) : ℕ := ∏ p ∈ S, p ^ n.factorization p

/-! ## Factorizations of unit parts -/

lemma factorization_prime_pow {p k : ℕ} (hp : p.Prime) (q : ℕ) :
    (p ^ k).factorization q = if q = p then k else 0 := by
  rw [Nat.factorization_pow, Nat.Prime.factorization hp]
  by_cases h : q = p
  · subst h
    simp
  · have hsingle : (Finsupp.single p (1 : ℕ)) q = 0 := by
      rw [Finsupp.single_apply, ite_eq_right (Ne.symm h)]
    rw [Finsupp.smul_apply, hsingle, smul_zero, ite_eq_right h]

/-- A unit part is supported exactly on `S`. -/
lemma factorization_unitaryPart {n : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (unitaryPart n S).factorization q = if q ∈ S then n.factorization q else 0 := by
  unfold unitaryPart
  rw [Nat.factorization_prod_apply (fun x hx => pow_ne_zero _ (hS x hx).ne_zero)]
  rw [Finset.sum_congr rfl (fun b hb => factorization_prime_pow (hS b hb) q)]
  exact Finset.sum_ite_eq S q (fun b => n.factorization b)

lemma unitaryPart_ne_zero {n : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : unitaryPart n S ≠ 0 := by
  unfold unitaryPart
  exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hS p hp).ne_zero

lemma unitaryPart_dvd {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    unitaryPart n S ∣ n := by
  rw [← Nat.factorization_le_iff_dvd (unitaryPart_ne_zero hS) hn]
  intro q
  rw [factorization_unitaryPart hS q]
  by_cases hq : q ∈ S <;> simp [hq]

/-! ## Reading exponents off the prime factorization -/

/-- A prime is in the support of the factorization once it divides the number. -/
lemma factorization_ne_zero_of_prime_dvd {a p : ℕ} (hp : p.Prime) (hpa : p ∣ a)
    (ha : a ≠ 0) : a.factorization p ≠ 0 := by
  intro h
  rcases (Nat.factorization_eq_zero_iff a p).mp h with h1 | h2 | h3
  · exact h1 hp
  · exact h2 hpa
  · exact ha h3

/-- An exponent vanishes off the prime factors. -/
lemma factorization_eq_zero_of_not_mem_primeFactors {n q : ℕ} (hq : q ∉ n.primeFactors) :
    n.factorization q = 0 := by
  rw [← Nat.support_factorization] at hq
  by_contra h
  exact hq (Finsupp.mem_support_iff.mpr h)

/-- An exponent is nonzero on the prime factors. -/
lemma factorization_ne_zero_of_mem_primeFactors {n q : ℕ} (hq : q ∈ n.primeFactors) :
    n.factorization q ≠ 0 := by
  rw [← Nat.support_factorization] at hq
  exact Finsupp.mem_support_iff.mp hq

/-- Coprimality amounts to disjoint supports of the two factorizations. -/
lemma coprime_iff_factorization {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.Coprime b ↔ ∀ p, a.factorization p = 0 ∨ b.factorization p = 0 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  constructor
  · intro h p
    by_contra hc
    rw [not_or] at hc
    obtain ⟨h1, h2⟩ := hc
    have hpa : p ∣ a := by
      by_contra hnp
      exact h1 (Nat.factorization_eq_zero_of_not_dvd hnp)
    have hpb : p ∣ b := by
      by_contra hnp
      exact h2 (Nat.factorization_eq_zero_of_not_dvd hnp)
    have hp1 : p ∣ 1 := h ▸ Nat.dvd_gcd hpa hpb
    have hpeq : p = 1 := Nat.dvd_one.mp hp1
    exact h1 ((Nat.factorization_eq_zero_iff a p).mpr (Or.inl (hpeq ▸ Nat.not_prime_one)))
  · intro h
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left a b)
    have hpb : p ∣ b := hpd.trans (Nat.gcd_dvd_right a b)
    rcases h p with h0 | h0
    · exact factorization_ne_zero_of_prime_dvd hp hpa ha h0
    · exact factorization_ne_zero_of_prime_dvd hp hpb hb h0

/-- A unit part is coprime to what is left of `n`. -/
lemma coprime_unitaryPart_div {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (unitaryPart n S).Coprime (n / unitaryPart n S) := by
  have hdvd : unitaryPart n S ∣ n := unitaryPart_dvd hn hS
  have hd0 : unitaryPart n S ≠ 0 := unitaryPart_ne_zero hS
  have hdiv0 : n / unitaryPart n S ≠ 0 := by
    have : 0 < n / unitaryPart n S :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hd0)
    exact this.ne'
  refine (coprime_iff_factorization hd0 hdiv0).mpr fun q => ?_
  by_cases hq : q ∈ S
  · right
    rw [Nat.factorization_div hdvd]
    simp [factorization_unitaryPart hS q, hq]
  · left
    rw [factorization_unitaryPart hS q, ite_eq_right hq]

/-! ## The subsets of `n.primeFactors` and the unitary divisors -/

/-- A unitary divisor is the unit part carried by the primes that actually divide it. -/
lemma eq_unitaryPart_of_mem {n d : ℕ} (hn : n ≠ 0) (hd : d ∈ unitaryDivisors n) :
    d = unitaryPart n (n.primeFactors.filter fun p => d.factorization p ≠ 0) := by
  rw [unitaryDivisors, mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdvd, -⟩, hcop⟩ := hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hdvd
    exact hn hdvd
  have hdiv0 : n / d ≠ 0 := by
    have : 0 < n / d :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hd0)
    exact this.ne'
  set S := n.primeFactors.filter (fun p => d.factorization p ≠ 0) with hSdef
  have hSsub : S ⊆ n.primeFactors := filter_subset _ _
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primeFactors.mp (hSsub hp)).1
  refine Nat.factorization_inj hd0 (unitaryPart_ne_zero hSp) ?_
  ext q
  rw [factorization_unitaryPart hSp q]
  have hval : n.factorization q = d.factorization q + (n / d).factorization q := by
    conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
    exact congrArg (fun f : ℕ →₀ ℕ => f q) (Nat.factorization_mul hd0 hdiv0)
  by_cases hq : q ∈ S
  · rw [ite_eq_left hq]
    have hqne : d.factorization q ≠ 0 := (mem_filter.mp hq).2
    have hzero : (n / d).factorization q = 0 := by
      rcases (coprime_iff_factorization hd0 hdiv0).mp hcop q with h0 | h0
      · exact absurd h0 hqne
      · exact h0
    rw [hval, hzero, add_zero]
  · rw [ite_eq_right hq]
    by_contra hne
    by_cases hqpf : q ∈ n.primeFactors
    · exact hq (mem_filter.mpr ⟨hqpf, hne⟩)
    · have hle : d.factorization q ≤ n.factorization q :=
        (Nat.factorization_le_iff_dvd hd0 hn).mpr hdvd q
      rw [factorization_eq_zero_of_not_mem_primeFactors hqpf, Nat.le_zero] at hle
      exact hne hle

/-- A unit part carried by a subset of the prime factors is a unitary divisor. -/
lemma unitaryPart_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ}
    (hS : S ⊆ n.primeFactors) : unitaryPart n S ∈ unitaryDivisors n := by
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primeFactors.mp (hS hp)).1
  exact mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨unitaryPart_dvd hn hSp, hn⟩, coprime_unitaryPart_div hn hSp⟩

/-- The support of a unit part is the subset it was taken over. -/
lemma filter_factorization_unitaryPart {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ n.primeFactors) :
    n.primeFactors.filter (fun p => (unitaryPart n S).factorization p ≠ 0) = S := by
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primeFactors.mp (hS hp)).1
  ext q
  rw [mem_filter]
  constructor
  · rintro ⟨-, hq⟩
    by_contra hqS
    rw [factorization_unitaryPart hSp q, ite_eq_right hqS] at hq
    exact hq rfl
  · intro hq
    refine ⟨hS hq, ?_⟩
    rw [factorization_unitaryPart hSp q, ite_eq_left hq]
    exact factorization_ne_zero_of_mem_primeFactors (hS hq)

/-! ## The Euler-type product -/

/-- `σ*(n)` is the sum of all unit parts. -/
lemma unitarySigma_eq_sum_powerset {n : ℕ} (hn : n ≠ 0) :
    unitarySigma n = ∑ S ∈ n.primeFactors.powerset, unitaryPart n S := by
  unfold unitarySigma
  refine Finset.sum_bij (fun d _ => n.primeFactors.filter (fun p => d.factorization p ≠ 0))
    ?_ ?_ ?_ ?_
  · intro d _
    exact mem_powerset.mpr (filter_subset _ _)
  · intro d1 hd1 d2 hd2 heq
    rw [eq_unitaryPart_of_mem hn hd1, eq_unitaryPart_of_mem hn hd2, heq]
  · intro S hS
    exact ⟨unitaryPart n S, unitaryPart_mem_unitaryDivisors hn (mem_powerset.mp hS),
      filter_factorization_unitaryPart (mem_powerset.mp hS)⟩
  · intro d hd
    exact eq_unitaryPart_of_mem hn hd

/-- `σ*(n) = ∏ (1 + p ^ v_p(n))` over the prime factors. -/
lemma unitarySigma_eq_prod {n : ℕ} (hn : n ≠ 0) :
    unitarySigma n = ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [unitarySigma_eq_sum_powerset hn]
  rw [show (∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p))
      = ∏ p ∈ n.primeFactors,
          ((fun _ => (1 : ℕ)) p + (fun p => p ^ n.factorization p) p) from rfl]
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one, one_mul]
  refine Finset.sum_bij (fun t _ => n.primeFactors \ t) ?_ ?_ ?_ ?_
  · intro t _
    exact mem_powerset.mpr Finset.sdiff_subset
  · intro t1 ht1 t2 ht2 heq
    rw [← Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht1),
      ← Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht2), heq]
  · intro t ht
    exact ⟨n.primeFactors \ t, mem_powerset.mpr Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht)⟩
  · intro t ht
    rw [Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht)]
    unfold unitaryPart
    simp

/-! ## The parity argument -/

/-- A unitary perfect number has `σ*(n) = 2 n`. -/
lemma unitarySigma_eq_two_mul {n : ℕ} (hn : 0 < n) (h : IsUnitaryPerfect n) :
    unitarySigma n = 2 * n := by
  obtain ⟨hsum, -⟩ := h
  have hn0 : n ≠ 0 := hn.ne'
  have hmem : n ∈ unitaryDivisors n := by
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩, ?_⟩
    rw [Nat.div_self hn]
    exact Nat.coprime_one_right n
  have hset : properUnitaryDivisors n = (unitaryDivisors n).erase n := by
    ext d
    simp only [properUnitaryDivisors, unitaryDivisors, mem_filter, mem_Ico, mem_erase,
      Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd, hcop⟩
      exact ⟨h2.ne, ⟨hdvd, hn0⟩, hcop⟩
    · rintro ⟨hne, ⟨hdvd, -⟩, hcop⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hn, lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hne⟩,
        hdvd, hcop⟩
  calc unitarySigma n = ∑ d ∈ unitaryDivisors n, d := rfl
    _ = ∑ d ∈ (unitaryDivisors n).erase n, d + n := (Finset.sum_erase_add _ _ hmem).symm
    _ = n + n := by rw [← hset, hsum]
    _ = 2 * n := by ring

/-- For odd `n`, each factor of the Euler product is even. -/
lemma even_one_add_pow {n p : ℕ} (hn : Odd n) (hp : p ∈ n.primeFactors) :
    Even (1 + p ^ n.factorization p) := by
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
  have hpodd : Odd p := by
    rcases hpprime.eq_two_or_odd with h2 | ho
    · exfalso
      rw [h2] at hpdvd
      exact Nat.not_even_iff_odd.mpr hn (even_iff_two_dvd.mpr hpdvd)
    · exact Nat.odd_iff.mpr ho
  have hpow : Odd (p ^ n.factorization p) := hpodd.pow
  simpa [add_comm] using hpow.add_one

/-- For odd `n`, the number of prime factors is bounded by the `2`-adic valuation of
`σ*(n)`. -/
lemma card_le_factorization_two {n : ℕ} (hn : Odd n) (hn0 : n ≠ 0) :
    n.primeFactors.card ≤ (unitarySigma n).factorization 2 := by
  have hfac : ∀ p ∈ n.primeFactors, 1 ≤ (1 + p ^ n.factorization p).factorization 2 := by
    intro p hp
    have heven := even_one_add_pow hn hp
    have hpos : 0 < 1 + p ^ n.factorization p := by positivity
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos.ne']
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    exact ⟨k, by ring⟩
  rw [unitarySigma_eq_prod hn0, Nat.factorization_prod_apply]
  · calc n.primeFactors.card = ∑ _p ∈ n.primeFactors, 1 := by simp
      _ ≤ ∑ p ∈ n.primeFactors, (1 + p ^ n.factorization p).factorization 2 :=
        Finset.sum_le_sum hfac
  · intro x hx
    positivity

/-- **Erdős 1052**: a unitary perfect number is even. -/
theorem even_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  obtain ⟨hsum, hpos⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  by_contra hne
  have hodd : Odd n := Nat.not_even_iff_odd.mp hne
  have hn1 : n ≠ 1 := by
    rintro rfl
    simp [properUnitaryDivisors] at hsum
  have hcardpos : 1 ≤ n.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (lt_of_le_of_ne hpos (Ne.symm hn1)))
  have hsig : unitarySigma n = 2 * n := unitarySigma_eq_two_mul hpos ⟨hsum, hpos⟩
  have hle := card_le_factorization_two hodd hn0
  -- `σ*(n) = 2 n` is even exactly to the first power
  have hfac2 : (unitarySigma n).factorization 2 = 1 := by
    rw [hsig]
    have hmul : (2 * n).factorization = (2 : ℕ).factorization + n.factorization :=
      Nat.factorization_mul (by norm_num) hn0
    have h1 : (2 : ℕ).factorization 2 = 1 := by
      simpa using Nat.factorization_pow_self (n := 1) Nat.prime_two
    have h0 : n.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun hd => Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hd))
    rw [hmul]
    simp [Finsupp.add_apply, h1, h0]
  rw [hfac2] at hle
  have hcard1 : n.primeFactors.card = 1 := le_antisymm hle hcardpos
  obtain ⟨p, hpcard⟩ := Finset.card_eq_one.mp hcard1
  have hpmem : p ∈ n.primeFactors := hpcard ▸ Finset.mem_singleton_self p
  have hpprime : p.Prime := (Nat.mem_primeFactors.mp hpmem).1
  -- a single prime factor makes `n` a prime power
  have hn_eq : n = p ^ n.factorization p := by
    have hpt : p ^ n.factorization p ≠ 0 := pow_ne_zero _ hpprime.ne_zero
    refine Nat.factorization_inj hn0 hpt ?_
    ext q
    by_cases hq : q = p
    · subst hq
      rw [factorization_prime_pow hpprime, ite_eq_left rfl]
    · rw [factorization_prime_pow hpprime, ite_eq_right hq]
      have hqpf : q ∉ n.primeFactors := by
        rw [hpcard]
        simpa using hq
      exact factorization_eq_zero_of_not_mem_primeFactors hqpf
  have hprod := unitarySigma_eq_prod hn0
  rw [hpcard] at hprod
  simp only [Finset.prod_singleton] at hprod
  have heq : 1 + p ^ n.factorization p = 2 * (p ^ n.factorization p) := by
    have h4 : 2 * n = 2 * (p ^ n.factorization p) := by
      conv_lhs => rw [hn_eq]
    linarith
  -- `1 + p ^ a = 2 p ^ a` forces `p ^ a = 1`, which a prime power cannot be
  have hfeq : p ^ n.factorization p = 1 := by linarith
  have hfpos : 1 ≤ n.factorization p := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization hpprime hn0]
    simpa using (Nat.mem_primeFactors.mp hpmem).2.1
  have hge : 2 ≤ p ^ n.factorization p :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ p ^ 1 := Nat.pow_le_pow_left hpprime.two_le 1
      _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right hpprime.one_lt.le hfpos
  linarith

end ChenGuang.Erdos1052

/-! ## Axiom audit -/

#print axioms ChenGuang.Erdos1052.even_of_isUnitaryPerfect
