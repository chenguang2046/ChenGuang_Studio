import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement

/-!
# Sylow's First Theorem: Formal Verification Slices

This file formalizes, in Lean 4 against mathlib, the first Sylow theorem for a finite
group `G` and a prime `p`:

* `sylow_first_exists_sylow_subgroup` : a Sylow `p`-subgroup of `G` exists
  (wrapped from mathlib `Sylow.nonempty`).
* `sylow_first_exists_subgroup_card_pow` : if `p ^ n` divides `|G|`, then `G` admits a
  subgroup of order `p ^ n` (wrapped from mathlib `Sylow.exists_subgroup_card_pow_prime`).
* `sylow_first_exists_prime_order_subgroup` : the task-core instance `n = 1`; if `p`
  divides `|G|`, then `G` admits a subgroup of order `p`.
* `sylow_subgroup_card` : the order of any Sylow `p`-subgroup is `p ^ v_p(|G|)`
  (wrapped from mathlib `Sylow.card_eq_multiplicity`).
* `sylow_first_exists_prime_order_element` : Cauchy-type corollary; if `p` divides
  `|G|`, then `G` contains an element of order `p`.

All statements are direct wrappers of mathlib theorems or short derived corollaries;
there are no `sorry`, no `admit`, and no invented lemmas.
-/

open scoped BigOperators

namespace Challenge012

section SylowFirst

variable {G : Type*} [Group G]

/-- Slice 1. Sylow's first theorem (existence). Every group admits a Sylow `p`-subgroup;
    wrapped from mathlib `Sylow.nonempty`. -/
theorem sylow_first_exists_sylow_subgroup (p : ℕ) : Nonempty (Sylow p G) :=
  Sylow.nonempty

/-- Slice 2. Sylow's first theorem (prime-power form). If `p ^ n ∣ |G|`, then `G` has a
    subgroup of order `p ^ n`; wrapped from mathlib `Sylow.exists_subgroup_card_pow_prime`. -/
theorem sylow_first_exists_subgroup_card_pow [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd

/-- Slice 3 (task core). If the prime `p` divides `|G|`, then `G` admits a subgroup of
    order `p` (the `n = 1` instance of Slice 2). -/
theorem sylow_first_exists_prime_order_subgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (hdvd : p ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p := by
  have hdvd' : p ^ 1 ∣ Nat.card G := by simpa using hdvd
  simpa using (sylow_first_exists_subgroup_card_pow p (n := 1) hdvd')

/-- Slice 4. The order of any Sylow `p`-subgroup of a finite group is
    `p ^ v_p(|G|)`; wrapped from mathlib `Sylow.card_eq_multiplicity`. -/
theorem sylow_subgroup_card [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    Nat.card P = p ^ Nat.factorization (Nat.card G) p :=
  P.card_eq_multiplicity

/-- Slice 5 (corollary). If the prime `p` divides `|G|`, then `G` contains an element
    of order `p` (a Cauchy-type consequence of the first Sylow theorem). -/
theorem sylow_first_exists_prime_order_element [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hdvd : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := by
  obtain ⟨K, hK⟩ := sylow_first_exists_prime_order_subgroup hdvd
  have hKlt : 1 < Nat.card K := by
    rw [hK]
    exact hp.out.one_lt
  haveI : Fintype K := Fintype.ofFinite K
  have hKlt' : 1 < Fintype.card K := by simpa [Nat.card_eq_fintype_card] using hKlt
  obtain ⟨b, hb1⟩ := Fintype.exists_ne_of_one_lt_card hKlt' (1 : K)
  refine ⟨(b : G), ?_⟩
  apply orderOf_eq_prime
  · have hxpowK : (b : K) ^ Nat.card K = 1 := pow_card_eq_one' (G := K) (x := b)
    have hxpowG : (b : G) ^ Nat.card K = 1 := by
      exact_mod_cast hxpowK
    rwa [hK] at hxpowG
  · exact_mod_cast hb1

end SylowFirst

end Challenge012

#print axioms Challenge012.sylow_first_exists_sylow_subgroup
#print axioms Challenge012.sylow_first_exists_subgroup_card_pow
#print axioms Challenge012.sylow_first_exists_prime_order_subgroup
#print axioms Challenge012.sylow_subgroup_card
#print axioms Challenge012.sylow_first_exists_prime_order_element
