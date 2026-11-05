import Slices_99.Challenge_021A_Index_Model
import Slices_99.Challenge_021B_Index_PrimePower

set_option linter.unnecessarySimpa false

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup QuotientGroup

namespace Challenge021Gamma0NIndex

/-! # Challenge_021C — 全局指数主定理（ChenGuang Studio）

本切片承载 **全局装配**：
* 平凡层 `gamma0_N_one_top`、`P1_card_one`；
* 基数乘性 `P1_card_mul`、素幂基数 `P1_card_primePow`、乘积基数 `P1_card_prod_pow`；
* 主结论 `P1_card` 与 **`Gamma0N_index_eq`（Γ₀(N) 指数 = ∏(p^{v_p(N)-1}(p+1))）**。
-/

lemma gamma0_N_one_top : gamma0_N 1 = ⊤ := by
  ext g
  rw [gamma0_N_mem_iff]
  constructor
  · intro _; trivial
  · intro _; exact Subsingleton.elim _ _

lemma P1_card_one : Nat.card (P1 1) = 1 := by
  haveI : NeZero 1 := ⟨by norm_num⟩
  calc
    Nat.card (P1 1) = Nat.card (SL(2, ℤ) ⧸ gamma0_N 1) :=
      (Nat.card_congr (gamma0_coset_equiv_P1 1)).symm
    _ = (gamma0_N 1).index := (Subgroup.index_eq_card (H := gamma0_N 1)).symm
    _ = 1 := by
      rw [gamma0_N_one_top]
      simp

lemma P1_card_mul (m n : ℕ) (h : m.Coprime n) :
    Nat.card (P1 (m * n)) = Nat.card (P1 m) * Nat.card (P1 n) := by
  calc
    Nat.card (P1 (m * n)) = Nat.card (P1 m × P1 n) := Nat.card_congr (P1_mul_equiv_prod m n h)
    _ = Nat.card (P1 m) * Nat.card (P1 n) := Nat.card_prod (α := P1 m) (β := P1 n)

lemma P1_card_primePow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    Nat.card (P1 (p ^ k)) = p ^ (k - 1) * (p + 1) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Nat.Prime.ne_zero (Fact.out : p.Prime))⟩
  calc
    Nat.card (P1 (p ^ k)) = Nat.card (SL(2, ℤ) ⧸ gamma0_N (p ^ k)) :=
      (Nat.card_congr (gamma0_coset_equiv_P1 (p ^ k))).symm
    _ = (gamma0_N (p ^ k)).index := (Subgroup.index_eq_card (H := gamma0_N (p ^ k))).symm
    _ = p ^ k + p ^ (k - 1) := Gamma0_primePow_index p k hk
    _ = p ^ (k - 1) * (p + 1) := by
      have hpow : p ^ k = p ^ (k - 1) * p := by
        simpa [Nat.sub_add_cancel hk] using pow_succ p (k - 1)
      rw [hpow]
      rw [mul_add]
      rw [mul_one]

lemma P1_card_prod_pow (s : Finset ℕ) (k : ℕ → ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Nat.card (P1 (s.prod (fun p => p ^ k p))) =
      s.prod (fun p => Nat.card (P1 (p ^ k p))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
    exact P1_card_one
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha]
    rw [Finset.prod_insert ha]
    have hpa : a.Prime := hs a (Finset.mem_insert_self a s')
    have hcop : a.Coprime (s'.prod (fun p => p ^ k p)) := by
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      by_cases hk0 : k p = 0
      · simp [hk0]
      · rw [Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hk0) a p]
        apply (Nat.Prime.coprime_iff_not_dvd hpa).2
        intro hd
        have hap_eq : p = a :=
          (Nat.Prime.dvd_iff_eq (hs p (Finset.mem_insert_of_mem hp)) (Nat.Prime.ne_one hpa)).mp hd
        exact ha (by simpa [hap_eq] using hp)
    have hcopk : (a ^ k a).Coprime (s'.prod (fun p => p ^ k p)) := by
      by_cases hka : k a = 0
      · simp [hka]
      · rw [Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hka) a (s'.prod (fun p => p ^ k p))]
        exact hcop
    rw [P1_card_mul (a ^ k a) (s'.prod (fun p => p ^ k p)) hcopk]
    rw [ih (by intro p hp; exact hs p (Finset.mem_insert_of_mem hp))]

theorem P1_card (N : ℕ) [NeZero N] :
    Nat.card (P1 N) = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) * (p + 1)) := by
  classical
  have hN : N ≠ 0 := (inferInstance : NeZero N).ne
  calc
    Nat.card (P1 N) = Nat.card (P1 (N.primeFactors.prod (fun p => p ^ N.factorization p))) := by
      nth_rewrite 1 [Nat.prod_primeFactors_pow_factorization hN]
      rfl
    _ = N.primeFactors.prod (fun p => Nat.card (P1 (p ^ N.factorization p))) := by
      exact P1_card_prod_pow N.primeFactors N.factorization
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
    _ = N.primeFactors.prod (fun p => (p ^ (N.factorization p - 1) * (p + 1))) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp_mem : Nat.Prime p ∧ p ∣ N ∧ N ≠ 0 := Nat.mem_primeFactors.mp hp
      have hk : 0 < N.factorization p := by
        by_contra hle
        have hz : N.factorization p = 0 := Nat.eq_zero_of_not_pos hle
        have hnot : ¬ Nat.Prime p ∨ ¬ p ∣ N ∨ N = 0 := (Nat.factorization_eq_zero_iff N p).1 hz
        rcases hp_mem with ⟨hprime, hdvd, hN0⟩
        rcases hnot with hnp | hnd | hNN
        · exact hnp hprime
        · exact hnd hdvd
        · exact hN0 hNN
      haveI : Fact p.Prime := ⟨hp_mem.1⟩
      exact P1_card_primePow p (N.factorization p) hk

theorem Gamma0N_index_eq (N : ℕ) [NeZero N] :
    (gamma0_N N).index = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) * (p + 1)) := by
  calc
    (gamma0_N N).index = Nat.card (SL(2, ℤ) ⧸ gamma0_N N) :=
      Subgroup.index_eq_card (H := gamma0_N N)
    _ = Nat.card (P1 N) := Nat.card_congr (gamma0_coset_equiv_P1 N)
    _ = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) * (p + 1)) := P1_card N

end Challenge021Gamma0NIndex
