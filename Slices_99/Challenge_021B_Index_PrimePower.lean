import Slices_99.Challenge_021A_Index_Model

set_option linter.unnecessarySimpa false

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup QuotientGroup

namespace Challenge021Gamma0NIndex

/-! # Challenge_021B — 素幂局部指数（ChenGuang Studio）

本切片承载 **局部（p^k）层**：
* `1 ≠ 0` 与 `ZMod (p^k)` 非单位元计数；
* 代表元 `rep_pow` 与四条陪集互异引理（`R`/`T` 交叉、同型互异）；
* 左陪集覆盖 `leftCoset_cover_primePow`、代表元单射 `inj_rep_pow`；
* 局部指数主定理 `Gamma0_primePow_index`、`Gamma0_prime_index`。
-/

lemma one_ne_zero_zmod {p : ℕ} [Fact p.Prime] : (1 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((1 : ℤ) : ZMod p) = 0 := by simpa using h
  have hdvd : (p : ℤ) ∣ (1 : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a := (1 : ℤ)) (b := p)).mp h'
  have hnat : p ∣ (1 : ℕ) := by
    exact_mod_cast hdvd
  have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hnat
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

lemma one_ne_zero_zmod_pow {p k : ℕ} [Fact p.Prime] (hk : 0 < k) :
    (1 : ZMod (p ^ k)) ≠ 0 := by
  intro h
  have h' : ((1 : ℤ) : ZMod (p ^ k)) = 0 := by simpa using h
  have hdvd : (p ^ k : ℤ) ∣ (1 : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a := (1 : ℤ)) (b := p ^ k)).mp h'
  have hnat : p ^ k ∣ (1 : ℕ) := by
    exact_mod_cast hdvd
  have hle : p ^ k ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < (1 : ℕ)) hnat
  have hpk : p ≤ p ^ k := Nat.le_self_pow (Nat.ne_of_gt hk) p
  have hge : 2 ≤ p ^ k := le_trans (Fact.out : p.Prime).two_le hpk
  omega

lemma notUnit_iff_prime_dvd_val (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (x : ZMod (p ^ k)) :
    ¬ IsUnit x ↔ p ∣ x.val := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Nat.Prime.ne_zero hp)⟩
  have hiff := ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := k) (a := x.val) hp hk
  have hcv : (x.val : ZMod (p ^ k)) = x := ZMod.natCast_zmod_val x
  constructor
  · intro hnot
    by_contra hnd
    apply hnot
    simpa [hcv] using hiff.mpr hnd
  · intro hdvd
    intro hx
    exact (hiff.mp (by simpa [hcv] using hx)) hdvd

lemma card_notUnit_primePow (p k : ℕ) [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k) :
    Nat.card {u : ZMod (p ^ k) // ¬ IsUnit u} = p ^ (k - 1) := by
  classical
  let A := {u : ZMod (p ^ k) // ¬ IsUnit u}
  let f : A → Fin (p ^ (k - 1)) := fun u => ⟨u.1.val / p, by
    have hdvd : p ∣ u.1.val := (notUnit_iff_prime_dvd_val p k hp hk u.1).mp u.2
    have hval_lt : u.1.val < p ^ k := ZMod.val_lt u.1
    have hpk : p ^ k = p * p ^ (k - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk]
      rw [pow_succ]
      rw [mul_comm (p ^ (k - 1)) p]
    have hmul' : p * (u.1.val / p) < p * p ^ (k - 1) := by
      rw [mul_comm p (u.1.val / p)]
      rw [Nat.div_mul_cancel hdvd]
      simpa [hpk] using hval_lt
    exact (Nat.mul_lt_mul_left (Nat.Prime.pos hp)).mp hmul'⟩
  let g : Fin (p ^ (k - 1)) → A := fun j => ⟨(j.1 * p : ℕ), by
    have hlt : j.1 * p < p ^ k := by
      have hjl : j.1 < p ^ (k - 1) := j.2
      have hpk : p ^ k = p ^ (k - 1) * p := by
        conv_lhs => rw [← Nat.sub_add_cancel hk]
        rw [pow_succ]
      have : j.1 * p < p ^ (k - 1) * p := Nat.mul_lt_mul_of_pos_right hjl (Nat.Prime.pos hp)
      simpa [hpk] using this
    have hval : ((j.1 * p : ℕ) : ZMod (p ^ k)).val = j.1 * p := by
      rw [ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt hlt]
    have hdvd : p ∣ ((j.1 * p : ℕ) : ZMod (p ^ k)).val := by
      rw [hval]
      exact dvd_mul_left p j.1
    exact (notUnit_iff_prime_dvd_val p k hp hk ((j.1 * p : ℕ) : ZMod (p ^ k))).mpr hdvd⟩
  have hleft : Function.LeftInverse g f := by
    intro u
    apply Subtype.ext
    have hdvd : p ∣ u.1.val := (notUnit_iff_prime_dvd_val p k hp hk u.1).mp u.2
    have hdiv : u.1.val / p * p = u.1.val := Nat.div_mul_cancel hdvd
    change (((u.1.val / p) * p : ℕ) : ZMod (p ^ k)) = u.1
    rw [hdiv]
    exact ZMod.natCast_zmod_val u.1
  have hright : Function.RightInverse g f := by
    intro j
    apply Fin.ext
    have hlt : j.1 * p < p ^ k := by
      have hjl : j.1 < p ^ (k - 1) := j.2
      have hpk : p ^ k = p ^ (k - 1) * p := by
        conv_lhs => rw [← Nat.sub_add_cancel hk]
        rw [pow_succ]
      have : j.1 * p < p ^ (k - 1) * p := Nat.mul_lt_mul_of_pos_right hjl (Nat.Prime.pos hp)
      simpa [hpk] using this
    have hval : ((j.1 * p : ℕ) : ZMod (p ^ k)).val = j.1 * p := by
      rw [ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt hlt]
    have hdiv : (j.1 * p) / p = j.1 := by
      simpa [mul_comm] using Nat.mul_div_right j.1 (Nat.Prime.pos hp)
    change ((j.1 * p : ℕ) : ZMod (p ^ k)).val / p = j.1
    rw [hval, hdiv]
  have hbij : Function.Bijective f :=
    ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩
  have hcard' : Nat.card A = Nat.card (Fin (p ^ (k - 1))) :=
    Nat.card_congr (Equiv.ofBijective f hbij)
  have hfin : Nat.card (Fin (p ^ (k - 1))) = p ^ (k - 1) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_fin (p ^ (k - 1))
  simpa [A] using hcard'.trans hfin

def rep_pow (p k : ℕ) [NeZero (p ^ k)] :
    (ZMod (p ^ k) ⊕ {u : ZMod (p ^ k) // ¬ IsUnit u}) → SL(2, ℤ)
  | Sum.inl t => R t.val
  | Sum.inr u => T u.1.val

lemma R_not_mem_gamma0_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) (t : ℕ)
    (h : R t ∈ gamma0_N (p ^ k)) : False := by
  rw [gamma0_N_mem_iff] at h
  have h1 : (R t : SL(2, ℤ)).1 1 0 = (1 : ℤ) := by
    simp [R]
  rw [h1] at h
  exact one_ne_zero_zmod_pow hk (by simpa using h)

lemma R_coset_ne_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) {c d : ZMod (p ^ k)}
    (hcd : c ≠ d) :
    ((R c.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k)) ≠ (R d.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k))) := by
  intro hq
  have hmem : (R c.val)⁻¹ * R d.val ∈ gamma0_N (p ^ k) := QuotientGroup.eq.mp hq
  rw [gamma0_N_mem_iff] at hmem
  rw [Matrix.SpecialLinearGroup.coe_mul] at hmem
  rw [Matrix.SpecialLinearGroup.coe_inv] at hmem
  rw [show ((R c.val).1).adjugate = !![0, 1; -1, (c.val : ℤ)] by
    change (!![(c.val : ℤ), -1; 1, 0]).adjugate = !![0, 1; -1, (c.val : ℤ)]
    rw [Matrix.adjugate_fin_two_of]
    rfl] at hmem
  rw [show (R d.val).1 = !![(d.val : ℤ), -1; 1, 0] by rfl] at hmem
  rw [Matrix.mul_apply] at hmem
  rw [Fin.sum_univ_two] at hmem
  simp at hmem
  have hz : c = d := by
    have hsub : c - d = 0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmem
    exact sub_eq_zero.mp hsub
  exact hcd hz

lemma R_coset_ne_one_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) (c : ZMod (p ^ k)) :
    ((R c.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k)) ≠
      (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ gamma0_N (p ^ k))) := by
  intro hq
  have hmem : (R c.val)⁻¹ * (1 : SL(2, ℤ)) ∈ gamma0_N (p ^ k) := QuotientGroup.eq.mp hq
  have hmem' : R c.val ∈ gamma0_N (p ^ k) := (gamma0_N (p ^ k)).inv_mem_iff.mp (by simpa using hmem)
  exact R_not_mem_gamma0_pow p k hk c.val hmem'

lemma T_coset_ne_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) {u v : ZMod (p ^ k)}
    (huv : u ≠ v) :
    ((T u.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k)) ≠ (T v.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k))) := by
  intro hq
  have hmem : (T u.val)⁻¹ * T v.val ∈ gamma0_N (p ^ k) := QuotientGroup.eq.mp hq
  rw [gamma0_N_mem_iff] at hmem
  rw [Matrix.SpecialLinearGroup.coe_mul] at hmem
  rw [Matrix.SpecialLinearGroup.coe_inv] at hmem
  rw [show ((T u.val).1).adjugate = !![1, 0; -(u.val : ℤ), 1] by
    change (!![1, 0; (u.val : ℤ), 1]).adjugate = !![1, 0; -(u.val : ℤ), 1]
    rw [Matrix.adjugate_fin_two_of]
    rfl] at hmem
  rw [show (T v.val).1 = !![1, 0; (v.val : ℤ), 1] by rfl] at hmem
  rw [Matrix.mul_apply] at hmem
  rw [Fin.sum_univ_two] at hmem
  simp at hmem
  have hsub : (v.val : ZMod (p ^ k)) - (u.val : ZMod (p ^ k)) = 0 := by
    simpa [sub_eq_add_neg, add_comm] using hmem
  have hcv : (u.val : ZMod (p ^ k)) = u := ZMod.natCast_zmod_val u
  have hdv : (v.val : ZMod (p ^ k)) = v := ZMod.natCast_zmod_val v
  have hz : u = v := by
    rw [hcv, hdv] at hsub
    exact (sub_eq_zero.mp hsub).symm
  exact huv hz

lemma R_coset_ne_T_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) (t : ZMod (p ^ k))
    {u : ZMod (p ^ k)} (hu : ¬ IsUnit u) :
    ((R t.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k)) ≠
      (T u.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k))) := by
  intro hq
  have hmem : (R t.val)⁻¹ * T u.val ∈ gamma0_N (p ^ k) := QuotientGroup.eq.mp hq
  rw [gamma0_N_mem_iff] at hmem
  rw [Matrix.SpecialLinearGroup.coe_mul] at hmem
  rw [Matrix.SpecialLinearGroup.coe_inv] at hmem
  rw [show ((R t.val).1).adjugate = !![0, 1; -1, (t.val : ℤ)] by
    change (!![(t.val : ℤ), -1; 1, 0]).adjugate = !![0, 1; -1, (t.val : ℤ)]
    rw [Matrix.adjugate_fin_two_of]
    rfl] at hmem
  rw [show (T u.val).1 = !![1, 0; (u.val : ℤ), 1] by rfl] at hmem
  rw [Matrix.mul_apply] at hmem
  rw [Fin.sum_univ_two] at hmem
  simp at hmem
  have ht : t * u = 1 := by
    have ht0 : t * u - 1 = 0 := by
      simpa [sub_eq_add_neg, add_comm] using hmem
    exact sub_eq_zero.mp ht0
  have hu_unit : IsUnit u := by
    refine ⟨⟨u, t, ?_, ?_⟩, rfl⟩
    · rw [mul_comm, ht]
    · exact ht
  exact hu hu_unit

lemma T_coset_ne_R_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k)
    {u : ZMod (p ^ k)} (hu : ¬ IsUnit u) (t : ZMod (p ^ k)) :
    ((T u.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k)) ≠
      (R t.val : SL(2, ℤ) ⧸ gamma0_N (p ^ k))) := by
  intro hq
  exact R_coset_ne_T_pow p k hk t hu hq.symm

lemma leftCoset_cover_primePow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) (g : SL(2, ℤ)) :
    ∃ i : (ZMod (p ^ k) ⊕ {u : ZMod (p ^ k) // ¬ IsUnit u}),
      (rep_pow p k i)⁻¹ * g ∈ gamma0_N (p ^ k) := by
  classical
  let a : ZMod (p ^ k) := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let c : ZMod (p ^ k) := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  by_cases hc : IsUnit c
  · let cbar : ZMod (p ^ k) := a * c⁻¹
    refine ⟨Sum.inl cbar, ?_⟩
    rw [gamma0_N_mem_iff]
    rw [show rep_pow p k (Sum.inl cbar) = R cbar.val by rfl]
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [R_inv_mul_g_10]
    rw [Int.cast_sub, Int.cast_mul]
    norm_num
    have hmul : cbar * c = a := by
      dsimp [cbar]
      rw [mul_assoc]
      rw [ZMod.inv_mul_of_unit c hc]
      rw [mul_one]
    have hg10 : (g 1 0 : ZMod (p ^ k)) = c := rfl
    have hg00 : (g 0 0 : ZMod (p ^ k)) = a := rfl
    rw [hg10, hg00]
    rw [← hmul]
    ring
  · have hcvd : p ∣ c.val := by
      exact (notUnit_iff_prime_dvd_val p k (Fact.out : p.Prime) hk c).mp hc
    have ha_nd : ¬ p ∣ a.val := by
      intro hpa
      have hdvd_p_pk : (p : ℤ) ∣ (p ^ k : ℤ) := by
        exact_mod_cast (dvd_pow (dvd_refl p) (Nat.ne_of_gt hk))
      have hg10 : (p : ℤ) ∣ (g 1 0 : ℤ) := by
        have hcong : (g 1 0 : ZMod (p ^ k)) = (c.val : ZMod (p ^ k)) := by
          dsimp [c]
          rw [ZMod.natCast_zmod_val]
        have hdiff : (↑((g 1 0 : ℤ) - (c.val : ℤ)) : ZMod (p ^ k)) = 0 := by
          rw [Int.cast_sub]
          rw [sub_eq_zero]
          simpa using hcong
        have hdvd_pk : (p ^ k : ℤ) ∣ (g 1 0 - (c.val : ℤ)) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (a := (g 1 0 : ℤ) - (c.val : ℤ)) (b := p ^ k)).mp hdiff
        have hdvd_p_diff : (p : ℤ) ∣ (g 1 0 - (c.val : ℤ)) := dvd_trans hdvd_p_pk hdvd_pk
        have hcval_z : (p : ℤ) ∣ (c.val : ℤ) := by exact_mod_cast hcvd
        have : (p : ℤ) ∣ ((g 1 0 - (c.val : ℤ)) + (c.val : ℤ)) := dvd_add hdvd_p_diff hcval_z
        simpa [sub_eq_add_neg, add_assoc] using this
      have hg00 : (p : ℤ) ∣ (g 0 0 : ℤ) := by
        have hcong : (g 0 0 : ZMod (p ^ k)) = (a.val : ZMod (p ^ k)) := by
          dsimp [a]
          rw [ZMod.natCast_zmod_val]
        have hdiff : (↑((g 0 0 : ℤ) - (a.val : ℤ)) : ZMod (p ^ k)) = 0 := by
          rw [Int.cast_sub]
          rw [sub_eq_zero]
          simpa using hcong
        have hdvd_pk : (p ^ k : ℤ) ∣ (g 0 0 - (a.val : ℤ)) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (a := (g 0 0 : ℤ) - (a.val : ℤ)) (b := p ^ k)).mp hdiff
        have hdvd_p_diff : (p : ℤ) ∣ (g 0 0 - (a.val : ℤ)) := dvd_trans hdvd_p_pk hdvd_pk
        have hpa_z : (p : ℤ) ∣ (a.val : ℤ) := by exact_mod_cast hpa
        have : (p : ℤ) ∣ ((g 0 0 - (a.val : ℤ)) + (a.val : ℤ)) := dvd_add hdvd_p_diff hpa_z
        simpa [sub_eq_add_neg, add_assoc] using this
      have hdet_mod : ((g 0 0 : ℤ) * (g 1 1) - (g 0 1) * (g 1 0) : ZMod p) = 1 := by
        have hdet : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.property
        rw [Matrix.det_fin_two] at hdet
        simpa [Int.cast_sub, Int.cast_mul] using congrArg (fun x : ℤ => (x : ZMod p)) hdet
      have hzero : ((g 0 0 : ℤ) * (g 1 1) - (g 0 1) * (g 1 0) : ZMod p) = 0 := by
        have hg00z : (g 0 0 : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (a := (g 0 0 : ℤ)) (b := p)).mpr hg00
        have hg10z : (g 1 0 : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (a := (g 1 0 : ℤ)) (b := p)).mpr hg10
        simp [hg00z, hg10z]
      have hone : (1 : ZMod p) = 0 := by
        simpa [hzero] using hdet_mod.symm
      exact one_ne_zero_zmod (p := p) hone
    have ha_unit : IsUnit a := by
      have hiff := ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := k) (a := a.val)
        (Fact.out : p.Prime) hk
      have hav : (a.val : ZMod (p ^ k)) = a := ZMod.natCast_zmod_val a
      rw [← hav]
      exact hiff.mpr ha_nd
    let u : ZMod (p ^ k) := c * a⁻¹
    have hu_not : ¬ IsUnit u := by
      intro hu
      have hua : u * a = c := by
        dsimp [u]
        rw [mul_assoc]
        rw [ZMod.inv_mul_of_unit a ha_unit]
        rw [mul_one]
      have hc_unit : IsUnit c := by
        rw [← hua]
        exact hu.mul ha_unit
      exact hc hc_unit
    refine ⟨Sum.inr ⟨u, hu_not⟩, ?_⟩
    rw [gamma0_N_mem_iff]
    rw [show rep_pow p k (Sum.inr ⟨u, hu_not⟩) = T u.val by rfl]
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [T_inv_mul_g_10]
    rw [Int.cast_sub, Int.cast_mul]
    norm_num
    have hg10 : (g 1 0 : ZMod (p ^ k)) = c := rfl
    have hg00 : (g 0 0 : ZMod (p ^ k)) = a := rfl
    have hua : u * a = c := by
      dsimp [u]
      rw [mul_assoc]
      rw [ZMod.inv_mul_of_unit a ha_unit]
      rw [mul_one]
    rw [hg10, hg00]
    rw [← hua]
    ring

lemma inj_rep_pow (p k : ℕ) [Fact p.Prime] (hk : 0 < k)
    (i j : ZMod (p ^ k) ⊕ {u : ZMod (p ^ k) // ¬ IsUnit u}) (h : i ≠ j) :
    ((rep_pow p k i : SL(2, ℤ) ⧸ gamma0_N (p ^ k)) ≠
      (rep_pow p k j : SL(2, ℤ) ⧸ gamma0_N (p ^ k))) := by
  intro hq
  cases i with
  | inl t =>
    cases j with
    | inl d =>
      have htd : t ≠ d := by
        intro ht
        exact h (by simp [ht])
      exact R_coset_ne_pow p k hk htd (by simpa [rep_pow] using hq)
    | inr u =>
      exact R_coset_ne_T_pow p k hk t u.2 (by simpa [rep_pow] using hq)
  | inr u =>
    cases j with
    | inl d =>
      exact T_coset_ne_R_pow p k hk u.2 d (by simpa [rep_pow] using hq)
    | inr v =>
      have huv : u.1 ≠ v.1 := by
        intro hx
        exact h (by
          simpa using congrArg (Sum.inr (α := ZMod (p ^ k)) (β := {u : ZMod (p ^ k) // ¬ IsUnit u})) (Subtype.ext hx))
      exact T_coset_ne_pow p k hk huv (by simpa [rep_pow] using hq)

theorem Gamma0_primePow_index (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (gamma0_N (p ^ k)).index = p ^ k + p ^ (k - 1) := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Nat.Prime.ne_zero (Fact.out : p.Prime))⟩
  let H : Subgroup (SL(2, ℤ)) := gamma0_N (p ^ k)
  let Q := SL(2, ℤ) ⧸ H
  let Rtyp := ZMod (p ^ k) ⊕ {u : ZMod (p ^ k) // ¬ IsUnit u}
  have surj : Function.Surjective (fun i : Rtyp => (rep_pow p k i : Q)) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    rcases leftCoset_cover_primePow p k hk g with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply QuotientGroup.eq.mpr
    exact hi
  have inj : Function.Injective (fun i : Rtyp => (rep_pow p k i : Q)) := by
    intro i j hij
    by_contra hne
    exact inj_rep_pow p k hk i j hne hij
  have hcard : Nat.card Q = p ^ k + p ^ (k - 1) := by
    let e : Rtyp ≃ Q := Equiv.ofBijective (fun i : Rtyp => (rep_pow p k i : Q)) ⟨inj, surj⟩
    have hnat : Nat.card Q = Nat.card Rtyp := Nat.card_congr e.symm
    have hsum : Nat.card Rtyp =
        Nat.card (ZMod (p ^ k)) + Nat.card {u : ZMod (p ^ k) // ¬ IsUnit u} := by
      dsimp [Rtyp]
      rw [Nat.card_sum]
    have hp : Nat.card (ZMod (p ^ k)) = p ^ k := by
      rw [Nat.card_eq_fintype_card]
      exact ZMod.card (p ^ k)
    have hnot : Nat.card {u : ZMod (p ^ k) // ¬ IsUnit u} = p ^ (k - 1) :=
      card_notUnit_primePow p k (Fact.out : p.Prime) hk
    calc
      Nat.card Q = Nat.card Rtyp := hnat
      _ = Nat.card (ZMod (p ^ k)) + Nat.card {u : ZMod (p ^ k) // ¬ IsUnit u} := hsum
      _ = p ^ k + Nat.card {u : ZMod (p ^ k) // ¬ IsUnit u} := by rw [hp]
      _ = p ^ k + p ^ (k - 1) := by rw [hnot]
  calc
    (gamma0_N (p ^ k)).index = Nat.card (SL(2, ℤ) ⧸ gamma0_N (p ^ k)) :=
      Subgroup.index_eq_card (H := gamma0_N (p ^ k))
    _ = p ^ k + p ^ (k - 1) := by
      simpa [Q, H] using hcard

theorem Gamma0_prime_index (p : ℕ) [Fact p.Prime] :
    (gamma0_N p).index = p + 1 := by
  have h := Gamma0_primePow_index (p := p) (k := 1) (hk := by norm_num)
  simpa [pow_one, pow_zero] using h


end Challenge021Gamma0NIndex
