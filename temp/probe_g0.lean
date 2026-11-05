/-
Gamma0(4) has index 6 in SL(2, Z) -- minimal-dependency rebuild
================================================================

Re-formalization of the statement `[SL(2,Z) : Γ₀(4)] = 6` WITHOUT depending on
the modular-forms library (`Mathlib.NumberTheory.ModularForms`).  The subgroup
Γ₀(4) is defined by hand as the stabilizer of the congruence condition

    (g : Matrix (Fin 2) (Fin 2) Z) 1 0 ≡ 0 (mod 4)

and its Subgroup structure (one, mul, inv) is proved directly.  Only the base
infrastructure of Mathlib is used: matrices, SL(2,Z), ZMod 4, quotients and
finite cardinalities.

The proof strategy is the same as in `Gamma0Index_Fixed.lean`:
give 6 explicit left-coset representatives, prove they cover SL(2,Z) and are
pairwise in distinct cosets, then conclude the index equals 6 via
`Subgroup.index_eq_card`.

A pure `Init` version is impossible: the statement "index = 6" needs
`Fintype` / `Nat.card`, which exist only in Mathlib, not in the core
library.  This is an honest infra-gap, recorded here.
-/
import Mathlib

open scoped MatrixGroups
open Matrix Matrix.SpecialLinearGroup QuotientGroup

namespace Gamma0Minimal

/-- SL-inverse's (1,0) entry is the negation of the (1,0) entry, mod 4.
SL's `Inv` is defined directly via `adjugate`, so no matrix-inverse API
round-trip is needed. -/
lemma inv_10_zmod (a : SL(2, ℤ)) :
    (((a⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 4) =
      - (a.1 1 0 : ZMod 4) := by
  change ((Matrix.adjugate (a.1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) =
    -(a.1 1 0 : ZMod 4)
  rw [Matrix.adjugate_fin_two]
  simp

/-- Γ₀(4) = { g ∈ SL(2,ℤ) | g 1 0 ≡ 0 (mod 4) }, hand-rolled subgroup. -/
def gamma0_4 : Subgroup (SL(2, ℤ)) where
  carrier := {g : SL(2, ℤ) | ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 4) = 0}
  one_mem' := by
    norm_num
  mul_mem' := by
    intro a b ha hb
    change (((a * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 4) = 0
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_two]
    have ha' : ((a : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 4) = 0 := by simpa using ha
    have hb' : ((b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 4) = 0 := by simpa using hb
    simp [ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : ((a : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 4) = 0 := ha
    change (((a⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 4) = 0
    rw [inv_10_zmod a]
    simpa using ha'

/-- Membership criterion for Γ₀(4), the hand-rolled analogue of
`CongruenceSubgroup.Gamma0_mem`. -/
lemma gamma0_4_mem_iff (g : SL(2, ℤ)) :
    g ∈ gamma0_4 ↔ ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod 4) = 0 :=
  Iff.rfl

/-- Six explicit left-coset representatives:
r₀ = 1, r₁ = S, r₂..r₅ as below. -/
def r2 : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by norm_num [Matrix.det_fin_two]⟩
def r3 : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by norm_num [Matrix.det_fin_two]⟩
def r4 : SL(2, ℤ) := ⟨!![1, 0; 3, 1], by norm_num [Matrix.det_fin_two]⟩
def r5 : SL(2, ℤ) := ⟨!![2, 1; 1, 1], by norm_num [Matrix.det_fin_two]⟩

def rep : Fin 6 → SL(2, ℤ)
  | 0 => 1
  | 1 => ModularGroup.S
  | 2 => r2
  | 3 => r3
  | 4 => r4
  | 5 => r5

/-! Mod-4 enumeration helpers -/

lemma zmod4_cases (x : ℤ) : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by
  have hge : 0 ≤ x % 4 := Int.emod_nonneg x (by norm_num : (4 : ℤ) ≠ 0)
  have hlt : x % 4 < 4 := Int.emod_lt x (by norm_num : (4 : ℤ) ≠ 0)
  omega

lemma zmod_zero_of_emod {x : ℤ} (h : x % 4 = 0) : (x : ZMod 4) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rwa [Int.dvd_iff_emod_eq_zero]

lemma zmod_of_emod {x k : ℤ} (h : x % 4 = k % 4) : (x : ZMod 4) = (k : ZMod 4) := by
  rwa [ZMod.intCast_eq_intCast_iff']

lemma zmod4_enum (x : ZMod 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hx : x = (x.val : ZMod 4) := (ZMod.natCast_zmod_val (n := 4) x).symm
  have hlt : x.val < 4 := x.val_lt
  have hcase : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 := by omega
  rcases hcase with h0 | h1 | h2 | h3
  · exact Or.inl (hx.trans (by rw [h0]; rfl))
  · exact Or.inr (Or.inl (hx.trans (by rw [h1]; rfl)))
  · exact Or.inr (Or.inr (Or.inl (hx.trans (by rw [h2]; rfl))))
  · exact Or.inr (Or.inr (Or.inr (hx.trans (by rw [h3]; rfl))))

/-! Matrix products: the (1,0) entry of `(rep i)⁻¹ * g` mod 4 -/

lemma S_inv_val : ((ModularGroup.S⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [ModularGroup.coe_S, Matrix.adjugate_fin_two_of]

lemma r2_inv_val : ((r2⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [r2, Matrix.adjugate_fin_two_of]

lemma r3_inv_val : ((r3⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -2, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [r3, Matrix.adjugate_fin_two_of]

lemma r4_inv_val : ((r4⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -3, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [r4, Matrix.adjugate_fin_two_of]

lemma r5_inv_val : ((r5⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; -1, 2] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [r5, Matrix.adjugate_fin_two_of]

lemma one_mul_g_10 (g : SL(2, ℤ)) :
    (((1⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  simp

lemma S_inv_mul_g_10 (g : SL(2, ℤ)) :
    (((ModularGroup.S⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = -(g 0 0 : ℤ) := by
  rw [Matrix.mul_apply]
  rw [S_inv_val]
  norm_num [Fin.sum_univ_two]

lemma r2_inv_mul_g_10 (g : SL(2, ℤ)) :
    (((r2⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = -(g 0 0 : ℤ) + (g 1 0 : ℤ) := by
  rw [Matrix.mul_apply]
  rw [r2_inv_val]
  norm_num [Fin.sum_univ_two]

lemma r3_inv_mul_g_10 (g : SL(2, ℤ)) :
    (((r3⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = -2 * (g 0 0 : ℤ) + (g 1 0 : ℤ) := by
  rw [Matrix.mul_apply]
  rw [r3_inv_val]
  norm_num [Fin.sum_univ_two]

lemma r4_inv_mul_g_10 (g : SL(2, ℤ)) :
    (((r4⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = -3 * (g 0 0 : ℤ) + (g 1 0 : ℤ) := by
  rw [Matrix.mul_apply]
  rw [r4_inv_val]
  norm_num [Fin.sum_univ_two]

lemma r5_inv_mul_g_10 (g : SL(2, ℤ)) :
    (((r5⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = -(g 0 0 : ℤ) + 2 * (g 1 0 : ℤ) := by
  rw [Matrix.mul_apply]
  rw [r5_inv_val]
  norm_num [Fin.sum_univ_two]

lemma zmod4_two_mul_ne_one (x : ZMod 4) : (2 : ZMod 4) * x ≠ 1 := by
  rcases zmod4_enum x with hx0 | hx1 | hx2 | hx3
  · rw [hx0]; decide
  · rw [hx1]; decide
  · rw [hx2]; decide
  · rw [hx3]; decide

/-! Surjectivity: every first column (a,c) mod 4 falls into one of the 6
primitive classes. -/

lemma leftCoset_cover (g : SL(2, ℤ)) :
    ∃ i : Fin 6, (rep i)⁻¹ * g ∈ gamma0_4 := by
  classical
  rcases zmod4_cases (g 1 0) with hc0 | hc1 | hc2 | hc3
  · have hc : (g 1 0 : ZMod 4) = 0 := zmod_zero_of_emod hc0
    refine ⟨0, ?_⟩
    rw [gamma0_4_mem_iff]
    change ((((1⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
    rw [one_mul_g_10]
    exact hc
  · have hc : (g 1 0 : ZMod 4) = (1 : ZMod 4) := zmod_of_emod (k := 1) (by simpa using hc1)
    rcases zmod4_cases (g 0 0) with ha0 | ha1 | ha2 | ha3
    · have ha : (g 0 0 : ZMod 4) = 0 := zmod_zero_of_emod ha0
      refine ⟨1, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((ModularGroup.S⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [S_inv_mul_g_10]
      simp [ha]
    · have ha : (g 0 0 : ZMod 4) = (1 : ZMod 4) := zmod_of_emod (k := 1) (by simpa using ha1)
      refine ⟨2, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((r2⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [r2_inv_mul_g_10]
      simp [ha, hc]
    · have ha : (g 0 0 : ZMod 4) = (2 : ZMod 4) := zmod_of_emod (k := 2) (by simpa using ha2)
      refine ⟨5, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((r5⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [r5_inv_mul_g_10]
      simp [ha, hc]
    · have ha : (g 0 0 : ZMod 4) = (3 : ZMod 4) := zmod_of_emod (k := 3) (by simpa using ha3)
      refine ⟨4, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((r4⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [r4_inv_mul_g_10]
      simp [ha, hc]; decide
  · have hc : (g 1 0 : ZMod 4) = (2 : ZMod 4) := zmod_of_emod (k := 2) (by simpa using hc2)
    rcases zmod4_cases (g 0 0) with ha0 | ha1 | ha2 | ha3
    · have ha : (g 0 0 : ZMod 4) = 0 := zmod_zero_of_emod ha0
      exfalso
      have hd : (g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) = 1 := by
        rw [← Matrix.det_fin_two]
        exact (g : SL(2, ℤ)).2
      have hd' : (((g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) : ℤ) : ZMod 4) = (1 : ZMod 4) := by
        rw [hd]; rfl
      simp [ha, hc] at hd'
      have htwo : (2 : ZMod 4) * (g 0 1 : ZMod 4) = 1 := by
        rw [← (show (-2 : ZMod 4) = 2 by decide)]
        ring_nf at hd' ⊢
        exact hd'
      exact zmod4_two_mul_ne_one (g 0 1 : ZMod 4) htwo
    · have ha : (g 0 0 : ZMod 4) = (1 : ZMod 4) := zmod_of_emod (k := 1) (by simpa using ha1)
      refine ⟨3, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((r3⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [r3_inv_mul_g_10]
      simp [ha, hc]
    · have ha : (g 0 0 : ZMod 4) = (2 : ZMod 4) := zmod_of_emod (k := 2) (by simpa using ha2)
      exfalso
      have hd : (g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) = 1 := by
        rw [← Matrix.det_fin_two]
        exact (g : SL(2, ℤ)).2
      have hd' : (((g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) : ℤ) : ZMod 4) = (1 : ZMod 4) := by
        rw [hd]; rfl
      simp [ha, hc] at hd'
      have htwo : (2 : ZMod 4) * ((g 1 1 : ZMod 4) - (g 0 1 : ZMod 4)) = 1 := by
        ring_nf at hd' ⊢
        exact hd'
      exact zmod4_two_mul_ne_one ((g 1 1 : ZMod 4) - (g 0 1 : ZMod 4)) htwo
    · have ha : (g 0 0 : ZMod 4) = (3 : ZMod 4) := zmod_of_emod (k := 3) (by simpa using ha3)
      refine ⟨3, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((r3⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [r3_inv_mul_g_10]
      simp [ha, hc]; decide
  · have hc : (g 1 0 : ZMod 4) = (3 : ZMod 4) := zmod_of_emod (k := 3) (by simpa using hc3)
    rcases zmod4_cases (g 0 0) with ha0 | ha1 | ha2 | ha3
    · have ha : (g 0 0 : ZMod 4) = 0 := zmod_zero_of_emod ha0
      refine ⟨1, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((ModularGroup.S⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [S_inv_mul_g_10]
      simp [ha]
    · have ha : (g 0 0 : ZMod 4) = (1 : ZMod 4) := zmod_of_emod (k := 1) (by simpa using ha1)
      refine ⟨4, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((r4⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [r4_inv_mul_g_10]
      simp [ha, hc]
    · have ha : (g 0 0 : ZMod 4) = (2 : ZMod 4) := zmod_of_emod (k := 2) (by simpa using ha2)
      refine ⟨5, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((r5⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [r5_inv_mul_g_10]
      simp [ha, hc]; decide
    · have ha : (g 0 0 : ZMod 4) = (3 : ZMod 4) := zmod_of_emod (k := 3) (by simpa using ha3)
      refine ⟨2, ?_⟩
      rw [gamma0_4_mem_iff]
      change ((((r2⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod 4) = 0
      rw [r2_inv_mul_g_10]
      simp [ha, hc]

/-! Pairwise distinct cosets -/

lemma inj_rep (i j : Fin 6) (h : i ≠ j) :
    ((rep i : SL(2, ℤ) ⧸ gamma0_4) ≠
      (rep j : SL(2, ℤ) ⧸ gamma0_4)) := by
  intro hq
  have hmem : (rep i)⁻¹ * rep j ∈ gamma0_4 := by
    exact QuotientGroup.eq.mp hq
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals
    rw [gamma0_4_mem_iff] at hmem
    rw [Matrix.SpecialLinearGroup.coe_mul] at hmem
    rw [Matrix.SpecialLinearGroup.coe_inv] at hmem
    norm_num [rep, r2, r3, r4, r5, ModularGroup.coe_S, ModularGroup.S_inv,
      Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_mk,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of] at hmem
    contradiction

/-! Main theorem -/

theorem Gamma0_index_eq_six : gamma0_4.index = 6 := by
  classical
  let H : Subgroup SL(2, ℤ) := gamma0_4
  let Q := SL(2, ℤ) ⧸ H
  have surj : Function.Surjective (fun i : Fin 6 => (rep i : Q)) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    rcases leftCoset_cover g with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply QuotientGroup.eq.mpr
    exact hi
  have inj : Function.Injective (fun i : Fin 6 => (rep i : Q)) := by
    intro i j hij
    by_contra hne
    exact inj_rep i j hne hij
  have hcard : Nat.card Q = 6 := by
    let F : Fintype Q := Fintype.ofEquiv (Fin 6) (Equiv.ofBijective
      (fun i : Fin 6 => (rep i : Q)) ⟨inj, surj⟩)
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.ofBijective
      (fun i : Fin 6 => (rep i : Q)) ⟨inj, surj⟩)
  rw [Subgroup.index_eq_card]
  simpa [Q, H] using hcard

end Gamma0Minimal

#print axioms Gamma0Minimal.Gamma0_index_eq_six
#print axioms Gamma0Minimal.inv_10_zmod
#print axioms Gamma0Minimal.leftCoset_cover
#print axioms Gamma0Minimal.inj_rep
