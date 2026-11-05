/-
Gamma0(4) has index 6 in SL(2, Z) -- minimal-dependency rebuild
================================================================

Re-formalization of the statement `[SL(2,Z) : 螕鈧€(4)] = 6` WITHOUT depending on
the modular-forms library (`Mathlib.NumberTheory.ModularForms`).  The subgroup
螕鈧€(4) is defined by hand as the stabilizer of the congruence condition

    (g : Matrix (Fin 2) (Fin 2) Z) 1 0 鈮?0 (mod 4)

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
lemma inv_10_zmod (a : SL(2, 鈩?) :
    (((a鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? 1 0 : ZMod 4) =
      - (a.1 1 0 : ZMod 4) := by
  change ((Matrix.adjugate (a.1 : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) =
    -(a.1 1 0 : ZMod 4)
  rw [Matrix.adjugate_fin_two]
  simp

/-- 螕鈧€(4) = { g 鈭?SL(2,鈩? | g 1 0 鈮?0 (mod 4) }, hand-rolled subgroup. -/
def gamma0_4 : Subgroup (SL(2, 鈩?) where
  carrier := {g : SL(2, 鈩? | ((g : Matrix (Fin 2) (Fin 2) 鈩? 1 0 : ZMod 4) = 0}
  one_mem' := by
    norm_num
  mul_mem' := by
    intro a b ha hb
    change (((a * b : SL(2, 鈩?) : Matrix (Fin 2) (Fin 2) 鈩? 1 0 : ZMod 4) = 0
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_two]
    have ha' : ((a : Matrix (Fin 2) (Fin 2) 鈩? 1 0 : ZMod 4) = 0 := by simpa using ha
    have hb' : ((b : Matrix (Fin 2) (Fin 2) 鈩? 1 0 : ZMod 4) = 0 := by simpa using hb
    simp [ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : ((a : Matrix (Fin 2) (Fin 2) 鈩? 1 0 : ZMod 4) = 0 := ha
    change (((a鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? 1 0 : ZMod 4) = 0
    rw [inv_10_zmod a]
    simpa using ha'

/-- Membership criterion for 螕鈧€(4), the hand-rolled analogue of
`CongruenceSubgroup.Gamma0_mem`. -/
lemma gamma0_4_mem_iff (g : SL(2, 鈩?) :
    g 鈭?gamma0_4 鈫?((g : Matrix (Fin 2) (Fin 2) 鈩? 1 0 : ZMod 4) = 0 :=
  Iff.rfl

/-- Six explicit left-coset representatives:
r鈧€ = 1, r鈧?= S, r鈧?.r鈧?as below. -/
def r2 : SL(2, 鈩? := 鉄?![1, 0; 1, 1], by norm_num [Matrix.det_fin_two]鉄?def r3 : SL(2, 鈩? := 鉄?![1, 0; 2, 1], by norm_num [Matrix.det_fin_two]鉄?def r4 : SL(2, 鈩? := 鉄?![1, 0; 3, 1], by norm_num [Matrix.det_fin_two]鉄?def r5 : SL(2, 鈩? := 鉄?![2, 1; 1, 1], by norm_num [Matrix.det_fin_two]鉄?
def rep : Fin 6 鈫?SL(2, 鈩?
  | 0 => 1
  | 1 => ModularGroup.S
  | 2 => r2
  | 3 => r3
  | 4 => r4
  | 5 => r5

/-! Mod-4 enumeration helpers -/

lemma zmod4_cases (x : 鈩? : x % 4 = 0 鈭?x % 4 = 1 鈭?x % 4 = 2 鈭?x % 4 = 3 := by
  have hge : 0 鈮?x % 4 := Int.emod_nonneg x (by norm_num : (4 : 鈩? 鈮?0)
  have hlt : x % 4 < 4 := Int.emod_lt x (by norm_num : (4 : 鈩? 鈮?0)
  omega

lemma zmod_zero_of_emod {x : 鈩 (h : x % 4 = 0) : (x : ZMod 4) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rwa [Int.dvd_iff_emod_eq_zero]

lemma zmod_of_emod {x k : 鈩 (h : x % 4 = k % 4) : (x : ZMod 4) = (k : ZMod 4) := by
  rwa [ZMod.intCast_eq_intCast_iff']

lemma zmod4_enum (x : ZMod 4) : x = 0 鈭?x = 1 鈭?x = 2 鈭?x = 3 := by
  have hx : x = (x.val : ZMod 4) := (ZMod.natCast_zmod_val (n := 4) x).symm
  have hlt : x.val < 4 := x.val_lt
  have hcase : x.val = 0 鈭?x.val = 1 鈭?x.val = 2 鈭?x.val = 3 := by omega
  rcases hcase with h0 | h1 | h2 | h3
  路 exact Or.inl (hx.trans (by rw [h0]; rfl))
  路 exact Or.inr (Or.inl (hx.trans (by rw [h1]; rfl)))
  路 exact Or.inr (Or.inr (Or.inl (hx.trans (by rw [h2]; rfl))))
  路 exact Or.inr (Or.inr (Or.inr (hx.trans (by rw [h3]; rfl))))

/-! Matrix products: the (1,0) entry of `(rep i)鈦宦?* g` mod 4 -/

lemma S_inv_val : ((ModularGroup.S鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? = !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [ModularGroup.coe_S, Matrix.adjugate_fin_two_of]

lemma r2_inv_val : ((r2鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? = !![1, 0; -1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [r2, Matrix.adjugate_fin_two_of]

lemma r3_inv_val : ((r3鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? = !![1, 0; -2, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [r3, Matrix.adjugate_fin_two_of]

lemma r4_inv_val : ((r4鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? = !![1, 0; -3, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [r4, Matrix.adjugate_fin_two_of]

lemma r5_inv_val : ((r5鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? = !![1, -1; -1, 2] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [r5, Matrix.adjugate_fin_two_of]

lemma one_mul_g_10 (g : SL(2, 鈩?) :
    (((1鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 = (g : Matrix (Fin 2) (Fin 2) 鈩? 1 0 := by
  simp

lemma S_inv_mul_g_10 (g : SL(2, 鈩?) :
    (((ModularGroup.S鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 = -(g 0 0 : 鈩? := by
  rw [Matrix.mul_apply]
  rw [S_inv_val]
  norm_num [Fin.sum_univ_two]

lemma r2_inv_mul_g_10 (g : SL(2, 鈩?) :
    (((r2鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 = -(g 0 0 : 鈩? + (g 1 0 : 鈩? := by
  rw [Matrix.mul_apply]
  rw [r2_inv_val]
  norm_num [Fin.sum_univ_two]

lemma r3_inv_mul_g_10 (g : SL(2, 鈩?) :
    (((r3鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 = -2 * (g 0 0 : 鈩? + (g 1 0 : 鈩? := by
  rw [Matrix.mul_apply]
  rw [r3_inv_val]
  norm_num [Fin.sum_univ_two]

lemma r4_inv_mul_g_10 (g : SL(2, 鈩?) :
    (((r4鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 = -3 * (g 0 0 : 鈩? + (g 1 0 : 鈩? := by
  rw [Matrix.mul_apply]
  rw [r4_inv_val]
  norm_num [Fin.sum_univ_two]

lemma r5_inv_mul_g_10 (g : SL(2, 鈩?) :
    (((r5鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 = -(g 0 0 : 鈩? + 2 * (g 1 0 : 鈩? := by
  rw [Matrix.mul_apply]
  rw [r5_inv_val]
  norm_num [Fin.sum_univ_two]

lemma zmod4_two_mul_ne_one (x : ZMod 4) : (2 : ZMod 4) * x 鈮?1 := by
  rcases zmod4_enum x with hx0 | hx1 | hx2 | hx3
  路 rw [hx0]; decide
  路 rw [hx1]; decide
  路 rw [hx2]; decide
  路 rw [hx3]; decide

/-! Surjectivity: every first column (a,c) mod 4 falls into one of the 6
primitive classes. -/

lemma leftCoset_cover (g : SL(2, 鈩?) :
    鈭?i : Fin 6, (rep i)鈦宦?* g 鈭?gamma0_4 := by
  classical
  rcases zmod4_cases (g 1 0) with hc0 | hc1 | hc2 | hc3
  路 have hc : (g 1 0 : ZMod 4) = 0 := zmod_zero_of_emod hc0
    refine 鉄?, ?_鉄?    rw [gamma0_4_mem_iff]
    change ((((1鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
    rw [one_mul_g_10]
    exact hc
  路 have hc : (g 1 0 : ZMod 4) = (1 : ZMod 4) := zmod_of_emod (k := 1) (by simpa using hc1)
    rcases zmod4_cases (g 0 0) with ha0 | ha1 | ha2 | ha3
    路 have ha : (g 0 0 : ZMod 4) = 0 := zmod_zero_of_emod ha0
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((ModularGroup.S鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [S_inv_mul_g_10]
      simp [ha]
    路 have ha : (g 0 0 : ZMod 4) = (1 : ZMod 4) := zmod_of_emod (k := 1) (by simpa using ha1)
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((r2鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [r2_inv_mul_g_10]
      simp [ha, hc]
    路 have ha : (g 0 0 : ZMod 4) = (2 : ZMod 4) := zmod_of_emod (k := 2) (by simpa using ha2)
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((r5鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [r5_inv_mul_g_10]
      simp [ha, hc]
    路 have ha : (g 0 0 : ZMod 4) = (3 : ZMod 4) := zmod_of_emod (k := 3) (by simpa using ha3)
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((r4鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [r4_inv_mul_g_10]
      simp [ha, hc]; decide
  路 have hc : (g 1 0 : ZMod 4) = (2 : ZMod 4) := zmod_of_emod (k := 2) (by simpa using hc2)
    rcases zmod4_cases (g 0 0) with ha0 | ha1 | ha2 | ha3
    路 have ha : (g 0 0 : ZMod 4) = 0 := zmod_zero_of_emod ha0
      exfalso
      have hd : (g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) = 1 := by
        rw [鈫?Matrix.det_fin_two]
        exact (g : SL(2, 鈩?).2
      have hd' : (((g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) : 鈩? : ZMod 4) = (1 : ZMod 4) := by
        rw [hd]; rfl
      simp [ha, hc] at hd'
      have htwo : (2 : ZMod 4) * (g 0 1 : ZMod 4) = 1 := by
        rw [鈫?(show (-2 : ZMod 4) = 2 by decide)]
        ring_nf at hd' 鈯?        exact hd'
      exact zmod4_two_mul_ne_one (g 0 1 : ZMod 4) htwo
    路 have ha : (g 0 0 : ZMod 4) = (1 : ZMod 4) := zmod_of_emod (k := 1) (by simpa using ha1)
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((r3鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [r3_inv_mul_g_10]
      simp [ha, hc]
    路 have ha : (g 0 0 : ZMod 4) = (2 : ZMod 4) := zmod_of_emod (k := 2) (by simpa using ha2)
      exfalso
      have hd : (g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) = 1 := by
        rw [鈫?Matrix.det_fin_two]
        exact (g : SL(2, 鈩?).2
      have hd' : (((g 0 0) * (g 1 1) - (g 0 1) * (g 1 0) : 鈩? : ZMod 4) = (1 : ZMod 4) := by
        rw [hd]; rfl
      simp [ha, hc] at hd'
      have htwo : (2 : ZMod 4) * ((g 1 1 : ZMod 4) - (g 0 1 : ZMod 4)) = 1 := by
        ring_nf at hd' 鈯?        exact hd'
      exact zmod4_two_mul_ne_one ((g 1 1 : ZMod 4) - (g 0 1 : ZMod 4)) htwo
    路 have ha : (g 0 0 : ZMod 4) = (3 : ZMod 4) := zmod_of_emod (k := 3) (by simpa using ha3)
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((r3鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [r3_inv_mul_g_10]
      simp [ha, hc]; decide
  路 have hc : (g 1 0 : ZMod 4) = (3 : ZMod 4) := zmod_of_emod (k := 3) (by simpa using hc3)
    rcases zmod4_cases (g 0 0) with ha0 | ha1 | ha2 | ha3
    路 have ha : (g 0 0 : ZMod 4) = 0 := zmod_zero_of_emod ha0
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((ModularGroup.S鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [S_inv_mul_g_10]
      simp [ha]
    路 have ha : (g 0 0 : ZMod 4) = (1 : ZMod 4) := zmod_of_emod (k := 1) (by simpa using ha1)
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((r4鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [r4_inv_mul_g_10]
      simp [ha, hc]
    路 have ha : (g 0 0 : ZMod 4) = (2 : ZMod 4) := zmod_of_emod (k := 2) (by simpa using ha2)
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((r5鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [r5_inv_mul_g_10]
      simp [ha, hc]; decide
    路 have ha : (g 0 0 : ZMod 4) = (3 : ZMod 4) := zmod_of_emod (k := 3) (by simpa using ha3)
      refine 鉄?, ?_鉄?      rw [gamma0_4_mem_iff]
      change ((((r2鈦宦?: SL(2, 鈩?).1 : Matrix (Fin 2) (Fin 2) 鈩? * (g : Matrix (Fin 2) (Fin 2) 鈩?) 1 0 : ZMod 4) = 0
      rw [r2_inv_mul_g_10]
      simp [ha, hc]

/-! Pairwise distinct cosets -/

lemma inj_rep (i j : Fin 6) (h : i 鈮?j) :
    ((rep i : SL(2, 鈩? 猝?gamma0_4) 鈮?      (rep j : SL(2, 鈩? 猝?gamma0_4)) := by
  intro hq
  have hmem : (rep i)鈦宦?* rep j 鈭?gamma0_4 := by
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
  let H : Subgroup SL(2, 鈩? := gamma0_4
  let Q := SL(2, 鈩? 猝?H
  have surj : Function.Surjective (fun i : Fin 6 => (rep i : Q)) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    rcases leftCoset_cover g with 鉄╥, hi鉄?    refine 鉄╥, ?_鉄?    apply QuotientGroup.eq.mpr
    exact hi
  have inj : Function.Injective (fun i : Fin 6 => (rep i : Q)) := by
    intro i j hij
    by_contra hne
    exact inj_rep i j hne hij
  have hcard : Nat.card Q = 6 := by
    let F : Fintype Q := Fintype.ofEquiv (Fin 6) (Equiv.ofBijective
      (fun i : Fin 6 => (rep i : Q)) 鉄╥nj, surj鉄?
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.ofBijective
      (fun i : Fin 6 => (rep i : Q)) 鉄╥nj, surj鉄?
  rw [Subgroup.index_eq_card]
  simpa [Q, H] using hcard

end Gamma0Minimal

/-
Rouch茅's theorem, discrete polynomial version
===============================================

Mathlib v4.34 does not contain a full complex-analysis Rouch茅 theorem
(whole-tree search found no Rouch茅 / argument-principle theorem).  Per the
task rule "report the gap honestly and degrade", this file completes the
polynomial / discrete version:

  * the core counting theorem `poly_rouche_discrete`: if `q` has strictly
    smaller degree than `p` (the polynomial analogue of the boundary
    condition `|g| < |f|`), then `p` and `p + q` have the same number of
    roots counted with multiplicity;
  * the finite instance `rouche_instance_cubic`: `f = X鲁 - X` and
    `g = X` (`deg g = 1 < 3 = deg f`), both have exactly 3 roots.

The boundary core lemma `rouche_boundary_core` (strict triangle inequality:
`鈥杣鈥?< 鈥杤鈥朻 forces `u + v 鈮?0`) lives in `Challenge_Rouche.lean` and is
reproduced here so that this file is self-contained for the counting part.

No `sorry`, no invented lemmas.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Norm

open Polynomial

namespace RoucheDiscrete

/-- Boundary core lemma (norm form of the strict triangle-inequality argument):
if `鈥杣鈥?< 鈥杤鈥朻 and `v 鈮?0`, then `u + v 鈮?0`.  In Rouch茅's setting this is the
local step preventing `f + g` from vanishing where the dominant term does not. -/
theorem rouche_boundary_core {u v : 鈩倉 (hlt : 鈥杣鈥?< 鈥杤鈥? (_hv0 : v 鈮?0) :
    u + v 鈮?0 := by
  intro h0
  have hle : 鈥杤鈥?鈮?鈥杣 + v鈥?+ 鈥杣鈥?:= by
    have h1 : 鈥?u + v) + (-u)鈥?鈮?鈥杣 + v鈥?+ 鈥?u鈥?:= norm_add_le (u + v) (-u)
    rw [show (u + v) + (-u) = v by ring] at h1
    rwa [norm_neg] at h1
  have hnorm0 : 鈥杣 + v鈥?= 0 := by simp [h0]
  linarith

/-- Discrete Rouch茅 (polynomial version): a strictly lower-degree perturbation
`q` does not change the number of roots (counted with multiplicity) of a
nonzero polynomial `p` over an algebraically closed field.  Here `鈩俙 is
algebraically closed, so every polynomial splits and
`roots.card = natDegree`. -/
theorem poly_rouche_discrete {p q : 鈩俒X]} (_hp : p 鈮?0) (hpq : p + q 鈮?0)
    (hdeg : q.natDegree < p.natDegree) :
    (p + q).roots.card = p.roots.card := by
  by_cases hq0 : q = 0
  路 subst hq0
    simp
  路 have hd : q.degree < p.degree := by
      exact (natDegree_lt_natDegree_iff (p := q) (q := p) hq0).mp hdeg
    have hnd : (p + q).natDegree = p.natDegree :=
      natDegree_add_eq_left_of_degree_lt (p := p) (q := q) hd
    calc
      (p + q).roots.card = (p + q).natDegree :=
        (IsAlgClosed.splits (p + q)).natDegree_eq_card_roots.symm
      _ = p.natDegree := hnd
      _ = p.roots.card := (IsAlgClosed.splits p).natDegree_eq_card_roots

/-- Finite instance: `f = X鲁 - X` and `g = X`.  Since `deg g = 1 < 3 = deg f`,
the discrete Rouch茅 theorem applies and `f + g = X鲁` has the same number of
roots as `f` (namely 3, counted with multiplicity). -/
theorem rouche_instance_cubic :
    ((X ^ 3 - X : 鈩俒X]) + X).roots.card = (X ^ 3 - X : 鈩俒X]).roots.card := by
  apply poly_rouche_discrete
  路 -- p = X鲁 - X 鈮?0
    intro h
    have hsub : (X : 鈩俒X]) ^ 3 = X := sub_eq_zero.mp h
    have hd := congrArg (fun r : 鈩俒X] => r.natDegree) hsub
    simp at hd
  路 -- (X鲁 - X) + X = X鲁 鈮?0
    intro h
    have hcube : (X : 鈩俒X]) ^ 3 = 0 := by
      have h' : (X ^ 3 - X : 鈩俒X]) + X = 0 := h
      rw [show (X ^ 3 - X : 鈩俒X]) + X = X ^ 3 by ring] at h'
      exact h'
    exact (pow_ne_zero 3 (X_ne_zero (R := 鈩?)) hcube
  路 -- deg g = 1 < 3 = deg f
    have hnd : (X ^ 3 - X : 鈩俒X]).natDegree = 3 := by
      rw [sub_eq_add_neg]
      have hdeg_lt : (-X : 鈩俒X]).degree < (X ^ 3 : 鈩俒X]).degree := by
        rw [degree_neg, degree_X, degree_X_pow]
        norm_num
      rw [natDegree_add_eq_left_of_degree_lt hdeg_lt]
      rw [natDegree_X_pow]
    rw [hnd]
    rw [natDegree_X]
    norm_num

/-- The same conclusion restated in the direction of the Rouch茅 statement:
`f` and `f + g` have the same number of zeros. -/
theorem rouche_finite_same_zeros :
    (X ^ 3 - X : 鈩俒X]).roots.card = ((X ^ 3 - X : 鈩俒X]) + X).roots.card :=
  rouche_instance_cubic.symm

end RoucheDiscrete

#print axioms Gamma0Minimal.Gamma0_index_eq_six
#print axioms Gamma0Minimal.inv_10_zmod
#print axioms Gamma0Minimal.leftCoset_cover
#print axioms Gamma0Minimal.inj_rep
#print axioms RoucheDiscrete.poly_rouche_discrete
#print axioms RoucheDiscrete.rouche_instance_cubic
#print axioms RoucheDiscrete.rouche_finite_same_zeros
#print axioms RoucheDiscrete.rouche_boundary_core