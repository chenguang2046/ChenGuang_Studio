import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

set_option linter.unnecessarySimpa false

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup QuotientGroup

namespace Challenge021Gamma0NIndex

/-! # Challenge_021 — Γ₀(N) 指数的群论构造（ChenGuang Studio） -/

lemma inv_10_zmod (N : ℕ) (a : SL(2, ℤ)) :
    (((a⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) =
      - (a.1 1 0 : ZMod N) := by
  change ((Matrix.adjugate (a.1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod N) =
    -(a.1 1 0 : ZMod N)
  rw [Matrix.adjugate_fin_two]
  simp

def gamma0_N (N : ℕ) : Subgroup (SL(2, ℤ)) where
  carrier := {g : SL(2, ℤ) | ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0}
  one_mem' := by
    norm_num
  mul_mem' := by
    intro a b ha hb
    change (((a * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0
    rw [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_two]
    have ha' : ((a : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 := by simpa using ha
    have hb' : ((b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 := by simpa using hb
    simp [ha', hb']
  inv_mem' := by
    intro a ha
    change (((a⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0
    rw [inv_10_zmod N]
    simpa using ha

lemma gamma0_N_mem_iff (N : ℕ) (g : SL(2, ℤ)) :
    g ∈ gamma0_N N ↔ ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 :=
  Iff.rfl

def R (k : ℕ) : SL(2, ℤ) :=
  ⟨!![(k : ℤ), -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

def T (u : ℕ) : SL(2, ℤ) :=
  ⟨!![1, 0; (u : ℤ), 1], by norm_num [Matrix.det_fin_two]⟩

lemma R_inv_val (k : ℕ) : ((R k)⁻¹ : SL(2, ℤ)).1 = !![0, 1; -1, (k : ℤ)] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [R, Matrix.adjugate_fin_two_of]

lemma R_inv_mul_g_10 (k : ℕ) (g : SL(2, ℤ)) :
    (((R k)⁻¹ : SL(2, ℤ)).1 * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      (k : ℤ) * (g 1 0) - (g 0 0) := by
  rw [Matrix.mul_apply]
  rw [R_inv_val]
  norm_num [Fin.sum_univ_two]
  ring

lemma T_inv_val (u : ℕ) : ((T u)⁻¹ : SL(2, ℤ)).1 = !![1, 0; -(u : ℤ), 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [T, Matrix.adjugate_fin_two_of]

lemma T_inv_mul_g_10 (u : ℕ) (g : SL(2, ℤ)) :
    (((T u)⁻¹ : SL(2, ℤ)).1 * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      (g 1 0) - (u : ℤ) * (g 0 0) := by
  rw [Matrix.mul_apply]
  rw [T_inv_val]
  norm_num [Fin.sum_univ_two]
  ring

lemma one_mul_g_10 (g : SL(2, ℤ)) :
    (((1⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  simp

#check ZMod.chineseRemainder
#check ZMod.prodEquivPi
#check ZMod.equivPi
#check ZMod.unitsEquivCoprime

structure CoprimeCol (N : ℕ) : Type where
  a : ZMod N
  b : ZMod N
  cop : ∃ s t : ZMod N, s * a + t * b = 1

def ProjRel (N : ℕ) (x y : CoprimeCol N) : Prop :=
  ∃ u : (ZMod N)ˣ, y.a = (u : ZMod N) * x.a ∧ y.b = (u : ZMod N) * x.b

instance projSetoid (N : ℕ) : Setoid (CoprimeCol N) where
  r := ProjRel N
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨1, by simp, by simp⟩
    · intro x y hxy
      rcases hxy with ⟨u, hu1, hu2⟩
      have hm : (↑(u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := by
        simpa using congrArg (fun x : (ZMod N)ˣ => (x : ZMod N)) (mul_left_inv u)
      refine ⟨u⁻¹, ?_, ?_⟩
      · calc
          x.a = (↑(u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.a) := by
            rw [← mul_assoc]
            rw [hm]
            simp
          _ = (↑(u⁻¹ : (ZMod N)ˣ) : ZMod N) * y.a := by rw [← hu1]
      · calc
          x.b = (↑(u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.b) := by
            rw [← mul_assoc]
            rw [hm]
            simp
          _ = (↑(u⁻¹ : (ZMod N)ˣ) : ZMod N) * y.b := by rw [← hu2]
    · intro x y z hxy hyz
      rcases hxy with ⟨u, hu1, hu2⟩
      rcases hyz with ⟨v, hv1, hv2⟩
      refine ⟨v * u, ?_, ?_⟩
      · calc
          z.a = (v : ZMod N) * y.a := hv1
          _ = (v : ZMod N) * ((u : ZMod N) * x.a) := by rw [hu1]
          _ = ((v : ZMod N) * (u : ZMod N)) * x.a := by ring
          _ = ((v * u : (ZMod N)ˣ) : ZMod N) * x.a := by rw [Units.val_mul]
      · calc
          z.b = (v : ZMod N) * y.b := hv2
          _ = (v : ZMod N) * ((u : ZMod N) * x.b) := by rw [hu2]
          _ = ((v : ZMod N) * (u : ZMod N)) * x.b := by ring
          _ = ((v * u : (ZMod N)ˣ) : ZMod N) * x.b := by rw [Units.val_mul]

def P1 (N : ℕ) : Type :=
  Quotient (projSetoid N)

lemma col_coprime_of_SL (N : ℕ) (g : SL(2, ℤ)) :
    ∃ s t : ZMod N, s * (g 0 0 : ZMod N) + t * (g 1 0 : ZMod N) = 1 := by
  refine ⟨(g 1 1 : ZMod N), -((g 0 1 : ZMod N)), ?_⟩
  have hd0 : (g.1 : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.property
  have hd : (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0) * ((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1) -
      ((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1) * ((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0) : ℤ) = 1 := by
    rw [← Matrix.det_fin_two]
    exact hd0
  have hdZ : (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) *
        (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) -
        (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod N) *
        (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 1 := by
    rw [← Int.cast_mul, ← Int.cast_mul]
    rw [← Int.cast_sub]
    rw [hd]
    norm_num
  calc
    (g 1 1 : ZMod N) * (g 0 0 : ZMod N) + -((g 0 1 : ZMod N)) * (g 1 0 : ZMod N) =
        (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) *
          (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) -
        (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod N) *
          (((g.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) := by
      ring
    _ = 1 := hdZ

lemma inv_mul_g_10_formula (g h : SL(2, ℤ)) :
    (((g⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) * (h : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      (g 0 0) * (h 1 0) - (g 1 0) * (h 0 0) := by
  change ((Matrix.adjugate (g.1 : Matrix (Fin 2) (Fin 2) ℤ)) * (h : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      (g 0 0) * (h 1 0) - (g 1 0) * (h 0 0)
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_two]
  rw [Matrix.adjugate_fin_two]
  norm_num
  ring

lemma projRel_of_det_zero {N : ℕ} {a b c d : ZMod N}
    (hx : ∃ s t : ZMod N, s * a + t * b = 1)
    (hy : ∃ s t : ZMod N, s * c + t * d = 1)
    (hdet : a * d = b * c) :
    ProjRel N ⟨a, b, hx⟩ ⟨c, d, hy⟩ := by
  rcases hx with ⟨s, t, hs⟩
  rcases hy with ⟨s', t', hs'⟩
  refine ⟨⟨s * c + t * d, s' * a + t' * b, ?_, ?_⟩, ?_, ?_⟩
  · calc
      (s * c + t * d) * (s' * a + t' * b) =
          s * s' * (a * c) + s * t' * (b * c) + t * s' * (a * d) + t * t' * (b * d) := by
        ring
      _ = s * s' * (a * c) + s * t' * (a * d) + t * s' * (b * c) + t * t' * (b * d) := by
        rw [hdet]
      _ = (s * a + t * b) * (s' * c + t' * d) := by
        ring
      _ = 1 := by
        rw [hs, hs']
        simp
  · calc
      (s' * a + t' * b) * (s * c + t * d) =
          s * s' * (a * c) + t * s' * (a * d) + s * t' * (b * c) + t * t' * (b * d) := by
        ring
      _ = s * s' * (a * c) + s * t' * (a * d) + t * s' * (b * c) + t * t' * (b * d) := by
        rw [hdet]
        ring
      _ = (s * a + t * b) * (s' * c + t' * d) := by
        ring
      _ = 1 := by
        rw [hs, hs']
        simp
  · calc
      c = (s * a + t * b) * c := by
        rw [hs]
        simp
      _ = s * (a * c) + t * (b * c) := by ring
      _ = s * (a * c) + t * (a * d) := by rw [← hdet]
      _ = (s * c + t * d) * a := by ring
  · calc
      d = (s * a + t * b) * d := by
        rw [hs]
        simp
      _ = s * (a * d) + t * (b * d) := by ring
      _ = s * (b * c) + t * (b * d) := by rw [hdet]
      _ = (s * c + t * d) * b := by ring

def col (N : ℕ) (g : SL(2, ℤ)) : CoprimeCol N :=
  ⟨(((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N),
    (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N),
    col_coprime_of_SL N g⟩

lemma col_projRel_of_same_coset {N : ℕ} (g h : SL(2, ℤ))
    (hcos : g⁻¹ * h ∈ gamma0_N N) :
    ProjRel N (col N g) (col N h) := by
  have h10 : ((((g⁻¹ : SL(2, ℤ)) * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      : ZMod N) = 0 := (gamma0_N_mem_iff N (g⁻¹ * h)).mp hcos
  have hzN : ((((g⁻¹ : SL(2, ℤ)).1 : Matrix (Fin 2) (Fin 2) ℤ) *
      (h : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ZMod N) = 0 := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using h10
  have hzN' : ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) *
        ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) -
        ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) * ((h : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)
        : ℤ) : ZMod N) = 0 := by
    rw [← inv_mul_g_10_formula g h]
    exact hzN
  have hdet : (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) *
        (((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) -
      (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) *
        (((h : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) = 0 := by
    simpa using hzN'
  exact projRel_of_det_zero (col_coprime_of_SL N g) (col_coprime_of_SL N h)
    (sub_eq_zero.mp hdet)

def cosetToP1 (N : ℕ) : SL(2, ℤ) ⧸ gamma0_N N → P1 N :=
  Quotient.lift (fun g : SL(2, ℤ) => Quotient.mk (projSetoid N) (col N g))
    (by
      intro g h hcos
      have hcos' : g⁻¹ * h ∈ gamma0_N N := leftRel_apply.mp hcos
      exact Quotient.sound (col_projRel_of_same_coset g h hcos'))

#check (∀ (N : ℕ), (SL(2, ℤ) ⧸ gamma0_N N) ≃ P1 N)
#check (∀ (m n : ℕ), m.Coprime n → P1 (m * n) ≃ P1 m × P1 n)
#check (∀ (N : ℕ), Nat.card (P1 N) = N * N.primeFactors.prod (fun p => p + 1))
#check (∀ (N : ℕ), (gamma0_N N).index = N * N.primeFactors.prod (fun p => p + 1))

lemma coprimecol_ext {N : ℕ} {x y : CoprimeCol N} (ha : x.a = y.a) (hb : x.b = y.b) :
    x = y := by
  cases x with
  | mk xa xb xcop =>
    cases y with
    | mk ya yb ycop =>
      simp at ha hb
      simp [ha, hb]

noncomputable def coprimecol_smul_def (N : ℕ) (u : (ZMod N)ˣ) (x : CoprimeCol N) :
    CoprimeCol N :=
  ⟨(u : ZMod N) * x.a, (u : ZMod N) * x.b, by
    rcases x.cop with ⟨s, t, hs⟩
    have huinv : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := by
      simpa [Units.val_mul] using
        congrArg (fun z : (ZMod N)ˣ => (z : ZMod N)) (mul_left_inv u)
    refine ⟨s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), t * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), ?_⟩
    calc
      s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.a) +
          t * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.b)
          = (s * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N))) * x.a +
              (t * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N))) * x.b := by
        ring
      _ = (s * 1) * x.a + (t * 1) * x.b := by rw [huinv]
      _ = s * x.a + t * x.b := by simp
      _ = 1 := hs⟩

noncomputable instance smulCoprimeCol (N : ℕ) : SMul (ZMod N)ˣ (CoprimeCol N) where
  smul := coprimecol_smul_def N

noncomputable instance mulActionCoprimeCol (N : ℕ) : MulAction (ZMod N)ˣ (CoprimeCol N) where
  one_smul := by
    intro x
    apply coprimecol_ext
    · change (1 : ZMod N) * x.a = x.a
      simp
    · change (1 : ZMod N) * x.b = x.b
      simp
  mul_smul := by
    intro u v x
    apply coprimecol_ext
    · change ((u * v : (ZMod N)ˣ) : ZMod N) * x.a = (u : ZMod N) * ((v : ZMod N) * x.a)
      simp [Units.val_mul, mul_assoc]
    · change ((u * v : (ZMod N)ˣ) : ZMod N) * x.b = (u : ZMod N) * ((v : ZMod N) * x.b)
      simp [Units.val_mul, mul_assoc]

@[simp] lemma coprimecol_smul_a (N : ℕ) (u : (ZMod N)ˣ) (x : CoprimeCol N) :
    (u • x).a = (u : ZMod N) * x.a :=
  rfl

@[simp] lemma coprimecol_smul_b (N : ℕ) (u : (ZMod N)ˣ) (x : CoprimeCol N) :
    (u • x).b = (u : ZMod N) * x.b :=
  rfl

lemma projRel_iff_mem_orbit {N : ℕ} (x y : CoprimeCol N) :
    ProjRel N x y ↔ y ∈ MulAction.orbit (ZMod N)ˣ x := by
  constructor
  · intro h
    rcases h with ⟨u, hu1, hu2⟩
    rw [MulAction.mem_orbit_iff]
    refine ⟨u, ?_⟩
    apply coprimecol_ext
    · change (u : ZMod N) * x.a = y.a
      exact hu1.symm
    · change (u : ZMod N) * x.b = y.b
      exact hu2.symm
  · intro h
    rw [MulAction.mem_orbit_iff] at h
    rcases h with ⟨u, hu⟩
    refine ⟨u, ?_, ?_⟩
    · simpa using (congrArg (fun z : CoprimeCol N => z.a) hu).symm
    · simpa using (congrArg (fun z : CoprimeCol N => z.b) hu).symm

lemma projRel_iff_orbitRel {N : ℕ} (x y : CoprimeCol N) :
    ProjRel N x y ↔ (MulAction.orbitRel (ZMod N)ˣ (CoprimeCol N)).r x y := by
  have hsym : ∀ {a b : CoprimeCol N}, ProjRel N a b → ProjRel N b a :=
    (projSetoid N).iseqv.symm
  calc
    ProjRel N x y ↔ ProjRel N y x := ⟨fun h => hsym h, fun h => hsym h⟩
    _ ↔ x ∈ MulAction.orbit (ZMod N)ˣ y := projRel_iff_mem_orbit y x
    _ ↔ (MulAction.orbitRel (ZMod N)ˣ (CoprimeCol N)).r x y := by
      change x ∈ MulAction.orbit (ZMod N)ˣ y ↔ x ∈ MulAction.orbit (ZMod N)ˣ y
      rfl

noncomputable def quotient_equiv_of_rel_iff {α : Type} (s₁ s₂ : Setoid α)
    (h : ∀ x y : α, s₁.r x y ↔ s₂.r x y) : Quotient s₁ ≃ Quotient s₂ where
  toFun := Quotient.lift (fun x : α => Quotient.mk s₂ x)
    (by intro x y hxy; exact Quotient.sound ((h x y).mp hxy))
  invFun := Quotient.lift (fun x : α => Quotient.mk s₁ x)
    (by intro x y hxy; exact Quotient.sound ((h x y).mpr hxy))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl

noncomputable def coprodf_equiv_P1 (N : ℕ) [NeZero N] :
    Quotient (MulAction.orbitRel (ZMod N)ˣ (CoprimeCol N)) ≃ P1 N := by
  simpa [P1] using
    (quotient_equiv_of_rel_iff (MulAction.orbitRel (ZMod N)ˣ (CoprimeCol N))
      (projSetoid N) (fun x y => (projRel_iff_orbitRel (N := N) x y).symm))

lemma exists_SL_col_projRel (N : ℕ) [NeZero N] (c : CoprimeCol N) :
    ∃ g : SL(2, ℤ), ProjRel N (col N g) c := by
  classical
  let a0 : ℕ := c.a.val
  let b0 : ℕ := c.b.val
  let d : ℕ := Nat.gcd a0 b0
  let A : ℕ := a0 / d
  let B : ℕ := b0 / d
  by_cases hd : d = 0
  ·
    have ha0 : a0 = 0 := (Nat.gcd_eq_zero_iff.mp (by simpa [d] using hd)).1
    have hb0 : b0 = 0 := (Nat.gcd_eq_zero_iff.mp (by simpa [d] using hd)).2
    have hca : c.a = 0 := by
      rw [← ZMod.natCast_zmod_val (n := N) c.a]
      simp [a0, ha0]
    have hcb : c.b = 0 := by
      rw [← ZMod.natCast_zmod_val (n := N) c.b]
      simp [b0, hb0]
    have hN1 : N = 1 := by
      rcases c.cop with ⟨s, t, hs⟩
      have hz : (1 : ZMod N) = 0 := by
        rw [← hs]
        rw [hca, hcb]
        simp
      exact ZMod.one_eq_zero_iff.mp hz
    have h10 : (1 : ZMod 1) = 0 := ZMod.one_eq_zero_iff.mpr rfl
    refine ⟨1, 1, ?_, ?_⟩
    · rw [hca, hN1]
      simp [h10]
    · rw [hcb, hN1]
      simp [h10]
  ·
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hA : a0 = d * A := by
      dsimp [A]
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left a0 b0)).symm
    have hB : b0 = d * B := by
      dsimp [B]
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_right a0 b0)).symm
    have hcopAB : A.Coprime B := by
      dsimp [A, B]
      exact Nat.coprime_div_gcd_div_gcd hdpos
    have hgcd1 : (Nat.gcd A B : ℤ) = 1 := by
      rw [hcopAB]
      norm_num
    have hbez : (A : ℤ) * Nat.gcdA A B + (B : ℤ) * Nat.gcdB A B = 1 := by
      rw [← Nat.gcd_eq_gcd_ab A B]
      exact hgcd1
    let g : SL(2, ℤ) := ⟨!![(A : ℤ), -Nat.gcdB A B; (B : ℤ), Nat.gcdA A B], by
      rw [Matrix.det_fin_two]
      simp
      ring_nf
      simpa [mul_comm] using hbez⟩
    have hrel : ((A : ℤ) : ZMod N) * c.b = ((B : ℤ) : ZMod N) * c.a := by
      rw [← ZMod.natCast_zmod_val c.b, ← ZMod.natCast_zmod_val c.a]
      change ((A : ℤ) : ZMod N) * (b0 : ZMod N) = ((B : ℤ) : ZMod N) * (a0 : ZMod N)
      rw [hB, hA]
      simp only [Nat.cast_mul, Int.cast_natCast]
      ring
    refine ⟨g, ?_⟩
    have hdetzero : (col N g).a * c.b = (col N g).b * c.a := by
      simpa [col, g] using hrel
    exact projRel_of_det_zero (col_coprime_of_SL N g) c.cop hdetzero

lemma cosetToP1_injective (N : ℕ) : Function.Injective (cosetToP1 N) := by
  intro x y hxy
  refine Quotient.inductionOn x (motive := fun q =>
    (cosetToP1 N q = cosetToP1 N y) → q = y) ?_ hxy
  intro g hg
  refine Quotient.inductionOn y (motive := fun q =>
    (cosetToP1 N (Quotient.mk (leftRel (gamma0_N N)) g) = cosetToP1 N q) →
      Quotient.mk (leftRel (gamma0_N N)) g = q) ?_ hg
  intro h hh
  have hq : (Quotient.mk (projSetoid N) (col N g) : P1 N) =
      Quotient.mk (projSetoid N) (col N h) := by
    change cosetToP1 N (Quotient.mk (leftRel (gamma0_N N)) g) =
      cosetToP1 N (Quotient.mk (leftRel (gamma0_N N)) h)
    exact hh
  have hproj : ProjRel N (col N g) (col N h) := Quotient.exact hq
  rcases hproj with ⟨u, hu1, hu2⟩
  have hu1' : (((h : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) =
      (u : ZMod N) * (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) := by
    simpa [col] using hu1
  have hu2' : (((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) =
      (u : ZMod N) * (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) := by
    simpa [col] using hu2
  have hz : ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) *
        (((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) -
      (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) *
        (((h : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N)) = 0 := by
    rw [hu1', hu2']
    ring
  apply Quotient.sound
  apply leftRel_apply.mpr
  rw [gamma0_N_mem_iff]
  rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [inv_mul_g_10_formula]
  simpa using hz

noncomputable def gamma0_coset_equiv_P1 (N : ℕ) [NeZero N] :
    (SL(2, ℤ) ⧸ gamma0_N N) ≃ P1 N :=
  Equiv.ofBijective (cosetToP1 N) ⟨cosetToP1_injective N, by
    intro x
    refine Quotient.inductionOn x ?_
    intro c
    rcases exists_SL_col_projRel N c with ⟨g, hproj⟩
    refine ⟨Quotient.mk (leftRel (gamma0_N N)) g, ?_⟩
    exact Quotient.sound hproj⟩

lemma coprime_col_crt_iff {m n : ℕ} (hmn : m.Coprime n) (a b : ZMod (m * n)) :
    (∃ s t : ZMod (m * n), s * a + t * b = 1) ↔
      (∃ s t : ZMod m, s * (ZMod.chineseRemainder hmn a).1 + t * (ZMod.chineseRemainder hmn b).1 = 1) ∧
      (∃ s t : ZMod n, s * (ZMod.chineseRemainder hmn a).2 + t * (ZMod.chineseRemainder hmn b).2 = 1) := by
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hmn
  constructor
  · intro h
    rcases h with ⟨s, t, hs⟩
    constructor
    · refine ⟨(e s).1, (e t).1, ?_⟩
      have he : (e (s * a + t * b)).1 = (e s).1 * (e a).1 + (e t).1 * (e b).1 := by
        simp [map_add, map_mul]
      calc
        (e s).1 * (e a).1 + (e t).1 * (e b).1 = (e (s * a + t * b)).1 := by
          rw [← he]
        _ = (e 1).1 := by rw [hs]
        _ = 1 := by simp
    · refine ⟨(e s).2, (e t).2, ?_⟩
      have he : (e (s * a + t * b)).2 = (e s).2 * (e a).2 + (e t).2 * (e b).2 := by
        simp [map_add, map_mul]
      calc
        (e s).2 * (e a).2 + (e t).2 * (e b).2 = (e (s * a + t * b)).2 := by
          rw [← he]
        _ = (e 1).2 := by rw [hs]
        _ = 1 := by simp
  · intro h
    rcases h with ⟨⟨s₁, t₁, hs₁⟩, ⟨s₂, t₂, hs₂⟩⟩
    refine ⟨e.symm (s₁, s₂), e.symm (t₁, t₂), ?_⟩
    apply e.injective
    apply Prod.ext
    · calc
        (e (e.symm (s₁, s₂) * a + e.symm (t₁, t₂) * b)).1 =
            (e (e.symm (s₁, s₂))).1 * (e a).1 + (e (e.symm (t₁, t₂))).1 * (e b).1 := by
          simp [map_add, map_mul]
        _ = s₁ * (e a).1 + t₁ * (e b).1 := by simp
        _ = (e 1).1 := by
          rw [hs₁]
          simp
    · calc
        (e (e.symm (s₁, s₂) * a + e.symm (t₁, t₂) * b)).2 =
            (e (e.symm (s₁, s₂))).2 * (e a).2 + (e (e.symm (t₁, t₂))).2 * (e b).2 := by
          simp [map_add, map_mul]
        _ = s₂ * (e a).2 + t₂ * (e b).2 := by simp
        _ = (e 1).2 := by
          rw [hs₂]
          simp

noncomputable def col_crt_fst {m n : ℕ} (hmn : m.Coprime n) (x : CoprimeCol (m * n)) : CoprimeCol m :=
  ⟨(ZMod.chineseRemainder hmn x.a).1, (ZMod.chineseRemainder hmn x.b).1,
    ((coprime_col_crt_iff hmn x.a x.b).1 x.cop).1⟩

noncomputable def col_crt_snd {m n : ℕ} (hmn : m.Coprime n) (x : CoprimeCol (m * n)) : CoprimeCol n :=
  ⟨(ZMod.chineseRemainder hmn x.a).2, (ZMod.chineseRemainder hmn x.b).2,
    ((coprime_col_crt_iff hmn x.a x.b).1 x.cop).2⟩

noncomputable def col_crt_mk {m n : ℕ} (hmn : m.Coprime n) (x : CoprimeCol m) (y : CoprimeCol n) :
    CoprimeCol (m * n) :=
  ⟨(ZMod.chineseRemainder hmn).symm (x.a, y.a), (ZMod.chineseRemainder hmn).symm (x.b, y.b), by
    refine (coprime_col_crt_iff hmn ((ZMod.chineseRemainder hmn).symm (x.a, y.a))
      ((ZMod.chineseRemainder hmn).symm (x.b, y.b))).2 ⟨?_, ?_⟩
    · simpa using x.cop
    · simpa using y.cop⟩

lemma col_crt_fst_mk {m n : ℕ} (hmn : m.Coprime n) (x : CoprimeCol m) (y : CoprimeCol n) :
    col_crt_fst hmn (col_crt_mk hmn x y) = x := by
  rcases x with ⟨xa, xb, xcop⟩
  rcases y with ⟨ya, yb, ycop⟩
  simp [col_crt_fst, col_crt_mk]

lemma col_crt_snd_mk {m n : ℕ} (hmn : m.Coprime n) (x : CoprimeCol m) (y : CoprimeCol n) :
    col_crt_snd hmn (col_crt_mk hmn x y) = y := by
  rcases x with ⟨xa, xb, xcop⟩
  rcases y with ⟨ya, yb, ycop⟩
  simp [col_crt_snd, col_crt_mk]

lemma col_crt_mk_fst_snd {m n : ℕ} (hmn : m.Coprime n) (z : CoprimeCol (m * n)) :
    col_crt_mk hmn (col_crt_fst hmn z) (col_crt_snd hmn z) = z := by
  rcases z with ⟨za, zb, zcop⟩
  simp [col_crt_fst, col_crt_snd, col_crt_mk]

lemma projRel_refl (N : ℕ) (x : CoprimeCol N) : ProjRel N x x := ⟨1, by simp, by simp⟩

lemma col_crt_fst_projRel {m n : ℕ} (hmn : m.Coprime n) {x y : CoprimeCol (m * n)}
    (hxy : ProjRel (m * n) x y) : ProjRel m (col_crt_fst hmn x) (col_crt_fst hmn y) := by
  rcases hxy with ⟨u, hu1, hu2⟩
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hmn
  let uf : (ZMod m)ˣ := (u.map e.toMonoidHom).map (MonoidHom.fst (ZMod m) (ZMod n))
  refine ⟨uf, ?_, ?_⟩
  · calc
      (col_crt_fst hmn y).a = (e y.a).1 := rfl
      _ = (e ((u : ZMod (m * n)) * x.a)).1 := by rw [hu1]
      _ = (e (u : ZMod (m * n))).1 * (e x.a).1 := by simp [map_mul]
      _ = (uf : ZMod m) * (col_crt_fst hmn x).a := by
        change (e (u : ZMod (m * n))).1 * (e x.a).1 = (e (u : ZMod (m * n))).1 * (e x.a).1
        rfl
  · calc
      (col_crt_fst hmn y).b = (e y.b).1 := rfl
      _ = (e ((u : ZMod (m * n)) * x.b)).1 := by rw [hu2]
      _ = (e (u : ZMod (m * n))).1 * (e x.b).1 := by simp [map_mul]
      _ = (uf : ZMod m) * (col_crt_fst hmn x).b := by
        change (e (u : ZMod (m * n))).1 * (e x.b).1 = (e (u : ZMod (m * n))).1 * (e x.b).1
        rfl

lemma col_crt_snd_projRel {m n : ℕ} (hmn : m.Coprime n) {x y : CoprimeCol (m * n)}
    (hxy : ProjRel (m * n) x y) : ProjRel n (col_crt_snd hmn x) (col_crt_snd hmn y) := by
  rcases hxy with ⟨u, hu1, hu2⟩
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hmn
  let un : (ZMod n)ˣ := (u.map e.toMonoidHom).map (MonoidHom.snd (ZMod m) (ZMod n))
  refine ⟨un, ?_, ?_⟩
  · calc
      (col_crt_snd hmn y).a = (e y.a).2 := rfl
      _ = (e ((u : ZMod (m * n)) * x.a)).2 := by rw [hu1]
      _ = (e (u : ZMod (m * n))).2 * (e x.a).2 := by simp [map_mul]
      _ = (un : ZMod n) * (col_crt_snd hmn x).a := by
        change (e (u : ZMod (m * n))).2 * (e x.a).2 = (e (u : ZMod (m * n))).2 * (e x.a).2
        rfl
  · calc
      (col_crt_snd hmn y).b = (e y.b).2 := rfl
      _ = (e ((u : ZMod (m * n)) * x.b)).2 := by rw [hu2]
      _ = (e (u : ZMod (m * n))).2 * (e x.b).2 := by simp [map_mul]
      _ = (un : ZMod n) * (col_crt_snd hmn x).b := by
        change (e (u : ZMod (m * n))).2 * (e x.b).2 = (e (u : ZMod (m * n))).2 * (e x.b).2
        rfl

lemma col_crt_mk_projRel {m n : ℕ} (hmn : m.Coprime n) {x x' : CoprimeCol m} {y y' : CoprimeCol n}
    (hx : ProjRel m x x') (hy : ProjRel n y y') :
    ProjRel (m * n) (col_crt_mk hmn x y) (col_crt_mk hmn x' y') := by
  rcases hx with ⟨u₁, hu₁1, hu₁2⟩
  rcases hy with ⟨u₂, hu₂1, hu₂2⟩
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hmn
  let u0 : (ZMod m × ZMod n)ˣ :=
    ⟨((u₁ : ZMod m), (u₂ : ZMod n)), (((u₁⁻¹ : (ZMod m)ˣ) : ZMod m), ((u₂⁻¹ : (ZMod n)ˣ) : ZMod n)),
      by ext <;> simp, by ext <;> simp⟩
  let u : (ZMod (m * n))ˣ := u0.map (e.symm).toMonoidHom
  refine ⟨u, ?_, ?_⟩
  · calc
      (col_crt_mk hmn x' y').a = (ZMod.chineseRemainder hmn).symm (x'.a, y'.a) := rfl
      _ = (ZMod.chineseRemainder hmn).symm (((u₁ : ZMod m) * x.a), ((u₂ : ZMod n) * y.a)) := by
        rw [hu₁1, hu₂1]
      _ = (u : ZMod (m * n)) * (col_crt_mk hmn x y).a := by
        change (ZMod.chineseRemainder hmn).symm (((u₁ : ZMod m), (u₂ : ZMod n)) * (x.a, y.a)) =
          (u : ZMod (m * n)) * (ZMod.chineseRemainder hmn).symm (x.a, y.a)
        rw [map_mul]
        rw [← show (ZMod.chineseRemainder hmn).symm ((u₁ : ZMod m), (u₂ : ZMod n)) =
          (u : ZMod (m * n)) by rfl]
  · calc
      (col_crt_mk hmn x' y').b = (ZMod.chineseRemainder hmn).symm (x'.b, y'.b) := rfl
      _ = (ZMod.chineseRemainder hmn).symm (((u₁ : ZMod m) * x.b), ((u₂ : ZMod n) * y.b)) := by
        rw [hu₁2, hu₂2]
      _ = (u : ZMod (m * n)) * (col_crt_mk hmn x y).b := by
        change (ZMod.chineseRemainder hmn).symm (((u₁ : ZMod m), (u₂ : ZMod n)) * (x.b, y.b)) =
          (u : ZMod (m * n)) * (ZMod.chineseRemainder hmn).symm (x.b, y.b)
        rw [map_mul]
        rw [← show (ZMod.chineseRemainder hmn).symm ((u₁ : ZMod m), (u₂ : ZMod n)) =
          (u : ZMod (m * n)) by rfl]

noncomputable def P1_mul_to_prod {m n : ℕ} (hmn : m.Coprime n) : P1 (m * n) → P1 m × P1 n :=
  Quotient.lift (fun x : CoprimeCol (m * n) =>
    ((Quotient.mk (projSetoid m) (col_crt_fst hmn x) : P1 m),
     (Quotient.mk (projSetoid n) (col_crt_snd hmn x) : P1 n)))
    (by
      intro x y hxy
      apply Prod.ext
      · exact Quotient.sound (col_crt_fst_projRel hmn hxy)
      · exact Quotient.sound (col_crt_snd_projRel hmn hxy))

lemma P1_mul_to_prod_mk {m n : ℕ} (hmn : m.Coprime n) (w : CoprimeCol (m * n)) :
    P1_mul_to_prod hmn (Quotient.mk (projSetoid (m * n)) w) =
      (Quotient.mk (projSetoid m) (col_crt_fst hmn w), Quotient.mk (projSetoid n) (col_crt_snd hmn w)) := by
  unfold P1_mul_to_prod
  rfl

noncomputable def P1_prod_to_mul {m n : ℕ} (hmn : m.Coprime n) : P1 m × P1 n → P1 (m * n) :=
  fun p =>
    (Quotient.lift (fun x : CoprimeCol m => Quotient.lift
        (fun y : CoprimeCol n => (Quotient.mk (projSetoid (m * n)) (col_crt_mk hmn x y) : P1 (m * n)))
        (by
          intro y y' hyy'
          exact Quotient.sound (col_crt_mk_projRel hmn (projRel_refl m x) hyy')))
      (by
        intro x x' hxx'
        funext y
        refine Quotient.inductionOn y ?_
        intro y0
        simp
        exact Quotient.sound (col_crt_mk_projRel hmn hxx' (projRel_refl n y0))) p.1) p.2

lemma P1_prod_to_mul_mk {m n : ℕ} (hmn : m.Coprime n) (x : CoprimeCol m) (y : CoprimeCol n) :
    P1_prod_to_mul hmn (Quotient.mk (projSetoid m) x, Quotient.mk (projSetoid n) y) =
      Quotient.mk (projSetoid (m * n)) (col_crt_mk hmn x y) := by
  unfold P1_prod_to_mul
  rfl

noncomputable def P1_mul_equiv_prod (m n : ℕ) (hmn : m.Coprime n) : P1 (m * n) ≃ P1 m × P1 n where
  toFun := P1_mul_to_prod hmn
  invFun := P1_prod_to_mul hmn
  left_inv := by
    intro z
    refine Quotient.inductionOn z ?_
    intro w
    exact congrArg (P1_prod_to_mul hmn) (P1_mul_to_prod_mk hmn w) |>.trans
      (P1_prod_to_mul_mk hmn (col_crt_fst hmn w) (col_crt_snd hmn w)) |>.trans
      (congrArg (Quotient.mk (projSetoid (m * n))) (col_crt_mk_fst_snd hmn w))
  right_inv := by
    intro p
    rcases p with ⟨q1, q2⟩
    refine Quotient.inductionOn q1 ?_
    intro x
    refine Quotient.inductionOn q2 ?_
    intro y
    exact congrArg (P1_mul_to_prod hmn) (P1_prod_to_mul_mk hmn x y) |>.trans
      (P1_mul_to_prod_mk hmn (col_crt_mk hmn x y)) |>.trans
      (by
        rw [col_crt_fst_mk, col_crt_snd_mk]
        rfl)

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
