import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Challenge_021A — Γ₀(N) 与投影线模型 P¹(N)（ChenGuang Studio）

本切片承载 **几何/群论底座**：
* `gamma0_N` 子群定义与成员判据；
* 生成元 `R`/`T` 及其在 `10` 列上的作用；
* 投影线模型 `CoprimeCol N`、等价关系 `ProjRel`、商类型 `P1 N`；
* `Γ₀(N) ⧸ Γ₀(N)` 与 `P1 N` 的双射 `gamma0_coset_equiv_P1`；
* `P1` 的 CRT 乘性分解 `P1_mul_equiv_prod`。
-/

set_option linter.unnecessarySimpa false

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup QuotientGroup

namespace Challenge021Gamma0NIndex


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


end Challenge021Gamma0NIndex
