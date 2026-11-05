import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Set.Basic

/-! # Challenge_007 — F₂ 悖论分解（空间 ⇒ 球悖论核心：Banach–Tarski） -/

namespace Challenge007

abbrev F2 := FreeGroup Bool

abbrev a : F2 := FreeGroup.of true

abbrev b : F2 := FreeGroup.of false

def startsWith (s : Bool × Bool) (x : F2) : Prop :=
  x.toWord.head? = some s

def W : Set F2 := {x | startsWith (true, true) x}
def X : Set F2 := {x | startsWith (true, false) x}
def Y : Set F2 := {x | startsWith (false, true) x}
def Z : Set F2 := {x | startsWith (false, false) x}

def aX : Set F2 := {x | ∃ y ∈ X, x = a * y}
def bZ : Set F2 := {x | ∃ y ∈ Z, x = b * y}

theorem of_true_ne_one : (FreeGroup.of true : F2) ≠ 1 :=
  FreeGroup.of_ne_one true

theorem of_false_ne_one : (FreeGroup.of false : F2) ≠ 1 :=
  FreeGroup.of_ne_one false

theorem inv_of_true_ne_one : (a : F2)⁻¹ ≠ 1 := by
  intro h
  have h2 : ((a : F2)⁻¹)⁻¹ = (1 : F2)⁻¹ := congrArg (fun z : F2 => z⁻¹) h
  have h3 : a = 1 := by
    rwa [inv_inv, inv_one] at h2
  exact of_true_ne_one h3

theorem inv_of_false_ne_one : (b : F2)⁻¹ ≠ 1 := by
  intro h
  have h2 : ((b : F2)⁻¹)⁻¹ = (1 : F2)⁻¹ := congrArg (fun z : F2 => z⁻¹) h
  have h3 : b = 1 := by
    rwa [inv_inv, inv_one] at h2
  exact of_false_ne_one h3

theorem head?_of_ne_one {x : F2} (h : x ≠ 1) : ∃ s : Bool × Bool, x.toWord.head? = some s := by
  cases hxword : x.toWord with
  | nil =>
      exfalso
      exact h (FreeGroup.toWord_eq_nil_iff.mp hxword)
  | cons s t => exact ⟨s, rfl⟩

theorem partition_cover (x : F2) : x = 1 ∨ x ∈ W ∨ x ∈ X ∨ x ∈ Y ∨ x ∈ Z := by
  by_cases h1 : x = 1
  · exact Or.inl h1
  · right
    by_cases hW : x ∈ W
    · exact Or.inl hW
    · by_cases hX : x ∈ X
      · exact Or.inr (Or.inl hX)
      · by_cases hY : x ∈ Y
        · exact Or.inr (Or.inr (Or.inl hY))
        · rcases head?_of_ne_one h1 with ⟨s, hs⟩
          rcases s with ⟨b1, b2⟩
          cases b1 with
          | false =>
              cases b2 with
              | false =>
                  exact Or.inr (Or.inr (Or.inr (by simpa [Z, startsWith] using hs)))
              | true =>
                  exfalso
                  apply hY
                  simpa [Y, startsWith] using hs
          | true =>
              cases b2 with
              | false =>
                  exfalso
                  apply hX
                  simpa [X, startsWith] using hs
              | true =>
                  exfalso
                  apply hW
                  simpa [W, startsWith] using hs

theorem disjoint_startsWith {s t : Bool × Bool} (hst : s ≠ t) :
    Disjoint {x : F2 | startsWith s x} {x : F2 | startsWith t x} := by
  rw [Set.disjoint_iff]
  rintro x hxs
  rcases hxs with ⟨hxs, hxt⟩
  change startsWith s x at hxs
  change startsWith t x at hxt
  unfold startsWith at hxs hxt
  rw [hxt] at hxs
  injection hxs with hst'
  exact hst hst'.symm

theorem disjoint_W_X : Disjoint W X := by
  simpa [W, X] using (disjoint_startsWith (s := (true, true)) (t := (true, false)) (by decide))

theorem disjoint_W_Y : Disjoint W Y := by
  simpa [W, Y] using (disjoint_startsWith (s := (true, true)) (t := (false, true)) (by decide))

theorem disjoint_W_Z : Disjoint W Z := by
  simpa [W, Z] using (disjoint_startsWith (s := (true, true)) (t := (false, false)) (by decide))

theorem disjoint_X_Y : Disjoint X Y := by
  simpa [X, Y] using (disjoint_startsWith (s := (true, false)) (t := (false, true)) (by decide))

theorem disjoint_X_Z : Disjoint X Z := by
  simpa [X, Z] using (disjoint_startsWith (s := (true, false)) (t := (false, false)) (by decide))

theorem disjoint_Y_Z : Disjoint Y Z := by
  simpa [Y, Z] using (disjoint_startsWith (s := (false, true)) (t := (false, false)) (by decide))

theorem disjoint_one_W : Disjoint ({1} : Set F2) W := by
  rw [Set.disjoint_iff]
  rintro x hx
  rcases hx with ⟨hx1, hxW⟩
  rw [Set.mem_singleton_iff] at hx1
  change startsWith (true, true) x at hxW
  rw [hx1] at hxW
  unfold startsWith at hxW
  rw [FreeGroup.toWord_one] at hxW
  simp at hxW

theorem disjoint_one_X : Disjoint ({1} : Set F2) X := by
  rw [Set.disjoint_iff]
  rintro x hx
  rcases hx with ⟨hx1, hxX⟩
  rw [Set.mem_singleton_iff] at hx1
  change startsWith (true, false) x at hxX
  rw [hx1] at hxX
  unfold startsWith at hxX
  rw [FreeGroup.toWord_one] at hxX
  simp at hxX

theorem disjoint_one_Y : Disjoint ({1} : Set F2) Y := by
  rw [Set.disjoint_iff]
  rintro x hx
  rcases hx with ⟨hx1, hxY⟩
  rw [Set.mem_singleton_iff] at hx1
  change startsWith (false, true) x at hxY
  rw [hx1] at hxY
  unfold startsWith at hxY
  rw [FreeGroup.toWord_one] at hxY
  simp at hxY

theorem disjoint_one_Z : Disjoint ({1} : Set F2) Z := by
  rw [Set.disjoint_iff]
  rintro x hx
  rcases hx with ⟨hx1, hxZ⟩
  rw [Set.mem_singleton_iff] at hx1
  change startsWith (false, false) x at hxZ
  rw [hx1] at hxZ
  unfold startsWith at hxZ
  rw [FreeGroup.toWord_one] at hxZ
  simp at hxZ

theorem union_W_aX (x : F2) : x ∈ W ∨ x ∈ aX := by
  by_cases hW : x ∈ W
  · exact Or.inl hW
  · right
    refine ⟨a⁻¹ * x, ?memX, ?eq⟩
    · change (a⁻¹ * x).toWord.head? = some (true, false)
      have hnot : x.toWord.head? ≠ some (true, true) := by
        intro hh
        exact hW hh
      have htm := FreeGroup.toWord_mk_mul_eq true false x
      change ((FreeGroup.of true : F2)⁻¹ * x).toWord.head? = some (true, false)
      rw [FreeGroup.of, FreeGroup.inv_mk]
      simp [FreeGroup.invRev]
      rw [htm]
      simp [hnot]
    · rw [← mul_assoc, mul_inv_cancel, one_mul]

theorem disjoint_W_aX : Disjoint W aX := by
  rw [Set.disjoint_iff]
  rintro x hx
  rcases hx with ⟨hWx, haXx⟩
  rcases haXx with ⟨y, hYx, hxy⟩
  change startsWith (true, true) x at hWx
  change startsWith (true, false) y at hYx
  unfold startsWith at hWx hYx
  have htm := FreeGroup.toWord_mk_mul_eq true true y
  have hcalc : (a * y).toWord = y.toWord.tail := by
    change ((FreeGroup.of true : F2) * y).toWord = y.toWord.tail
    rw [FreeGroup.of, htm]
    rw [show (FreeGroup.toWord y).head? = some (true, !true) from by simpa using hYx]
    simp
  have hxw : x.toWord = y.toWord.tail := by
    rw [hxy, hcalc]
  have htw : y.toWord.tail.head? = some (true, true) := by
    rw [← hxw]
    exact hWx
  have hyn : y.toWord ≠ [] := by
    intro h
    rw [h] at hYx
    cases hYx
  have hword : y.toWord = (true, false) :: y.toWord.tail := by
    cases hlist : y.toWord with
    | nil => exact (hyn hlist).elim
    | cons s t =>
        rw [hlist] at hYx
        simp only [List.head?_cons] at hYx
        injection hYx with hs
        simp [hs]
  have htwne : y.toWord.tail ≠ [] := by
    intro h
    rw [h] at htw
    cases htw
  have htailword : y.toWord.tail = (true, true) :: y.toWord.tail.tail := by
    cases hlist2 : y.toWord.tail with
    | nil => exact (htwne hlist2).elim
    | cons s2 t2 =>
        rw [hlist2] at htw
        simp only [List.head?_cons] at htw
        injection htw with hs2
        simp [hs2]
  have hfull : y.toWord = (true, false) :: (true, true) :: y.toWord.tail.tail := by
    calc
      y.toWord = (true, false) :: y.toWord.tail := hword
      _ = (true, false) :: (true, true) :: y.toWord.tail.tail := by
        exact congrArg (List.cons (true, false)) htailword
  have hstep : FreeGroup.Red.Step y.toWord y.toWord.tail.tail := by
    rw [hfull]
    exact FreeGroup.Red.Step.cons_not (x := true) (b := false) (L := y.toWord.tail.tail)
  exact (FreeGroup.IsReduced.not_step (FreeGroup.isReduced_toWord (x := y)) hstep).elim

theorem union_Y_bZ (x : F2) : x ∈ Y ∨ x ∈ bZ := by
  by_cases hY : x ∈ Y
  · exact Or.inl hY
  · right
    refine ⟨b⁻¹ * x, ?memZ, ?eq⟩
    · change (b⁻¹ * x).toWord.head? = some (false, false)
      have hnot : x.toWord.head? ≠ some (false, true) := by
        intro hh
        exact hY hh
      have htm := FreeGroup.toWord_mk_mul_eq false false x
      change ((FreeGroup.of false : F2)⁻¹ * x).toWord.head? = some (false, false)
      rw [FreeGroup.of, FreeGroup.inv_mk]
      simp [FreeGroup.invRev]
      rw [htm]
      simp [hnot]
    · rw [← mul_assoc, mul_inv_cancel, one_mul]

theorem disjoint_Y_bZ : Disjoint Y bZ := by
  rw [Set.disjoint_iff]
  rintro x hx
  rcases hx with ⟨hYx, hbZx⟩
  rcases hbZx with ⟨y, hZy, hxy⟩
  change startsWith (false, true) x at hYx
  change startsWith (false, false) y at hZy
  unfold startsWith at hYx hZy
  have htm := FreeGroup.toWord_mk_mul_eq false true y
  have hcalc : (b * y).toWord = y.toWord.tail := by
    change ((FreeGroup.of false : F2) * y).toWord = y.toWord.tail
    rw [FreeGroup.of, htm]
    rw [show (FreeGroup.toWord y).head? = some (false, !true) from by simpa using hZy]
    simp
  have hxw : x.toWord = y.toWord.tail := by
    rw [hxy, hcalc]
  have htw : y.toWord.tail.head? = some (false, true) := by
    rw [← hxw]
    exact hYx
  have hyn : y.toWord ≠ [] := by
    intro h
    rw [h] at hZy
    cases hZy
  have hword : y.toWord = (false, false) :: y.toWord.tail := by
    cases hlist : y.toWord with
    | nil => exact (hyn hlist).elim
    | cons s t =>
        rw [hlist] at hZy
        simp only [List.head?_cons] at hZy
        injection hZy with hs
        simp [hs]
  have htwne : y.toWord.tail ≠ [] := by
    intro h
    rw [h] at htw
    cases htw
  have htailword : y.toWord.tail = (false, true) :: y.toWord.tail.tail := by
    cases hlist2 : y.toWord.tail with
    | nil => exact (htwne hlist2).elim
    | cons s2 t2 =>
        rw [hlist2] at htw
        simp only [List.head?_cons] at htw
        injection htw with hs2
        simp [hs2]
  have hfull : y.toWord = (false, false) :: (false, true) :: y.toWord.tail.tail := by
    calc
      y.toWord = (false, false) :: y.toWord.tail := hword
      _ = (false, false) :: (false, true) :: y.toWord.tail.tail := by
        exact congrArg (List.cons (false, false)) htailword
  have hstep : FreeGroup.Red.Step y.toWord y.toWord.tail.tail := by
    rw [hfull]
    exact FreeGroup.Red.Step.cons_not (x := false) (b := false) (L := y.toWord.tail.tail)
  exact (FreeGroup.IsReduced.not_step (FreeGroup.isReduced_toWord (x := y)) hstep).elim

theorem F2_paradoxical_decomposition :
    (∀ x : F2, x = 1 ∨ x ∈ W ∨ x ∈ X ∨ x ∈ Y ∨ x ∈ Z) ∧
    Disjoint W X ∧ Disjoint W Y ∧ Disjoint W Z ∧
    Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
    Disjoint ({1} : Set F2) W ∧ Disjoint ({1} : Set F2) X ∧
    Disjoint ({1} : Set F2) Y ∧ Disjoint ({1} : Set F2) Z ∧
    (∀ x : F2, x ∈ W ∨ x ∈ aX) ∧ Disjoint W aX ∧
    (∀ x : F2, x ∈ Y ∨ x ∈ bZ) ∧ Disjoint Y bZ := by
  exact ⟨partition_cover, disjoint_W_X, disjoint_W_Y, disjoint_W_Z,
    disjoint_X_Y, disjoint_X_Z, disjoint_Y_Z,
    disjoint_one_W, disjoint_one_X, disjoint_one_Y, disjoint_one_Z,
    union_W_aX, disjoint_W_aX, union_Y_bZ, disjoint_Y_bZ⟩

#check F2_paradoxical_decomposition

end Challenge007

#print axioms Challenge007.F2_paradoxical_decomposition
#print axioms Challenge007.union_W_aX
#print axioms Challenge007.disjoint_W_aX
#print axioms Challenge007.partition_cover
