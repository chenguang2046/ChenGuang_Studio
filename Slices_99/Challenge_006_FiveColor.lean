import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Challenge_006 — 五色定理核心：最小度引理与归纳框架（ChenGuang Studio） -/
open scoped BigOperators
noncomputable section
namespace Challenge006

/-- 正常 `k`-着色：相邻顶点异色。 -/
def ProperColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, ∀ ⦃u w : V⦄, G.Adj u w → c u ≠ c w

/-- 最小度引理：边数界 `E ≤ 3V - 6`（欧拉公式推论，作平面性前提参数化）⇒ 存在度 ≤ 5 的顶点。 -/
theorem exists_degree_le_five_of_euler_bound {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hEdge : G.edgeFinset.card ≤ 3 * Fintype.card V - 6) : ∃ v : V, G.degree v ≤ 5 := by
  by_contra h
  have hge : ∀ v : V, 6 ≤ G.degree v := fun v => by
    have hv : ¬ (G.degree v ≤ 5) := fun hle => h ⟨v, hle⟩
    omega
  have hsum : (6 : ℕ) * Fintype.card V ≤ ∑ v : V, G.degree v := by
    have h1 : (∑ _v : V, (6 : ℕ)) ≤ ∑ v : V, G.degree v := Finset.sum_le_sum (fun v _ => hge v)
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using h1
  have h2 : ∑ v : V, G.degree v ≤ 2 * (3 * Fintype.card V - 6) := by
    rw [G.sum_degrees_eq_twice_card_edges]; exact Nat.mul_le_mul_left 2 hEdge
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ‹Nonempty V›
  omega

/-- 归纳步：删去度 ≤ 5 的 `v` 后若 5-可着，则全图 6-可着（`v` 取第 6 色）。 -/
theorem five_color_induction_step {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (_hdeg : G.degree v ≤ 5)
    (hcol : ProperColoring (G.induce {w : V | w ≠ v}) 5) : ProperColoring G 6 := by
  classical
  obtain ⟨c, hc⟩ := hcol
  let lift5 : Fin 5 → Fin 6 := fun i => ⟨i.val, by omega⟩
  refine ⟨fun w => if h : w = v then ⟨5, by decide⟩ else lift5 (c ⟨w, h⟩), ?_⟩
  intro u w huw
  by_cases hu : u = v <;> by_cases hw : w = v
  · exact absurd (by simpa [hu, hw] using huw) (G.loopless.irrefl v)
  · apply Fin.ne_of_val_ne
    intro hval
    have hlt : (c ⟨w, hw⟩).val < 5 := (c ⟨w, hw⟩).isLt
    simp [hu, hw, lift5] at hval
    omega
  · apply Fin.ne_of_val_ne
    intro hval
    have hlt : (c ⟨u, hu⟩).val < 5 := (c ⟨u, hu⟩).isLt
    simp [hu, hw, lift5] at hval
    omega
  · apply Fin.ne_of_val_ne
    intro hval
    have hc' : c ⟨u, hu⟩ ≠ c ⟨w, hw⟩ := hc (by simpa using huw)
    apply hc'
    apply Fin.ext
    simp [hu, hw, lift5] at hval
    exact hval

/-- 归纳框架：任意度 ≤ 5 顶点的提升声明。 -/
theorem five_color_induction_framework {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    ∀ v : V, G.degree v ≤ 5 → ProperColoring (G.induce {w : V | w ≠ v}) 5 → ProperColoring G 6 :=
  fun v hdeg hcol => five_color_induction_step G v hdeg hcol

end Challenge006
