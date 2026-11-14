/-
# Erdős Problem 91: distinct distances, uniqueness of the minimiser

Source: `FormalConjectures/ErdosProblems/91.lean` (`erdos_91.variants.eight`,
`erdos_91.variants.nine`; both `sorry` upstream, marked research-solved).

Reference: github.com/linrock/math-proofs, `erdos-91/` (Solution.lean and Proofs/*.lean,
rev cd3cf0b).

Write `d n` for the minimal number of distinct distances determined by a planar set of
`n` points, and call a set *optimal* if it attains `d n`.  A set is the unique
minimiser when every optimal set for `n` is similar to it.  Both upstream variants
assert the failure of uniqueness, one for `n = 8` and one for `n = 9`, and both
arguments in the reference pass through the localisation of `d 8` and `d 9`; there
they are conditional (`4 ≤ d 9 → ¬ UniqueMinimizer 9`, `d 9 = 3 → ¬ UniqueMinimizer 8`).

This file formalises the layer that is independent of the actual values of `d 8` and
`d 9`: the distance-set and minimiser vocabulary matching the upstream signatures, and
the abstract lemmas on which every such reduction rests — `d n ≤ k` from an explicit
witness, monotonicity of `d` under removing points, and the equivalence turning
`¬ UniqueMinimizer n` into a pair of non-similar optimal sets.  The two explicit
configurations of the reference (`triangularNine`, `regularNonagon`) are not reproduced
here, so `d 9 ≤ 4` and `4 ≤ d 9` are both left open rather than axiomatised, and no
claim below depends on them.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.DilationEquiv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section

namespace ChenGuang.Erdos91

/-- The plane, taken as `ℂ` (isometric to `EuclideanSpace ℝ (Fin 2)`); complex
coordinates keep the explicit constructions short. -/
abbrev Plane := ℂ

/-- The set of distances occurring between distinct points of `points`. -/
def distanceSet {X : Type*} [PseudoMetricSpace X] (points : Finset X) : Finset ℝ :=
  points.offDiag.image (fun p : X × X => dist p.1 p.2)

/-- Number of distinct distances determined by `points`. -/
def distinctDistances {X : Type*} [PseudoMetricSpace X] (points : Finset X) : ℕ :=
  (distanceSet points).card

/-- The minimum number of distinct distances determined by an `n`-point set. -/
def minimalDistinctDistances (X : Type*) [PseudoMetricSpace X] (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, points.card = n ∧ distinctDistances points = m}

/-- `A` is optimal for `n`: it has `n` points and the minimum possible number of
distinct distances. -/
def IsOptimal (A : Finset Plane) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances Plane n

/-- Two point sets are similar if some isometry equivalence of the plane carries
one onto the other (the upstream `DilationEquivSimilar`). -/
def DilationEquivSimilar (A B : Finset Plane) : Prop :=
  ∃ f : Plane ≃ᵈ Plane, (f '' (A : Set Plane)) = (B : Set Plane)

/-- `n` has a unique minimising configuration up to similarity. -/
def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset Plane, IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

/-! ## Abstract lemmas used by the reduction -/

/-- A concrete `n`-point set determining at most `k` distinct distances bounds `d n`
from above.  This is the only way `minimalDistinctDistances` ever receives an upper
bound: the bound is carried by a real witness, never by an assumption. -/
theorem minimalDistinctDistances_le_of_witness {X : Type*} [PseudoMetricSpace X]
    (A : Finset X) (n k : ℕ) (hA : A.card = n) (hk : distinctDistances A ≤ k) :
    minimalDistinctDistances X n ≤ k :=
  (Nat.sInf_le (show ∃ points : Finset X,
      points.card = n ∧ distinctDistances points = distinctDistances A from ⟨A, hA, rfl⟩)).trans hk

/-- Deleting points never increases the number of distinct distances. -/
theorem distinctDistances_mono {X : Type*} [PseudoMetricSpace X]
    {A B : Finset X} (h : B ⊆ A) : distinctDistances B ≤ distinctDistances A := by
  refine Finset.card_le_card ?_
  intro d hd
  rw [distanceSet, Finset.mem_image] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  rw [distanceSet, Finset.mem_image]
  refine ⟨p, ?_, rfl⟩
  rw [Finset.mem_offDiag] at hp ⊢
  exact ⟨h hp.1, h hp.2.1, hp.2.2⟩

/-- Monotonicity of `d`: an optimal `m`-point configuration witnesses `d n ≤ d m` for
every `n ≤ m`, since deleting `m - n` points leaves an `n`-point set that determines no
more distances. -/
theorem minimalDistinctDistances_monotone_of_witness {X : Type*} [PseudoMetricSpace X]
    (A : Finset X) {n m : ℕ} (hA : A.card = m)
    (hopt : distinctDistances A = minimalDistinctDistances X m) (hn : n ≤ m) :
    minimalDistinctDistances X n ≤ minimalDistinctDistances X m := by
  obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq (s := A) (by omega : n ≤ A.card)
  rw [← hopt]
  exact (minimalDistinctDistances_le_of_witness B n (distinctDistances B) hBcard le_rfl).trans
    (distinctDistances_mono hBA)

/-- Failure of uniqueness, in witness form: two optimal configurations that are not
similar.  This is the exact shape of `variants.eight` and `variants.nine`, and the shape
in which the reference proofs conclude. -/
theorem not_uniqueMinimizer_iff (n : ℕ) :
    ¬ UniqueMinimizer n ↔
      ∃ A B : Finset Plane,
        IsOptimal A n ∧ IsOptimal B n ∧ ¬ DilationEquivSimilar A B := by
  constructor
  · intro h
    by_contra hc
    exact h fun A B hA hB => by_contra fun hAB => hc ⟨A, B, hA, hB, hAB⟩
  · rintro ⟨A, B, hA, hB, hAB⟩ hU
    exact hAB (hU A B hA hB)

/-- A single point determines no distances, so `d 1 = 0`. -/
theorem minimalDistinctDistances_one : minimalDistinctDistances Plane 1 = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine minimalDistinctDistances_le_of_witness (A := ({0} : Finset Plane)) 1 0 ?_ ?_
  · simp
  · simp [distinctDistances, distanceSet]

end ChenGuang.Erdos91

/-! ## Axiom audit -/

#print axioms ChenGuang.Erdos91.minimalDistinctDistances_one
#print axioms ChenGuang.Erdos91.not_uniqueMinimizer_iff
