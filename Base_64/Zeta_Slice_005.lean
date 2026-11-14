import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Slice 005 : The Dirichlet eta function and the Riemann zeta function

We verify the classical functional relation, valid for `Re s > 1`,

    eta (s) = (1 - 2 ^ (1 - s)) * zeta (s),

where `eta` is the alternating series with terms `(-1)^n / (n+1)^s` and
`zeta` is the Riemann zeta function.

All statements are derived from existing mathlib lemmas; no axioms are
introduced and no `sorry` is used.
-/

noncomputable section

namespace Slice005

/-- The Dirichlet eta function, defined by the alternating series
`sum (-1)^n / (n+1)^s`. -/
def dirichletEta (s : Complex) : Complex :=
  tsum (fun n : Nat => (-1 : Complex) ^ n / (n + 1 : Complex) ^ s)

lemma summable_shift {s : Complex} (hs : 1 < s.re) :
    Summable (fun n : Nat => 1 / (n + 1 : Complex) ^ s) := by
  have h0 : Summable (fun n : Nat => 1 / (n : Complex) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  simpa [Nat.cast_add] using ((summable_nat_add_iff 1 (G := Complex)).mpr h0)

lemma summable_alt {s : Complex} (hs : 1 < s.re) :
    Summable (fun n : Nat => (-1 : Complex) ^ n / (n + 1 : Complex) ^ s) := by
  have hnorm : Summable (fun n : Nat => norm (1 / (n + 1 : Complex) ^ s)) := by
    exact (summable_norm_iff.mpr (summable_shift hs))
  refine Summable.of_norm_bounded hnorm ?_
  intro n
  rw [norm_div, norm_div, norm_pow]
  norm_num

/-- Splitting an alternating series into its even/odd parts:
`sum (-1)^n * f n = sum f n - 2 * sum f (2k+1)`, for a summable family `f`. -/
lemma tsum_alt_split {f : Nat -> Complex} (hf : Summable (fun n : Nat => norm (f n))) :
    (tsum (fun n : Nat => (-1 : Complex) ^ n * f n)) =
      tsum (fun n : Nat => f n) - 2 * tsum (fun n : Nat => f (2 * n + 1)) := by
  have hdecomp : (fun n : Nat => (-1 : Complex) ^ n * f n) =
      fun n : Nat => f n - 2 * (if Odd n then f n else 0) := by
    funext n
    by_cases hn : Odd n
    . rw [if_pos hn]
      rw [Odd.neg_one_pow hn]
      ring
    . rw [if_neg hn]
      have he : Even n := Nat.not_odd_iff_even.mp hn
      rw [Even.neg_one_pow he]
      ring
  rw [hdecomp]
  have hadd : (fun n : Nat => f n - 2 * (if Odd n then f n else 0)) =
      fun n : Nat => f n + (-2 : Complex) * (if Odd n then f n else 0) := by
    funext n
    ring
  rw [hadd]
  have hf_s : Summable (fun n : Nat => f n) := (summable_norm_iff.mp hf)
  have hite : Summable (fun n : Nat => (if Odd n then f n else 0)) := by
    refine Summable.of_norm_bounded hf ?_
    intro n
    by_cases hn : Odd n
    . rw [if_pos hn]
    . rw [if_neg hn]
      simp
  have hg : Summable (fun n : Nat => (-2 : Complex) * (if Odd n then f n else 0)) :=
    Summable.mul_left (-2) hite
  rw [Summable.tsum_add hf_s hg]
  rw [tsum_mul_left]
  have hsub : (tsum (fun n : Nat => if Odd n then f n else 0)) =
      tsum (fun k : Nat => f (2 * k + 1)) := by
    let e : Equiv Nat ({n : Nat | Odd n} : Set Nat) :=
      { toFun := fun k => { val := 2 * k + 1, property := Exists.intro k rfl },
        invFun := fun x => (x.val - 1) / 2,
        left_inv := by
          intro k
          dsimp
          rw [show 2 * k = k * 2 by omega]
          rw [Nat.mul_div_left k (by decide : 0 < 2)]
        right_inv := by
          intro x
          match x.property with
          | Exists.intro k hk =>
              dsimp
              apply Subtype.ext
              rw [hk]
              rw [show 2 * k + 1 - 1 = 2 * k by omega]
              conv_lhs => rw [show 2 * k = k * 2 by omega]
              rw [Nat.mul_div_left k (by decide : 0 < 2)] }
    calc
      (tsum (fun n : Nat => if Odd n then f n else 0))
          = tsum (fun n : Nat => ({n : Nat | Odd n} : Set Nat).indicator f n) := by
              congr 1
              funext n
              by_cases h : Odd n
              case pos => simp [h, Set.mem_setOf_eq]
              case neg => simp [h, Set.mem_setOf_eq]
      _ = tsum (fun x : ({n : Nat | Odd n} : Set Nat) => f x) := by
              simpa using (tsum_subtype {n : Nat | Odd n} f).symm
      _ = tsum (fun k : Nat => f (2 * k + 1)) := by
              simpa [e] using (Equiv.tsum_eq e (fun x : ({n : Nat | Odd n} : Set Nat) => f x)).symm
  rw [hsub]
  ring

/-- The Riemann zeta function on the half-plane `Re s > 1` is the Dirichlet series
`sum 1 / (n+1)^s`. -/
lemma zeta_shift_eq {s : Complex} (hs : 1 < s.re) :
    (tsum (fun n : Nat => 1 / (n + 1 : Complex) ^ s)) = riemannZeta s := by
  exact (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm

/-- `eta (s) = (1 - 2 ^ (1 - s)) * zeta (s)` for `Re s > 1`. -/
theorem eta_eq_one_sub_two_zeta {s : Complex} (hs : 1 < s.re) :
    dirichletEta s = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  unfold dirichletEta
  have hzeta_eq : (tsum (fun n : Nat => 1 / (n + 1 : Complex) ^ s)) =
      riemannZeta s := zeta_shift_eq hs
  have hnorm : Summable (fun n : Nat => norm (1 / (n + 1 : Complex) ^ s)) := by
    exact (summable_norm_iff.mpr (summable_shift hs))
  have hsplit := tsum_alt_split (f := fun n : Nat => 1 / (n + 1 : Complex) ^ s) hnorm
  have hodd : (tsum (fun k : Nat => 1 / (2 * k + 2 : Complex) ^ s)) =
      (2 : Complex) ^ (-s) * (tsum (fun k : Nat => 1 / (k + 1 : Complex) ^ s)) := by
    calc
      (tsum (fun k : Nat => 1 / (2 * k + 2 : Complex) ^ s))
          = tsum (fun k : Nat => (2 : Complex) ^ (-s) * (1 / (k + 1 : Complex) ^ s)) := by
              apply tsum_congr
              intro k
              have hk2 : (2 * k + 2 : Complex) = (2 : Complex) * (k + 1 : Complex) := by
                ring
              rw [hk2]
              have hmul : ((2 : Complex) * (k + 1 : Complex)) ^ s =
                  (2 : Complex) ^ s * ((k + 1 : Complex) ^ s) := by
                simpa [← Nat.cast_mul] using (Complex.natCast_mul_natCast_cpow 2 (k + 1) s)
              rw [hmul]
              rw [Complex.cpow_neg]
              simp [div_eq_mul_inv, mul_comm, mul_left_comm]
      _ = (2 : Complex) ^ (-s) * (tsum (fun k : Nat => 1 / (k + 1 : Complex) ^ s)) := by
              exact tsum_mul_left
  have h2 : (2 : Complex) ^ (1 - s) = (2 : Complex) * (2 : Complex) ^ (-s) := by
    calc
      (2 : Complex) ^ (1 - s) = (2 : Complex) ^ (1 + (-s)) := by
              rw [← sub_eq_add_neg]
      _ = (2 : Complex) ^ 1 * (2 : Complex) ^ (-s) :=
              Complex.cpow_add (1 : Complex) (-s) (by norm_num : Ne (2 : Complex) 0)
      _ = (2 : Complex) * (2 : Complex) ^ (-s) := by
              simp
  calc
    (tsum (fun n : Nat => (-1 : Complex) ^ n / (n + 1 : Complex) ^ s))
        = tsum (fun n : Nat => (-1 : Complex) ^ n * (1 / (n + 1 : Complex) ^ s)) := by
            apply tsum_congr
            intro n
            rw [div_eq_mul_one_div]
    _ = tsum (fun n : Nat => 1 / (n + 1 : Complex) ^ s)
        - 2 * tsum (fun k : Nat => 1 / (2 * k + 2 : Complex) ^ s) := by
            rw [hsplit]
            congr 1
            congr 1
            apply tsum_congr
            intro k
            congr 1
            congr 1
            norm_cast
    _ = tsum (fun n : Nat => 1 / (n + 1 : Complex) ^ s)
        - 2 * ((2 : Complex) ^ (-s) * (tsum (fun k : Nat => 1 / (k + 1 : Complex) ^ s))) := by
            rw [hodd]
    _ = (1 - 2 * (2 : Complex) ^ (-s)) * (tsum (fun n : Nat => 1 / (n + 1 : Complex) ^ s)) := by
            ring
    _ = (1 - 2 ^ (1 - s)) * riemannZeta s := by
            rw [hzeta_eq]
            congr 1
            rw [h2]

end Slice005
