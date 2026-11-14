/-
Riemann_Slice_001.lean
======================

Formal verification slice (Slice 001) for the Euler product formula
of the Riemann zeta function, in Lean 4.

Standard form under verification:
    zeta(s) = prod over primes p of (1 - p^(-s))^(-1)

The task sheet writes this concisely as "prod_p (1/p^s)"; following
the agreed convention we interpret it as the standard Euler product
written above.  A finite truncation of the geometric series expansion
is the algebraic core verified in this slice.

Scope of this slice (finite truncated algebraic identities only):
  A. (1 - x) * (1 + x + x^2 + ... + x^D) = 1 - x^(D+1)
     (truncated geometric series identity)
  B. coefficient convolution for the product of two truncated
     geometric polynomials:
        coeff_k (geoPoly D * geoPoly D)
          = #{ (i,j) in [0,D]^2 : i + j = k }
     (lattice-point counting interpretation)
  C. numerical instances for the primes {2,3,5}:
        sum over (a,b,c) in {0,1,2}^3 of
          2^(2(2-a)) * 3^(2(2-b)) * 5^(2(2-c))  =  21 * 91 * 651
     and the merged-coefficient expansion
        (1 + x + x^2)^3 = [1, 3, 6, 7, 6, 3, 1]

Sensitive topics (analytic continuation, zero distribution, and
convergence of the infinite product) are deliberately OUT OF SCOPE
for this slice and are not addressed.

Environment note: the local mathlib checkout on this machine is
incomplete (several build artifacts are missing), so this file uses
only the Lean 4 Init library.  A separate gap report accompanies
this file (see the delivery report).
-/

namespace EulerProduct

-- ------------------------------------------------------------------
-- 1. Definitions
-- ------------------------------------------------------------------

-- coeffAt p k : coefficient of x^k in the polynomial p (as a list
-- of coefficients; the i-th entry is the coefficient of x^i).
def coeffAt : List Int -> Nat -> Int
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, k + 1 => coeffAt cs k

-- pointwise addition of two polynomials.
def addPoly : List Int -> List Int -> List Int
  | [], qs => qs
  | ps, [] => ps
  | p :: ps, q :: qs => (p + q) :: addPoly ps qs

-- multiplication of a polynomial by a scalar.
def scalePoly (c : Int) : List Int -> List Int
  | [] => []
  | a :: as => (c * a) :: scalePoly c as

-- multiplication of two polynomials by the recurrence
--   (f0 + x f1) * g = f0*g + x * (f1*g)
-- which is exactly the coefficient convolution.
def polyMul : List Int -> List Int -> List Int
  | [], _ => []
  | c :: cs, g => addPoly (scalePoly c g) (0 :: polyMul cs g)

-- truncated geometric polynomial 1 + x + x^2 + ... + x^D.
def geoPoly (D : Nat) : List Int := List.replicate (D + 1) 1

-- integer sum of a list of coefficients.
def sumInt (l : List Int) : Int := l.foldr (fun x acc => x + acc) 0

-- ------------------------------------------------------------------
-- 2. Basic coefficient and summation lemmas
-- ------------------------------------------------------------------

theorem coeffAt_replicate (n : Nat) (a : Int) (i : Nat) :
    coeffAt (List.replicate n a) i = if i < n then a else 0 := by
  induction n generalizing i with
  | zero => simp [coeffAt]
  | succ n ih =>
      cases i with
      | zero => simp [coeffAt, List.replicate_succ]
      | succ i =>
          simp [coeffAt, List.replicate_succ, ih, Nat.succ_lt_succ_iff]

theorem addPoly_coeff (p q : List Int) (k : Nat) :
    coeffAt (addPoly p q) k = coeffAt p k + coeffAt q k := by
  induction p generalizing q k with
  | nil => simp [addPoly, coeffAt]
  | cons a as ih =>
      induction q generalizing k with
      | nil => simp [addPoly, coeffAt]
      | cons b bs ihq =>
          cases k with
          | zero => simp [addPoly, coeffAt]
          | succ k => simp [addPoly, coeffAt, ih]

theorem scalePoly_coeff (c : Int) (g : List Int) (k : Nat) :
    coeffAt (scalePoly c g) k = c * coeffAt g k := by
  induction g generalizing k with
  | nil => simp [scalePoly, coeffAt]
  | cons b bs ih =>
      cases k with
      | zero => simp [scalePoly, coeffAt]
      | succ k => simp [scalePoly, coeffAt, ih]

theorem coeffAt_zero_shift (p : List Int) (k : Nat) :
    coeffAt (0 :: p) k = if k = 0 then 0 else coeffAt p (k - 1) := by
  cases k with
  | zero => simp [coeffAt]
  | succ k => simp [coeffAt]

theorem sumInt_cons (x : Int) (l : List Int) :
    sumInt (x :: l) = x + sumInt l := by
  rfl

theorem sumInt_append (l : List Int) (x : Int) :
    sumInt (l ++ [x]) = sumInt l + x := by
  induction l with
  | nil => simp [sumInt]
  | cons a as ih => simp [sumInt_cons, ih, Int.add_assoc]

theorem sumInt_range_succ (n : Nat) (F : Nat -> Int) :
    sumInt ((List.range (n + 1)).map F) = sumInt ((List.range n).map F) + F n := by
  rw [List.range_succ]
  simp [List.map_append, sumInt_append]

theorem sumInt_shift_range (n : Nat) (F : Nat -> Int) :
    sumInt ((List.range (n + 1)).map F)
      = F 0 + sumInt ((List.range n).map (fun i => F (i + 1))) := by
  induction n with
  | zero =>
      simp [List.range_succ, sumInt_cons]
  | succ n ih =>
      rw [List.range_succ]
      simp [List.map_append, sumInt_append]
      rw [ih]
      rw [Int.add_assoc]
      rw [List.range_succ]
      simp [List.map_append, sumInt_append]

theorem sumInt_zero_map (l : List Nat) :
    sumInt (List.map (fun _ : Nat => (0 : Int)) l) = 0 := by
  induction l with
  | nil => simp [sumInt]
  | cons a as ih => simp [sumInt_cons, ih]

theorem sumInt_ext {n : Nat} {F G : Nat -> Int}
    (h : forall i, i ∈ List.range n -> F i = G i) :
    sumInt ((List.range n).map F) = sumInt ((List.range n).map G) := by
  induction n with
  | zero => simp [sumInt]
  | succ n ih =>
      rw [List.range_succ]
      simp [List.map_append, sumInt_append]
      rw [ih (fun i hi => h i (by
        rw [List.mem_range] at hi ⊢
        exact Nat.lt_trans hi (Nat.lt_succ_self n)))]
      rw [h n (List.mem_range.mpr (Nat.lt_succ_self n))]

-- Int.ofNat respects addition (used to convert counting results).
theorem Int_ofNat_succ (n : Nat) : Int.ofNat (n + 1) = Int.ofNat n + (1 : Int) := by
  rfl

theorem Int_ofNat_add (a b : Nat) : Int.ofNat (a + b) = Int.ofNat a + Int.ofNat b := by
  induction b with
  | zero => simp [Int.add_zero]
  | succ b ih =>
      rw [Nat.add_succ]
      rw [Int_ofNat_succ]
      rw [ih]
      rw [Int.add_assoc]
      rw [Int_ofNat_succ]

theorem Int_ofNat_bool (b : Bool) :
    (if b then (1 : Int) else 0) = Int.ofNat (if b then 1 else 0) := by
  cases b <;> simp

-- Sum of Boolean indicators equals the count of true entries.
theorem sumInt_of_countP (n : Nat) (P : Nat -> Bool) :
    sumInt ((List.range n).map (fun i => if P i then (1 : Int) else 0))
      = Int.ofNat ((List.range n).countP P) := by
  induction n with
  | zero => simp [sumInt]
  | succ n ih =>
      rw [List.range_succ]
      simp [List.map_append, sumInt_append, List.countP_append]
      rw [ih]
      rw [Int_ofNat_bool]
      rfl

-- Product of two Boolean indicators equals the indicator of their AND.
theorem if_and_mul (b1 b2 : Bool) :
    (if b1 then (1 : Int) else 0) * (if b2 then (1 : Int) else 0)
      = if (b1 && b2) then (1 : Int) else 0 := by
  cases b1 <;> cases b2 <;> simp

-- ------------------------------------------------------------------
-- 3. Part A : truncated geometric series identity
--    (1 - x) * (1 + x + ... + x^D) = 1 - x^(D+1)
-- ------------------------------------------------------------------

theorem negate_replicate (n : Nat) :
    List.map (fun z : Int => -z) (List.replicate n 1) = List.replicate n (-1) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem scalePoly_one (l : List Int) : scalePoly 1 l = l := by
  induction l with
  | nil => simp [scalePoly]
  | cons a as ih => simp [scalePoly, Int.one_mul, ih]

theorem scalePoly_neg (l : List Int) : scalePoly (-1) l = List.map (fun z : Int => -z) l := by
  induction l with
  | nil => simp [scalePoly]
  | cons a as ih => simp [scalePoly, Int.neg_one_mul, ih]

theorem addPoly_ones_neg_mid (D : Nat) :
    addPoly (List.replicate D 1) (List.replicate (D + 1) (-1))
      = List.replicate D 0 ++ [(-1 : Int)] := by
  induction D with
  | zero => simp [addPoly]
  | succ D ih =>
      calc
        addPoly (List.replicate (D + 1) 1) (List.replicate (D + 2) (-1))
            = addPoly (1 :: List.replicate D 1) (-1 :: List.replicate (D + 1) (-1)) := by
                rw [List.replicate_succ, List.replicate_succ]
        _ = (1 + (-1 : Int)) :: addPoly (List.replicate D 1) (List.replicate (D + 1) (-1)) := by
                simp [addPoly]
        _ = (1 + (-1 : Int)) :: (List.replicate D 0 ++ [(-1 : Int)]) := by
                rw [ih]
        _ = List.replicate (D + 1) 0 ++ [(-1 : Int)] := by
                simp [List.replicate_succ, Int.add_right_neg]

theorem geo_trunc_identity (D : Nat) :
    polyMul [1, (-1 : Int)] (geoPoly D)
      = [1] ++ List.replicate D 0 ++ [(-1 : Int)] := by
  induction D with
  | zero =>
      simp [polyMul, geoPoly, scalePoly, addPoly]
  | succ D ih =>
      have hg : geoPoly (D + 1) = 1 :: List.replicate (D + 1) 1 := by
        simp [geoPoly, List.replicate_succ]
      rw [hg]
      simp [polyMul, scalePoly_one, scalePoly_neg, addPoly]
      have hmid : addPoly (List.replicate (D + 1) 1) ((-1) :: List.replicate (D + 1) (-1))
          = 0 :: (List.replicate D 0 ++ [(-1 : Int)]) := by
        rw [List.replicate_succ]
        simp [addPoly, Int.add_right_neg]
        rw [addPoly_ones_neg_mid D]
      rw [hmid]
      simp [List.replicate_succ]

-- ------------------------------------------------------------------
-- 4. Part B : coefficient convolution for two truncated geometric
--    polynomials
--    coeff_k (geoPoly D * geoPoly D) = #{ (i,j) in [0,D]^2 : i+j = k }
-- ------------------------------------------------------------------

-- Algebraic lemma isolating the induction step of the convolution
-- theorem: peeling the constant coefficient c off the first factor.
theorem conv_succ (c : Int) (cs g : List Int) (k : Nat) :
    c * coeffAt g (k.succ)
        + sumInt ((List.range (k + 1)).map (fun j => coeffAt cs j * coeffAt g (k - j)))
      = sumInt ((List.range (k.succ + 1)).map (fun i => coeffAt (c :: cs) i * coeffAt g (k.succ - i))) := by
  have hF0 : coeffAt (c :: cs) 0 * coeffAt g (k.succ - 0) = c * coeffAt g (k.succ) := by
    simp [coeffAt]
  have hFstep :
      (fun i => coeffAt (c :: cs) (i + 1) * coeffAt g (k.succ - (i + 1)))
        = (fun i => coeffAt cs i * coeffAt g (k - i)) := by
    funext i
    have hc : coeffAt (c :: cs) (i + 1) = coeffAt cs i := by
      simp [coeffAt]
    have hsub : k.succ - (i + 1) = k - i := by
      rw [Nat.succ_sub_succ]
    rw [hc, hsub]
  have hFlast : coeffAt (c :: cs) (k + 1) * coeffAt g (k.succ - (k + 1))
      = coeffAt cs k * coeffAt g (k - k) := by
    have hc2 : coeffAt (c :: cs) (k + 1) = coeffAt cs k := by
      simp [coeffAt]
    have hsub2 : k.succ - (k + 1) = k - k := by
      rw [Nat.succ_sub_succ]
    rw [hc2, hsub2]
  rw [sumInt_range_succ k]
  rw [sumInt_range_succ (k + 1)]
  rw [hFlast]
  rw [sumInt_shift_range]
  rw [hF0]
  rw [hFstep]
  rw [Int.add_assoc]

-- Coefficient formula for the product of two polynomials
-- (convolution): coeff_k (f * g) = sum_{i=0..k} coeff_i f * coeff_{k-i} g.
theorem polyMul_coeff (f g : List Int) (k : Nat) :
    coeffAt (polyMul f g) k
      = sumInt ((List.range (k + 1)).map (fun i => coeffAt f i * coeffAt g (k - i))) := by
  induction f generalizing g k with
  | nil =>
      simp [polyMul, coeffAt]
      rw [sumInt_zero_map]
  | cons c cs ih =>
      rw [polyMul]
      rw [addPoly_coeff]
      rw [scalePoly_coeff]
      rw [coeffAt_zero_shift]
      cases k with
      | zero =>
          simp [coeffAt, sumInt]
      | succ k =>
          simp
          rw [ih g k]
          exact conv_succ c cs g k

-- Coefficients of the truncated geometric polynomial.
theorem geoPoly_coeff (D i : Nat) :
    coeffAt (geoPoly D) i = if decide (i <= D) then (1 : Int) else 0 := by
  unfold geoPoly
  rw [coeffAt_replicate]
  by_cases h : i <= D
  · have hlt : i < D + 1 := (Nat.lt_succ_iff).mpr h
    simp [hlt, h]
  · have hnlt : Not (i < D + 1) := by
      intro hlt
      exact h ((Nat.lt_succ_iff).mp hlt)
    simp [hnlt, h]

-- Counting interpretation of the convolution: the coefficient of
-- x^k in (1 + ... + x^D)^2 is the number of pairs (i,j) in
-- [0,D]^2 with i + j = k.
theorem two_factor_count (D k : Nat) :
    coeffAt (polyMul (geoPoly D) (geoPoly D)) k
      = Int.ofNat ((List.range (k + 1)).countP (fun i => decide (i <= D) && decide (k - i <= D))) := by
  rw [polyMul_coeff]
  have h1 :
      sumInt ((List.range (k + 1)).map (fun i => coeffAt (geoPoly D) i * coeffAt (geoPoly D) (k - i)))
      = sumInt ((List.range (k + 1)).map (fun i => if (decide (i <= D) && decide (k - i <= D)) then (1 : Int) else 0)) := by
    apply sumInt_ext
    intro i hi
    rw [geoPoly_coeff, geoPoly_coeff]
    exact if_and_mul (decide (i <= D)) (decide (k - i <= D))
  rw [h1]
  rw [sumInt_of_countP]

-- ------------------------------------------------------------------
-- 5. Part C : numerical instances for the primes {2,3,5}
-- ------------------------------------------------------------------

-- Unmerged sum over all exponent triples (a,b,c) in {0,1,2}^3 of the
-- numerators arising from the Euler factors for p = 2,3,5 with
-- truncation degree D = 2 (each of the 27 summands has coefficient 1).
def monomSum : Int :=
  (List.range 3).foldl (fun accA a =>
    accA + (List.range 3).foldl (fun accB b =>
      accB + (List.range 3).foldl (fun accC c =>
        accC + (2 : Int) ^ (2 * (2 - a)) * (3 : Int) ^ (2 * (2 - b)) * (5 : Int) ^ (2 * (2 - c))) 0) 0) 0

theorem sample_factor_2 : (2 : Int) ^ 4 + (2 : Int) ^ 2 + (2 : Int) ^ 0 = 21 := by
  decide

theorem sample_factor_3 : (3 : Int) ^ 4 + (3 : Int) ^ 2 + (3 : Int) ^ 0 = 91 := by
  decide

theorem sample_factor_5 : (5 : Int) ^ 4 + (5 : Int) ^ 2 + (5 : Int) ^ 0 = 651 := by
  decide

-- Separable product: sum over the Cartesian product of the three
-- prime factors equals the product of the three partial sums.
theorem sample_euler_product : monomSum = (21 : Int) * 91 * 651 := by
  decide

-- Merged-coefficient expansion: (1 + x + x^2)^3.  After collecting
-- equal powers, the coefficients are the lattice-point counts
-- 1, 3, 6, 7, 6, 3, 1 (a finite analogue of the multiplicity with
-- which each exponent occurs in the three-factor Euler product).
def expand3 : List Int := polyMul (polyMul (geoPoly 2) (geoPoly 2)) (geoPoly 2)

theorem expand3_value : expand3 = [1, 3, 6, 7, 6, 3, 1] := by
  decide

-- ------------------------------------------------------------------
-- Axiom audit
-- ------------------------------------------------------------------
-- Run externally, e.g.:
--   lean -E <file>  (or)  #print axioms EulerProduct.geo_trunc_identity
-- Expected: only the standard trusted axioms
--   propext, funext, Classical.choice, Quot.sound
-- (all proofs above are constructive, no sorry, no extra axioms).

end EulerProduct
