-- Riemann Slice 002B: The Möbius function μ(n) and its fundamental summation identity.
--
-- Environment: Lean 4.34, bare Init (mathlib intentionally disabled).
-- All definitions are explicit, non-recursive computations on Nat / Int built from
-- finite lists; ground verification uses kernel reduction via the tactic `decide`.
--
-- Contents:
--   1. Primality test (trial division) and prime-factor machinery over finite ranges.
--   2. The Möbius function μ(n): square-factor criterion and parity of the number
--      of distinct prime factors.
--   3. The divisor sum S(n) = Σ_{d | n} μ(d), verified to equal 1 at n = 1 and 0
--      for n > 1 on all ground instances n = 1 .. 50 (by evaluation) and on a
--      selected set of instances (by kernel-reduction proofs).
--   4. Dirichlet convolution (f ⋆ g)(n) = Σ_{d | n} f(d) g(n/d) over integer-valued
--      functions on positive naturals: proof of distributivity (pointwise addition)
--      by list induction, and a ground instance of associativity.

import Init

namespace MobiusSlice

-- ---------------------------------------------------------------------------
-- 1. Prime factors by trial division over finite ranges
-- ---------------------------------------------------------------------------

/-- Primality by trial division over the finite range [2, p - 2]. -/
def isPrime (p : Nat) : Bool :=
  2 ≤ p && ((List.range (p - 1)).drop 2).all (fun k => p % k ≠ 0)

/-- The list of all prime divisors of n in the interval [2, n]. -/
def primeCandidates (n : Nat) : List Nat :=
  ((List.range (n + 1)).drop 2).filter (fun p => isPrime p && p ∣ n)

/-- The p-adic valuation v_p(n), computed as the number of k ≥ 0 with
p^(k+1) | n.  For prime p and n ≥ 1 this count equals v_p(n). -/
def valuation (n p : Nat) : Nat :=
  (List.range n).filter (fun k => p ^ (k + 1) ∣ n) |>.length

/-- Whether n admits a prime factor p with p * p | n, i.e. n is not squarefree. -/
def hasSquareFactor (n : Nat) : Bool :=
  primeCandidates n |>.any (fun p => p * p ∣ n)

-- ---------------------------------------------------------------------------
-- 2. The Möbius function
-- ---------------------------------------------------------------------------

/-- The Möbius function μ(n):
  μ(0) := 0 (convention), μ(1) := 1,
  μ(n) := 0 if n is not squarefree, otherwise (-1)^k where k is the number
  of distinct prime factors of n. -/
def mobius (n : Nat) : Int :=
  if n = 0 then 0
  else if n = 1 then 1
  else if hasSquareFactor n then 0
  else if (primeCandidates n).length % 2 = 0 then 1 else -1

-- ---------------------------------------------------------------------------
-- 3. The divisor sum of μ
-- ---------------------------------------------------------------------------

/-- The list of positive divisors of n in increasing order. -/
def divisors (n : Nat) : List Nat :=
  (List.range (n + 1)).drop 1 |>.filter (fun d => d ∣ n)

/-- S(n) = Σ_{d | n} μ(d). -/
def mobiusSum (n : Nat) : Int :=
  (divisors n).foldr (fun d acc => mobius d + acc) 0

/-- Ground checks of μ at selected instances, by kernel reduction.
Expected values: μ(1)=1, μ(2)=-1, μ(3)=-1, μ(6)=1, μ(30)=-1. -/
example : mobius 1 = 1 := by
  decide

example : mobius 2 = -1 := by
  decide

example : mobius 3 = -1 := by
  decide

example : mobius 6 = 1 := by
  decide

example : mobius 30 = -1 := by
  decide

/-- Ground check: S(n) = 1 for n = 1 and S(n) = 0 for n = 2 .. 50,
by kernel reduction on the whole finite range. -/
example : List.all ((List.range 51).drop 1)
    (fun n => decide (if n = 1 then mobiusSum n = 1 else mobiusSum n = 0)) = true := by
  decide

/-- Theorem: S(1) = 1, by kernel reduction. -/
theorem mobiusSum_one : mobiusSum 1 = 1 := by
  decide

/-- Theorems: S(n) = 0 for a selection of composite and prime instances n > 1,
each by kernel reduction. -/
theorem mobiusSum_two : mobiusSum 2 = 0 := by
  decide

theorem mobiusSum_three : mobiusSum 3 = 0 := by
  decide

theorem mobiusSum_four : mobiusSum 4 = 0 := by
  decide

theorem mobiusSum_five : mobiusSum 5 = 0 := by
  decide

theorem mobiusSum_six : mobiusSum 6 = 0 := by
  decide

theorem mobiusSum_eight : mobiusSum 8 = 0 := by
  decide

theorem mobiusSum_ten : mobiusSum 10 = 0 := by
  decide

theorem mobiusSum_twelve : mobiusSum 12 = 0 := by
  decide

theorem mobiusSum_sixteen : mobiusSum 16 = 0 := by
  decide

theorem mobiusSum_thirty : mobiusSum 30 = 0 := by
  decide

-- ---------------------------------------------------------------------------
-- 4. Dirichlet convolution and its algebraic properties
-- ---------------------------------------------------------------------------

/-- The Dirichlet convolution (f ⋆ g)(n) = Σ_{d | n} f(d) g(n / d). -/
def dirichletConvolution (f g : Nat → Int) (n : Nat) : Int :=
  (divisors n).foldr (fun d acc => f d * g (n / d) + acc) 0

/-- Auxiliary identity for four integer summands, used in the distributivity proof:
(a + b) + (c + d) = (a + c) + (b + d). -/
theorem add_four_swap (a b c d : Int) : (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := by rw [Int.add_assoc]
    _ = a + ((c + d) + b) := by rw [Int.add_comm b (c + d)]
    _ = a + (c + (d + b)) := by rw [Int.add_assoc]
    _ = (a + c) + (d + b) := by rw [Int.add_assoc]
    _ = (a + c) + (b + d) := by rw [Int.add_comm d b]

/-- Pointwise congruence of the right-fold used in the convolution: if u and v
agree on every element of the list then the accumulated sums agree. -/
theorem foldr_congr_pointwise {xs : List Nat} {u v : Nat → Int}
    (h : ∀ d, u d = v d) :
    (xs.foldr (fun d acc => u d + acc) (0 : Int)) =
      (xs.foldr (fun d acc => v d + acc) (0 : Int)) := by
  induction xs with
  | nil => rfl
  | cons d ds ih =>
      change u d + (ds.foldr (fun d acc => u d + acc) 0)
            = v d + (ds.foldr (fun d acc => v d + acc) 0)
      rw [h d, ih]

/-- Distributivity of the convolution over pointwise addition, proven by
induction on the finite divisor list:
  ((f + g) ⋆ h)(n) = (f ⋆ h)(n) + (g ⋆ h)(n). -/
theorem foldr_add_distrib (xs : List Nat) (f g k : Nat → Int) :
    (xs.foldr (fun d acc => (f d + g d) * k d + acc) (0 : Int))
      = (xs.foldr (fun d acc => f d * k d + acc) (0 : Int))
      + (xs.foldr (fun d acc => g d * k d + acc) (0 : Int)) := by
  induction xs with
  | nil =>
      change 0 = 0 + 0
      rw [Int.zero_add]
  | cons d ds ih =>
      change (f d + g d) * k d
            + (ds.foldr (fun d acc => (f d + g d) * k d + acc) 0)
          = (f d * k d + (ds.foldr (fun d acc => f d * k d + acc) 0))
          + (g d * k d + (ds.foldr (fun d acc => g d * k d + acc) 0))
      rw [Int.add_mul, ih]
      exact add_four_swap (f d * k d) (g d * k d)
        (ds.foldr (fun d acc => f d * k d + acc) 0)
        (ds.foldr (fun d acc => g d * k d + acc) 0)

/-- The convolution is distributive over pointwise addition. -/
theorem dirichletConvolution_add (f g h : Nat → Int) (n : Nat) :
    dirichletConvolution (fun d => f d + g d) h n
      = dirichletConvolution f h n + dirichletConvolution g h n := by
  unfold dirichletConvolution
  exact foldr_add_distrib (divisors n) f g (fun d => h (n / d))

/-- Connection with the divisor sum: (μ ⋆ 1)(n) = S(n), since g ≡ 1 contributes
the factor 1 = g(n/d) to every summand. -/
theorem dirichletConvolution_mobius_one (n : Nat) :
    dirichletConvolution mobius (fun _ => 1) n = mobiusSum n := by
  unfold dirichletConvolution mobiusSum
  apply foldr_congr_pointwise
  intro d
  change mobius d * 1 = mobius d
  exact Int.mul_one (mobius d)

/-- Ground instance of associativity for constant functions on n = 10:
((2 ⋆ 3) ⋆ 5)(10) = (2 ⋆ (3 ⋆ 5))(10), by kernel reduction. -/
theorem dirichletConvolution_assoc_const :
    dirichletConvolution
        (dirichletConvolution (fun _ : Nat => (2 : Int)) (fun _ => (3 : Int)))
        (fun _ => (5 : Int)) 10
      = dirichletConvolution (fun _ : Nat => (2 : Int))
        (dirichletConvolution (fun _ => (3 : Int)) (fun _ => (5 : Int))) 10 := by
  decide

/-- Ground check of the same associativity instance for n = 1 .. 10,
by kernel reduction. -/
example : List.all ((List.range 11).drop 1)
    (fun n =>
      decide
        (dirichletConvolution
            (dirichletConvolution (fun _ : Nat => (2 : Int)) (fun _ => (3 : Int)))
            (fun _ => (5 : Int)) n
          = dirichletConvolution (fun _ : Nat => (2 : Int))
            (dirichletConvolution (fun _ => (3 : Int)) (fun _ => (5 : Int))) n)) = true := by
  decide

-- ---------------------------------------------------------------------------
-- Axiom audit
-- ---------------------------------------------------------------------------

#print axioms mobiusSum_one
#print axioms mobiusSum_thirty
#print axioms dirichletConvolution_add
#print axioms dirichletConvolution_mobius_one
#print axioms dirichletConvolution_assoc_const

end MobiusSlice
