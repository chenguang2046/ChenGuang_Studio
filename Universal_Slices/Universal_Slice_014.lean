import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.Divisors

/-!
# Universal Slice 014: Dirichlet convolution algebra of arithmetic functions

This slice verifies basic algebraic properties of the Dirichlet convolution
on arithmetic functions: commutativity, associativity, and the multiplicative
identity element, together with the defining convolution formula.

References:
`ArithmeticFunction.mul_apply`, `ArithmeticFunction.one_apply`,
`ArithmeticFunction.one_one`, `ArithmeticFunction.mul_comm`,
`ArithmeticFunction.mul_assoc`, `ArithmeticFunction.one_mul`,
`ArithmeticFunction.mul_one`, `ArithmeticFunction.map_zero`,
`ArithmeticFunction.mul_apply_one`, `ArithmeticFunction.add_apply`,
`ArithmeticFunction.ext`.
-/

noncomputable section

namespace UniversalSlice014

open ArithmeticFunction

/-- The convolution product, expanded over divisor antidiagonals. -/
theorem mul_apply_def {R : Type*} [Semiring R] {f g : ArithmeticFunction R} {n : ℕ} :
    (f * g) n = ∑ x ∈ Nat.divisorsAntidiagonal n, f x.1 * g x.2 :=
  mul_apply

/-- The identity for the Dirichlet convolution: it is 1 at 1 and 0 elsewhere. -/
theorem one_apply_def {R : Type*} [Semiring R] {x : ℕ} :
    (1 : ArithmeticFunction R) x = if x = 1 then 1 else 0 :=
  one_apply

/-- Value of the identity at 1. -/
theorem one_one_def {R : Type*} [Semiring R] : (1 : ArithmeticFunction R) 1 = 1 :=
  one_one

/-- Commutativity of the Dirichlet convolution. -/
theorem mul_comm_def {R : Type*} [CommSemiring R] (f g : ArithmeticFunction R) :
    f * g = g * f :=
  mul_comm f g

/-- Associativity of the Dirichlet convolution. -/
theorem mul_assoc_def {R : Type*} [Semiring R] (f g h : ArithmeticFunction R) :
    (f * g) * h = f * (g * h) :=
  mul_assoc f g h

/-- The multiplicative identity is a left identity. -/
theorem one_mul_def {R : Type*} [Semiring R] (f : ArithmeticFunction R) :
    (1 : ArithmeticFunction R) * f = f :=
  one_mul f

/-- The multiplicative identity is a right identity. -/
theorem mul_one_def {R : Type*} [Semiring R] (f : ArithmeticFunction R) :
    f * (1 : ArithmeticFunction R) = f :=
  mul_one f

/-- Vanishing at zero is part of the definition of an arithmetic function. -/
theorem map_zero_def {R : Type*} [Zero R] {f : ArithmeticFunction R} : f 0 = 0 :=
  map_zero

/-- Value of the convolution at 1 is the product of the values at 1. -/
theorem mul_apply_one_def {R : Type*} [Semiring R] {f g : ArithmeticFunction R} :
    (f * g) 1 = f 1 * g 1 :=
  mul_apply_one

/-- Pointwise addition of arithmetic functions. -/
theorem add_apply_def {R : Type*} [AddCommMonoid R] {f g : ArithmeticFunction R} {n : ℕ} :
    (f + g) n = f n + g n :=
  add_apply

/-- Extensionality of arithmetic functions. -/
theorem ext_def {R : Type*} [Zero R] {f g : ArithmeticFunction R} (h : ∀ n, f n = g n) :
    f = g :=
  ext h

end UniversalSlice014
