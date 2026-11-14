/-
Universal_Slice_003: Algebraic properties of the Dirichlet convolution
of arithmetic functions (结合律、交换律、单位元)

Content:
  1. dirichletConvolution_apply: the pointwise definition
     (f * g)(n) = sum over x * y = n of f(x) * g(y).
  2. dirichletConvolution_assoc: associativity.
  3. dirichletConvolution_one_mul / _mul_one: the identity element.
  4. dirichletConvolution_comm: commutativity (over a commutative semiring).
-/
import Mathlib.NumberTheory.ArithmeticFunction.Defs

noncomputable section

open scoped BigOperators

namespace UniversalSlice003

variable {R : Type*} [Semiring R]

/-- Pointwise definition of the Dirichlet convolution:
    (f * g)(n) = sum over x * y = n of f(x) * g(y). -/
theorem dirichletConvolution_apply (f g : ArithmeticFunction R) (n : ℕ) :
    (f * g) n = ∑ x ∈ Nat.divisorsAntidiagonal n, f x.1 * g x.2 := by
  simp

/-- Associativity of the Dirichlet convolution:
    (f * g) * h = f * (g * h). -/
theorem dirichletConvolution_assoc (f g h : ArithmeticFunction R) :
    (f * g) * h = f * (g * h) :=
  mul_assoc f g h

/-- Left identity: 1 * f = f. -/
theorem dirichletConvolution_one_mul (f : ArithmeticFunction R) :
    (1 : ArithmeticFunction R) * f = f :=
  one_mul f

/-- Right identity: f * 1 = f. -/
theorem dirichletConvolution_mul_one (f : ArithmeticFunction R) :
    f * (1 : ArithmeticFunction R) = f :=
  mul_one f

variable {R : Type*} [CommSemiring R]

/-- Commutativity of the Dirichlet convolution:
    f * g = g * f. -/
theorem dirichletConvolution_comm (f g : ArithmeticFunction R) :
    f * g = g * f :=
  mul_comm f g

end UniversalSlice003
