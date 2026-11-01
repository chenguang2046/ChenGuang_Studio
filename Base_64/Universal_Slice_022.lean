import Mathlib.Data.Int.ModEq

/-!
# Universal Slice 022: Basic congruence arithmetic modulo an integer

Pure textbook statement: if a is congruent to b and c is congruent to d modulo n,
then their sums, differences, products and powers are congruent as well.
-/

namespace UniversalSlice022

/-- Addition is compatible with the congruence relation. -/
theorem modEq_add {a b c d n : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] :=
  Int.ModEq.add h1 h2

/-- Subtraction is compatible with the congruence relation. -/
theorem modEq_sub {a b c d n : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] :=
  Int.ModEq.sub h1 h2

/-- Multiplication is compatible with the congruence relation. -/
theorem modEq_mul {a b c d n : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] :=
  Int.ModEq.mul h1 h2

/-- Exponentiation is compatible with the congruence relation. -/
theorem modEq_pow {a b : ℤ} {m : ℕ} {n : ℤ} (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] :=
  Int.ModEq.pow m h

/-- Congruence modulo n is equivalent to divisibility of the difference. -/
theorem modEq_iff_dvd {a b n : ℤ} : a ≡ b [ZMOD n] ↔ n ∣ b - a :=
  Int.modEq_iff_dvd

end UniversalSlice022

#print axioms UniversalSlice022.modEq_add
#print axioms UniversalSlice022.modEq_sub
#print axioms UniversalSlice022.modEq_mul
#print axioms UniversalSlice022.modEq_pow
#print axioms UniversalSlice022.modEq_iff_dvd
