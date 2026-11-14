import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex DirichletCharacter
open scoped ComplexConjugate

noncomputable section

namespace DirichletNonvanishing

/-! ## 命题 1：非平凡 Dirichlet 特征的 L(1, χ) ≠ 0 -/

/-- 对任意模 `q` 的 Dirichlet 特征 `χ`，若 `χ` 非平凡（`χ ≠ 1`），则 `L(1, χ) ≠ 0`。
直接引用 mathlib 现成定理 `DirichletCharacter.LFunction_apply_one_ne_zero`。 -/
theorem L_one_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    LFunction χ 1 ≠ 0 :=
  LFunction_apply_one_ne_zero hχ

/-! ## 命题 2：Dirichlet 定理（素数等差数列） -/

/-- 若整数 `a` 与 `q` 互素，则存在无穷多个素数 `p ≡ a (mod q)`。
强形式（任意大）来自 mathlib 的 `Nat.forall_exists_prime_gt_and_zmodEq`。 -/
theorem exists_prime_gt_congruent_int {q : ℕ} (a : ℤ) (hq : q ≠ 0) (h : IsCoprime a q) (n : ℕ) :
    ∃ p > n, p.Prime ∧ p ≡ a [ZMOD q] :=
  Nat.forall_exists_prime_gt_and_zmodEq n hq h

/-- 集合形式：`{p | p 为素数 ∧ p ≡ a (mod q)}` 是无穷集合。 -/
theorem infinite_primes_congruent_int {q : ℕ} (a : ℤ) (hq : q ≠ 0) (h : IsCoprime a q) :
    {p : ℕ | p.Prime ∧ p ≡ a [ZMOD q]}.Infinite := by
  set_option linter.style.haveILetI false in
  haveI : NeZero q := ⟨hq⟩
  rw [Set.infinite_iff_exists_gt]
  intro n
  rcases Nat.forall_exists_prime_gt_and_zmodEq n hq h with ⟨p, hgt, hpp, hcong⟩
  exact ⟨p, ⟨hpp, by simpa using hcong⟩, hgt⟩

end DirichletNonvanishing

-- 公理审计
#print axioms DirichletNonvanishing.L_one_ne_zero
#print axioms DirichletNonvanishing.exists_prime_gt_congruent_int
#print axioms DirichletNonvanishing.infinite_primes_congruent_int
