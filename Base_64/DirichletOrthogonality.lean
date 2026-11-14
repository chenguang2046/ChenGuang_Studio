import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Data.Nat.Totient

open scoped BigOperators Complex ComplexConjugate

noncomputable section

/-!
# Dirichlet 特征的正交关系（独立命题）

对任意模 N 的 Dirichlet 特征 χ : DirichletCharacter ℂ N = MulChar (ZMod N) ℂ：

1. χ ≠ 1（非平凡）⟹  ∑ a mod N, χ(a) = 0
2. χ = 1（平凡）   ⟹  ∑ a mod N, χ(a) = φ(N)
3. χ₁ ≠ χ₂        ⟹  ∑ a mod N, χ₁(a) · conj(χ₂(a)) = 0

全部使用 mathlib 现成引理，无 sorry。
-/

namespace DirichletOrthogonality

variable {N : ℕ} [NeZero N]

/-- 命题 1：非平凡 Dirichlet 特征在模 N 剩余类上的和为 0。 -/
theorem sum_eq_zero_of_ne_one (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    (∑ a : ZMod N, χ a) = 0 :=
  MulChar.sum_eq_zero_of_ne_one (R := ZMod N) (R' := ℂ) hχ

/-- 命题 2：平凡 Dirichlet 特征在模 N 剩余类上的和为 φ(N)。 -/
theorem sum_eq_totient_of_eq_one (χ : DirichletCharacter ℂ N) (hχ : χ = 1) :
    (∑ a : ZMod N, χ a) = (N.totient : ℂ) := by
  rw [hχ]
  have h1 : (∑ a : ZMod N, (1 : DirichletCharacter ℂ N) a) = (Fintype.card (ZMod N)ˣ : ℂ) :=
    MulChar.sum_one_eq_card_units (R := ZMod N) (R' := ℂ)
  have h2 : (Fintype.card (ZMod N)ˣ : ℂ) = (N.totient : ℂ) := by
    exact_mod_cast (ZMod.card_units_eq_totient N)
  exact h1.trans h2

/-- 命题 3（star 形式）：两个不同 Dirichlet 特征的正交性：∑ χ₁(a) · star(χ₂(a)) = 0。
（在 ℂ 中 star 即共轭，`Complex.star_def : star = conj`。） -/
theorem sum_mul_star_eq_zero (χ₁ χ₂ : DirichletCharacter ℂ N) (hne : χ₁ ≠ χ₂) :
    (∑ a : ZMod N, χ₁ a * star (χ₂ a)) = 0 := by
  have hne' : χ₁ * χ₂⁻¹ ≠ 1 := by
    intro h
    apply hne
    calc
      χ₁ = χ₁ * 1 := by simp
      _ = χ₁ * (χ₂⁻¹ * χ₂) := by simp
      _ = (χ₁ * χ₂⁻¹) * χ₂ := by rw [mul_assoc]
      _ = 1 * χ₂ := by rw [h]
      _ = χ₂ := by simp
  have hsum : (∑ a : ZMod N, (χ₁ * χ₂⁻¹) a) = 0 :=
    MulChar.sum_eq_zero_of_ne_one (R := ZMod N) (R' := ℂ) hne'
  simpa [MulChar.mul_apply, MulChar.star_apply',
    MulChar.inv_apply_eq_inv'] using hsum

/-- 命题 3（共轭形式）：∑ χ₁(a) · conj(χ₂(a)) = 0。 -/
theorem sum_mul_conj_eq_zero (χ₁ χ₂ : DirichletCharacter ℂ N) (hne : χ₁ ≠ χ₂) :
    (∑ a : ZMod N, χ₁ a * conj (χ₂ a)) = 0 := by
  simpa [Complex.star_def] using sum_mul_star_eq_zero χ₁ χ₂ hne

end DirichletOrthogonality

-- 公理审计：主定理依赖的公理应仅为
-- [propext, Classical.choice, Quot.sound]
#print axioms DirichletOrthogonality.sum_eq_zero_of_ne_one
#print axioms DirichletOrthogonality.sum_eq_totient_of_eq_one
#print axioms DirichletOrthogonality.sum_mul_star_eq_zero
#print axioms DirichletOrthogonality.sum_mul_conj_eq_zero
