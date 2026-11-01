import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Universal Slice 005

给定同余子群 `Γ ≤ GL(2, ℝ)` 与权 `k : ℤ`，模形式集合 `ModularForm Γ k`
构成复向量空间。

mathlib 中 `ModularForm Γ k` 已配备代数结构实例：
* `AddCommGroup (ModularForm Γ k)`：加法、零元、取负；
* `Module ℂ (ModularForm Γ k)`（前提 `[Γ.HasDetOne]`）：复数数乘。

本文直接实例化这些结构，形式化向量空间的若干公理：加法单位元、
结合律、交换律、逆元、数乘分配律、数乘结合律与零元性质。
-/

namespace UniversalSlice005

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- 零元是加法左单位元：`0 + f = f`。 -/
theorem zero_add_left (f : ModularForm Γ k) : 0 + f = f :=
  zero_add f

/-- 零元是加法右单位元：`f + 0 = f`。 -/
theorem zero_add_right (f : ModularForm Γ k) : f + 0 = f :=
  add_zero f

/-- 加法结合律。 -/
theorem add_assoc_form (f g h : ModularForm Γ k) : (f + g) + h = f + (g + h) :=
  add_assoc f g h

/-- 加法交换律。 -/
theorem add_comm_form (f g : ModularForm Γ k) : f + g = g + f :=
  add_comm f g

/-- 加法逆元：`-f + f = 0`。 -/
theorem neg_add_cancel_form (f : ModularForm Γ k) : -f + f = 0 :=
  neg_add_cancel f

variable [Γ.HasDetOne]

/-- 数乘对向量加法的分配律：`c • (f + g) = c • f + c • g`。 -/
theorem smul_add_form (c : ℂ) (f g : ModularForm Γ k) : c • (f + g) = c • f + c • g :=
  smul_add c f g

/-- 数乘对标量加法的分配律：`(c + d) • f = c • f + d • f`。 -/
theorem add_smul_form (c d : ℂ) (f : ModularForm Γ k) : (c + d) • f = c • f + d • f :=
  add_smul c d f

/-- 单位标量的作用：`1 • f = f`。 -/
theorem one_smul_form (f : ModularForm Γ k) : (1 : ℂ) • f = f :=
  one_smul ℂ f

/-- 标量乘法的结合性：`a • (b • f) = (a * b) • f`。 -/
theorem mul_smul_form (a b : ℂ) (f : ModularForm Γ k) : a • (b • f) = (a * b) • f :=
  smul_smul a b f

/-- 零向量被任意标量作用仍为零向量：`c • 0 = 0`。 -/
theorem smul_zero_form (c : ℂ) : c • (0 : ModularForm Γ k) = 0 :=
  smul_zero c

/-- 零标量作用任意向量为零向量：`0 • f = 0`。 -/
theorem zero_smul_form (f : ModularForm Γ k) : (0 : ℂ) • f = 0 :=
  zero_smul ℂ f

end UniversalSlice005
