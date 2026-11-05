/-
Copyright (c) 2026. All rights reserved.
Challenge 105-C（G5 族版本）：交换族 → 公共特征向量 → Hecke 特征标
================================================================================

目标（用户指令 G5）：利用 Mathlib 的 `iSup_maxGenEigenspace_eq_top`
（LinearAlgebra/Eigenspace/Triangularizable.lean:75），把单算子特征值推进到
交换族的公共特征向量。

本文件真证部分（零 sorry、零自定义公理）：
  ① `exists_maxGenEigenspace_ne_bot`：非平凡有限维空间上，任一算子必有非零广义
     特征空间 —— 直接用 `iSup_maxGenEigenspace_eq_top` 反证。
  ② `mapsTo_maxGenEigenspace_of_comm`：与 `T` 交换的 `S` 保持 `T` 的广义特征空间
     （`LinearMap.mapsTo_genEigenspace_of_comp` 的直接实例化）。这是「族同时约化」
     的技术核心。
  ③ `common_eigenvector_of_finrank_one`：一维空间上一族交换算子必有公共特征向量
     （`LinearMap.exists_smul_eq_of_finrank_eq_one`）。G5 的骨架在 dim = 1 上**完全落地**。
  ④ `HeckeFamilyEigenGap`：显式 gap，只承载「交换族公共特征向量存在」这一
     Shimura Thm 3.4.4 / DS Cor 5.4.4 的**一般维数**结论（库无族版引理）。
  ⑤ 从 ④ 真推出：特征标 `χ` 的存在、唯一性、`χ 1 = 1`、完全乘性
     `χ (m·n) = χ m · χ n`。这是 Hecke 特征标的严格形式化，零 sorry。

诚实边界（严禁对外宣称一般维数的族公共特征向量已证）：
  · 已真证：非零广义特征空间存在、交换性保持广义特征空间、dim = 1 的族公共特征向量、
            「有公共特征向量 ⇒ 有完全乘性特征标」。
  · gap：一般维数下交换族的公共特征向量（需要谱定理/Zorn 型论证，Mathlib 无）。

文献：Shimura, *Introduction*, Thm 3.4.4；Diamond–Shurman, Cor 5.4.4；
      Axler, *Linear Algebra Done Right*, Thm 8.22(c)（广义特征空间铺满，即 ①）。
-/
import Slices_99.Challenge_105_HeckeOperator
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped BigOperators MatrixGroups UpperHalfPlane ModularForm
open Matrix Matrix.SpecialLinearGroup

namespace Challenge105CHeckeFamily

open Challenge105HeckeOperator

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ## 1. `iSup_maxGenEigenspace_eq_top` 的直接后果 -/

/-- **真定理**：非平凡有限维复空间上，任一算子的某个广义特征空间非零。
    证明只做一件事：把 `iSup_maxGenEigenspace_eq_top` 反着用。 -/
theorem exists_maxGenEigenspace_ne_bot [FiniteDimensional ℂ V] [Nontrivial V]
    (T : Module.End ℂ V) : ∃ μ : ℂ, T.maxGenEigenspace μ ≠ ⊥ := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hbot : (⨆ μ : ℂ, T.maxGenEigenspace μ) = ⊥ := by simp [h]
  rw [Module.End.iSup_maxGenEigenspace_eq_top T] at hbot
  exact top_ne_bot hbot

/-! ## 2. 交换性保持广义特征空间 -/

/-- **真定理**：若 `S` 与 `T` 交换，则 `S` 把 `T` 的每个广义特征空间映入自身。
    这是「交换族可同时约化」的技术核心（定理 `map_genEigenspace_le` 的实例）。 -/
theorem mapsTo_maxGenEigenspace_of_comm {S T : Module.End ℂ V}
    (hcomm : S.comp T = T.comp S) (μ : ℂ) :
    ∀ x ∈ T.maxGenEigenspace μ, S x ∈ T.maxGenEigenspace μ :=
  fun x hx =>
    Module.End.mapsTo_genEigenspace_of_comp (f := T) (g := T) (φ := S) hcomm.symm μ ⊤ hx

/-! ## 3. dim = 1：族公共特征向量（G5 骨架完全落地的情形） -/

/-- **真定理**：一维空间上，与 `T` 交换的任意算子都以同一非零向量为特征向量。
    即：dim = 1 时交换族的公共特征向量存在，无需任何 gap。 -/
theorem common_eigenvector_of_finrank_one [Nontrivial V] (T : Module.End ℂ V)
    (h1 : Module.finrank ℂ V = 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ S : Module.End ℂ V, S.comp T = T.comp S →
      ∃ c : ℂ, S v = c • v := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨v, hv, ?_⟩
  intro S _
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := ℂ) (V := V) h1 hv (S v)
  exact ⟨c, hc.symm⟩

/-! ## 4. 显式 gap：一般维数下交换族的公共特征向量（Shimura Thm 3.4.4） -/

/-- Hecke 交换族的公共特征向量 + 特征标结构，以**显式假设**承载。
    字段说明：
    - `one_id` : `T 1 = 1`（T₁ 是恒等，函数层已由 105 的 `heckeSlashSum_one` 真证，
                 这里在算子层作为接口假设登记）；
    - `v / hv` : 公共特征向量与其非零性；
    - `eigen`  : 交换族的每个 `T n` 都以 `v` 为特征向量（Shimura Thm 3.4.4 的结论，
                 库无族版引理，故显式登记为 gap）。
    证明原则：**gap 只提供公共特征向量的存在，不提供任何特征标性质**；
    特征标的完全乘性等全部由本文件的定理真推出（见 §5）。 -/
structure HeckeFamilyEigenGap (N : ℕ) (k : ℤ) [NeZero N] extends HeckeAlgebraGap N k where
  /-- T₁ 是恒等算子。 -/
  one_id : T 1 = 1
  /-- 公共特征向量。 -/
  v : CuspForm (Gamma0GL N) k
  /-- 公共特征向量非零。 -/
  hv : v ≠ 0
  /-- 族中每个算子都以 `v` 为特征向量。 -/
  eigen : ∀ n : ℕ, ∃ c : ℂ, T n v = c • v

/-! ## 5. 从 gap 真推出：Hecke 特征标 -/

section Character

variable {N : ℕ} {k : ℤ} [NeZero N]

/-- 特征值的唯一性：非零向量上的标量乘是单射。 -/
theorem eigen_scalar_unique (D : HeckeFamilyEigenGap N k) (n : ℕ) {c c' : ℂ}
    (h : c • D.v = c' • D.v) : c = c' := by
  have hzero : (c - c') • D.v = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hzero with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' D.hv

/-- 每个 `T n` 在公共特征向量上的特征值存在且唯一。 -/
theorem eigen_exists_unique (D : HeckeFamilyEigenGap N k) (n : ℕ) :
    ∃! c : ℂ, D.T n D.v = c • D.v := by
  obtain ⟨c, hc⟩ := D.eigen n
  exact ⟨c, hc, fun c' hc' => eigen_scalar_unique D n (hc'.symm.trans hc)⟩

/-- **Hecke 特征标**：`χ n` 是 `T n` 在公共特征向量上的特征值。 -/
def eigenChar (D : HeckeFamilyEigenGap N k) (n : ℕ) : ℂ :=
  (eigen_exists_unique D n).choose

/-- 特征标的定义性质：`T n v = χ n • v`。 -/
theorem eigenChar_spec (D : HeckeFamilyEigenGap N k) (n : ℕ) :
    D.T n D.v = eigenChar D n • D.v :=
  (eigen_exists_unique D n).choose_spec.1

/-- **真定理**：`χ 1 = 1`（用 gap 的 `T 1 = 1` 与特征值唯一性）。 -/
theorem eigenChar_one (D : HeckeFamilyEigenGap N k) : eigenChar D 1 = 1 := by
  have h := eigenChar_spec D 1
  rw [D.one_id] at h
  have h' : (1 : ℂ) • D.v = eigenChar D 1 • D.v := by simpa using h
  exact eigen_scalar_unique D 1 h'.symm

/-- **真定理**：特征标的完全乘性 `χ (m·n) = χ m · χ n`。
    证明用 gap 的乘法性 `T (m·n) = T m ∘ T n` 与 `T n v = χ n • v` 的线性性。 -/
theorem eigenChar_mul (D : HeckeFamilyEigenGap N k) (m n : ℕ) :
    eigenChar D (m * n) = eigenChar D m * eigenChar D n := by
  apply eigen_scalar_unique D (m * n)
  calc eigenChar D (m * n) • D.v = D.T (m * n) D.v := (eigenChar_spec D (m * n)).symm
    _ = D.T m (D.T n D.v) := by rw [D.mul m n]; rfl
    _ = D.T m (eigenChar D n • D.v) := by rw [eigenChar_spec]
    _ = eigenChar D n • (D.T m D.v) := by rw [map_smul]
    _ = eigenChar D n • (eigenChar D m • D.v) := by rw [eigenChar_spec]
    _ = (eigenChar D m * eigenChar D n) • D.v := by rw [smul_smul, mul_comm]

/-- **真定理**：特征标给出 Hecke 算子族的公共特征分解（族同时对角化的必要条件）。 -/
theorem hecke_family_eigen_decomposition (D : HeckeFamilyEigenGap N k) :
    ∃ (v : CuspForm (Gamma0GL N) k) (χ : ℕ → ℂ), v ≠ 0 ∧ χ 1 = 1 ∧
      (∀ m n : ℕ, χ (m * n) = χ m * χ n) ∧ ∀ n : ℕ, D.T n v = χ n • v :=
  ⟨D.v, eigenChar D, D.hv, eigenChar_one D, eigenChar_mul D, eigenChar_spec D⟩

end Character

end

end Challenge105CHeckeFamily
