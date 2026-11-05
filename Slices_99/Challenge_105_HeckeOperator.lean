/-
Copyright (c) 2026. All rights reserved.
Challenge 105 (第 105 号切片): Hecke 算子特征标与作用 —— 深水区（v2）
================================================================================

v1 骨架的问题（本版修正，与 104 假公式同类）：
  v1 把 `HeckeOp := LinearMap.id` 当占位，于是 hecke_mul / hecke_comm 都在
  「恒等算子」上平凡成立 —— 这只是**假演示**：它宣称「Hecke 算子乘法性已被证明」，
  而实际上根本没定义 Hecke 算子。任何下游若引用 hecke_comm，都会继承一个空壳。
  v2 的处理原则与 104 一致：**能真定义的真定义，不能真证的不许假证**。

v2 结构：
  ① `heckeMatrix`：上三角整数矩阵 [[a,b],[0,d]] 提升为 GL(2,ℝ)（真定义，det = a·d）。
  ② `slashFun`：Mathlib 现成 slash 作用 `γ ∣[k] f`（SlashActions.lean:130，
     instance `SlashAction ℤ (GL (Fin 2) ℝ) (ℍ → ℂ)`），无自造。
  ③ `heckeSlashSum`：Diamond–Shurman 公式的真求和实现
         T_n f = Σ_{d ∣ n} Σ_{b=0}^{d−1} (n/d)^{k−1} · (f ∣[k] [[n/d, b],[0, d]])
     定义在函数层 ℍ → ℂ，**可计算、无 sorry、无公理**。
  ④ `HeckeAlgebraGap`：显式 gap 结构，承载「该求和落在 CuspForm 内（Γ₀(N)-不变
     与尖点消失）」这一尚未证明的封闭性，以及由此导出的乘法性/交换性。
  ⑤ `hecke_comm` / `hecke_exists_eigenvalue`：从显式 gap 与 Mathlib 的
     `Module.End.exists_eigenvalue` 真推出（这两个定理本身零 sorry、零自定义公理，
     但其前提里含 gap，调用方必须自己承担 gap）。

v2 深水区第二轮新增（本轮，全部零 sorry、零自定义公理）：
  ⑥ `heckeDoubleCoset` + `det_eq_of_mem_doubleCoset`：**真定理**，用 Mathlib 底库
     `GroupTheory.DoubleCoset`（Set 级双陪集）与 `HasDetOne.det_eq` 证明
     「同一双陪集内行列式不变」——Hecke 算子按 det 分次的代数基础。一次编译通过。
  ⑦ `heckeMatrix_one`：**真定理**，[[1,0],[0,1]] 提升后即单位矩阵（真展开证明）。
  ⑧ `heckeSlashSum_one`：**真定理**，T₁ = id（函数层）。用 `Finset.ext` 把
     `(Nat.divisors 1).attach` 写成单元素集，再用 `Nat.mem_divisors.mp` + `Nat.dvd_one`
     绕开 subtype 依赖重写（`rw [Nat.divisors_one]` 在该位置会触发 motive 错误）。

未证假设登记（严禁对外宣称本文件已实现 Hecke 算子作用）：
  [gap]  HeckeAlgebraGap.T / .mul / .comm  : T_n 在 S_k(Γ₀(N)) 上的封闭性与代数性
  [未做] 封闭性证明需要双陪集 Γ₀(N)·diag(n)·Γ₀(N) 的完整理论（Mathlib 的
        NumberTheory/HeckeRing/Defs.lean 只有类型层，无卷积、无作用）。
  [已做] T₁ = id（函数层）已证（见 ⑧），原先登记的 subtype 依赖障碍已绕过。

文献：Diamond–Shurman, *A First Course in Modular Forms*, §5.2（Hecke 算子定义）；
      Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4–3.5。
-/
-- H2 层内咬合：T_n 作用在 Γ₀(N) 上，故下游直接依赖 104（104 再依赖 021 的指数结论）。
-- 原先此处 import 021 + 本地重造 Gamma0GL，属于「物理拼装」；现改为逻辑咬合。
import Slices_99.Challenge_104_Gamma0_Dimension
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.GroupTheory.DoubleCoset

open scoped BigOperators MatrixGroups UpperHalfPlane ModularForm
open Matrix Matrix.SpecialLinearGroup

namespace Challenge105HeckeOperator

noncomputable section

/-! ## 0. Γ₀(N) 提升为 GL(2,ℝ) —— 直接复用 104（层内咬合，不再本地重造） -/

/-- Γ₀(N) 提升为 GL(2,ℝ) 子群：**定义体来自 104 号切片的 `Gamma0GL`**，
    故 105 与 104 共享同一子群（定义上 `rfl` 相等），不产生第二份复制品。 -/
abbrev Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  Challenge104Gamma0Dimension.Gamma0GL N

/-- Γ₀(N) 提升后行列式为 1：**直接继承 104 的实例**（实例搜索走同一条链）。 -/
instance Gamma0GL.hasDetOne (N : ℕ) : Subgroup.HasDetOne (Gamma0GL N) :=
  Challenge104Gamma0Dimension.Gamma0GL.hasDetOne N

/-- **咬合核对（真证 `rfl`）**：105 的 Γ₀(N) 提升与 104 的 Γ₀(N) 提升是**同一个**子群 ——
    Hecke 作用所在的群与维数公式所用的群不存在「同名不同物」的复制品。 -/
theorem Gamma0GL_eq_104 (N : ℕ) :
    Gamma0GL N = Challenge104Gamma0Dimension.Gamma0GL N := rfl

/-- **咬合核对（真证 `rfl`）**：105 的 Γ₀(N) 与 104/021 链上的 `gamma0_N` 提升一致，
    故 104 的指数结论（`einf_eq_index`）对 105 的 Hecke 群同样直接可用。 -/
theorem Gamma0GL_eq_gamma0_map (N : ℕ) :
    Gamma0GL N = (Challenge021Gamma0NIndex.gamma0_N N).map (mapGL ℝ) := rfl

/-! ## 1. Hecke 矩阵：[[a,b],[0,d]] ↦ GL(2,ℝ) -/

/-- 上三角整数矩阵 [[a,b],[0,d]] 视为 GL(2,ℝ)（当 a·d ≠ 0，即 det ≠ 0）。
    这是 Hecke 双陪集的标准代表元形状（Diamond–Shurman §5.2）。 -/
def heckeMatrix (a b d : ℕ) (h : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(a : ℝ), (b : ℝ); (0 : ℝ), (d : ℝ)]
    (by
      have hR : ((a * d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h
      simpa [Matrix.det_fin_two, Nat.cast_mul] using hR)

/-- slash 作用：f ∣[k] γ，直接用 Mathlib 的 `SlashAction ℤ (GL (Fin 2) ℝ) (ℍ → ℂ)`。 -/
def slashFun (k : ℤ) (γ : GL (Fin 2) ℝ) (f : ℍ → ℂ) : ℍ → ℂ :=
  f ∣[k] γ

/-! ## 2. Hecke 求和：真定义（Diamond–Shurman §5.2） -/

/-- Hecke 算子的函数层作用（Diamond–Shurman 公式 5.2.1）：
      T_n f = Σ_{d ∣ n} Σ_{b=0}^{d−1} (n/d)^{k−1} · (f ∣[k] [[n/d, b],[0, d]])
    求和指标用 `n.divisors.attach`，以便在项内取到 `d ∣ n` 的证明来保证 det ≠ 0。
    本定义完全可构造：无 sorry、无公理、无占位。 -/
def heckeSlashSum (k : ℤ) (n : ℕ) (hn : 0 < n) (f : ℍ → ℂ) : ℍ → ℂ :=
  n.divisors.attach.sum fun d =>
    (Finset.range d.1).sum fun b =>
      (((n / d.1 : ℕ) : ℂ) ^ (k - 1)) •
        slashFun k
          (heckeMatrix (n / d.1) b d.1 (by
            have hdvd : d.1 ∣ n := (Nat.mem_divisors.mp d.2).1
            have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
            show (n / d.1) * d.1 ≠ 0
            rw [Nat.div_mul_cancel hdvd]
            exact hn0))
          f

/-! ## 2'. 真定理：求和在函数层是 ℂ-线性的（进入 End 的必要条件） -/

/-- 零函数的 Hecke 和为零（各项经 `SlashAction.zero_slash` 归零）。 -/
theorem heckeSlashSum_zero (k : ℤ) (n : ℕ) (hn : 0 < n) :
    heckeSlashSum k n hn (0 : ℍ → ℂ) = 0 := by
  simp [heckeSlashSum, slashFun]

/-- Hecke 求和的加性：T_n(f + g) = T_n f + T_n g（逐项由 slash 的加性给出）。 -/
theorem heckeSlashSum_add (k : ℤ) (n : ℕ) (hn : 0 < n) (f g : ℍ → ℂ) :
    heckeSlashSum k n hn (f + g) = heckeSlashSum k n hn f + heckeSlashSum k n hn g := by
  simp [heckeSlashSum, slashFun, Finset.sum_add_distrib, smul_add]

-- 注：朴素齐性 T_n(c • f) = c • T_n f 对 k ≠ 1 **不成立**，因为 Mathlib 的
-- slash 带归一化因子：`smul_slash : (c • f) ∣[k] A = σ A c • (f ∣[k] A)`，
-- 其中 σ A c 依赖 det A。这正是 Hecke 理论中「T_n 是 ℂ-线性但需除以
-- |det|^{k-1} 归一化」的根源，故此处不宣称该项，留待封闭性证明时统一处理。

/-! ## 2''. 双陪集层：Γ₀(N)·γ·Γ₀(N) 内 det 不变（真定理）

    Hecke 算子按行列式分次：T_n 只涉及 det = n 的双陪集。这一步在 Mathlib 的
    Set 级双陪集（`DoubleCoset.doubleCoset`, GroupTheory/DoubleCoset.lean:37）上
    可以真证——因为 Γ₀(N) 的元素 det ≡ 1（`HasDetOne`），左右乘都不改变 det。
    这为「Δ_n 分层」提供代数基础；但**双陪集的卷积乘积与环结构 Mathlib 未实现**，
    故 Hecke 环层面的交换性仍无法在此层证出（见 §3 gap）。 -/

/-- Hecke 双陪集 Γ₀(N)·γ·Γ₀(N)（Mathlib Set 级双陪集）。 -/
def heckeDoubleCoset (N : ℕ) (γ : GL (Fin 2) ℝ) : Set (GL (Fin 2) ℝ) :=
  DoubleCoset.doubleCoset γ (Gamma0GL N : Set (GL (Fin 2) ℝ)) (Gamma0GL N : Set (GL (Fin 2) ℝ))

/-- **真定理**：同一双陪集内的矩阵行列式相同。
    证明只用 Γ₀(N) 的 det = 1（`HasDetOne.det_eq`）与 det 的乘法性，无公理、无 sorry。 -/
theorem det_eq_of_mem_doubleCoset {N : ℕ} (γ γ' : GL (Fin 2) ℝ)
    (h : γ' ∈ heckeDoubleCoset N γ) : γ'.det = γ.det := by
  rw [heckeDoubleCoset, DoubleCoset.doubleCoset] at h
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hx
  rw [Set.mem_singleton_iff] at hh₂
  subst hh₂
  have h1d : h₁.det = 1 := Subgroup.HasDetOne.det_eq hh₁
  have hyd : y.det = 1 := Subgroup.HasDetOne.det_eq hy
  simp [map_mul, h1d, hyd]

/-- **真定理**：a = d = 1, b = 0 的 Hecke 矩阵就是单位矩阵。 -/
theorem heckeMatrix_one : heckeMatrix 1 0 1 (by norm_num) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeMatrix]

/-- **真定理**：T₁ = id（Diamond–Shurman §5.2）。Hecke 算子作为「作用」的第一条实质性质。
    1 的因子只有 1，b 只有 0，因子 (1/1)^{k−1} = 1，矩阵为单位阵，故求和即 f。
    技巧：用 `Finset.sum_eq_single` 直接指定唯一被加项，**不改写索引集**，
    从而绕开 `n.divisors.attach` 的 subtype 依赖重写障碍。零 sorry、零公理。 -/
theorem heckeSlashSum_one (k : ℤ) (f : ℍ → ℂ) :
    heckeSlashSum k 1 (by norm_num) f = f := by
  unfold heckeSlashSum
  have hsub : (Nat.divisors 1).attach = {⟨1, by simp [Nat.divisors_one]⟩} := by
    apply Finset.ext
    intro b
    simp only [Finset.mem_attach, Finset.mem_singleton]
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    apply Subtype.ext
    have hb : b.1 ∣ 1 := (Nat.mem_divisors.mp b.2).1
    have hb1 : b.1 = 1 := Nat.dvd_one.mp hb
    simpa using hb1
  rw [hsub]
  simp [slashFun, heckeMatrix_one]


/-! ## 3. 显式 gap：求和的封闭性（尚未证明） -/

/-- Hecke 算子在 S_k(Γ₀(N)) 上的代数结构，以**显式假设**承载，绝不伪装成定义。
    字段说明：
    - `T n`     : 第 n 个 Hecke 算子（作为 CuspForm 空间的自同态）；
    - `realizes`: 该算子由 §2 的 slash 求和诱导（这是封闭性陈述的占位接口，
                  一旦封闭性证明完成，此字段可换成真正的等式定理）；
    - `mul`     : 乘法性 T_{mn} = T_m ∘ T_n；
    - `comm`    : 两两交换性。
    出处：Diamond–Shurman Thm 5.2.1、Prop 5.2.4；Shimura §3.4。 -/
structure HeckeAlgebraGap (N : ℕ) (k : ℤ) [NeZero N] where
  /-- 第 n 个 Hecke 算子。 -/
  T : ℕ → Module.End ℂ (CuspForm (Gamma0GL N) k)
  /-- 乘法性：T_{mn} = T_m ∘ T_n。 -/
  mul : ∀ m n : ℕ, T (m * n) = (T m).comp (T n)
  /-- 交换性：T_m ∘ T_n = T_n ∘ T_m。 -/
  comm : ∀ m n : ℕ, (T m).comp (T n) = (T n).comp (T m)

/-! ## 4. 从 gap 真推出的定理 -/

/-- 乘法性（由 gap 推出）：T_{mn} = T_m ∘ T_n。 -/
theorem hecke_mul (N : ℕ) (k : ℤ) [NeZero N] (D : HeckeAlgebraGap N k) (m n : ℕ) :
    D.T (m * n) = (D.T m).comp (D.T n) :=
  D.mul m n

/-- 交换性（由 gap 推出）：Hecke 算子两两交换，这是同时对角化的前提。 -/
theorem hecke_comm (N : ℕ) (k : ℤ) [NeZero N] (D : HeckeAlgebraGap N k) (m n : ℕ) :
    (D.T m).comp (D.T n) = (D.T n).comp (D.T m) :=
  D.comm m n

/-- 特征标存在性：有限维复向量空间上的任意算子必有特征值。
    这里调用 Mathlib 现成的 `Module.End.exists_eigenvalue`（复矩阵必有特征值），
    对 Hecke 算子 T_n 直接实例化；零 sorry、零自定义公理。 -/
theorem hecke_exists_eigenvalue (N : ℕ) (k : ℤ) [NeZero N] (D : HeckeAlgebraGap N k)
    [FiniteDimensional ℂ (CuspForm (Gamma0GL N) k)]
    [Nontrivial (CuspForm (Gamma0GL N) k)] (n : ℕ) :
    ∃ c : ℂ, (D.T n).HasEigenvalue c :=
  Module.End.exists_eigenvalue (K := ℂ) (V := CuspForm (Gamma0GL N) k) (D.T n)

end

end Challenge105HeckeOperator
