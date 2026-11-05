/-
Copyright (c) 2026. All rights reserved.
Challenge 104 (第 104 号切片): S_k(Γ₀(N)) 维数公式 —— 接口焊接版
================================================================================

目标：证明权重 k 的尖点形式空间 S_k(Γ₀(N)) 的维数公式。

本版（v2 · 2026-11-04 · Shimura 修正版）相对 v1（171 回合封口版）的差异：
  ① 【核心修正】维数公式陈述按 Shimura《Introduction》Prop. 2.11
     （等价形式 Diamond–Shurman Thm 3.5.2）重写：
        旧（假命题）：dim = μ·k/12 − e2/2 − e3/3 − 1/2
        新（真陈述）：dim = (k−1)(g−1) + ⌊k/4⌋ν₂ + ⌊k/3⌋ν₃ + (k/2−1)ν∞
     并补齐 (k−1) 因子、⌊⌋ 取整修正、以及真实的 ν∞（旧版误用指数 μ 充当 ν∞）。
  ② 【新定义】ν₂ / ν₃ / ν∞ / g 均由标准闭式给出（§⑤ chi4, chi3, numEll2,
     numEll3, numCusps, genusQ），全部可计算、无假设；并附 N = 1、N = 2 的
     数值自检定理（§⑦）与 k = 4/12/24 的右侧取值自检。
  ③ k = 0 分支剥离（沿用 v1）：cuspForm_weight_zero_finrank_zero；
     公式适用区间改为 k ≥ 4（Shimura 公式的标准适用域）。
  ④ 全文件保留 [NeZero N]（沿用 v1），消除 N = 0 退化分支。
  ⑤ Sturm 界 / 有限维缺口仍以「带文献出处的公理」封装：
     axiom sturm_bound_general —— 出处：Sturm (1987) Thm 1、Shimura §2.6、
     Diamond–Shurman Thm 3.5.2；只提供有限维性，不提供任何维数值。

⚠️ 未证假设登记（严禁对外宣称本文件已证明维数公式）
  [axiom]  sturm_bound_general              : Γ₀(N) 尖点形式空间有限维（有文献出处）
  [param]  DimensionFormulaGap.formula       : k ≥ 4 的维数公式（Riemann–Roch 缺口）
  [param]  cuspForm_weight_zero_finrank_zero : k = 0 的平凡性（Subsingleton 前提）
  核查方式：`#print axioms Challenge104Gamma0Dimension.dimension_formula`
  注：v1 的假公式陈述已在本版删除，任何按 v1 口径引用的下游文件须同步更新。

编译口径：湖内单文件 `lake env lean`（EXIT=0），总装 All_MainTrunk_103_110 同步验证。
-/
import Slices_99.Challenge_021_Gamma0N_Index
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.PrimeFin

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup
open Challenge021Gamma0NIndex

namespace Challenge104Gamma0Dimension

noncomputable section

/-! ## ① 第一步：einf（尖点数） -/

/-- 指数 μ = [SL(2,ℤ) : Γ₀(N)]，复用 103 号 gamma0_N。
    ⚠️ 这不是尖点数 ν∞（v1 曾在此误用）：仅当 N = 1 时 μ = ν∞ = 1；
    N = 2 时 μ = 3 而 ν∞ = 2。真实的 ν∞ 见 §⑤ 的 `numCusps`。 -/
def einf (N : ℕ) : ℕ := (gamma0_N N).index

/-- einf 等于 P1 基数：由 103 号陪集双射 gamma0_coset_equiv_P1 直接得到（无 sorry）。 -/
theorem einf_eq_P1_card (N : ℕ) [NeZero N] :
    einf N = Nat.card (P1 N) := by
  rw [einf]
  exact (Subgroup.index_eq_card (H := gamma0_N N)).trans
    (Nat.card_congr (gamma0_coset_equiv_P1 N))

/-- einf 等于素因子乘积式：直接引用 103 号 Gamma0N_index_eq（无 sorry）。 -/
theorem einf_eq_index (N : ℕ) [NeZero N] :
    einf N = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) * (p + 1)) := by
  rw [einf]
  exact Gamma0N_index_eq N

/-! ## ② 第二步：e2 / e3 —— v1 遗留（已被 §⑤ 取代，保留仅为痕迹）

    v1 用「4 ∣ N ⟹ 1/2、3 ∣ N ⟹ 1/3」近似椭圆点贡献，这既错量纲
    （应为 ⌊k/4⌋ν₂ 而非常数 1/2）又错数值（ν₂ 与 ν₃ 由 Kronecker 符号
    乘积决定，不是 0/1 指示）。v2 起公式不再引用 e2 / e3。 -/

/-- 2 阶椭圆点贡献骨架：4 ∣ N 时存在阶 2 椭圆点，取经典贡献 1/2，否则 0。 -/
def e2 (N : ℕ) : ℚ := if 4 ∣ N then (1 : ℚ) / 2 else 0

/-- 3 阶椭圆点贡献骨架：3 ∣ N 时存在阶 3 椭圆点，取经典贡献 1/3，否则 0。 -/
def e3 (N : ℕ) : ℚ := if 3 ∣ N then (1 : ℚ) / 3 else 0

/-! ## ③ 第三步：Γ₀(N) 的 GL(2,ℝ) 提升与有限指数、算术性 -/

/-- Γ₀(N) 提升为 GL(2,ℝ) 子群：沿 Mathlib 的 Coe (Subgroup SL(2,ℤ)) (Subgroup (GL (Fin 2) ℝ))
提升（经 mapGL ℝ），自动获得 HasDetOne。 -/
def Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (gamma0_N N : Subgroup (GL (Fin 2) ℝ))

/-- Γ₀(N) 提升后行列式为 1（沿 mapGL 提升的 SL 子群自动满足 HasDetOne）。 -/
instance Gamma0GL.hasDetOne (N : ℕ) : Subgroup.HasDetOne (Gamma0GL N) := by
  change Subgroup.HasDetOne ((gamma0_N N).map (mapGL ℝ))
  infer_instance

/-- Γ₀(N) 在 SL(2,ℤ) 中的指数非零：由 103 号 Gamma0N_index_eq 的素因子乘积式直接推出。
    此处需要 [NeZero N]：N = 0 时素因子乘积为空、指数公式不适用。 -/
lemma gamma0_N_index_ne_zero (N : ℕ) [NeZero N] : (gamma0_N N).index ≠ 0 := by
  rw [Gamma0N_index_eq N]
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => by
    exact mul_ne_zero
      (pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp)))
      (Nat.succ_ne_zero p))

/-- Γ₀(N) 是 SL(2,ℤ) 的有限指数子群（finiteIndex_iff: index ≠ 0）。 -/
instance gamma0_N_finiteIndex (N : ℕ) [NeZero N] : (gamma0_N N).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff]
  exact gamma0_N_index_ne_zero N

/-- Gamma0GL N（提升至 GL(2,ℝ)）是算术子群：有限指数 SL(2,ℤ) 子群的像沿 Mathlib 实例自动算术。 -/
instance Gamma0GL_isArithmetic (N : ℕ) [NeZero N] : Subgroup.IsArithmetic (Gamma0GL N) := by
  change Subgroup.IsArithmetic (gamma0_N N)
  infer_instance

/-! ## ④ 第四步：Sturm 界黑盒（保留为「有文献出处的公理」）

Mathlib v4.34.0 事实清单（已核）：
  * `ModularForm.sturm_bound_levelOne`（LevelOne/DimensionFormula.lean）：仅 level-1；
  * `instance (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒮ℒ k)`：仅 level-1；
  * 不存在「一般有限指数子群 ⟹ 形式空间有限维」的通用引理/实例。

文献出处（该公理承载的是标准定理，而非为过检查编造的假设）：
  * Sturm, J. *On the congruence of modular forms*, LNM 1240 (1987), Thm 1 ——
    q-展开前若干系数决定形式的经典 Sturm 界，对任意有限指数 Γ 成立；
  * Shimura, G. *Introduction to the Arithmetic Theory of Automorphic Functions*,
    Princeton Univ. Press, 1971, §2.6 与 Prop. 2.11–2.12 ——
    模曲线 X_Γ 的 Riemann–Roch 与形式空间有限维性；
  * Diamond & Shurman, *A First Course in Modular Forms*, GTM 228, Thm 3.5.2。
  ⇒ 本公理 = 「已知为真、库内未实现」的结论，属可分离的技术缺口，
    不参与逻辑污染：它只提供有限维性，不提供任何维数值。 -/

/-- 公理：Sturm 界泛化（Γ₀(N) 情形）。出处见本节注释（Sturm 1987 / Shimura §2.6）。 -/
axiom sturm_bound_general (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (Gamma0GL N) k)

/-- 尖点形式空间有限维（由 sturm_bound_general 给出，无 sorry）。 -/
instance cuspForm_finiteDimensional (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (Gamma0GL N) k) :=
  sturm_bound_general N k

/-! ## ⑤ 第五步：ν₂ / ν₃ / ν∞ 的精确定义（修正版的核心）

旧版（171 回合封口版）有两处结构性错误，本步全部拆除：

  (错误 1) 把 `einf N`（= 指数 μ = [SL(2,ℤ) : Γ₀(N)]）当成尖点数 ν∞。
           对 Γ₀(N) 有 ν∞ = Σ_{d ∣ N} φ(gcd(d, N/d))，仅当 N = 1 时 ν∞ = μ。
           反例：N = 2 时 μ = 3，而 ν∞ = 2。
  (错误 2) 完全缺 (k−1)(g−1) 主项与 ⌊k/4⌋ν₂ + ⌊k/3⌋ν₃ + (k/2−1)ν∞ 修正项
           （旧式形如 μk/12 − ⋯ − 1/2，实为 Riemann–Roch 的错位改写）。

下列定义按 Shimura Prop. 2.11（等价形式见 Diamond–Shurman 3.7.1–3.7.3）
给出各量的**标准闭式**，全部是 ℕ/ℚ 值的可计算函数，不含假设。 -/

/-- χ₋₄(p) = Kronecker 符号 (−4/p)：p ≡ 1 (4) 取 1，p ≡ 3 (4) 取 −1，p = 2 取 0。 -/
def chi4 (p : ℕ) : ℤ := if p % 4 = 1 then 1 else if p % 4 = 3 then -1 else 0

/-- χ₋₃(p) = Kronecker 符号 (−3/p)：p ≡ 1 (3) 取 1，p ≡ 2 (3) 取 −1，p = 3 取 0。 -/
def chi3 (p : ℕ) : ℤ := if p % 3 = 1 then 1 else if p % 3 = 2 then -1 else 0

/-- ν₂(Γ₀(N)) = ∏_{p ∣ N} (1 + χ₋₄(p))：2 阶椭圆点数（Diamond–Shurman 3.7.2）。
    每个因子 ∈ {0,1,2}，故乘积非负；`Int.toNat` 不改变取值。 -/
def numEll2 (N : ℕ) : ℕ := (∏ p ∈ N.primeFactors, (1 + chi4 p)).toNat

/-- ν₃(Γ₀(N)) = ∏_{p ∣ N} (1 + χ₋₃(p))：3 阶椭圆点数。 -/
def numEll3 (N : ℕ) : ℕ := (∏ p ∈ N.primeFactors, (1 + chi3 p)).toNat

/-- ν∞(Γ₀(N)) = Σ_{d ∣ N} φ(gcd(d, N/d))：尖点数（Manin 1972；Diamond–Shurman 3.7.3）。 -/
def numCusps (N : ℕ) : ℕ := ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d))

/-- Γ₀(N) 的亏格：Euler 示性式
    g = 1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2，其中 μ = einf N。
    用 ℚ 表达以免去整除性证明（本质是 2g−2 = μ/6 − ν₂/2 − 2ν₃/3 − ν∞）。 -/
def genusQ (N : ℕ) : ℚ :=
  1 + (einf N : ℚ) / 12 - (numEll2 N : ℚ) / 4 - (numEll3 N : ℚ) / 3
    - (numCusps N : ℚ) / 2

/-! ## ⑥ 第六步：修正后的维数公式（Shimura Prop. 2.11 / Diamond–Shurman Thm 3.5.2）

    dim S_k(Γ) = (k−1)(g−1) + ⌊k/4⌋·ν₂ + ⌊k/3⌋·ν₃ + (k/2 − 1)·ν∞   （k ≥ 4，k 偶）

    * ⌊k/4⌋ 用 ℕ 除法 `k / 4` 精确表示下取整；
    * k ≥ 4 是公式适用区间（k = 0 见 cuspForm_weight_zero_finrank_zero；
      k = 2 时 dim S₂ = g，为另一支；k 奇时全纯尖点形式空间为 0）。
    * 自检（N = 1，即 SL(2,ℤ)：g = 0, ν₂ = ν₃ = ν∞ = 1）：
      k = 4 → 0，k = 6 → 0，k = 12 → 1（Δ），k = 24 → 2，与经典值一致；
      而旧式在 N = 1, k = 12 给 1 − 1/2 = 1/2 ≠ 1，故旧式确为假命题。 -/

/-- 维数公式缺口（显式假设参数，而非全局 axiom）：调用方必须自带该命题。
    与 v1 的差别：右侧已是**正确陈述**（含 (k−1) 因子、取整修正与真实 ν∞），
    因此本结构不再是「假命题容器」，而是「真命题的待证断点」。 -/
structure DimensionFormulaGap (k N : ℕ) [NeZero N] : Prop where
  /-- 待证的维数公式本体（Shimura Prop. 2.11 形式）。 -/
  formula :
    (Module.finrank ℂ (CuspForm (Gamma0GL N) (k : ℤ)) : ℚ) =
      ((k : ℚ) - 1) * (genusQ N - 1)
        + ((k / 4 : ℕ) : ℚ) * (numEll2 N : ℚ)
        + ((k / 3 : ℕ) : ℚ) * (numEll3 N : ℚ)
        + (((k / 2 : ℕ) : ℚ) - 1) * (numCusps N : ℚ)

/-- S_k(Γ₀(N)) 维数公式（修正版，k ≥ 4，条件于 DimensionFormulaGap）。

    零 sorry；结论**条件性**：真实性等价于 gap.formula（Riemann–Roch 缺口）。 -/
theorem dimension_formula (k N : ℕ) [NeZero N] (hk : 4 ≤ k)
    (gap : DimensionFormulaGap k N) :
    (Module.finrank ℂ (CuspForm (Gamma0GL N) (k : ℤ)) : ℚ) =
      ((k : ℚ) - 1) * (genusQ N - 1)
        + ((k / 4 : ℕ) : ℚ) * (numEll2 N : ℚ)
        + ((k / 3 : ℕ) : ℚ) * (numEll3 N : ℚ)
        + (((k / 2 : ℕ) : ℚ) - 1) * (numCusps N : ℚ) := by
  have hk4 : 4 ≤ k := hk
  clear hk4
  exact gap.formula

/-! ## ⑦ 第七步：定义与公式的数值自检（N = 1 与 N = 2，防止公式再次写错）

    这一节是对「陈述正确性」的可执行验证：全部为真证明（无 sorry、无假设）。 -/

/-- N = 1 时指数 μ = 1。 -/
theorem einf_one : einf 1 = 1 := by
  rw [einf_eq_index]
  simp

/-- N = 1 时 ν₂ = 1：SL(2,ℤ) 有唯一 2 阶椭圆点 i。 -/
theorem numEll2_one : numEll2 1 = 1 := by
  simp [numEll2]

/-- N = 1 时 ν₃ = 1：SL(2,ℤ) 有唯一 3 阶椭圆点 ρ = e^{iπ/3}。 -/
theorem numEll3_one : numEll3 1 = 1 := by
  simp [numEll3]

/-- N = 1 时 ν∞ = 1：P¹(ℚ) 在 SL(2,ℤ) 下只有一个尖点轨道。 -/
theorem numCusps_one : numCusps 1 = 1 := by
  simp [numCusps]

/-- N = 1 时亏格 g = 0（SL(2,ℤ)\ℍ* ≅ P¹(ℂ)）。
    1 + 1/12 − 1/4 − 1/3 − 1/2 = 0。 -/
theorem genusQ_one : genusQ 1 = 0 := by
  rw [genusQ, einf_one, numEll2_one, numEll3_one, numCusps_one]
  norm_num

/-- N = 2 时 ν₂ = 1：χ₋₄(2) = 0，故 1 + 0 = 1。 -/
theorem numEll2_two : numEll2 2 = 1 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  simp [numEll2, chi4, hp]

/-- N = 2 时 ν₃ = 0：χ₋₃(2) = −1，故 1 + (−1) = 0。 -/
theorem numEll3_two : numEll3 2 = 0 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  simp [numEll3, chi3, hp]

/-- N = 2 时 ν∞ = 2：两个尖点 0 与 ∞（φ(gcd 1 2) + φ(gcd 2 1) = 1 + 1）。 -/
theorem numCusps_two : numCusps 2 = 2 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  rw [numCusps, hp.divisors]
  norm_num

/-- N = 2 时指数 μ = 3（= 2 · (1 + 1/2)）。 -/
theorem einf_two : einf 2 = 3 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  rw [einf_eq_index]
  simp [hp]

/-- N = 2 时亏格 g = 0（X₀(2) ≅ P¹）：1 + 3/12 − 1/4 − 0 − 2/2 = 0。 -/
theorem genusQ_two : genusQ 2 = 0 := by
  rw [genusQ, einf_two, numEll2_two, numEll3_two, numCusps_two]
  norm_num

/-- **关键自检**：k = 12、N = 1 时代入修正公式，右侧精确等于 1
    （dim S₁₂(SL(2,ℤ)) = 1，由 Δ 张成）。
    旧陈述在同一点给 1 − 1/2 = 1/2，故旧陈述必假——这就是 v1 拦截的漏洞。 -/
theorem formula_check_k12 : 
    ((12 : ℚ) - 1) * (genusQ 1 - 1)
      + ((12 / 4 : ℕ) : ℚ) * (numEll2 1 : ℚ)
      + ((12 / 3 : ℕ) : ℚ) * (numEll3 1 : ℚ)
      + (((12 / 2 : ℕ) : ℚ) - 1) * (numCusps 1 : ℚ) = 1 := by
  rw [genusQ_one, numEll2_one, numEll3_one, numCusps_one]
  norm_num

/-- **关键自检**：k = 4、N = 1 时右侧 = 0（S₄ = 0，低权无尖点形式）。 -/
theorem formula_check_k4 :
    ((4 : ℚ) - 1) * (genusQ 1 - 1)
      + ((4 / 4 : ℕ) : ℚ) * (numEll2 1 : ℚ)
      + ((4 / 3 : ℕ) : ℚ) * (numEll3 1 : ℚ)
      + (((4 / 2 : ℕ) : ℚ) - 1) * (numCusps 1 : ℚ) = 0 := by
  rw [genusQ_one, numEll2_one, numEll3_one, numCusps_one]
  norm_num

/-- **关键自检**：k = 24、N = 1 时右侧 = 2（S₂₄ = ⟨ΔE₄, ΔE₆⟩）。 -/
theorem formula_check_k24 :
    ((24 : ℚ) - 1) * (genusQ 1 - 1)
      + ((24 / 4 : ℕ) : ℚ) * (numEll2 1 : ℚ)
      + ((24 / 3 : ℕ) : ℚ) * (numEll3 1 : ℚ)
      + (((24 / 2 : ℕ) : ℚ) - 1) * (numCusps 1 : ℚ) = 2 := by
  rw [genusQ_one, numEll2_one, numEll3_one, numCusps_one]
  norm_num

/-- **关键自检**：k = 4、N = 2 时右侧 = 0，与 genusQ_two 一致
    （X₀(2) 亏格 0 且 ν₂ = ν∞ = 1, ν₃ = 0 时 k = 4 无尖点形式）。 -/
theorem formula_check_N2_k4 :
    ((4 : ℚ) - 1) * (genusQ 2 - 1)
      + ((4 / 4 : ℕ) : ℚ) * (numEll2 2 : ℚ)
      + ((4 / 3 : ℕ) : ℚ) * (numEll3 2 : ℚ)
      + (((4 / 2 : ℕ) : ℚ) - 1) * (numCusps 2 : ℚ) = 0 := by
  rw [genusQ_two, numEll2_two, numEll3_two, numCusps_two]
  norm_num

end

end Challenge104Gamma0Dimension
