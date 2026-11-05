/-
Copyright (c) 2026. All rights reserved.
Challenge 105-B（G3 低成本版）：Γ(1) 层级双陪集封闭性地基
================================================================================

目标（用户指令 G3）：在最基础的地基 Γ(1) = SL(2,ℤ) 上，把 Hecke 双陪集的
"封闭性"拆成可证的代数部分与必须显式登记的组论部分，绝不用假定义蒙混。

本文件结构：
  ① `Gamma1GL`：Γ(1) 提升为 GL(2,ℝ) 子群（真定义，`⊤ : Subgroup (SL(2,ℤ))` 经
     `mapGL ℝ` 映入 GL(2,ℝ)），并给出 `HasDetOne` 实例（infer_instance 成功）。
  ② `doubleCosetSet` + `det_eq_of_mem_doubleCoset`：**真定理**，双陪集内 det 不变
     （纯代数，只用 det = 1）。
  ③ `slash_invariant_conj`：**真定理（G3 的代数核心）**。若 f 在 G 下 slash-不变，
     则对任意 γ，f∣[k]γ 在共轭子群 γ⁻¹Gγ 下不变。这正是 Hecke 理论中
     「双陪集每个单子项落在其稳定化子的不变子空间里」的严格表述
     （Diamond–Shurman §5.2 的逐项论证）。证明只用 `SlashAction.slash_mul`。
  ④ `slash_sum_invariant`：**真定理**，不变性对求和封闭（`SlashAction.sum_slash`）。
  ⑤ `RepPermData` / `sum_slash_invariant_of_permData`：**真定理（非重言）**。
     把「代表元族 M 在 Γ(1) 作用下被置换」这一组合数据形式化为结构体，
     并**真推出**：裸双陪集和 Σ_i f∣[k]M_i 在 Γ(1) 下不变。
  ⑥ `Gamma1RepPermGap`：显式 gap，只承载⑤中那个**组合事实**（Smith 标准形 /
     双陪集有限性下代表元的置换存在性，Mathlib 无此定理），不承载任何结论。

诚实边界（严禁对外宣称 T_n 在 Γ(1) 上已封闭）：
  · 已真证：单子项共轭不变性、求和封闭性、置换数据 ⇒ 和不变性。
  · 仍缺：代表元置换数据的存在性（Smith 标准形的组论部分）；
  · 仍缺（技术性，非数学难点）：T_n 完整公式里的幂权标量因子 (n/d)^{k−1}
    在 slash 下需 `UpperHalfPlane.σ` 固定实数标量这一事实的接入。

文献：Diamond–Shurman, *A First Course in Modular Forms*, §5.2；
      Shimura, §3.4。
-/
import Slices_99.Challenge_105_HeckeOperator
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.GroupTheory.DoubleCoset

open scoped BigOperators MatrixGroups UpperHalfPlane ModularForm
open Matrix Matrix.SpecialLinearGroup

namespace Challenge105BGamma1

noncomputable section

/-! ## 0. Γ(1) = SL(2,ℤ) 的 GL(2,ℝ) 实现 -/

/-- Γ(1) 提升为 GL(2,ℝ)：`SL(2,ℤ)` 经 `mapGL` 映入 `GL(2,ℝ)`。 -/
def Gamma1GL : Subgroup (GL (Fin 2) ℝ) :=
  (⊤ : Subgroup (SpecialLinearGroup (Fin 2) ℤ)).map (mapGL ℝ)

/-- Γ(1) 的元素行列式恒为 1（由 `SL(2,ℤ)` 的 `HasDetOne` 在其像上继承）。 -/
instance Gamma1GL.hasDetOne : Subgroup.HasDetOne Gamma1GL := by
  change Subgroup.HasDetOne ((⊤ : Subgroup (SpecialLinearGroup (Fin 2) ℤ)).map (mapGL ℝ))
  infer_instance

/-! ## 1. 双陪集与行列式分层 -/

/-- 双陪集 G·γ·G（显式定义，便于在 Lean 中直接展开）。 -/
def doubleCosetSet (G : Subgroup (GL (Fin 2) ℝ)) (γ : GL (Fin 2) ℝ) : Set (GL (Fin 2) ℝ) :=
  {γ' | ∃ a ∈ G, ∃ b ∈ G, γ' = a * γ * b}

/-- **真定理**：同一双陪集内行列式不变（Hecke 算子按 det = n 分次的代数基础）。 -/
theorem det_eq_of_mem_doubleCoset {G : Subgroup (GL (Fin 2) ℝ)} [Subgroup.HasDetOne G]
    {γ γ' : GL (Fin 2) ℝ} (h : γ' ∈ doubleCosetSet G γ) : γ'.det = γ.det := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  rw [map_mul, map_mul, Subgroup.HasDetOne.det_eq ha, Subgroup.HasDetOne.det_eq hb, one_mul,
    mul_one]

/-- Γ(1) 情形的行列式分层（① + ② 的实例化）。 -/
theorem det_eq_of_mem_doubleCoset_gamma1 {γ γ' : GL (Fin 2) ℝ}
    (h : γ' ∈ doubleCosetSet Gamma1GL γ) : γ'.det = γ.det :=
  det_eq_of_mem_doubleCoset h

/-! ## 2. G3 的代数核心：单子项的共轭不变性 -/

/-- **真定理（G3 核心）**：若 `f` 在子群 `G` 下 slash-不变，则对任意 `γ : GL(2,ℝ)`，
`f ∣[k] γ` 在共轭子群 `γ⁻¹ G γ` 下不变。

    这是 Hecke 算子封闭性证明中「每个双陪集代表元只需在其稳定化子上检验」
    的严格形式：Diamond–Shurman §5.2 逐项论证的代数部分。
    证明只用 slash 的乘性 `SlashAction.slash_mul` 与 `group`。 -/
theorem slash_invariant_conj {k : ℤ} {G : Subgroup (GL (Fin 2) ℝ)} {f : ℍ → ℂ}
    (hG : ∀ g ∈ G, f ∣[k] g = f) (γ : GL (Fin 2) ℝ) (δ : G) :
    (f ∣[k] γ) ∣[k] ((γ⁻¹ * (δ : GL (Fin 2) ℝ)) * γ) = f ∣[k] γ := by
  rw [← SlashAction.slash_mul]
  have hγ : γ * ((γ⁻¹ * (δ : GL (Fin 2) ℝ)) * γ) = (δ : GL (Fin 2) ℝ) * γ := by group
  rw [hγ, SlashAction.slash_mul, hG δ δ.2]

/-! ## 3. 不变性对求和封闭 -/

/-- **真定理**：若每一项都在 `δ` 下 slash-不变，则有限和也不变。 -/
theorem slash_sum_invariant {k : ℤ} {ι : Type*} {G : Subgroup (GL (Fin 2) ℝ)}
    {δ : G} {s : Finset ι} {a : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, (a i) ∣[k] (δ : GL (Fin 2) ℝ) = a i) :
    (∑ i ∈ s, a i) ∣[k] (δ : GL (Fin 2) ℝ) = ∑ i ∈ s, a i := by
  rw [SlashAction.sum_slash]
  exact Finset.sum_congr rfl h

/-! ## 4. 代表元置换数据 ⇒ 双陪集和的不变性（真推导，非重言） -/

/-- 代表元族的**置换数据**：`δ` 把每个代表元 `M i` 送去「Γ(1) 元素 × 另一个代表元」。
    这是「双陪集代表元在 Γ 的作用下被置换」的精确形式化。 -/
structure RepPermData (ι : Type*) [DecidableEq ι] (M : ι → GL (Fin 2) ℝ)
    (δ : GL (Fin 2) ℝ) where
  /-- 代表元上的置换。 -/
  perm : ι ≃ ι
  /-- 每个代表元乘以 δ 后落回 Γ(1) 乘另一个代表元。 -/
  rho : ι → Gamma1GL
  eq : ∀ i, M i * δ = (rho i : GL (Fin 2) ℝ) * M (perm i)

/-- **真定理（G3 主定理）**：给定置换数据，裸双陪集和 `Σ_i f∣[k]M_i` 在 Γ(1) 下不变。

    这是「Hecke 算子保持 Γ(1)-不变性」的代数骨架：证明完全由
    ③ 与 ⑤ 的数据与 `Equiv.sum_comp` 重排完成，零 sorry、零自定义公理。 -/
theorem sum_slash_invariant_of_permData {k : ℤ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → GL (Fin 2) ℝ} {f : ℍ → ℂ} (hf : ∀ g ∈ Gamma1GL, f ∣[k] g = f)
    (δ : Gamma1GL) (D : RepPermData ι M (δ : GL (Fin 2) ℝ)) :
    (∑ i, f ∣[k] M i) ∣[k] (δ : GL (Fin 2) ℝ) = ∑ i, f ∣[k] M i := by
  rw [SlashAction.sum_slash]
  have hterm : ∀ i, (f ∣[k] M i) ∣[k] (δ : GL (Fin 2) ℝ) = f ∣[k] M (D.perm i) := by
    intro i
    rw [← SlashAction.slash_mul, D.eq i, SlashAction.slash_mul, hf (D.rho i) (D.rho i).2]
  simp only [hterm]
  exact Equiv.sum_comp D.perm (fun i => f ∣[k] M i)

/-! ## 5. 显式 gap：置换数据的存在性（组论部分，Mathlib 未提供） -/

/-- **显式 gap**：对每个 `δ ∈ Γ(1)`，代表元族存在置换数据。
    这是 Smith 标准形/双陪集有限性的组论内容（Diamond–Shurman §5.2 的
    「Δ_n = ⊔_j Γ α_j」那一步），Mathlib 的 `HeckeRing/Defs.lean` 只有类型层，
    无此定理；故以显式假设承载，绝不伪装成已证。 -/
def Gamma1RepPermGap (ι : Type*) [Fintype ι] [DecidableEq ι]
    (M : ι → GL (Fin 2) ℝ) : Prop :=
  ∀ δ : Gamma1GL, Nonempty (RepPermData ι M (δ : GL (Fin 2) ℝ))

/-- **条件定理**：若置换数据存在（gap），则裸双陪集和在 Γ(1) 下不变。
    结论与 gap 严格分离：gap 只提供组合数据，不提供结论本身。 -/
theorem gamma1_invariant_of_repPermGap {k : ℤ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → GL (Fin 2) ℝ} {f : ℍ → ℂ} (hf : ∀ g ∈ Gamma1GL, f ∣[k] g = f)
    (hgap : Gamma1RepPermGap ι M) :
    ∀ δ : Gamma1GL, (∑ i, f ∣[k] M i) ∣[k] (δ : GL (Fin 2) ℝ) = ∑ i, f ∣[k] M i := by
  intro δ
  obtain ⟨D⟩ := hgap δ
  exact sum_slash_invariant_of_permData hf δ D

end

end Challenge105BGamma1
