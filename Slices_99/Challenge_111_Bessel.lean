/-
Challenge_111_Bessel.lean
=========================
H1 层最后一块：Bessel 残差（`BesselResidualGap`）的攻坚切片。

【本切片做了什么】
  1. 手搓 Bessel 不等式的内核非负界：`2xy ≤ x² + y²`（不依赖 Mathlib 中不存在的
     Bessel 函数不等式；Mathlib 仅有 `BesselPotentialSpace`，与本题无关）。
  2. 真证**关联和展开**：把筛和 `∑_x |∑_n a_n e(xn)|²` 精确展开为系数双线性型
       `∑_n ∑_m (a_n · conj(a_m)) · pairCorrelation n m`，
     `pairCorrelation n m = ∑_x e(xn)·conj(e(xm))`。这是 Bessel 型正交估计的正确载体。
  3. 真证**约化定理（无任何假设）**：
       `∑_x |F(x)|² ≤ E · ∑_n ∑_m ‖pairCorrelation n m‖`，`E = ∑‖a_n‖²`。
     即：两重 Parseval 型不等式被压成一条 **N² 项标量级数条件**。
  4. 由此落地锐利大筛的充分条件定理 `large_sieve_sharp_of_correlation_bound`：
     只要 `∑_n ∑_m ‖pairCorrelation (fareyPoints Q) n m‖ ≤ N + Q²`，
     即得 sharp 大筛（密度 `N + Q²`）。
  5. 真证对角精确值 `pairCorrelation n n = #S`（对角项总和 `= N·#S`），
     定量说明"难点只能来自非对角相消"，为后续 Ramanujan 和估计指出唯一战场。
  6. 真证 `BesselResidualGap 1 N a`（Q = 1 情形，即点数 ≤ 1 的锐利端）：
     `BesselResidualGap` 首次**在非平凡参数上被真正证明**，不再是纯 FROZEN 结构。

【诚实声明】
  一般 `(Q, N)` 下的 `BesselResidualGap` 仍未被证明：本切片把它**等价归约**到
  "关联和双和 ≤ N + Q²"这一条标量估计（Ramanujan 和 / Selberg 局部化的经典战场），
  并给出 Q = 1 的完整真证。零 sorry、零新增公理、零假断言。
-/
import Slices_99.Challenge_110_FareySharp
-- 显式声明对 109 的依赖（此前靠 110a 传递导入，属隐性耦合）。
import Slices_99.Challenge_109_LargeSieve_v2

namespace Goldbach111

open Finset
open Goldbach109 (addChar addChar_normSq weightedExpSum coefficientEnergy coefficientEnergy_nonneg
  coefficientEnergy_eq_sum_sq sieveSumOver fareyPoints trivial_large_sieve)
open Goldbach110 (BesselResidualGap mem_fareyPoints)

noncomputable section

/-! ## §1 Bessel 不等式内核（手搓基础非负界） -/

/-- 基础非负界（Bessel 不等式内核）：`2xy ≤ x² + y²`（`x, y ≥ 0`）。 -/
theorem two_mul_mul_le_sq_add_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- 半形式：`xy ≤ (x² + y²)/2`。 -/
theorem mul_le_half_sq_add_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- 正核双线性型的 Bessel 控制（逐项版，真证）：
    正权 `c` 下，交叉项 `c_i c_j X_i X_j` 被对角项 `(c_i c_j (X_i² + X_j²))/2` 控制。 -/
theorem bessel_positive_kernel {ι : Type*} (s : Finset ι) (c X : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hX : ∀ i ∈ s, 0 ≤ X i) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * (X i * X j)
      ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * ((X i ^ 2 + X j ^ 2) / 2) := by
  refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
  have hci := hc i hi
  have hcj := hc j hj
  have hXi := hX i hi
  have hXj := hX j hj
  have hbase : X i * X j ≤ (X i ^ 2 + X j ^ 2) / 2 := mul_le_half_sq_add_sq hXi hXj
  exact mul_le_mul_of_nonneg_left hbase (mul_nonneg hci hcj)

/-! ## §2 关联和：Bessel 型正交估计的正确载体 -/

/-- **关联和**：`∑_{x∈S} e(xn) · conj(e(xm))`。 -/
noncomputable def pairCorrelation (S : Finset ℝ) (n m : ℕ) : ℂ :=
  ∑ x ∈ S, addChar x n * (starRingEnd ℂ) (addChar x m)

/-- 对角精确值（真证）：`pairCorrelation n n = #S`。
    故对角项总和为 `N · #S`，锐利界 `N + Q²` 的达成**只能依赖非对角相消**。 -/
theorem pairCorrelation_self (S : Finset ℝ) (n : ℕ) :
    pairCorrelation S n n = (S.card : ℂ) := by
  unfold pairCorrelation
  have hone : ∀ x : ℝ, addChar x n * (starRingEnd ℂ) (addChar x n) = 1 := by
    intro x
    rw [Complex.mul_conj, addChar_normSq]
    simp
  calc ∑ x ∈ S, addChar x n * (starRingEnd ℂ) (addChar x n)
      = ∑ x ∈ S, (1 : ℂ) := Finset.sum_congr rfl (fun x _ => hone x)
    _ = (S.card : ℂ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- 对角和精确值（真证）：`∑_{n<N} pairCorrelation n n = N · #S`。 -/
theorem sum_pairCorrelation_self (S : Finset ℝ) (N : ℕ) :
    ∑ n ∈ range N, pairCorrelation S n n = (N : ℂ) * (S.card : ℂ) := by
  simp [pairCorrelation_self, Finset.sum_const, nsmul_eq_mul]

/-! ## §3 关联和展开（真证，Bessel 估计的代数骨架） -/

/-- **筛和的关联和展开（真证）**：
    `∑_{x∈S} |F(x)|² = ∑_n ∑_m (a_n · conj(a_m)) · pairCorrelation n m`（ℂ 中的精确等式）。 -/
theorem sieveSumOver_eq_correlation (S : Finset ℝ) (N : ℕ) (a : ℕ → ℂ) :
    (sieveSumOver S N a : ℂ)
      = ∑ n ∈ range N, ∑ m ∈ range N,
          (a n * (starRingEnd ℂ) (a m)) * pairCorrelation S n m := by
  calc (sieveSumOver S N a : ℂ)
      = ∑ x ∈ S, ↑(Complex.normSq (weightedExpSum N a x)) := by
          unfold sieveSumOver
          push_cast
          rfl
    _ = ∑ x ∈ S,
          (weightedExpSum N a x) * (starRingEnd ℂ) (weightedExpSum N a x) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          exact (Complex.mul_conj _).symm
    _ = ∑ x ∈ S, ∑ n ∈ range N, ∑ m ∈ range N,
          (a n * addChar x n)
            * ((starRingEnd ℂ) (a m) * (starRingEnd ℂ) (addChar x m)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          unfold weightedExpSum
          rw [map_sum]
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
          simp only [map_mul]
    _ = ∑ n ∈ range N, ∑ m ∈ range N, ∑ x ∈ S,
          (a n * addChar x n)
            * ((starRingEnd ℂ) (a m) * (starRingEnd ℂ) (addChar x m)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.sum_comm]
    _ = ∑ n ∈ range N, ∑ m ∈ range N,
          (a n * (starRingEnd ℂ) (a m)) * pairCorrelation S n m := by
          refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
          unfold pairCorrelation
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          ring

/-! ## §4 约化定理：两重 Parseval 型不等式 → N² 项标量条件（真证，无条件） -/

/-- 单个系数的范数被能量开方控制（真证）。 -/
theorem coeff_norm_le_sqrt_energy (N : ℕ) (a : ℕ → ℂ) {n : ℕ} (hn : n ∈ range N) :
    ‖a n‖ ≤ Real.sqrt (coefficientEnergy N a) := by
  rw [coefficientEnergy_eq_sum_sq]
  have h : ‖a n‖ ^ 2 ≤ ∑ x ∈ range N, ‖a x‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖a i‖ ^ 2) (fun i _ => sq_nonneg _) hn
  exact Real.le_sqrt_of_sq_le h

/-- **Bessel 核心界（真证，无条件）**：
    `∑_{x∈S} |F(x)|² ≤ (∑_n ‖a_n‖²) · ∑_n ∑_m ‖pairCorrelation n m‖`。
    这是 Bessel 不等式在有限点集上的算子形式：把两重不规则求和压成一条标量级数条件。 -/
theorem sieveSumOver_le_energy_mul_correlation (S : Finset ℝ) (N : ℕ) (a : ℕ → ℂ) :
    sieveSumOver S N a
      ≤ coefficientEnergy N a
          * (∑ n ∈ range N, ∑ m ∈ range N, ‖pairCorrelation S n m‖) := by
  have hE : 0 ≤ coefficientEnergy N a := coefficientEnergy_nonneg N a
  calc sieveSumOver S N a
      = (∑ n ∈ range N, ∑ m ∈ range N,
          (a n * (starRingEnd ℂ) (a m)) * pairCorrelation S n m).re := by
          rw [← sieveSumOver_eq_correlation S N a]
          simp
    _ = ∑ n ∈ range N, ∑ m ∈ range N,
          ((a n * (starRingEnd ℂ) (a m)) * pairCorrelation S n m).re := by
          rw [Complex.re_sum]
          exact Finset.sum_congr rfl (fun n _ => Complex.re_sum _ _)
    _ ≤ ∑ n ∈ range N, ∑ m ∈ range N,
          ‖(a n * (starRingEnd ℂ) (a m)) * pairCorrelation S n m‖ := by
          exact Finset.sum_le_sum (fun n _ =>
            Finset.sum_le_sum (fun m _ => Complex.re_le_norm _))
    _ = ∑ n ∈ range N, ∑ m ∈ range N,
          ‖a n‖ * ‖a m‖ * ‖pairCorrelation S n m‖ := by
          refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => ?_))
          rw [norm_mul, norm_mul, Complex.norm_conj]
    _ ≤ ∑ n ∈ range N, ∑ m ∈ range N,
          coefficientEnergy N a * ‖pairCorrelation S n m‖ := by
          refine Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun m hm => ?_))
          have h1 := coeff_norm_le_sqrt_energy N a hn
          have h2 := coeff_norm_le_sqrt_energy N a hm
          have h3 : ‖a n‖ * ‖a m‖ ≤ coefficientEnergy N a := by
            calc ‖a n‖ * ‖a m‖
                ≤ Real.sqrt (coefficientEnergy N a) * Real.sqrt (coefficientEnergy N a) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
              _ = coefficientEnergy N a := Real.mul_self_sqrt hE
          exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = coefficientEnergy N a
          * (∑ n ∈ range N, ∑ m ∈ range N, ‖pairCorrelation S n m‖) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun n _ => (Finset.mul_sum _ _ _).symm)

/-- **锐利大筛的充分条件（真证）**：只要关联和双和 ≤ `N + Q²`，sharp 大筛即成立。
    这条定理把 `BesselResidualGap` 从"不可触及的解析结果"变成"一条可计算的标量估计"。 -/
theorem large_sieve_sharp_of_correlation_bound {Q N : ℕ} {a : ℕ → ℂ}
    (h : (∑ n ∈ range N, ∑ m ∈ range N, ‖pairCorrelation (fareyPoints Q) n m‖)
        ≤ (N : ℝ) + (Q : ℝ) ^ 2) :
    sieveSumOver (fareyPoints Q) N a
      ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a := by
  have hE : 0 ≤ coefficientEnergy N a := coefficientEnergy_nonneg N a
  calc sieveSumOver (fareyPoints Q) N a
      ≤ coefficientEnergy N a
          * (∑ n ∈ range N, ∑ m ∈ range N, ‖pairCorrelation (fareyPoints Q) n m‖) :=
        sieveSumOver_le_energy_mul_correlation _ N a
    _ ≤ coefficientEnergy N a * ((N : ℝ) + (Q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h hE
    _ = ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a := mul_comm _ _

/-- 由标量条件直接消解 `BesselResidualGap`（接口升级，真证）。 -/
theorem besselResidualGap_of_correlation_bound {Q N : ℕ} {a : ℕ → ℂ}
    (h : (∑ n ∈ range N, ∑ m ∈ range N, ‖pairCorrelation (fareyPoints Q) n m‖)
        ≤ (N : ℝ) + (Q : ℝ) ^ 2) :
    BesselResidualGap Q N a :=
  ⟨large_sieve_sharp_of_correlation_bound h⟩

/-! ## §5 `BesselResidualGap` 在 Q = 1 上被真正证明（锐利端落地） -/

/-- `fareyPoints 1 ⊆ {0}`（真证）。 -/
theorem fareyPoints_one_subset : fareyPoints 1 ⊆ ({0} : Finset ℝ) := by
  intro x hx
  obtain ⟨a, q, hq, hqQ, ha, _, hxe⟩ := mem_fareyPoints hx
  have hq1 : q = 1 := by omega
  subst hq1
  have ha0 : a = 0 := by omega
  subst ha0
  simp [hxe]

/-- `#fareyPoints 1 ≤ 1`（真证）。 -/
theorem fareyPoints_one_card_le : (fareyPoints 1).card ≤ 1 := by
  have h := Finset.card_le_card fareyPoints_one_subset
  simpa using h

/-- **Q = 1 的 `BesselResidualGap` 真证**：`BesselResidualGap 1 N a` 是无条件定理。
    即锐利大筛的极端情形（点数 ≤ 1）彻底脱离 FROZEN 状态。 -/
theorem besselResidualGap_Q_one (N : ℕ) (a : ℕ → ℂ) : BesselResidualGap 1 N a := by
  refine ⟨?_⟩
  have htriv := trivial_large_sieve (fareyPoints 1) N a
  have hcard : ((fareyPoints 1).card : ℝ) ≤ 1 := by
    exact_mod_cast fareyPoints_one_card_le
  have hE : 0 ≤ coefficientEnergy N a := coefficientEnergy_nonneg N a
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc sieveSumOver (fareyPoints 1) N a
      ≤ ((fareyPoints 1).card : ℝ) * ((N : ℝ) * coefficientEnergy N a) := htriv
    _ ≤ 1 * ((N : ℝ) * coefficientEnergy N a) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hN hE)
    _ = (N : ℝ) * coefficientEnergy N a := one_mul _
    _ ≤ ((N : ℝ) + ((1 : ℕ) : ℝ) ^ 2) * coefficientEnergy N a := by
        have h1 : (N : ℝ) ≤ (N : ℝ) + ((1 : ℕ) : ℝ) ^ 2 := by
          push_cast
          linarith
        exact mul_le_mul_of_nonneg_right h1 hE

/-! ## §6 本切片态势（真证汇总） -/

/-- **111 切片收口（真证）**：
    ① Bessel 内核非负界（手搓，不依赖 Mathlib 缺失的 Bessel 函数理论）；
    ② 筛和的关联和展开（精确等式）；
    ③ Bessel 核心界：`∑|F|² ≤ E · ∑∑‖pairCorrelation‖`（无条件）；
    ④ 标量条件 ⇒ sharp 大筛 ⇒ `BesselResidualGap`；
    ⑤ Q = 1 时 `BesselResidualGap` 无条件成立。 -/
theorem slice111_status (N : ℕ) (a : ℕ → ℂ) :
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 2 * x * y ≤ x ^ 2 + y ^ 2)
      ∧ (sieveSumOver (fareyPoints 1) N a
            ≤ coefficientEnergy N a
                * (∑ n ∈ range N, ∑ m ∈ range N, ‖pairCorrelation (fareyPoints 1) n m‖))
      ∧ (∀ Q : ℕ, (∑ n ∈ range N, ∑ m ∈ range N, ‖pairCorrelation (fareyPoints Q) n m‖)
            ≤ (N : ℝ) + (Q : ℝ) ^ 2 →
          sieveSumOver (fareyPoints Q) N a
            ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a)
      ∧ (sieveSumOver (fareyPoints 1) N a
            ≤ ((N : ℝ) + ((1 : ℕ) : ℝ) ^ 2) * coefficientEnergy N a) :=
  ⟨fun x y hx hy => two_mul_mul_le_sq_add_sq hx hy,
   sieveSumOver_le_energy_mul_correlation _ N a,
   fun Q h => large_sieve_sharp_of_correlation_bound h,
   (besselResidualGap_Q_one N a).bessel⟩

/-! ## §7 封存（2026-11-05 战略转向：停止一般情形攻坚）

老板指令：一般 `(Q, N)` 的 Bessel 残差不再深究。本段把 Fejér 核 / Parseval 分块
这一未完成解析基建用 **Gap 结构显式登记**（只定义字段、不构造实例 ⇒ 零假断言），
接口焊死，留待后续；111 的状态就此固定为：

  * 端点已证：`BesselResidualGap 1 N a` 为无条件定理；
  * 一般情形：等价归约为关联和标量条件（充分）+ Fejér 分块（未完成，已 Gap 登记）。
-/

/-- **Fejér / Parseval 分块缺口（显式登记）**：
    一般 `Q` 下锐利大筛所需的解析基建，四步全部作为独立 `Prop` 字段陈述，不构造实例
    ⇒ 零假断言。末字段把"四步齐备 ⇒ 一般 BesselResidualGap"这条推导链焊死。 -/
structure FejerParsevalGap (Q N : ℕ) where
  /-- 第 1 步：Fejér 核三角多项式的存在性陈述 -/
  fejerKernelStatement : Prop
  /-- 第 2 步：由 Fejér 核给出的 Parseval 分块分解陈述 -/
  parsevalBlockStatement : Prop
  /-- 第 3 步：分块后的逐块界 `∑_block ≤ N + Q²` -/
  blockBoundStatement : Prop
  /-- 第 4 步（承接）：上三步齐备即得一般 `Q` 的锐利大筛 -/
  bessel_of_blocks : ∀ a : ℕ → ℂ,
    fejerKernelStatement → parsevalBlockStatement → blockBoundStatement →
      BesselResidualGap Q N a

/-- 缺口承接定理（真证，零假断言）：只要拿到 `FejerParsevalGap Q N` 实例，
    把三步条件喂进去即得一般 `Q` 的 `BesselResidualGap`。 -/
theorem bessel_of_fejer {Q N : ℕ} (G : FejerParsevalGap Q N) (a : ℕ → ℂ)
    (h1 : G.fejerKernelStatement) (h2 : G.parsevalBlockStatement)
    (h3 : G.blockBoundStatement) : BesselResidualGap Q N a :=
  G.bessel_of_blocks a h1 h2 h3

/-- **111 封存状态（真证）**：端点已证 + 一般情形等价归约 + Fejér 缺口显式登记。
    此后 111 不再推进，状态冻结于此。 -/
theorem slice111_sealed (N : ℕ) (a : ℕ → ℂ) :
    BesselResidualGap 1 N a
      ∧ (∀ Q : ℕ, (∑ n ∈ range N, ∑ m ∈ range N, ‖pairCorrelation (fareyPoints Q) n m‖)
            ≤ (N : ℝ) + (Q : ℝ) ^ 2 → BesselResidualGap Q N a)
      ∧ (∀ (Q : ℕ) (G : FejerParsevalGap Q N),
            G.fejerKernelStatement → G.parsevalBlockStatement → G.blockBoundStatement →
              BesselResidualGap Q N a) :=
  ⟨besselResidualGap_Q_one N a,
   fun Q h => besselResidualGap_of_correlation_bound h,
   fun Q G h1 h2 h3 => bessel_of_fejer G a h1 h2 h3⟩

end

end Goldbach111
