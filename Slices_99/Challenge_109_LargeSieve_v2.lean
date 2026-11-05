/-
Copyright (c) 2026 ChenGuang Studio. All rights reserved.
Challenge 109 v2（第 109 号切片）：H1 层圆法/大筛法不等式骨架
================================================================================

【战术（用户 2026-11-04 指令，方案二）】
  108 的 `ContourResidueGap`（复分析围道留数）**正式封存冻结**，不再阻塞主干；
  H1 层（圆法 / 大筛）正面拉起，零点侧留作 110+ 的终极远景。
  去底库找 `Complex.normSq` 与平方和界限的现成定理，能真证的立刻真证，不能的用高阶 Gap 隔离。

【本切片相对旧骨架（Challenge_109_LargeSieve.lean，149 行、核心定理 sorry）的升级】
  旧骨架：`large_sieve_inequality` 整条 `by sorry`，正交性也是 sorry。
  v2：把大筛法拆成 5 个可分离环节，前 4 环**全部真证**，只剩 2 个高阶 Gap：

  （真证）A. 加法特征基本性质：‖e(x·n)‖ = 1、normSq = 1、乘法性、幂形式；
  （真证）B. 几何和公式 + 一般正交性：`∑_{n<q} e(xn) = 0`（当 e(x)=1 的有理条件成立）；
  （真证）C. 有理点特征值判定：`e(a/q) = 1 ↔ q ∣ a`（直接吃库定理
             `Complex.exp_two_pi_mul_I_mul_div_eq_one_iff`），由此**真证** Farey 点上的
             特征正交性 `∑_{n<q} e(an/q) = 0`（旧骨架的头号 sorry 被消灭）；
  （真证）D. 单点 Cauchy–Schwarz 界：`normSq (∑_{n<N} a_n e(xn)) ≤ N · ∑‖a_n‖²`
             （吃 `Real.sum_mul_le_sqrt_mul_sqrt`），大筛法的解析引擎；
  （真证）E. 平凡大筛：`∑_{x∈S} ‖∑_{n<N} a_n e(xn)‖² ≤ #S · N · ∑‖a_n‖²`。

  （Gap）G-H1α `LargeSieveGap`：Farey 点族上的 sharp 密度因子 `N + Q²` 版大筛不等式；
  （Gap）G-H1β `GridParsevalGap`：有理网格上的 Parseval 精确等式（等号型）。

【与 108 的接口】
  `ContourResidueGap` 状态 = FROZEN（108 已封存，零 sorry，公理仅 propext/Classical.choice/Quot.sound）。
  本切片不 import 108，亦不复用其围道 Gap；H1 层自成闭环。

红线：绝不去补 Mathlib 基建（不碰 LevelNFE / G1 / 复分析 residue API）。
-/

-- H3→H1 跨层咬合：素数侧系数（108）作为大筛（109）的输入系数序列。
import Slices_99.Challenge_108_PolePrime
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Real.Sqrt

namespace Goldbach109

open Finset

/-! ## §1 加法特征 `e(x·n) = exp(2πi·x·n)` 的基本性质（真证） -/

/-- 加法特征：`addChar x n = exp(2πi·x·n)`。 -/
noncomputable def addChar (x : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * x * (n : ℝ)) : ℝ) * Complex.I)

/-- 加法特征模长恒为 1。 -/
theorem addChar_norm (x : ℝ) (n : ℕ) : ‖addChar x n‖ = 1 := by
  have h : addChar x n = Complex.exp (((2 * Real.pi * x * (n : ℝ)) : ℝ) * Complex.I) := rfl
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- 加法特征的 `normSq` 恒为 1（`Complex.normSq` 现成定理链）。 -/
theorem addChar_normSq (x : ℝ) (n : ℕ) : Complex.normSq (addChar x n) = 1 := by
  rw [Complex.normSq_eq_norm_sq, addChar_norm]
  norm_num

/-- `x = 0` 时特征退化为 1。 -/
@[simp] theorem addChar_zero_arg (n : ℕ) : addChar 0 n = 1 := by
  unfold addChar
  simp

/-- `n = 0` 时特征取 1。 -/
@[simp] theorem addChar_zero_idx (x : ℝ) : addChar x 0 = 1 := by
  unfold addChar
  simp

/-- 指数上的加法对应特征相乘。 -/
theorem addChar_add (x : ℝ) (m n : ℕ) : addChar x (m + n) = addChar x m * addChar x n := by
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- 特征可写成一次特征之幂（几何和化归的关键）。 -/
theorem addChar_pow (x : ℝ) (n : ℕ) : addChar x n = addChar x 1 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [addChar_add, ih, pow_succ]

/-! ## §2 几何和公式与一般正交性（真证） -/

/-- 一次特征非平凡时的几何和闭式（吃 `geom_sum_eq`）。 -/
theorem addChar_geom_sum (x : ℝ) {N : ℕ} (h : addChar x 1 ≠ 1) :
    ∑ n ∈ range N, addChar x n = (addChar x N - 1) / (addChar x 1 - 1) := by
  have hrewrite : (∑ n ∈ range N, addChar x n) = ∑ n ∈ range N, addChar x 1 ^ n :=
    Finset.sum_congr rfl (fun n _ => addChar_pow x n)
  rw [hrewrite, addChar_pow x N]
  exact geom_sum_eq h N

/-- **正交性（一般形式）**：若 `e(x)^q = 1` 且 `e(x) ≠ 1`，则长度 `q` 的特征和为零。 -/
theorem addChar_orthogonal (x : ℝ) {q : ℕ} (hq : addChar x q = 1) (h1 : addChar x 1 ≠ 1) :
    ∑ n ∈ range q, addChar x n = 0 := by
  have h := addChar_geom_sum x (N := q) h1
  rw [hq] at h
  exact h.trans (by norm_num)

/-! ## §3 有理点上的特征值判定与 Farey 正交性（真证，直接吃库定理） -/

/-- `addChar` 在有理点 `a/q` 上可写成 `exp(2πi·a/q)` 的标准形式。 -/
theorem addChar_div_eq_exp (a q : ℕ) (hq : q ≠ 0) :
    addChar ((a : ℝ) / (q : ℝ)) 1
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (q : ℂ)) := by
  unfold addChar
  congr 1
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  push_cast
  field_simp

/-- **有理特征值判定**：`e(a/q) = 1 ↔ q ∣ a`（库定理 `exp_two_pi_mul_I_mul_div_eq_one_iff`）。 -/
theorem addChar_div_eq_one_iff {a q : ℕ} (hq : q ≠ 0) :
    addChar ((a : ℝ) / (q : ℝ)) 1 = 1 ↔ q ∣ a := by
  rw [addChar_div_eq_exp a q hq, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hq]

/-- `q` 次幂必回到 1：`e(a/q)^q = 1`。 -/
theorem addChar_div_self {a q : ℕ} (hq : 0 < q) :
    addChar ((a : ℝ) / (q : ℝ)) q = 1 := by
  have hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  have hL : addChar ((a : ℝ) / (q : ℝ)) q
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / ((1 : ℕ) : ℂ)) := by
    unfold addChar
    congr 1
    have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq0
    push_cast
    field_simp
  rw [hL, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by norm_num : (1 : ℕ) ≠ 0)]
  exact one_dvd a

/-- **Farey 点上的特征正交性（旧骨架头号 sorry 的真证落地）**：
    `q ≥ 2` 且 `q ∤ a` 时，`∑_{n<q} e(an/q) = 0`。 -/
theorem exponentialSum_div_orthogonal {a q : ℕ} (hq : 2 ≤ q) (h : ¬ q ∣ a) :
    ∑ n ∈ range q, addChar ((a : ℝ) / (q : ℝ)) n = 0 := by
  have hq0 : q ≠ 0 := by omega
  have hne : addChar ((a : ℝ) / (q : ℝ)) 1 ≠ 1 := fun hcontra =>
    h ((addChar_div_eq_one_iff hq0).mp hcontra)
  have h := addChar_geom_sum ((a : ℝ) / (q : ℝ)) (N := q) hne
  rw [addChar_div_self (by omega)] at h
  exact h.trans (by norm_num)

/-! ## §4 加权指数和与系数能量（真证） -/

/-- 加权指数和：`∑_{n<N} a_n · e(x·n)`。 -/
noncomputable def weightedExpSum (N : ℕ) (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ range N, a n * addChar x n

/-- 系数能量：`∑_{n<N} |a_n|²`（用 `Complex.normSq`）。 -/
noncomputable def coefficientEnergy (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ range N, Complex.normSq (a n)

/-- `normSq` 型能量与 `‖·‖²` 型能量一致。 -/
theorem coefficientEnergy_eq_sum_sq (N : ℕ) (a : ℕ → ℂ) :
    coefficientEnergy N a = ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  unfold coefficientEnergy
  exact Finset.sum_congr rfl (fun n _ => Complex.normSq_eq_norm_sq (a n))

/-- 系数能量非负。 -/
theorem coefficientEnergy_nonneg (N : ℕ) (a : ℕ → ℂ) : 0 ≤ coefficientEnergy N a := by
  rw [coefficientEnergy_eq_sum_sq]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ## §5 单点 Cauchy–Schwarz 界（大筛法解析引擎，真证） -/

/-- 单点界（根式形式）：`‖∑_{n<N} a_n e(xn)‖ ≤ √(∑‖a_n‖²) · √N`。 -/
theorem weightedExpSum_norm_le (N : ℕ) (a : ℕ → ℂ) (x : ℝ) :
    ‖weightedExpSum N a x‖ ≤ Real.sqrt (∑ n ∈ range N, ‖a n‖ ^ 2) * Real.sqrt (N : ℝ) := by
  have h1 : ‖weightedExpSum N a x‖ ≤ ∑ n ∈ range N, ‖a n‖ := by
    unfold weightedExpSum
    calc ‖∑ n ∈ range N, a n * addChar x n‖ ≤ ∑ n ∈ range N, ‖a n * addChar x n‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ range N, ‖a n‖ := by
          refine Finset.sum_congr rfl ?_
          intro n _
          rw [norm_mul, addChar_norm, mul_one]
  have h2 : ∑ n ∈ range N, ‖a n‖
      ≤ Real.sqrt (∑ n ∈ range N, ‖a n‖ ^ 2) * Real.sqrt (N : ℝ) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (range N) (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    simpa using hcs
  exact h1.trans h2

/-- 单点界（`normSq` 形式）：`normSq (∑_{n<N} a_n e(xn)) ≤ N · ∑ normSq(a_n)`。 -/
theorem weightedExpSum_normSq_le (N : ℕ) (a : ℕ → ℂ) (x : ℝ) :
    Complex.normSq (weightedExpSum N a x) ≤ (N : ℝ) * coefficientEnergy N a := by
  have hE : (0 : ℝ) ≤ ∑ n ∈ range N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h := weightedExpSum_norm_le N a x
  rw [Complex.normSq_eq_norm_sq, coefficientEnergy_eq_sum_sq]
  calc ‖weightedExpSum N a x‖ ^ 2
      = ‖weightedExpSum N a x‖ * ‖weightedExpSum N a x‖ := by ring
    _ ≤ (Real.sqrt (∑ n ∈ range N, ‖a n‖ ^ 2) * Real.sqrt (N : ℝ))
          * (Real.sqrt (∑ n ∈ range N, ‖a n‖ ^ 2) * Real.sqrt (N : ℝ)) :=
        mul_self_le_mul_self (norm_nonneg _) h
    _ = (Real.sqrt (∑ n ∈ range N, ‖a n‖ ^ 2)) ^ 2 * (Real.sqrt (N : ℝ)) ^ 2 := by ring
    _ = (∑ n ∈ range N, ‖a n‖ ^ 2) * (N : ℝ) := by
        rw [Real.sq_sqrt hE, Real.sq_sqrt hN]
    _ = (N : ℝ) * (∑ n ∈ range N, ‖a n‖ ^ 2) := by ring

/-! ## §6 平凡大筛（真证） -/

/-- 任意实数点集上的筛和：`∑_{x∈S} normSq(∑_{n<N} a_n e(xn))`。 -/
noncomputable def sieveSumOver (S : Finset ℝ) (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ x ∈ S, Complex.normSq (weightedExpSum N a x)

/-- **平凡大筛**：`∑_{x∈S} ‖∑_{n<N} a_n e(xn)‖² ≤ #S · N · ∑‖a_n‖²`。 -/
theorem trivial_large_sieve (S : Finset ℝ) (N : ℕ) (a : ℕ → ℂ) :
    sieveSumOver S N a ≤ (S.card : ℝ) * ((N : ℝ) * coefficientEnergy N a) := by
  have hpt : ∀ x ∈ S, Complex.normSq (weightedExpSum N a x)
      ≤ (N : ℝ) * coefficientEnergy N a :=
    fun x _ => weightedExpSum_normSq_le N a x
  calc sieveSumOver S N a ≤ ∑ x ∈ S, (N : ℝ) * coefficientEnergy N a :=
        Finset.sum_le_sum hpt
    _ = (S.card : ℝ) * ((N : ℝ) * coefficientEnergy N a) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## §7 Farey 点族（真证定义与基数界） -/

/-- 分母 `≤ Q` 的既约分数 `a/q ∈ [0,1)` 构成的点族。 -/
noncomputable def fareyPoints (Q : ℕ) : Finset ℝ :=
  ((range (Q + 1)).filter (fun q => 0 < q)).biUnion fun q =>
    ((range q).filter (fun a => Nat.Coprime a q)).image (fun a : ℕ => (a : ℝ) / (q : ℝ))

/-- Farey 点族基数界：`#fareyPoints Q ≤ (Q+1)²`。 -/
theorem fareyPoints_card_le (Q : ℕ) : (fareyPoints Q).card ≤ (Q + 1) * (Q + 1) := by
  unfold fareyPoints
  refine (Finset.card_biUnion_le).trans ?_
  have h1 : ∑ q ∈ (range (Q + 1)).filter (fun q => 0 < q),
        (((range q).filter (fun a => Nat.Coprime a q)).image (fun a : ℕ => (a : ℝ) / (q : ℝ))).card
      ≤ ∑ q ∈ (range (Q + 1)).filter (fun q => 0 < q), q := by
    refine Finset.sum_le_sum ?_
    intro q _
    calc (((range q).filter (fun a => Nat.Coprime a q)).image (fun a : ℕ => (a : ℝ) / (q : ℝ))).card
          ≤ ((range q).filter (fun a => Nat.Coprime a q)).card := Finset.card_image_le
      _ ≤ (range q).card := Finset.card_filter_le _ _
      _ = q := Finset.card_range q
  have h2 : ∑ q ∈ (range (Q + 1)).filter (fun q => 0 < q), q
      ≤ ∑ q ∈ (range (Q + 1)).filter (fun q => 0 < q), Q := by
    refine Finset.sum_le_sum ?_
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    omega
  refine (h1.trans h2).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((range (Q + 1)).filter (fun q => 0 < q)).card ≤ Q + 1 :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range (Q + 1))
  calc ((range (Q + 1)).filter (fun q => 0 < q)).card * Q
      ≤ (Q + 1) * Q := Nat.mul_le_mul_right Q hc
    _ ≤ (Q + 1) * (Q + 1) := Nat.mul_le_mul_left (Q + 1) (Nat.le_succ Q)

/-! ## §8 高阶 Gap 隔离（命题型封装，零公理污染） -/

/-- **G-H1α**：Farey 点族上的 sharp 大筛不等式（密度因子 `N + Q²`）。
    这是 H1 层唯一的核心缺口：需 well-spaced 结构 + Bessel 型正交估计，留作后续切片。 -/
structure LargeSieveGap (Q N : ℕ) (a : ℕ → ℂ) : Prop where
  bound : sieveSumOver (fareyPoints Q) N a
    ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a

/-- **G-H1β**：有理网格上的 Parseval 精确等式（等号型，双层求和的交换工作）。 -/
structure GridParsevalGap (M N : ℕ) (a : ℕ → ℂ) : Prop where
  parseval : ∑ k ∈ range M, Complex.normSq (weightedExpSum N a ((k : ℝ) / (M : ℝ)))
    = (M : ℝ) * coefficientEnergy N a

/-- 由 `LargeSieveGap` 直接落地 sharp 形式的大筛不等式（接口焊死）。 -/
theorem large_sieve_of_gap {Q N : ℕ} {a : ℕ → ℂ} (h : LargeSieveGap Q N a) :
    sieveSumOver (fareyPoints Q) N a
      ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a :=
  h.bound

/-- sharp 密度因子不弱于平凡密度因子（真证）：`N ≤ N + Q²`。 -/
theorem sharp_density_ge_trivial (Q N : ℕ) :
    (N : ℝ) ≤ (N : ℝ) + (Q : ℝ) ^ 2 := by
  have h : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := sq_nonneg _
  linarith

/-! ## §9 封口：H1 层已落地清单 -/

/-- Farey 点族上的平凡大筛（真证落地：H1 层无条件可用的防线）。 -/
theorem farey_trivial_large_sieve (Q N : ℕ) (a : ℕ → ℂ) :
    sieveSumOver (fareyPoints Q) N a
      ≤ ((fareyPoints Q).card : ℝ) * ((N : ℝ) * coefficientEnergy N a) :=
  trivial_large_sieve (fareyPoints Q) N a

/-- H1 层态势汇总（真证）：平凡界对 Farey 点族有效，sharp 界等价于消解 `LargeSieveGap`。 -/
theorem h1_layer_status (Q N : ℕ) (a : ℕ → ℂ) :
    sieveSumOver (fareyPoints Q) N a
        ≤ ((fareyPoints Q).card : ℝ) * ((N : ℝ) * coefficientEnergy N a)
      ∧ (LargeSieveGap Q N a →
          sieveSumOver (fareyPoints Q) N a
            ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a) :=
  ⟨farey_trivial_large_sieve Q N a, fun h => h.bound⟩

end Goldbach109


namespace Goldbach109

/-! ## ★ 跨层焊点（H3 → H1）：素数侧系数接入大筛机器

    108 号切片把显式公式右侧拆成「极点侧 + 素数侧 + 零点侧」，其中素数侧给出
    系数序列 `n ↦ primeSideTerm s n = (Λ n : ℂ) · n^{-s}`（Λ 为 von Mangoldt）。
    109 号切片的大筛只需要一个抽象系数序列 `a : ℕ → ℂ`。
    本节把两者**真的接上**：素数侧系数直接喂进大筛，得到可复用的上界与能量非负性。
    这不是 #check 层的并列，而是证明体里 `trivial_large_sieve` 被素数侧实例化。 -/

/-- **H3→H1 连接引理（真证）**：素数侧系数序列可被平凡大筛界约束。 -/
theorem primeSide_large_sieve_bound (S : Finset ℝ) (s : ℂ) (N : ℕ) :
    sieveSumOver S N (fun n => Challenge108.primeSideTerm s n)
      ≤ (S.card : ℝ) * ((N : ℝ) * coefficientEnergy N (fun n => Challenge108.primeSideTerm s n)) :=
  trivial_large_sieve S N _

/-- 素数侧系数的能量非负（真证）。 -/
theorem primeSide_coefficientEnergy_nonneg (s : ℂ) (N : ℕ) :
    0 ≤ coefficientEnergy N (fun n => Challenge108.primeSideTerm s n) :=
  coefficientEnergy_nonneg N _

/-- **跨层打包（108 与 109 在同一命题体内咬合）**：
    素数侧能量非负 ∧ 素数侧指数和被大筛界控制。 -/
theorem primeSide_sieve_bundle (S : Finset ℝ) (s : ℂ) (N : ℕ) :
    0 ≤ coefficientEnergy N (fun n => Challenge108.primeSideTerm s n)
      ∧ sieveSumOver S N (fun n => Challenge108.primeSideTerm s n)
          ≤ (S.card : ℝ) * ((N : ℝ) * coefficientEnergy N (fun n => Challenge108.primeSideTerm s n)) :=
  ⟨primeSide_coefficientEnergy_nonneg s N, primeSide_large_sieve_bound S s N⟩

end Goldbach109
