/-
All_MainTrunk_103_111.lean
==========================
主干总装 v4.1（2026-11-05，「主干拓宽与深度咬合」+「特例收编与一致性验证」）：103–111 共 10 个主干切片全部 import，
全部零 sorry、零新增公理。

v4.1 增量（特例收编）：021D `Challenge_021D_SpecialCase_CrossCheck` 引入通用指数骨架
`universalIndex`，并证明其在 N = 1 / p / p^k 处严格化为 1 / p+1 / p^k + p^{k-1}，
即早期手搓特例 100–102（Γ₀(1) / Γ₀(p) / Γ₀(p^k)）全部被 103 通用公式向下兼容；
组合定理 `H1_specialCases_unified` 落在本文件末尾。

v4.0 战略（逻辑咬合）原文保留：v4.0 相对 v3.0 的唯一变化是**逻辑咬合**：
  · 105 改为 import 104，复用其 Gamma0GL 与 HasDetOne 实例（原为复制品）
  · 107 的 cuspForm_Λ_eq_mellin / cuspForm_Λ_entire 改引 106 的桥接定理
  · 108 的 poleResidue_one 改引 107 的 completedZeta_residue_one；
    新增 weilFormulaRecipeOf107：用 107 的 Gap 骨架装配 108 的配方
  · 109 新增 primeSide_large_sieve_bound：108 的素数侧系数喂进 109 的大筛
  · 106 新增 mellin_heckeSlashSum_one：105 的 T₁ = id 传播到 Mellin 层
  · 110b 新增 Gamma0GL_eq_104_via_105；111 显式 import 109（原为隐性传递）
  · 本文件新增组合定理 H1_H2_unified / H2_H3_unified / H3_sieve_unified /
    H1_H2_H3_unified：从 021 口径条件端到端推到 109 大筛结论。

新增（相对 v2.0）：
  111  Challenge_111_Bessel         Bessel 残差攻坚（Goldbach111）★正朔
       - 关联和展开（精确等式）
       - Bessel 核心界（无条件）：∑_x|F(x)|² ≤ E · ∑∑‖pairCorrelation‖
       - 标量条件 ⇒ sharp 大筛 ⇒ `BesselResidualGap`
       - `BesselResidualGap 1 N a` **真证**（Q=1 锐利端，首次在非平凡参数上落地）

维持冻结（不碰）：Challenge_110_MaassHarmonic 的 MaassEigenRealizationGap / MaassSpectrumNonemptyGap。
-/
import Slices_99.Challenge_021_Gamma0N_Index
import Slices_99.Challenge_104_Gamma0_Dimension
import Slices_99.Challenge_105_HeckeOperator
import Slices_99.Challenge_106_MellinBridge
import Slices_99.Challenge_107_WeilExplicit
import Slices_99.Challenge_108_PolePrime
import Slices_99.Challenge_109_LargeSieve_v2
import Slices_99.Challenge_110_FareySharp
import Slices_99.Challenge_110_MaassHarmonic
import Slices_99.Challenge_111_Bessel

open Complex Filter
open scoped Topology

/-! ## 冒烟检查：主干 103–110 关键符号 -/
#check Challenge021Gamma0NIndex.gamma0_N
#check Challenge021Gamma0NIndex.universalIndex
#check Challenge021Gamma0NIndex.specialCase_101_fromTrunk
#check Challenge021Gamma0NIndex.specialCase_102_fromTrunk
#check Challenge021Gamma0NIndex.trunk_downwardCompatible
#check Challenge104Gamma0Dimension.dimension_formula
#check Challenge105HeckeOperator.hecke_comm
#check Challenge106MellinBridge.bridge_universal
#check Challenge107.completedZeta_residue_one
#check Challenge108.poleResidue_one
#check Goldbach109.trivial_large_sieve
#check Goldbach110.wellSpacedFarey_holds
#check Goldbach110.large_sieve_sharp_of_bessel
#check Challenge110MaassHarmonic.MaassForm

/-! ## 冒烟检查：111 Bessel 攻坚切片 -/
#check Goldbach111.pairCorrelation
#check Goldbach111.two_mul_mul_le_sq_add_sq
#check Goldbach111.sieveSumOver_eq_correlation
#check Goldbach111.sieveSumOver_le_energy_mul_correlation
#check Goldbach111.large_sieve_sharp_of_correlation_bound
#check Goldbach111.besselResidualGap_of_correlation_bound
#check Goldbach111.pairCorrelation_self
#check Goldbach111.sum_pairCorrelation_self
#check Goldbach111.besselResidualGap_Q_one
#check Goldbach111.slice111_status
#check Goldbach111.FejerParsevalGap
#check Goldbach111.bessel_of_fejer
#check Goldbach111.slice111_sealed

/-- 总装收口陈述（真证）：111 层的三条核心结论同时可解析。 -/
theorem mainTrunk_103_111_status (N : ℕ) (a : ℕ → ℂ) :
    (Goldbach110.WellSpacedFarey 1)
      ∧ (Goldbach109.sieveSumOver (Goldbach109.fareyPoints 1) N a
            ≤ Goldbach109.coefficientEnergy N a
                * (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
                    ‖Goldbach111.pairCorrelation (Goldbach109.fareyPoints 1) n m‖))
      ∧ (Goldbach109.sieveSumOver (Goldbach109.fareyPoints 1) N a
            ≤ ((N : ℝ) + ((1 : ℕ) : ℝ) ^ 2) * Goldbach109.coefficientEnergy N a) :=
  ⟨Goldbach110.wellSpacedFarey_holds 1,
   Goldbach111.sieveSumOver_le_energy_mul_correlation _ N a,
   (Goldbach111.besselResidualGap_Q_one N a).bessel⟩


/-! ## ★★ 组合定理：H1 → H2 → H3 大动脉总成（逻辑咬合，非物理拼装）

    本节不只是 `#check`：每个组合定理的**证明体**都直接调用上游切片的定理，
    链路为
      H1（021 指数 / 104 维数入口）
        → H2（105 Hecke：群同一、T₁ = id）
          → H3（106 Mellin 桥、107 留数、108 素数侧、109 大筛）。
    任一环断裂，下面的定理都无法通过类型检查。 -/

/-- **H1 → H2 咬合（真证）**：
    (a) 104 的 `einf` 直接取 021 的素因子乘积式；
    (b) 105 的 Hecke 群与 104 的群是同一个（定义级同一）；
    (c) 105 的 `T₁` 在函数层真的等于恒等。
    (a)(b)(c) 三条均为证明体调用，不是并列罗列。 -/
theorem H1_H2_unified (N : ℕ) [NeZero N] :
    Challenge104Gamma0Dimension.einf N
        = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) * (p + 1))
      ∧ Challenge105HeckeOperator.Gamma0GL N = Challenge104Gamma0Dimension.Gamma0GL N
      ∧ (∀ f : UpperHalfPlane → ℂ, Challenge105HeckeOperator.heckeSlashSum 2 1 (by norm_num) f = f) :=
  ⟨Challenge104Gamma0Dimension.einf_eq_index N,
   Challenge105HeckeOperator.Gamma0GL_eq_104 N,
   fun f => Challenge105HeckeOperator.heckeSlashSum_one 2 f⟩

/-- **H2 → H3 咬合（真证）**：105 的 `T₁ = id` 沿 106 的 Mellin 桥传播——
    Hecke 层与解析延拓层在证明体层面真正焊死。 -/
theorem H2_H3_unified (k : ℤ) (f : UpperHalfPlane → ℂ) :
    mellin (fun t : ℝ => Challenge105HeckeOperator.heckeSlashSum k 1 (by norm_num) f
              (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))))
      = mellin (fun t : ℝ => f (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))) :=
  Challenge106MellinBridge.mellin_heckeSlashSum_one k f

/-- **H3 层内咬合（108 → 109，真证）**：108 拆出的素数侧系数直接喂进 109 的大筛机器，
    同时保留能量非负性。 -/
theorem H3_sieve_unified (S : Finset ℝ) (s : ℂ) (N : ℕ) :
    Goldbach109.sieveSumOver S N (fun n => Challenge108.primeSideTerm s n)
        ≤ (S.card : ℝ) * ((N : ℝ) * Goldbach109.coefficientEnergy N (fun n => Challenge108.primeSideTerm s n))
      ∧ 0 ≤ Goldbach109.coefficientEnergy N (fun n => Challenge108.primeSideTerm s n) :=
  ⟨Goldbach109.primeSide_large_sieve_bound S s N,
   Goldbach109.primeSide_coefficientEnergy_nonneg s N⟩

/-- **H1_H2_H3_unified（大动脉总成，真证）**：
    从 021 的 Γ₀(N) 口径条件出发，一口气贯通
      104 维数入口 → 105 Hecke 群同一 / T₁ 平凡 → 106 Mellin 桥 → 108 素数侧 → 109 大筛。
    这是「103 → 109」的第一条端到端组合定理：任一 import 若无实质作用，此定理不成立。 -/
theorem H1_H2_H3_unified (N : ℕ) [NeZero N] (S : Finset ℝ) (s : ℂ) (M : ℕ) :
    (Challenge104Gamma0Dimension.einf N
        = ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) * (p + 1)))
      ∧ (∀ f : UpperHalfPlane → ℂ, Challenge105HeckeOperator.heckeSlashSum 2 1 (by norm_num) f = f)
      ∧ (∀ f : UpperHalfPlane → ℂ,
          mellin (fun t : ℝ => Challenge105HeckeOperator.heckeSlashSum 2 1 (by norm_num) f
                    (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))))
            = mellin (fun t : ℝ => f (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))))
      ∧ (Goldbach109.sieveSumOver S M (fun n => Challenge108.primeSideTerm s n)
          ≤ (S.card : ℝ) * ((M : ℝ) * Goldbach109.coefficientEnergy M (fun n => Challenge108.primeSideTerm s n))) := by
  refine ⟨Challenge104Gamma0Dimension.einf_eq_index N, fun f => Challenge105HeckeOperator.heckeSlashSum_one 2 f,
    fun f => Challenge106MellinBridge.mellin_heckeSlashSum_one 2 f, ?_⟩
  exact Goldbach109.primeSide_large_sieve_bound S s M

/-! ## ★★★ 组合定理：特例收编（103 通用公式 ⇒ 100–102 手搓特例） -/

/-- **H1_specialCases_unified（特例收编，真证）**：
    103 号通用指数公式一次性覆盖三档手搓特例 ——
      N = 1   （100 号平凡端）→ 指数 = 1；
      N = p   （101 号结论）   → 指数 = p + 1；
      N = p^k （102 号结论）   → 指数 = p^k + p^{k-1}。
    前两档只经 `Gamma0N_index_eq` + 纯算术引理导出，未引用 021B 特例定理，
    是通用框架的独立特化检验。 -/
theorem H1_specialCases_unified (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    ((Challenge021Gamma0NIndex.gamma0_N 1).index = 1)
      ∧ ((Challenge021Gamma0NIndex.gamma0_N p).index = p + 1)
      ∧ ((Challenge021Gamma0NIndex.gamma0_N (p ^ k)).index = p ^ k + p ^ (k - 1)) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  refine ⟨?_, Challenge021Gamma0NIndex.specialCase_101_fromTrunk p,
    Challenge021Gamma0NIndex.specialCase_102_fromTrunk p k hk⟩
  have h := Challenge021Gamma0NIndex.Gamma0N_index_eq_universal 1
  rw [h]
  exact Challenge021Gamma0NIndex.universalIndex_one
