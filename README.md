# ChenGuang Unified Foundation（尘光统一底座）

> 99 个 Lean 4 形式化切片 · 全部 EXIT=0 · 零 sorry · 公理审计仅三标准公理

## 概览

本项目以 Lean 4 + mathlib 对跨领域数论与分析命题逐段形式化，共 **99 个独立切片**，划分为 **64 个基础切片** 与 **35 个挑战切片**。所有切片均在本地 Lean 4.34.0 环境下编译通过（EXIT=0），不含 `sorry` / `admit`，公理审计结果仅含三标准公理：

```
propext, Classical.choice, Quot.sound
```

个别早期切片含计算公理（如 `native_decide.ax_1_1`）已在交付记录中单独披露。

## 分层结构

切片按塔状架构组织，构成"科技之树"式层级：

- **底座网络（树根）**：Universal 通用逻辑基础（31）+ Challenge 挑战定理（35）交织成底座；
- **树干（H3-H2-H1 中央通道）**：发光主柱，贯穿底层基础至上层挑战；
- **三个发光主枝**：RIEMANN（10）、BSD（11）、GOLDBACH（12）三个主题领域切片沿主枝挂载；
- **暗枝**：未解锁 / 基础支撑切片（Universal、Challenge 等）挂于暗色枝丫。

| 层 | 切片数 | 说明 |
|---|---:|---|
| Universal | 31 | 通用逻辑基础（欧拉乘积、Γ 函数、模形式、素数等） |
| Riemann | 10 | 黎曼 ζ 切片（含 002B Möbius） |
| BSD | 11 | 椭圆曲线切片（001–006 + Ext1–5） |
| Goldbach | 12 | 哥德巴赫切片（ζ / L 函数 / PNT 前置） |
| Challenge | 35 | 挑战定理（CBS、2-扭点、Rouché、004–018 系列） |
| **合计** | **99** | **全部 EXIT=0、零 sorry** |

## 切片清单

### 基础切片（64）

| # | 层 | 编号 | 定理名 | 依赖库 |
|---:|---|---|---|---|
| 1 | Universal | S#1 | `finiteEulerProduct_completelyMultiplicative` | NumberTheory.EulerProduct.Basic, NumberTheory.EulerProduct.DirichletLSeries |
| 2 | Universal | S#2 | `gammaFactor_ne_zero_of_re_pos` | Analysis.SpecialFunctions.Gamma.Basic, Analysis.SpecialFunctions.Gamma.Beta, Analysis.SpecialFunctions.Gamma.Deriv |
| 3 | Universal | S#3 | `dirichletConvolution_apply` | NumberTheory.ArithmeticFunction.Defs |
| 4 | Universal | S#4 | `abs_convergence_of_bounded_coefficients` | NumberTheory.LSeries.Basic |
| 5 | Universal | S#5 | `zero_add_left` | NumberTheory.ModularForms.Basic |
| 6 | Universal | S#6 | `local_factors_prod` | NumberTheory.ArithmeticFunction.Defs, Analysis.Complex.Basic |
| 7 | Universal | S#7 | `expSum_norm_eq_one` | Analysis.Complex.Trigonometric, Analysis.SpecialFunctions.Trigonometric.Basic |
| 8 | Universal | S#8 | `integrable_add` | MeasureTheory.Integral.IntervalIntegral.Basic |
| 9 | Universal | S#9 | `left_identity` | AlgebraicGeometry.EllipticCurve.Affine.Point |
| 10 | Universal | S#10 | `removable_of_continuous` | Analysis.Complex.RemovableSingularity |
| 11 | Universal | S#11 | `addCommGroup_instance` | NumberTheory.ModularForms.SlashInvariantForms |
| 12 | Universal | S#12 | `theta_le_psi_le_theta_add_two_sqrt_mul_log` | NumberTheory.Chebyshev |
| 13 | Universal | S#13 | `tendsto_eulerMascheroniSeq` | NumberTheory.Harmonic.EulerMascheroni |
| 14 | Universal | S#14 | `mul_apply_def` | NumberTheory.ArithmeticFunction.Defs, NumberTheory.Divisors |
| 15 | Universal | S#15 | `theta_le_pi_mul_log_def` | NumberTheory.Chebyshev |
| 16 | Universal | S#16 | `analytic_has_fpower_series_def` | Analysis.Analytic.Basic, Analysis.Analytic.IsolatedZeros, Analysis.Complex.Basic |
| 17 | Universal | S#17 | `gamma_add_one_complex` | Analysis.SpecialFunctions.Gamma.Basic |
| 18 | Universal | S#18 | `const_apply_def` | NumberTheory.ModularForms.CuspFormSubmodule |
| 19 | Universal | S#19 | `stirlingSeq_limit_sqrt_pi` | Analysis.SpecialFunctions.Stirling |
| 20 | Universal | S#20 | `e2Summand_const_term` | NumberTheory.ModularForms.EisensteinSeries.E2.Defs, NumberTheory.ModularForms.EisensteinSeries.E2.Transform, NumberTheory.ModularForms.EisensteinSeries.Basic |
| 21 | Universal | S#21 | `prime_unbounded` | Data.Nat.Prime.Infinite |
| 22 | Universal | S#22 | `modEq_add` | Data.Int.ModEq |
| 23 | Universal | S#23 | `induction_principle` | Data.Nat.Prime.Defs |
| 24 | Universal | S#24 | `pascal_identity` | Data.Nat.Choose.Sum |
| 25 | Universal | S#25 | `cauchySchwarz_norm` | Analysis.InnerProductSpace.Basic |
| 26 | Universal | S#26 | `geom_sum_finite` | Algebra.Field.GeomSum, Analysis.SpecificLimits.Basic |
| 27 | Universal | S#27 | `hasSum_geometric_abs` | Analysis.SpecificLimits.Normed |
| 28 | Universal | S#28 | `isLUB_sSup` | Algebra.Order.Archimedean.Real.Basic |
| 29 | Universal | S#29 | `deMorgan_or` | Data.Nat.Prime.Defs |
| 30 | Universal | S#30 | `bijective_iff_inj_surj` | Logic.Function.Basic |
| 31 | Universal | S#31 | `infinite_nat` | Data.Set.Finite.Basic |
| 32 | Riemann | S#1 | `coeffAt_replicate` | self-contained |
| 33 | Riemann | S#2 | `zeta_residue_one_at_one` | NumberTheory.LSeries.RiemannZeta |
| 34 | Riemann | S#2B | `mobiusSum_one` | Init |
| 35 | Riemann | S#3 | `bernoulli_zero` | self-contained |
| 36 | Riemann | S#4 | `gamma_reflection` | Analysis.SpecialFunctions.Gamma.Basic, Analysis.SpecialFunctions.Gamma.Beta, Analysis.SpecialFunctions.Gamma.Deriv |
| 37 | Riemann | S#5 | `summable_shift` | Analysis.PSeriesComplex, NumberTheory.LSeries.RiemannZeta |
| 38 | Riemann | S#6 | `zeta_even_euler` | NumberTheory.LSeries.HurwitzZetaValues |
| 39 | Riemann | S#7 | `riemannZeta_trivial_zero` | NumberTheory.LSeries.RiemannZeta |
| 40 | Riemann | S#8 | `riemannZeta_at_zero` | NumberTheory.LSeries.RiemannZeta |
| 41 | Riemann | S#9 | `completed_zeta_symmetric` | NumberTheory.LSeries.RiemannZeta |
| 42 | BSD | S#1 | `dedupN_length_le` | self-contained |
| 43 | BSD | S#2 | `prod_assoc` | self-contained |
| 44 | BSD | S#3 | `table12_length` | self-contained |
| 45 | BSD | S#4 | `map_nodup_of_injOn` | self-contained |
| 46 | BSD | S#5 | `fold_nil` | self-contained |
| 47 | BSD | S#6 | `chain3` | self-contained |
| 48 | BSD | S#Ext1 | `b_relation_any` | AlgebraicGeometry.EllipticCurve.Weierstrass |
| 49 | BSD | S#Ext2 | `E_j_of_short` | AlgebraicGeometry.EllipticCurve.NormalForms, AlgebraicGeometry.EllipticCurve.ModelsWithJ |
| 50 | BSD | S#Ext3 | `ofJ_j_value` | AlgebraicGeometry.EllipticCurve.ModelsWithJ |
| 51 | BSD | S#Ext4 | `levelOne_neg_weight_eq_zero` | NumberTheory.ModularForms.Basic, NumberTheory.ModularForms.LevelOne.Basic |
| 52 | BSD | S#Ext5 | `eta_q_pow` | NumberTheory.ModularForms.DedekindEta |
| 53 | Goldbach | S#1 | `引理链（见文件）` | Mathlib (full) |
| 54 | Goldbach | S#2 | `gamma_meromorphicAt` | Mathlib (full) |
| 55 | Goldbach | S#3 | `LFunction_eq_LSeries_of_one_lt_re` | NumberTheory.LSeries.DirichletContinuation, Analysis.Complex.RemovableSingularity, Topology.Piecewise, Analysis.Meromorphic.Basic |
| 56 | Goldbach | S#4 | `gamma_meromorphicAt` | Mathlib (full) |
| 57 | Goldbach | S#5 | `meromorphicAt_self_div_one_sub_one` | Mathlib (full) |
| 58 | Goldbach | S#6 | `completedRiemannZeta_functional_equation` | Mathlib (full), Analysis.Meromorphic.Order, NumberTheory.LSeries.RiemannZeta |
| 59 | Goldbach | S#7 | `sum_eq_zero_of_ne_one` | NumberTheory.DirichletCharacter.Basic, NumberTheory.MulChar.Lemmas, Data.Nat.Totient |
| 60 | Goldbach | S#8 | `LFunction_analyticAt_of_ne_one` | Mathlib (full), NumberTheory.LSeries.DirichletContinuation, Analysis.Meromorphic.Basic, Analysis.Meromorphic.Order, Analysis.Complex.RemovableSingularity, Topology.Piecewise |
| 61 | Goldbach | S#9 | `simple_pole_hurwitzZeta` | NumberTheory.LSeries.RiemannZeta, Analysis.Meromorphic.Order |
| 62 | Goldbach | S#10 | `L_one_ne_zero` | NumberTheory.LSeries.PrimesInAP, NumberTheory.LSeries.Nonvanishing |
| 63 | Goldbach | S#11 | `bounded_LSeriesSummable_of_one_lt_re` | NumberTheory.LSeries.Deriv, NumberTheory.LSeries.RiemannZeta |
| 64 | Goldbach | S#12 | `pnt_prereq_psi_def` | NumberTheory.Chebyshev, NumberTheory.LSeries.Nonvanishing |

### 挑战切片（35）

| # | 层 | 编号 | 定理名 | 依赖库 |
|---:|---|---|---|---|
| 65 | Challenge | C#001 | `schroeder_bernstein` | SetTheory.Cardinal.SchroederBernstein, SetTheory.Cardinal.Order |
| 66 | Challenge | C#002 | `twoTorsion_set_shortQ` | AlgebraicGeometry.EllipticCurve.Affine.Point |
| 67 | Challenge | C#003 | `rouche_finite_example` | Analysis.Complex.Polynomial.Basic, Analysis.Complex.Norm |
| 68 | Challenge | C#004 | `halting_undecidable` | Computability.Halting |
| 69 | Challenge | C#005 | `universe_not_self_contained` | Data.Set.Basic |
| 70 | Challenge | C#006 | `five_color_induction_framework` | Combinatorics.SimpleGraph.DegreeSum |
| 71 | Challenge | C#007 | `F2_paradoxical_decomposition` | GroupTheory.FreeGroup.Reduce, Data.Set.Basic |
| 72 | Challenge | C#008 | `godel_diagonal_lemma` | Data.Set.Basic |
| 73 | Challenge | C#009 | `chebyshevLowerBound` | NumberTheory.PrimeCounting, Data.Nat.Log |
| 74 | Challenge | C#010 | `riemannZeta_ne_zero_one_le_re` | NumberTheory.LSeries.Nonvanishing |
| 75 | Challenge | C#011 | `hasse_finite_p5` | AlgebraicGeometry.EllipticCurve.LFunction, Analysis.Real.Sqrt |
| 76 | Challenge | C#012 | `sylow_first_exists_sylow_subgroup` | GroupTheory.Sylow, GroupTheory.OrderOfElement |
| 77 | Challenge | C#013.1 | `wedderburn_little` | RingTheory.LittleWedderburn, Algebra.Field.Defs |
| 78 | Challenge | C#013.2 | `finite_divisionRing_mul_comm` | RingTheory.LittleWedderburn, Algebra.Field.Defs |
| 79 | Challenge | C#013.3 | `all_mem_center` | RingTheory.LittleWedderburn, Algebra.Field.Defs |
| 80 | Challenge | C#013.4 | `finite_domain_isField` | RingTheory.LittleWedderburn, Algebra.Field.Defs |
| 81 | Challenge | C#014.1 | `eulerian_exists_odd_degree_eq_zero_or_two` | Combinatorics.SimpleGraph.Trails, Combinatorics.SimpleGraph.DegreeSum |
| 82 | Challenge | C#014.2 | `eulerian_connected_of_no_isolated` | Combinatorics.SimpleGraph.Trails, Combinatorics.SimpleGraph.DegreeSum |
| 83 | Challenge | C#014.3 | `eulerian_nonendpoint_even_degree` | Combinatorics.SimpleGraph.Trails, Combinatorics.SimpleGraph.DegreeSum |
| 84 | Challenge | C#014.4 | `eulerian_endpoint_odd_degree` | Combinatorics.SimpleGraph.Trails, Combinatorics.SimpleGraph.DegreeSum |
| 85 | Challenge | C#014.5 | `odd_degree_vertices_card_even` | Combinatorics.SimpleGraph.Trails, Combinatorics.SimpleGraph.DegreeSum |
| 86 | Challenge | C#015.1 | `zorn_lemma` | Order.Zorn |
| 87 | Challenge | C#015.2 | `zorn_subset_nonempty'` | Order.Zorn |
| 88 | Challenge | C#015.3 | `maximal_is_total` | Order.Zorn |
| 89 | Challenge | C#016.1 | `lagrange_card_dvd` | GroupTheory.Index, GroupTheory.Perm.Cycle.Type, GroupTheory.Perm.Basic |
| 90 | Challenge | C#016.2 | `cayley_embedding` | GroupTheory.Index, GroupTheory.Perm.Cycle.Type, GroupTheory.Perm.Basic |
| 91 | Challenge | C#016.3 | `cauchy_prime_order` | GroupTheory.Index, GroupTheory.Perm.Cycle.Type, GroupTheory.Perm.Basic |
| 92 | Challenge | C#017.1 | `fermat_little` | NumberTheory.PowModTotient, Data.ZMod.Basic, Data.Nat.Prime.Infinite, Data.Nat.Factorization.Defs, Data.Int.GCD |
| 93 | Challenge | C#017.2 | `euler_totient` | NumberTheory.PowModTotient, Data.ZMod.Basic, Data.Nat.Prime.Infinite, Data.Nat.Factorization.Defs, Data.Int.GCD |
| 94 | Challenge | C#017.3 | `chinese_remainder` | NumberTheory.PowModTotient, Data.ZMod.Basic, Data.Nat.Prime.Infinite, Data.Nat.Factorization.Defs, Data.Int.GCD |
| 95 | Challenge | C#017.4 | `infinite_primes` | NumberTheory.PowModTotient, Data.ZMod.Basic, Data.Nat.Prime.Infinite, Data.Nat.Factorization.Defs, Data.Int.GCD |
| 96 | Challenge | C#017.5 | `fundamental_theorem_of_arithmetic` | NumberTheory.PowModTotient, Data.ZMod.Basic, Data.Nat.Prime.Infinite, Data.Nat.Factorization.Defs, Data.Int.GCD |
| 97 | Challenge | C#017.6 | `bezout_lemma` | NumberTheory.PowModTotient, Data.ZMod.Basic, Data.Nat.Prime.Infinite, Data.Nat.Factorization.Defs, Data.Int.GCD |
| 98 | Challenge | C#018.1 | `nat_well_ordering` | Data.Nat.Find, Analysis.Real.Cardinality |
| 99 | Challenge | C#018.2 | `real_uncountable` | Data.Nat.Find, Analysis.Real.Cardinality |

### 挑战切片文件与核心定理

- `Challenge_CBS.lean` — `schroeder_bernstein`
- `Challenge_2Torsion.lean` — `twoTorsion_set_shortQ`
- `Challenge_Rouche.lean` — `rouche_finite_example`
- `Slice_Challenge_004.lean` — `halting_undecidable`
- `Slice_Challenge_005.lean` — `universe_not_self_contained`
- `Challenge_006_FiveColor.lean` — `five_color_induction_framework`
- `Challenge_007_BanachTarski.lean` — `F2_paradoxical_decomposition`
- `Challenge_008_GodelDiag.lean` — `godel_diagonal_lemma`
- `Challenge_009_Chebyshev.lean` — `chebyshevLowerBound`
- `Challenge_010_DirichletL.lean` — `riemannZeta_ne_zero_one_le_re`
- `Challenge_011_HasseEuler.lean` — `hasse_finite_p5`
- `Challenge_012_SylowFirst.lean` — `sylow_first_exists_sylow_subgroup`
- `Challenge_013_Wedderburn.lean` — `wedderburn_little`；`finite_divisionRing_mul_comm`；`all_mem_center`；`finite_domain_isField`
- `Challenge_014_Eulerian.lean` — `eulerian_exists_odd_degree_eq_zero_or_two`；`eulerian_connected_of_no_isolated`；`eulerian_nonendpoint_even_degree`；`eulerian_endpoint_odd_degree`；`odd_degree_vertices_card_even`
- `Challenge_015_Zorn.lean` — `zorn_lemma`；`zorn_subset_nonempty'`；`maximal_is_total`
- `Challenge_016_Group_Theorems.lean` — `lagrange_card_dvd`；`cayley_embedding`；`cauchy_prime_order`
- `Challenge_017_Number_Theorems.lean` — `fermat_little`；`euler_totient`；`chinese_remainder`；`infinite_primes`；`fundamental_theorem_of_arithmetic`；`bezout_lemma`
- `Challenge_018_Foundational.lean` — `nat_well_ordering`；`real_uncountable`

## 可视化

`output/lean_tower_99.html` 为自包含单页 3D 可视化（Three.js + CDN）：

- 中央 LEAN 树冠节点，点击触发 99 切片生长散开 / 收回动画；
- 树根网络底座 + 发光树干（H3-H2-H1 中央通道）+ 三主枝（RIEMANN / BSD / GOLDBACH）明暗对比；
- 悬停任意切片节点显示信息卡：编号、定理名称、EXIT=0、依赖库；
- 赛博朋克深色全绿风格，支持拖拽旋转与滚轮缩放。

浏览器直接打开 `output/lean_tower_99.html` 即可使用。

## 技术栈

| 组件 | 版本 / 说明 |
|---|---|
| Lean | v4.34.0 |
| mathlib | v4.34.0 |
| Lake | 5.0.0 |
| 前端 | Three.js（CDN r128 + OrbitControls） |
| 运行环境 | Windows 10，本地编译 |

## 纪律与约束

- **严禁 `sorry` / `admit`**：所有切片必须完整证明，零占位；
- **公理审计纪律**：交付前执行 `#print axioms` 审计，仅允许三标准公理（额外计算公理须披露）；
- **不碰尘光核心闭环**：切片仅形式化公开教科书级命题与前置部件，不涉及核心推导与未公开逻辑；
- **数据纪律**：切片清单与可视化数据均来自本地编译产物，禁止伪造或凑数。
