/-
All_MainTrunk_103_110.lean
===========================
主干总装测试：103–110 共 8 个主干切片全部 import。
====================================================
切片清单（103 即 Challenge_021_Gamma0N_Index，根目录/ Slices_99 双份同源）：
  103  Challenge_021_Gamma0N_Index    Γ₀(N) 乘性指数公式骨架（Challenge021Gamma0NIndex）
  104  Challenge_104_Gamma0_Dimension 模形式空间维数公式（Challenge104Gamma0Dimension）
  105  Challenge_105_HeckeOperator     Hecke 算子（Challenge105HeckeOperator）
  106  Challenge_106_AnalyticContinuation 解析延拓（Challenge106AnalyticContinuation）
  107  Challenge_107_WeilExplicitFormula  Weil 显式公式（Challenge107WeilExplicitFormula）
  108  Challenge_108_FareyArcDecomposition 圆法优弧/劣弧分解（Challenge108FareyArc）
  109  Challenge_109_LargeSieve        大筛法不等式（Challenge109LargeSieve）
  110  Challenge_110_MaassHarmonic     Maass 形式调和分析基础（Challenge110MaassHarmonic）

瓦力避坑说明：
- 命名冲突：8 个切片命名空间各自独立，import 后互不遮蔽；
  本总控文件不使用任何 open，仅做 import 级总装，避免变量/记号冲突。
- 类型冲突：104 的 CuspForm 引用 Mathlib ModularForm 底层；
  110 的 MaassForm 为自定义非全纯结构，与 104 不冲突。
- 编译目标：EXIT=0（允许已声明 sorry 警告）。
-/
import Slices_99.Challenge_021_Gamma0N_Index
import Slices_99.Challenge_104_Gamma0_Dimension
import Slices_99.Challenge_105_HeckeOperator
import Slices_99.Challenge_106_AnalyticContinuation
import Slices_99.Challenge_107_WeilExplicitFormula
import Slices_99.Challenge_108_FareyArcDecomposition
import Slices_99.Challenge_109_LargeSieve
import Slices_99.Challenge_110_MaassHarmonic

/-! ## 总装冒烟检查：各切片命名空间内的关键符号可解析（info 级） -/

#check Challenge021Gamma0NIndex.gamma0_N
#check Challenge104Gamma0Dimension.einf
#check Challenge104Gamma0Dimension.dimension_formula
#check Challenge105HeckeOperator.HeckeOp
#check Challenge105HeckeOperator.hecke_comm
#check Challenge106AnalyticContinuation.HasAnalyticContinuation
#check Challenge107WeilExplicitFormula.Weil_explicit_formula
#check Challenge108FareyArc.FareyMajorArc
#check Challenge109LargeSieve.large_sieve_inequality
#check Challenge110MaassHarmonic.MaassForm
#check Challenge110MaassHarmonic.maassLaplacian
