/-
Audit_SpecialCases_103_101_102.lean
===================================
特例收编审计（2026-11-05）：
对「103 通用指数公式 ⇒ 100–102 手搓特例」的交叉验证定理做类型检查与公理审计。
若 021D 中的交叉验证定理实际依赖 021B 特例定理作为证明入口，或引入新公理，
下方 `#print axioms` 会暴露出来。
-/
import All_MainTrunk_103_111

#check Challenge021Gamma0NIndex.universalIndex
#check Challenge021Gamma0NIndex.Gamma0N_index_eq_universal
#check Challenge021Gamma0NIndex.universalIndex_one
#check Challenge021Gamma0NIndex.universalIndex_prime
#check Challenge021Gamma0NIndex.universalIndex_primePow
#check Challenge021Gamma0NIndex.specialCase_101_fromTrunk
#check Challenge021Gamma0NIndex.specialCase_102_fromTrunk
#check Challenge021Gamma0NIndex.specialization_101
#check Challenge021Gamma0NIndex.specialization_102
#check Challenge021Gamma0NIndex.trunk_downwardCompatible
#check H1_specialCases_unified

#print axioms Challenge021Gamma0NIndex.universalIndex_prime
#print axioms Challenge021Gamma0NIndex.universalIndex_primePow
#print axioms Challenge021Gamma0NIndex.specialCase_101_fromTrunk
#print axioms Challenge021Gamma0NIndex.specialCase_102_fromTrunk
#print axioms Challenge021Gamma0NIndex.specialization_101
#print axioms Challenge021Gamma0NIndex.specialization_102
#print axioms Challenge021Gamma0NIndex.trunk_downwardCompatible
#print axioms Challenge021Gamma0NIndex.crossCheck_101_agreesWithHandRolled
#print axioms Challenge021Gamma0NIndex.crossCheck_102_agreesWithHandRolled
#print axioms H1_specialCases_unified

-- 回归保护：021B 手搓定理仍在
#print axioms Challenge021Gamma0NIndex.Gamma0_prime_index
#print axioms Challenge021Gamma0NIndex.Gamma0_primePow_index
