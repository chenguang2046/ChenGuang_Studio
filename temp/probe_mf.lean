import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

open scoped ModularForm

-- Gamma0 与 Gamma（主同余子群）的定义与成员刻画
#check CongruenceSubgroup.Gamma0
#check CongruenceSubgroup.Gamma0_mem
#check CongruenceSubgroup.Gamma_mem
#check CongruenceSubgroup.Gamma_mem'
#check CongruenceSubgroup.instFiniteIndexGamma0

-- ModularForm 与向量空间结构
#check ModularForm
#check SlashInvariantForm
#check ModularForm.instModule
#check SlashInvariantForm.instModule

-- LevelOne 有限维实例
#check ModularForm.SL2Z
#check ModularForm.FiniteDimensional -- 猜测名
#check LevelOne

-- mapGL 提升
#check Matrix.SpecialLinearGroup.mapGL

-- 反例矩阵（上三角幂单矩阵 T）
#check ModularGroup.S T
