import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

open scoped ModularForm

-- 𝒮ℒ 定义与 LevelOne 有限维实例
#check SlashInvariantForms.SL2Z
#check ModularForm.SL2Z
#check SlashInvariantForm.SL2Z
#check Matrix.SpecialLinearGroup.SL2Z
#check ModularGroup.SL2Z

-- 提升：SL(2,Z) 子群 → GL(2,R) 子群
#check Subgroup.map
#check CongruenceSubgroup.Gamma_one_coe_eq_SL
#check Matrix.SpecialLinearGroup.mapGL
#check (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 4) : Subgroup (GL (Fin 2) ℝ))

-- 向量空间实例
example {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} : Module ℂ (SlashInvariantForm Γ k) := inferInstance
example {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} : Module ℂ (ModularForm Γ k) := inferInstance

-- LevelOne 有限维实例（匿名实例用可判类型推断）
example (k : ℤ) : FiniteDimensional ℂ (ModularForm (SlashInvariantForms.SL2Z) k) := inferInstance

-- Gamma_mem 使用（主同余子群 Γ(4) 刻画）
example {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} :
    γ ∈ CongruenceSubgroup.Gamma 4 ↔
      (γ 0 0 : ZMod 4) = 1 ∧ (γ 0 1 : ZMod 4) = 0 ∧
      (γ 1 0 : ZMod 4) = 0 ∧ (γ 1 1 : ZMod 4) = 1 :=
  CongruenceSubgroup.Gamma_mem

-- T = [[1,1],[0,1]] 反例元素
#check ModularGroup.T
#check Matrix.SpecialLinearGroup.mk
