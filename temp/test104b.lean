import Slices_99.Challenge_021_Gamma0N_Index
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup
open Challenge021Gamma0NIndex

namespace Test104

noncomputable section

def Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (gamma0_N N : Subgroup (GL (Fin 2) ℝ))

instance Gamma0GL.hasDetOne (N : ℕ) : Subgroup.HasDetOne (Gamma0GL N) := by
  change Subgroup.HasDetOne ((gamma0_N N).map (mapGL ℝ))
  infer_instance

-- 战术2: 由 Gamma0N_index_eq 推出 (gamma0_N N).index ≠ 0, 进而 FiniteIndex
lemma gamma0_N_index_ne_zero (N : ℕ) [NeZero N] : (gamma0_N N).index ≠ 0 := by
  rw [Gamma0N_index_eq N]
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => by
    exact mul_ne_zero
      (pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp)))
      (Nat.succ_ne_zero (p + 1)))

instance gamma0_N_finiteIndex (N : ℕ) [NeZero N] : (gamma0_N N).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff]
  exact gamma0_N_index_ne_zero N

-- 桥接: 有限指数 SL2Z 子群提升后是算术子群
instance Gamma0GL_isArithmetic (N : ℕ) [NeZero N] : Subgroup.IsArithmetic (Gamma0GL N) := by
  change Subgroup.IsArithmetic (gamma0_N N)
  infer_instance

-- 尝试: 有了 IsArithmetic 后, CuspForm 能否有限维 (预期失败, 库无通用实例)
example (N : ℕ) [NeZero N] (k : ℤ) : FiniteDimensional ℂ (CuspForm (Gamma0GL N) k) := by
  infer_instance

end

end Test104
