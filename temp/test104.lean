import Slices_99.Challenge_021_Gamma0N_Index
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

open scoped MatrixGroups
open Matrix Matrix.SpecialLinearGroup
open Challenge021Gamma0NIndex

namespace Test104

noncomputable section

def Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (gamma0_N N : Subgroup (GL (Fin 2) ℝ))

instance Gamma0GL.hasDetOne (N : ℕ) : Subgroup.HasDetOne (Gamma0GL N) := by
  change Subgroup.HasDetOne ((gamma0_N N).map (mapGL ℝ))
  infer_instance

-- 尝试1: IsArithmetic 是否可由 gamma0_N FiniteIndex 自动得到
example (N : ℕ) [NeZero N] : Subgroup.IsArithmetic (Gamma0GL N) := by
  infer_instance

-- 尝试2: FiniteDimensional 是否可由 infer_instance 直接得到
example (N : ℕ) (k : ℤ) : FiniteDimensional ℂ (CuspForm (Gamma0GL N) k) := by
  infer_instance

-- 尝试3: ModularForm 是否有限维
example (N : ℕ) (k : ℤ) : FiniteDimensional ℂ (ModularForm (Gamma0GL N) k) := by
  infer_instance

end

end Test104
