import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic

noncomputable abbrev Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)

example (N : ℕ) : (Gamma0GL N).HasDetOne := inferInstance
example (N : ℕ) (k : ℤ) : AddCommGroup (ModularForm (Gamma0GL N) k) := inferInstance
example (N : ℕ) (k : ℤ) : Module ℂ (ModularForm (Gamma0GL N) k) := inferInstance
example : (CongruenceSubgroup.Gamma0 4).FiniteIndex := inferInstance
