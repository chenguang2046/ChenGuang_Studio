import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Complex

/-- 谱参数 → 特征值 -/
def specParam (s : ℂ) : ℂ := s * (1 - s)

/-- 谱参数高度 → Selberg 特征值 -/
def spectralValueOfHeight (t : ℝ) : ℝ := 1 / 4 + t ^ 2

theorem spec_reflect (s : ℂ) : specParam (1 - s) = specParam s := by
  unfold specParam; ring

theorem spec_quarter (s : ℂ) : specParam s = 1 / 4 - (s - 1 / 2) ^ 2 := by
  unfold specParam; ring

theorem spec_on_critical (γ : ℝ) :
    specParam ((1 / 2 : ℝ) + γ * I) = ((spectralValueOfHeight γ : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [specParam, spectralValueOfHeight, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, pow_two] <;> ring

theorem spec_eq_quarter_iff (s : ℂ) : specParam s = 1 / 4 ↔ s = 1 / 2 := by
  constructor
  · intro h
    have h1 : (s - 1 / 2) ^ 2 = 0 := by
      calc (s - 1 / 2) ^ 2 = 1 / 4 - specParam s := by rw [spec_quarter]; ring
        _ = 0 := by rw [h]; ring
    have h2 : s - 1 / 2 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1
    exact sub_eq_zero.mp h2
  · intro h; rw [h]; unfold specParam; ring

theorem spectralValue_ge_quarter (t : ℝ) : 1 / 4 ≤ spectralValueOfHeight t := by
  unfold spectralValueOfHeight; nlinarith [sq_nonneg t]

theorem spectralValue_pos (t : ℝ) : 0 < spectralValueOfHeight t := by
  have := spectralValue_ge_quarter t; linarith

theorem zeta_zero_reflect {s : ℂ} (h : completedRiemannZeta s = 0) :
    completedRiemannZeta (1 - s) = 0 := by
  rw [completedRiemannZeta_one_sub, h]
