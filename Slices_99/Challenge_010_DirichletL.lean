/-
Challenge_010 — Dirichlet L 函数在 s=1 的解析非零性（Dirichlet 定理实战）
目标：证明任意非平凡 Dirichlet 特征 χ 的 L(1, χ) ≠ 0。
方法（mathlib 现成定理直接包装）：
  mathlib v4.34 的 Mathlib.NumberTheory.LSeries.Nonvanishing 已完整证明
  "L 函数在 Re(s) ≥ 1 不消失"，核心结论即为
  DirichletCharacter.LFunction_apply_one_ne_zero (hχ : χ ≠ 1) : LFunction χ 1 ≠ 0。
  本文件包装该定理及两个直接推论（Re(s) ≥ 1 的一般非零性、ζ 不消失），
  并自建一个等价重述（¬ L(1,χ) = 0 形式）作为补充，不依赖虚构引理。
零 sorry，公理审计见文件尾。
-/

import Mathlib.NumberTheory.LSeries.Nonvanishing

open scoped Complex
open Complex

namespace Challenge010

-- 核心：任意非平凡 Dirichlet 特征 χ 的 L(χ, 1) ≠ 0
theorem LFunction_one_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

-- 一般化：Re(s) ≥ 1 且 (χ 非平凡 ∨ s ≠ 1) 时 L(χ, s) ≠ 0
--（平凡特征在 s=1 有极点，这正是 Dirichlet 定理避开平凡特征的原因）
theorem LFunction_ne_zero_of_one_le_re_general {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs

-- 推论（PNT 前置）：Riemann ζ 在闭半平面 Re(s) ≥ 1 不消失
theorem riemannZeta_ne_zero_one_le_re (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

-- 自建等价重述：L(1, χ) ≠ 0 写成 ¬ L(1, χ) = 0（同一命题的否定形式）
theorem LFunction_one_ne_zero_reformulated {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : ¬ (DirichletCharacter.LFunction χ 1 = 0) := by
  exact LFunction_one_ne_zero χ hχ

end Challenge010

-- 公理审计
#print axioms Challenge010.LFunction_one_ne_zero
#print axioms Challenge010.LFunction_ne_zero_of_one_le_re_general
#print axioms Challenge010.riemannZeta_ne_zero_one_le_re
