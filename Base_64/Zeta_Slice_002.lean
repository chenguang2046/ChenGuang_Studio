import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Riemann Slice 002 — 黎曼 ζ 在 s = 1 处的单极点与留数

本切片验证（安全区，不涉及零点分布或解析延拓）：

  lim_{s → 1} (s - 1) · ζ(s) = 1

即黎曼 ζ 函数在 s = 1 处有单极点，留数为 1。

mathlib 已提供核心定理 `riemannZeta_residue_one`
（见 Mathlib/NumberTheory/LSeries/RiemannZeta.lean），
本文件直接引用并给出规范表述。
-/

open Filter
open scoped Topology

namespace RiemannSlice002

/-- 黎曼 ζ 在 s = 1 处的留数：lim_{s→1} (s-1)·ζ(s) = 1。

   陈述采用 punctured neighborhood 的 Tendsto 形式
   （`𝓝[≠] 1` 即 `nhdsWithin 1 {1}ᶜ`），
   与 mathlib 的 `riemannZeta_residue_one` 完全一致。 -/
theorem zeta_residue_one_at_one :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  exact riemannZeta_residue_one

/-- 等价的点斜记法：在 `s = 1` 的邻域内（除去 1 本身），
   `(s - 1) · ζ(s)` 趋近于 `1`。 -/
theorem zeta_residue_one_at_one' :
    Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (nhdsWithin 1 ({1}ᶜ)) (nhds 1) :=
  riemannZeta_residue_one

end RiemannSlice002

-- 公理审计：确认本切片不引入额外公理（预期仅 propext / Classical.choice / Quot.sound）
#print axioms RiemannSlice002.zeta_residue_one_at_one
#print axioms RiemannSlice002.zeta_residue_one_at_one'
