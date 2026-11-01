import Mathlib.Order.Zorn

/-!
# Challenge 015.1 — Zorn 引理（mathlib 版本）

从 Challenge_015_Zorn.lean 拆分（台账 id 86 / no 015.1）。
本文件仅包含切片 1：`zorn_lemma`
（偏序集每条链有上界，则存在极大元；mathlib `zorn_le` 的直接包装）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace Challenge015

universe u v

section ZornStatements

/-- **切片 1 · Zorn 引理（mathlib 版本）**：偏序集每条链有上界，则存在极大元。
mathlib 定理 `zorn_le` 的直接包装（mathlib 用选择公理证明之，即 AC ⟹ Zorn）。 -/
theorem zorn_lemma (α : Type u) [PartialOrder α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) : ∃ m : α, IsMax m := by
  exact zorn_le h

end ZornStatements

end Challenge015

/-! # 公理审计 -/
#print axioms Challenge015.zorn_lemma
