import Mathlib.Order.Zorn

/-!
# Challenge 015.2 — Zorn 引理的集合形式

从 Challenge_015_Zorn.lean 拆分（台账 id 87 / no 015.2）。
本文件仅包含切片 2：`zorn_subset_nonempty'`
（对一族集合，若每条链在族内有上界，则族内存在包含极大元）。

全程零 sorry / admit，公理审计见文件尾部 `#print axioms`。
-/

namespace Challenge015

universe u v

section ZornStatements

/-- **切片 2 · Zorn 引理的集合形式**：对一族集合，若每条链（按包含序）在族内有上界，
则族内存在包含极大元。mathlib `zorn_subset_nonempty` 的直接包装。 -/
theorem zorn_subset_nonempty' (α : Type u) (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub)
    (x : Set α) (hx : x ∈ S) : ∃ m, x ⊆ m ∧ Maximal (· ∈ S) m := by
  exact zorn_subset_nonempty S H x hx

end ZornStatements

end Challenge015

/-! # 公理审计 -/
#print axioms Challenge015.zorn_subset_nonempty'
