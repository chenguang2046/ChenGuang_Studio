import Mathlib.Order.Zorn

/-!
# Challenge 015 — Zorn 引理与选择公理等价性的关键推导

mathlib 中 Zorn 引理（`zorn_le` 等）已由选择公理（`Classical.choice`）证明，
本文件提取三个关键切片：

1. `zorn_lemma` — 链有上界 ⟹ 极大元存在（Zorn 引理本身，AC ⟹ Zorn 方向）；
2. `zorn_subset_nonempty'` — Zorn 引理的集合包含形式（链并上界版本）；
3. `maximal_is_total` — **Zorn ⟹ 选择公理的关键推导**：在「部分选择函数」偏序上
   应用 Zorn 得到极大元，再证明极大元必为全定义（否则可插入新对扩展，矛盾），
   从而构造出选择函数 `choiceFn : (i : ι) → A i`。

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

/-- **切片 2 · Zorn 引理的集合形式**：对一族集合，若每条链（按包含序）在族内有上界，
则族内存在包含极大元。mathlib `zorn_subset_nonempty` 的直接包装。 -/
theorem zorn_subset_nonempty' (α : Type u) (S : Set (Set α))
    (H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub)
    (x : Set α) (hx : x ∈ S) : ∃ m, x ⊆ m ∧ Maximal (· ∈ S) m := by
  exact zorn_subset_nonempty S H x hx

end ZornStatements

/-! ## Zorn ⟹ 选择公理的关键推导 -/

namespace ZornImpliesChoice

variable {ι : Type u} (A : ι → Type v)

/-- 部分选择函数：`(Σ i, A i)` 的子集，满足单值性
（同一下标至多对应一个值，即它是某个函数的图像）。 -/
def Partial (A : ι → Type v) : Set (Set (Σ i, A i)) :=
  {f | ∀ ⦃p q : Σ i, A i⦄, p ∈ f → q ∈ f → ∀ h : p.1 = q.1, p.2 = h ▸ q.2}

/-- 链的并集仍保持单值性：链中任意两个元素可比较（⊆），
故同一下标的值必同属于较大的那个集合，其单值性由该集合保证。 -/
lemma union_chain_in_Partial {c : Set (Set (Σ i, A i))}
    (hc : IsChain (· ⊆ ·) c) (hcS : c ⊆ Partial A) :
    (⋃₀ c) ∈ Partial A := by
  rw [Partial]
  intro p q hp hq hpq
  rcases Set.mem_sUnion.mp hp with ⟨fp, hfp, hpp⟩
  rcases Set.mem_sUnion.mp hq with ⟨fq, hfq, hqq⟩
  by_cases hsame : fp = fq
  · subst hsame
    exact (hcS hfp) hpp hqq hpq
  · rcases hc hfp hfq hsame with hsub | hsub
    · -- fp ⊆ fq：p、q 同属 fq，用 fq 的单值性
      exact (hcS hfq) (hsub hpp) hqq hpq
    · -- fq ⊆ fp：p、q 同属 fp，用 fp 的单值性
      exact (hcS hfp) hpp (hsub hqq) hpq

/-- **切片 3 · 关键推导：Zorn 极大元是全定义的**。
在 `Partial A` 上应用 Zorn（链有上界 `⋃₀ c`），得到极大元 `m`；
若 `m` 在某下标 `i` 上未定义，则可把 `⟨i, Classical.choice (hA i)⟩`
插入 `m` 得到更大的部分选择函数，与极大性矛盾。
因此对每个 `i` 都存在 `p ∈ m` 且 `p.1 = i`。 -/
lemma maximal_is_total (hA : ∀ i, Nonempty (A i)) (m : Set (Σ i, A i))
    (hm : m ∈ Partial A) (hmax : Maximal (· ∈ Partial A) m) :
    ∀ i, ∃ p ∈ m, p.1 = i := by
  intro i
  by_contra hnone
  let e : Σ i, A i := ⟨i, Classical.choice (hA i)⟩
  have he_notin : e ∉ m := by
    intro he
    exact hnone ⟨e, he, rfl⟩
  have hsing : Partial A (insert e m) := by
    rw [Partial]
    intro p q hp hq hpq
    simp only [Set.mem_insert_iff] at hp hq
    rcases hp with rfl | hp
    · rcases hq with rfl | hq
      · cases hpq
        rfl
      · exfalso
        exact hnone ⟨q, hq, hpq.symm⟩
    · rcases hq with rfl | hq
      · exfalso
        exact hnone ⟨p, hp, hpq⟩
      · exact hm hp hq hpq
  have hmax' : ¬ Maximal (· ∈ Partial A) m := by
    intro h
    have hy : insert e m ⊆ m := h.2 hsing (Set.subset_insert e m)
    exact (Set.ssubset_insert he_notin).ne (le_antisymm (Set.subset_insert e m) hy)
  exact False.elim (hmax' hmax)

/-- 由 Zorn 极大元构造的选择函数：`choiceFn A hA m hm hmax i : A i`。 -/
noncomputable def choiceFn (hA : ∀ i, Nonempty (A i)) (m : Set (Σ i, A i))
    (hm : m ∈ Partial A) (hmax : Maximal (· ∈ Partial A) m) (i : ι) : A i := by
  let p := Classical.choose (maximal_is_total A hA m hm hmax i)
  let hps := Classical.choose_spec (maximal_is_total A hA m hm hmax i)
  exact Eq.mp (by rw [hps.2]) p.2

end ZornImpliesChoice

end Challenge015

/-! # 公理审计 -/
#print axioms Challenge015.zorn_lemma
#print axioms Challenge015.zorn_subset_nonempty'
#print axioms Challenge015.ZornImpliesChoice.union_chain_in_Partial
#print axioms Challenge015.ZornImpliesChoice.maximal_is_total
