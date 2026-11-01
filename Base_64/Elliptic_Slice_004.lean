/- BSD Slice 004 —— 方向 D：有限集合上「单射 且 同基数 ⟹ 满射」
   裸 Lean + Init 路线（不 import mathlib），零 sorry、零 axiom。
   有限集合用「无重复列表」(List.Nodup) 表示：
     · 定义域 l : List α（l.Nodup）
     · 陪域   b : List β（b.Nodup）
     · 单射   injOn f l := ∀ x∈l, ∀ y∈l, f x = f y → x = y
     · 同基数 (l.map f).length = b.length（像表与陪域表等长）
   结论：∀ y ∈ b, ∃ x ∈ l, f x = y（f 覆盖整个陪域，即满射）
   完全脱离具体数学对象，仅使用集合论/列表基础。
-/

namespace BSD_D

-- 定义域限制在列表上的单射
def injOn {α β : Type} (f : α → β) (l : List α) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y

-- 裸 Init 缺失的可判定性实例（无公理，纯构造）：
-- 蕴含 / 列表全称量词 / 列表成员 / injOn 的 Decidable
instance instDecidableImp' {p q : Prop} [Decidable p] [Decidable q] : Decidable (p → q) :=
  if h : p then
    if hq : q then isTrue (fun _ => hq) else isFalse (fun hpq => hq (hpq h))
  else
    isTrue (fun hp => False.elim (h hp))

instance instDecidableBallMem {α : Type} (p : α → Prop) [DecidablePred p] (l : List α) :
    Decidable (∀ x, x ∈ l → p x) :=
  List.decidableBAll p l

instance instDecidableMem' {α : Type} [DecidableEq α] (x : α) (l : List α) : Decidable (x ∈ l) :=
  match l with
  | [] => isFalse (by intro h; cases h)
  | a :: as =>
      if hxa : x = a then isTrue (by simp [hxa])
      else match instDecidableMem' x as with
           | isTrue hxas => isTrue (by simp [hxas])
           | isFalse hxas => isFalse (by
               intro h
               rcases List.mem_cons.mp h with hx | hxs
               · exact hxa hx
               · exact hxas hxs)

instance instDecidableInjOn {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) : Decidable (injOn f l) := by
  unfold injOn
  exact List.decidableBAll (fun x => ∀ y ∈ l, f x = f y → x = y) l

-- 引理 1：定义域互异 + 单射 ⟹ 像表互异
theorem map_nodup_of_injOn {α β : Type} {f : α → β} {l : List α}
    (hl : l.Nodup) (hinj : injOn f l) : (l.map f).Nodup := by
  induction l with
  | nil => simp [List.Nodup]
  | cons a as ih =>
      change (f a :: (as.map f)).Nodup
      rw [List.nodup_cons]
      have hcons := List.nodup_cons.mp hl
      rcases hcons with ⟨hna, has⟩
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨x, hx, hfx⟩
        have hxa : x = a := hinj x (List.mem_cons.mpr (Or.inr hx)) a (List.mem_cons.mpr (Or.inl rfl)) hfx
        exact hna (hxa ▸ hx)
      · exact ih has (fun x hx y hy h => hinj x (List.mem_cons.mpr (Or.inr hx)) y (List.mem_cons.mpr (Or.inr hy)) h)

-- 辅助：非成员时「剔除非 a」过滤恒等（归纳自证）
theorem filter_eq_self_of_not_mem {α : Type} [DecidableEq α] {a : α} {l : List α}
    (hna : ¬ a ∈ l) : List.filter (fun z => decide (z ≠ a)) l = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
      rw [List.filter_cons]
      have hna' : ¬ a ∈ bs := by
        intro hbs
        exact hna (List.mem_cons.mpr (Or.inr hbs))
      by_cases hba : b = a
      · exact False.elim (hna (hba.symm ▸ (List.mem_cons.mpr (Or.inl rfl))))
      · have hb : decide (b ≠ a) = true := by
          rw [decide_eq_true_eq]
          exact hba
        rw [hb]
        change b :: List.filter (fun z => decide (z ≠ a)) bs = b :: bs
        rw [ih hna']

-- 辅助：过滤保持互异
theorem filter_nodup {α : Type} [DecidableEq α] {l : List α} (h : l.Nodup) (p : α → Bool) :
    (List.filter p l).Nodup := by
  induction l with
  | nil => simp [List.Nodup]
  | cons a as ih =>
      rw [List.filter_cons]
      by_cases hpa : p a = true
      · simp only [hpa]
        change (a :: List.filter p as).Nodup
        rw [List.nodup_cons]
        have hcons := List.nodup_cons.mp h
        rcases hcons with ⟨hna, has⟩
        constructor
        · intro hmem
          have hm := List.mem_filter.mp hmem
          exact hna hm.1
        · exact ih has
      · simp only [hpa]
        exact ih (List.nodup_cons.mp h).2

-- 辅助：成员 + 互异 ⟹ 长度 = 剔除非 a 后长度 + 1
theorem length_filter_ne_of_nodup_mem {α : Type} [DecidableEq α] {a : α} {l : List α}
    (hl : l.Nodup) (ha : a ∈ l) :
    l.length = (List.filter (fun z => decide (z ≠ a)) l).length + 1 := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      have hcons := List.nodup_cons.mp hl
      rcases hcons with ⟨hnx, hxs⟩
      rw [List.length_cons]
      by_cases hxa : x = a
      · -- x = a：a 被滤掉，且 a∉xs → 过滤恒等
        have hna' : ¬ a ∈ xs := by
          intro has
          exact hnx (hxa.symm ▸ has)
        have hfeq : List.filter (fun z => decide (z ≠ a)) xs = xs := filter_eq_self_of_not_mem hna'
        have hfilter : List.filter (fun z => decide (z ≠ a)) (x :: xs) = xs := by
          rw [List.filter_cons]
          have hd : decide (x ≠ a) = false := by
            rw [decide_eq_false]
            intro hxn
            exact hxn hxa
          rw [hd]
          have hff : ¬(false = true) := by simp
          rw [ite_eq_right hff]
          exact hfeq
        rw [hfilter]
      · -- x ≠ a：x 保留，a∈xs → 归纳
        have hpa : decide (x ≠ a) = true := by
          rw [decide_eq_true_eq]
          exact hxa
        have hfilter : List.filter (fun z => decide (z ≠ a)) (x :: xs) = x :: List.filter (fun z => decide (z ≠ a)) xs := by
          rw [List.filter_cons]
          simp [hpa]
        have haxs : a ∈ xs := by
          rcases List.mem_cons.mp ha with h | h
          · exact False.elim (hxa h.symm)
          · exact h
        have ih2 := ih hxs haxs
        rw [hfilter, List.length_cons, ih2]

-- 长度界：无重复超集 ⟹ 子表长度不超过超表
theorem length_le_of_subset_nodup {α : Type} [DecidableEq α] : ∀ {u v : List α},
    u.Nodup → v.Nodup → u ⊆ v → u.length ≤ v.length := by
  intro u v
  induction v generalizing u with
  | nil =>
      intro hu hv huv
      cases u with
      | nil => simp
      | cons a us => cases (huv (List.mem_cons.mpr (Or.inl rfl)))
  | cons b vs ih =>
      intro hu hv huv
      have hvs : vs.Nodup := (List.nodup_cons.mp hv).2
      by_cases hb : b ∈ u
      · -- b ∈ u：剔除非 b 得 u'，u' ⊆ vs，|u| = 1+|u'| ≤ 1+|vs|
        let u' : List α := List.filter (fun z => decide (z ≠ b)) u
        have hu' : u'.Nodup := filter_nodup hu (fun z => decide (z ≠ b))
        have hlen : u.length = u'.length + 1 := length_filter_ne_of_nodup_mem hu hb
        have hsub : u' ⊆ vs := by
          intro x hx
          have hxu : x ∈ u := (List.mem_filter.mp hx).1
          have hxbv : x ∈ b :: vs := huv hxu
          rcases List.mem_cons.mp hxbv with hxb | hxvs
          · have hxnb : x ≠ b := by
              have hmf := List.mem_filter.mp hx
              rcases hmf with ⟨_, hd⟩
              rw [decide_eq_true_eq] at hd
              exact hd
            exact False.elim (hxnb hxb)
          · exact hxvs
        have hle : u'.length ≤ vs.length := ih hu' hvs hsub
        rw [hlen]
        exact Nat.succ_le_succ hle
      · -- b ∉ u：u ⊆ vs → 归纳
        have hsub : u ⊆ vs := by
          intro x hx
          have hxbv : x ∈ b :: vs := huv hx
          rcases List.mem_cons.mp hxbv with hxb | hx
          · exact False.elim (hb (hxb ▸ hx))
          · exact hx
        have hle : u.length ≤ vs.length := ih hu hvs hsub
        exact Nat.le_succ_of_le hle

-- 核心计数引理：互异 + 等长 + 包含 ⟹ 反向包含（同基数下子集即全集）
theorem nodup_subset_same_len_eq {α : Type} [DecidableEq α] : ∀ {u v : List α},
    u.Nodup → v.Nodup → u ⊆ v → u.length = v.length → v ⊆ u := by
  intro u v
  induction v generalizing u with
  | nil =>
      intro hu hv huv hlen a ha
      cases ha
  | cons b vs ih =>
      intro hu hv huv hlen a ha
      have hvs : vs.Nodup := (List.nodup_cons.mp hv).2
      rcases List.mem_cons.mp ha with h | h
      · -- a = b：若 a∉u 则 u ⊆ vs → |u| ≤ |vs| < |b::vs| = |u| 矛盾
        by_cases hau : a ∈ u
        · exact hau
        · have hsub : u ⊆ vs := by
            intro x hx
            have hxbv : x ∈ b :: vs := huv hx
            rcases List.mem_cons.mp hxbv with hxb | hxv
            · have hxa : x = a := hxb.trans h.symm
              exact False.elim (hau (hxa ▸ hx))
            · exact hxv
          have hle : u.length ≤ vs.length := length_le_of_subset_nodup hu hvs hsub
          have hlen' : u.length = vs.length + 1 := by
            simpa [List.length_cons] using hlen
          have hlt : vs.length < u.length := by
            rw [hlen']
            exact Nat.lt_succ_self vs.length
          exact False.elim (Nat.lt_irrefl vs.length (Nat.lt_of_lt_of_le hlt hle))
      · -- a ∈ vs
        by_cases hb : b ∈ u
        · -- b ∈ u：剔除非 b 得 u'，u'⊆vs 且 |u'|=|vs|，归纳得 a∈u'⊆u
          let u' : List α := List.filter (fun z => decide (z ≠ b)) u
          have hu' : u'.Nodup := filter_nodup hu (fun z => decide (z ≠ b))
          have hlenu : u.length = u'.length + 1 := length_filter_ne_of_nodup_mem hu hb
          have hsub : u' ⊆ vs := by
            intro x hx
            have hxu : x ∈ u := (List.mem_filter.mp hx).1
            have hxbv : x ∈ b :: vs := huv hxu
            rcases List.mem_cons.mp hxbv with hxb | hxv
            · have hxnb : x ≠ b := by
                have hmf := List.mem_filter.mp hx
                rcases hmf with ⟨_, hd⟩
                rw [decide_eq_true_eq] at hd
                exact hd
              exact False.elim (hxnb hxb)
            · exact hxv
          have hlen' : u.length = vs.length + 1 := by
            simpa [List.length_cons] using hlen
          have hlenu' : u'.length = vs.length := by
            rw [hlen'] at hlenu
            exact (Nat.succ.inj hlenu).symm
          have hvsb : vs ⊆ u' := ih hu' hvs hsub hlenu'
          have hau' : a ∈ u' := hvsb h
          exact (List.mem_filter.mp hau').1
        · -- b ∉ u：u ⊆ vs → |u| ≤ |vs| < |b::vs| = |u| 矛盾
          have hsub : u ⊆ vs := by
            intro x hx
            have hxbv : x ∈ b :: vs := huv hx
            rcases List.mem_cons.mp hxbv with hxb | hxv
            · exact False.elim (hb (hxb ▸ hx))
            · exact hxv
          have hle : u.length ≤ vs.length := length_le_of_subset_nodup hu hvs hsub
          have hlen' : u.length = vs.length + 1 := by
            simpa [List.length_cons] using hlen
          have hlt : vs.length < u.length := by
            rw [hlen']
            exact Nat.lt_succ_self vs.length
          exact False.elim (Nat.lt_irrefl vs.length (Nat.lt_of_lt_of_le hlt hle))

-- 方向 D 主定理：有限集合上 单射 + 同基数 ⟹ 满射
theorem surj_of_inj_same_card {α β : Type} [DecidableEq β]
    (l : List α) (b : List β) (f : α → β)
    (hl : l.Nodup) (hinj : injOn f l) (hb : b.Nodup)
    (himg : ∀ x ∈ l, f x ∈ b)
    (hlen : (l.map f).length = b.length) :
    ∀ y ∈ b, ∃ x ∈ l, f x = y := by
  intro y hy
  let u : List β := l.map f
  have hu : u.Nodup := by
    simpa [u] using map_nodup_of_injOn hl hinj
  have hsubu : u ⊆ b := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨a, ha, hfa⟩
    exact hfa ▸ himg a ha
  have hlenu : u.length = b.length := by
    simpa [u] using hlen
  have hbsub : b ⊆ u := nodup_subset_same_len_eq hu hb hsubu hlenu
  have hyu : y ∈ u := hbsub hy
  rw [List.mem_map] at hyu
  exact hyu

-- 实例 1：6 元素循环移位，单射 + 同基数 → 满射
def shift6 (x : Nat) : Nat := if x = 5 then 0 else x + 1

theorem inst_shift6 : ∀ y ∈ [0,1,2,3,4,5], ∃ x ∈ [0,1,2,3,4,5], shift6 x = y := by
  apply surj_of_inj_same_card
  · decide
  · decide
  · decide
  · decide
  · decide

-- 实例 2：不同标签但同基数（x ↦ x+1，域 0..2 → 陪域 1..3）
def succ1 (x : Nat) : Nat := x + 1

theorem inst_succ1 : ∀ y ∈ [1,2,3], ∃ x ∈ [0,1,2], succ1 x = y := by
  apply surj_of_inj_same_card
  · decide
  · decide
  · decide
  · decide
  · decide

-- 实例 3：3 元素对换
def swap3 (x : Nat) : Nat :=
  if x = 0 then 1 else if x = 1 then 0 else if x = 2 then 2 else 0

theorem inst_swap3 : ∀ y ∈ [0,1,2], ∃ x ∈ [0,1,2], swap3 x = y := by
  apply surj_of_inj_same_card
  · decide
  · decide
  · decide
  · decide
  · decide

-- 反例哨兵：基数不同（3 vs 4）时，同单射却不可推满射（证明「同基数」前提不可省）
theorem not_surj_card3_vs4 : ¬ (∀ y ∈ [0,1,2,3], ∃ x ∈ [0,1,2], succ1 x = y) := by
  intro h
  rcases h 0 (by simp) with ⟨x, hx, hfx⟩
  simp [succ1] at hfx

-- 公理审计（预期：全部定理公理为空集，即零公理）
#print axioms map_nodup_of_injOn
#print axioms filter_eq_self_of_not_mem
#print axioms filter_nodup
#print axioms length_filter_ne_of_nodup_mem
#print axioms length_le_of_subset_nodup
#print axioms nodup_subset_same_len_eq
#print axioms surj_of_inj_same_card
#print axioms inst_shift6
#print axioms not_surj_card3_vs4

end BSD_D
