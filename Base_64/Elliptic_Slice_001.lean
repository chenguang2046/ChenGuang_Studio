-- ============================================================
-- BSD_Slice_001.lean
-- 方向 A: 有限群同态核与像的基本代数性质
-- ------------------------------------------------------------
-- 内容: 以模 2 约化同态 red2 : Z/6Z -> Z/2Z 为具体实例, 验证:
--   * 同态保持加法与零元 (同态基本性质)
--   * 核集合的精确刻画: x 属于核当且仅当 red2 x = 0
--   * 像集合的精确刻画: 像 = {0, 1}
--   * 基数关系 |ker| * |im| = |G| = 6 (第一同构定理的基数形式, 实例)
--   * 一般组合事实: 任意函数下, 像集合基数不超过定义域基数
-- 环境: 裸 Lean 4.34 (Init), 不依赖 mathlib, 零公理 (decide/rfl/自证)。
-- 数学背景: 核与像是有限群同态的最基本对象; 本切片只验证其
--   定义层逻辑关系, 不涉及任何深层同源理论。
-- ============================================================

set_option maxRecDepth 1000000

-- ------------------------------------------------------------
-- 1. 基础定义
-- ------------------------------------------------------------

-- 模 2 约化 (加法群 Z -> Z/2 的同态像)
def red2 (x : Nat) : Nat := x % 2

-- 定义域表: Z/6Z 的代表元 0..5
def G6 : List Nat := List.range 6

-- 列表成员判定
def memN : Nat → List Nat → Bool
  | _, [] => false
  | a, b :: bs => if a = b then true else memN a bs

-- 去重 (保序), 用于像集合计数
def dedupN : List Nat → List Nat
  | [] => []
  | a :: as => if memN a as then dedupN as else a :: dedupN as

-- 核: red2 在 G6 中的核集合 {x | red2 x = 0}
def kernel2 : List Nat := G6.filter (fun x => red2 x = 0)

-- 像: red2 在 G6 上的像集合 (去重后)
def image2 : List Nat := dedupN (G6.map red2)

-- ------------------------------------------------------------
-- 2. 一般组合引理 (自证, 零公理)
-- ------------------------------------------------------------

-- 去重不增加长度: |dedup l| <= |l|
theorem dedupN_length_le : ∀ l : List Nat, (dedupN l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp [dedupN]
  | cons a as ih =>
      by_cases h : memN a as
      · simp [dedupN, h]
        exact Nat.le_trans ih (Nat.le_succ _)
      · simp [dedupN, h]
        exact ih

-- 任意函数 f 下, 像集合基数不超过定义域基数
theorem image_card_le_domain_card (f : Nat → Nat) (l : List Nat) :
    (dedupN (l.map f)).length ≤ l.length := by
  have hmap : (l.map f).length = l.length := by
    induction l with
    | nil => simp
    | cons a as ih => simp [ih]
  have hded := dedupN_length_le (l.map f)
  rwa [hmap] at hded

-- ------------------------------------------------------------
-- 3. 同态性质 (模 2 约化)
-- ------------------------------------------------------------

-- 保持加法: red2 (a + b) = (red2 a + red2 b) mod 2
theorem hom_add : ∀ a b : Nat, red2 (a + b) = (red2 a + red2 b) % 2 := by
  intro a b
  unfold red2
  exact Nat.add_mod a b 2

-- 保持零元: red2 0 = 0
theorem hom_zero : red2 0 = 0 := by
  decide

-- 保持乘法: red2 (a * b) = (red2 a * red2 b) mod 2
theorem hom_mul : ∀ a b : Nat, red2 (a * b) = (red2 a * red2 b) % 2 := by
  intro a b
  unfold red2
  exact Nat.mul_mod a b 2

-- ------------------------------------------------------------
-- 4. 核与像的精确刻画与基数 (实例)
-- ------------------------------------------------------------

-- 核集合精确等于 {0, 2, 4}
theorem kernel_exact_list : kernel2 = [0, 2, 4] := by
  decide

-- 像集合精确等于 {0, 1}
theorem image_exact_list : image2 = [0, 1] := by
  decide

-- 核基数 = 3
theorem kernel_card : kernel2.length = 3 := by
  decide

-- 像基数 = 2
theorem image_card : image2.length = 2 := by
  decide

-- 定义域基数 = 6
theorem domain_card : G6.length = 6 := by
  decide

-- 第一同构定理的基数形式 (实例): |ker| * |im| = |G|
theorem card_relation : kernel2.length * image2.length = G6.length := by
  decide

-- 核非空 (零元属于核)
theorem kernel_nonempty : memN 0 kernel2 = true := by
  decide

-- 像非空 (零元属于像, 因为 f 0 = 0)
theorem image_nonempty : memN 0 image2 = true := by
  decide

-- 核元素逻辑刻画 (全域真值表): x 属于核 <-> red2 x = 0 (对定义域内元素)
theorem kernel_iff_all :
    (G6.all (fun x => decide (memN x kernel2 ↔ red2 x = 0))) = true := by
  decide

-- 核是定义域的子集 (由 filter 定义直接成立, 真值表确认)
theorem kernel_subset_domain : kernel2.all (fun x => memN x G6) = true := by
  decide

-- 像是陪域代表元的子集: 像的所有元素均 < 2
theorem image_subset_codomain : image2.all (fun x => x < 2) = true := by
  decide

-- ------------------------------------------------------------
-- 5. 公理依赖审计
-- ------------------------------------------------------------
#print axioms hom_add
#print axioms hom_zero
#print axioms hom_mul
#print axioms kernel_exact_list
#print axioms image_exact_list
#print axioms kernel_card
#print axioms image_card
#print axioms domain_card
#print axioms card_relation
#print axioms kernel_nonempty
#print axioms image_nonempty
#print axioms kernel_iff_all
#print axioms kernel_subset_domain
#print axioms image_subset_codomain
#print axioms dedupN_length_le
#print axioms image_card_le_domain_card
