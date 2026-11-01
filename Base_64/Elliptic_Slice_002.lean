-- ============================================================
-- BSD_Slice_002.lean
-- 方向 B: 欧拉积局部因子结合律 (纯代数验证)
-- ------------------------------------------------------------
-- 内容: 欧拉积的局部因子 L_p(X) = 1 - a X + p X^2 建模为系数
--   三元组, 验证:
--   * 整数环乘法公理实例 (结合律 / 交换律 / 幺元)
--   * 局部因子在截断多项式环 R[X]/(X^3) 中的乘法结合律实例
--   * 有限乘积的结合顺序无关性 (左折叠 = 右折叠, 归纳自证)
-- 环境: 裸 Lean 4.34 (Init), 不依赖 mathlib, 零公理。
-- 数学背景: 欧拉积 L(s) = ∏_p L_p(p^{-s}) 中每个局部因子都是
--   多项式环中的元素; 环乘法满足结合律是本切片验证的纯代数性质,
--   不涉及任何全局函数方程。
-- ============================================================

-- ------------------------------------------------------------
-- 1. 整数环乘法公理实例
-- ------------------------------------------------------------

-- 结合律
theorem prod_assoc (x y z : Int) : (x * y) * z = x * (y * z) :=
  Int.mul_assoc x y z

-- 交换律
theorem prod_comm (x y : Int) : x * y = y * x :=
  Int.mul_comm x y

-- 右幺元
theorem prod_one (x : Int) : x * 1 = x :=
  Int.mul_one x

-- 左幺元
theorem one_prod (x : Int) : 1 * x = x :=
  Int.one_mul x

-- ------------------------------------------------------------
-- 2. 局部因子系数三元组 (截断多项式环 R[X]/(X^3))
-- ------------------------------------------------------------

-- 最高 2 次的一元多项式系数 (c0, c1, c2)
structure Poly2 where
  c0 : Int
  c1 : Int
  c2 : Int
deriving DecidableEq, Repr

-- 局部因子 L_p(X) = 1 - a X + p X^2 的系数三元组
def localFactor (a p : Int) : Poly2 :=
  { c0 := 1, c1 := -a, c2 := p }

-- 截断多项式乘法 (R[X]/(X^3) 中的乘法)
def mulP (u v : Poly2) : Poly2 :=
  { c0 := u.c0 * v.c0,
    c1 := u.c0 * v.c1 + u.c1 * v.c0,
    c2 := u.c0 * v.c2 + u.c1 * v.c1 + u.c2 * v.c0 }

-- ------------------------------------------------------------
-- 3. 局部因子乘法的数值验证 (decide, 零公理)
-- ------------------------------------------------------------

-- 常数项恒为 1
theorem lf_const : (localFactor 2 3).c0 = 1 := by
  decide

-- 结合律实例 (三个具体局部因子)
theorem assoc_sample :
    mulP (mulP (localFactor 1 2) (localFactor (-1) 3)) (localFactor 2 5)
    = mulP (localFactor 1 2) (mulP (localFactor (-1) 3) (localFactor 2 5)) := by
  decide

-- 结合律实例二 (另一组参数)
theorem assoc_sample2 :
    mulP (mulP (localFactor 3 7) (localFactor 1 11)) (localFactor (-2) 13)
    = mulP (localFactor 3 7) (mulP (localFactor 1 11) (localFactor (-2) 13)) := by
  decide

-- 交换律实例
theorem comm_sample :
    mulP (localFactor 1 2) (localFactor (-1) 3)
    = mulP (localFactor (-1) 3) (localFactor 1 2) := by
  decide

-- ------------------------------------------------------------
-- 4. 有限乘积结合顺序无关性 (归纳自证)
-- ------------------------------------------------------------

-- 有限乘积: 左折叠 (((1*x)*y)*z ...)
def prodL (l : List Int) : Int :=
  l.foldl (fun acc x => acc * x) 1

-- 有限乘积: 右折叠 (1 * (x * (y * z ...)))
def prodR (l : List Int) : Int :=
  l.foldr (fun x acc => acc * x) 1

-- 辅助: 左折叠可"剥离"出前缀因子
theorem foldl_detach : ∀ (l : List Int) (acc : Int),
    l.foldl (fun a x => a * x) acc = acc * prodL l := by
  intro l
  induction l with
  | nil => simp [prodL]
  | cons x xs ih =>
      intro acc
      simp [prodL]
      rw [ih (acc * x)]
      rw [ih x]
      rw [Int.mul_assoc]

-- 辅助: 右折叠可"剥离"出前缀因子
theorem foldr_detach : ∀ (l : List Int) (b : Int),
    l.foldr (fun x acc => acc * x) b = b * prodR l := by
  intro l
  induction l with
  | nil => simp [prodR]
  | cons x xs ih =>
      intro b
      simp [prodR]
      rw [ih b]
      rw [Int.mul_assoc]
      rfl

-- 核心: 有限乘积与结合顺序无关 (左折叠 = 右折叠)
theorem prodL_eq_prodR : ∀ l : List Int, prodL l = prodR l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      change xs.foldl (fun a y => a * y) (1 * x) = (xs.foldr (fun y a => a * y) 1) * x
      rw [foldl_detach xs (1 * x)]
      rw [Int.one_mul]
      rw [ih]
      rw [Int.mul_comm]
      rfl

-- 数值实例: 四个局部因子的整数乘积, 两种结合顺序结果一致
theorem fold_sample : prodL [1, 2, 3, 4] = prodR [1, 2, 3, 4] := by
  decide

-- ------------------------------------------------------------
-- 5. 公理依赖审计
-- ------------------------------------------------------------
#print axioms prod_assoc
#print axioms prod_comm
#print axioms prod_one
#print axioms one_prod
#print axioms lf_const
#print axioms assoc_sample
#print axioms assoc_sample2
#print axioms comm_sample
#print axioms foldl_detach
#print axioms foldr_detach
#print axioms prodL_eq_prodR
#print axioms fold_sample
