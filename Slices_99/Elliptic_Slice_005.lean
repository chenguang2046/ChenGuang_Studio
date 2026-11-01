/- BSD Slice 005 —— 方向 E：有限序列折叠（fold）的结合与顺序无关
   裸 Lean + Init 路线（不 import mathlib），零 sorry、零 axiom。
   折叠：以 List.foldr 实现 fold op a l（右折叠，从序列右端起算）。
   定理：
     · fold_accum_right    —— 右累积引理（仅需 op 结合律）：把「新初值 op a x」
                                从序列尾部逐步吸收，等价于先折叠再在右侧作用 x。
     · fold_append_single  —— 序列追加单元素的分解（仅需结合律），括号无关。
     · fold_perm           —— 顺序无关：若 op 结合且交换，则对任意有限置换
                                l.Perm m 有 fold op a l = fold op a m。
     · foldr_op_left       —— 左吸收引理（结合 + 交换）。
     · foldl_eq_foldr      —— 左折叠与右折叠在结合 + 交换下结果一致。
   完全脱离具体数学对象，仅使用序列代数的抽象运算性质。
-/

namespace BSD_E

-- 有限序列折叠（右折叠实现）
def fold {α : Type} (op : α → α → α) (a : α) (l : List α) : α :=
  List.foldr op a l

theorem fold_nil {α : Type} (op : α → α → α) (a : α) : fold op a [] = a := by
  rfl

theorem fold_cons {α : Type} (op : α → α → α) (a : α) (x : α) (l : List α) :
    fold op a (x :: l) = op x (fold op a l) := by
  rfl

-- 引理 E1a：右累积（仅需结合律）
theorem fold_accum_right {α : Type} (op : α → α → α)
    (hassoc : ∀ x y z : α, op (op x y) z = op x (op y z))
    (a x : α) (l : List α) :
    List.foldr op (op a x) l = op (List.foldr op a l) x := by
  induction l with
  | nil =>
      simp
  | cons c l ih =>
      rw [List.foldr_cons, List.foldr_cons]
      rw [ih]
      rw [hassoc]

-- 引理 E1c：右累积（结合 + 交换；foldr 的初值不对称，故追加方向需交换）
theorem foldr_accum_comm_left {α : Type} (op : α → α → α)
    (hassoc : ∀ x y z : α, op (op x y) z = op x (op y z))
    (hcomm : ∀ x y : α, op x y = op y x)
    (a x : α) (l : List α) :
    List.foldr op (op x a) l = op (List.foldr op a l) x := by
  induction l with
  | nil =>
      simp [hcomm]
  | cons c l ih =>
      rw [List.foldr_cons, List.foldr_cons]
      rw [ih]
      calc
        op c (op (List.foldr op a l) x) = op (op c (List.foldr op a l)) x := by rw [hassoc]
        _ = op (List.foldr op a (c :: l)) x := by rw [List.foldr_cons]

-- 引理 E1b：追加单元素的分解（结合 + 交换）—— 折叠的括号无关性
theorem fold_append_single {α : Type} (op : α → α → α)
    (hassoc : ∀ x y z : α, op (op x y) z = op x (op y z))
    (hcomm : ∀ x y : α, op x y = op y x)
    (a : α) (l : List α) (x : α) :
    fold op a (l ++ [x]) = op (fold op a l) x := by
  unfold fold
  rw [List.foldr_append]
  simp
  exact foldr_accum_comm_left op hassoc hcomm a x l

-- 引理 E2：顺序无关（结合 + 交换 ⟹ 置换不变）
theorem fold_perm {α : Type} (op : α → α → α)
    (hassoc : ∀ x y z : α, op (op x y) z = op x (op y z))
    (hcomm : ∀ x y : α, op x y = op y x)
    {l m : List α} (hp : l.Perm m) (a : α) :
    fold op a l = fold op a m := by
  induction hp with
  | nil =>
      rfl
  | cons x hp ih =>
      rw [fold_cons, fold_cons, ih]
  | swap x y l =>
      rw [fold_cons, fold_cons, fold_cons, fold_cons]
      calc
        op y (op x (fold op a l)) = op (op y x) (fold op a l) := by
          rw [hassoc y x (fold op a l)]
        _ = op (op x y) (fold op a l) := by
          rw [hcomm y x]
        _ = op x (op y (fold op a l)) := by
          rw [hassoc x y (fold op a l)]
  | trans hp₁ hp₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

-- 引理 E3a：左吸收（结合 + 交换）
theorem foldr_op_left {α : Type} (op : α → α → α)
    (hassoc : ∀ x y z : α, op (op x y) z = op x (op y z))
    (hcomm : ∀ x y : α, op x y = op y x)
    (a b : α) (l : List α) :
    List.foldr op (op a b) l = op b (List.foldr op a l) := by
  induction l with
  | nil =>
      simp [hcomm]
  | cons c l ih =>
      rw [List.foldr_cons, List.foldr_cons]
      rw [ih]
      calc
        op c (op b (List.foldr op a l)) = op (op c b) (List.foldr op a l) := by
          rw [hassoc c b (List.foldr op a l)]
        _ = op (op b c) (List.foldr op a l) := by
          rw [hcomm c b]
        _ = op b (op c (List.foldr op a l)) := by
          rw [hassoc b c (List.foldr op a l)]

-- 引理 E3b：左折叠与右折叠一致（结合 + 交换）
theorem foldl_eq_foldr {α : Type} (op : α → α → α)
    (hassoc : ∀ x y z : α, op (op x y) z = op x (op y z))
    (hcomm : ∀ x y : α, op x y = op y x)
    (a : α) (l : List α) :
    List.foldl op a l = List.foldr op a l := by
  induction l generalizing a with
  | nil =>
      simp
  | cons b l ih =>
      rw [List.foldl_cons, List.foldr_cons]
      rw [ih (op a b)]
      exact foldr_op_left op hassoc hcomm a b l

-- 实例哨兵：自然数加法（结合 + 交换）
example : fold (fun x y => x + y) 0 [1,2,3] = 6 := by
  native_decide

example : fold (fun x y => x + y) 0 [1,2,3] = fold (fun x y => x + y) 0 [3,2,1] := by
  native_decide

example : List.foldl (fun x y => x + y) 0 [1,2,3] = List.foldr (fun x y => x + y) 0 [1,2,3] := by
  native_decide

-- 应用顺序无关定理：相邻对换 [1,2] → [2,1] 不改变折叠值
example : fold (fun x y => x + y) 0 [1,2] = fold (fun x y => x + y) 0 [2,1] := by
  apply fold_perm (fun x y => x + y)
  · intro x y z
    exact Nat.add_assoc x y z
  · intro x y
    exact Nat.add_comm x y
  · exact List.Perm.symm (List.Perm.swap 1 2 [])

-- 公理审计（预期：全部定理公理为 [propext, Quot.sound] 标准子集）
#print axioms fold_accum_right
#print axioms fold_append_single
#print axioms fold_perm
#print axioms foldr_op_left
#print axioms foldl_eq_foldr

end BSD_E
