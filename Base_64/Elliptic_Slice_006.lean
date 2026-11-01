/- BSD Slice 006 —— 方向 F：多命题逻辑依赖链的传递性
   裸 Lean + Init 路线（不 import mathlib），零 sorry、零 axiom。
   验证命题链「P1 成立 ∧ P1→P2 ∧ P2→P3 ⟹ P3 成立」的传递性，
   并推广到任意多节点（显式四元链、Nat 索引无限链、有界步进链）。
   纯命题逻辑构造，不依赖任何具体数学对象。
-/

namespace BSD_F

-- 定理 F1：三元依赖链传递
theorem chain3 {P1 P2 P3 : Prop} (h1 : P1) (h12 : P1 → P2) (h23 : P2 → P3) : P3 :=
  h23 (h12 h1)

-- 定理 F2：四元依赖链传递（推广 1 个节点）
theorem chain4 {P1 P2 P3 P4 : Prop}
    (h1 : P1) (h12 : P1 → P2) (h23 : P2 → P3) (h34 : P3 → P4) : P4 :=
  h34 (h23 (h12 h1))

-- 定理 F3：合取打包的三元链（与任务表述一致：P1∧(P1→P2)∧(P2→P3)→P3）
theorem chain_conj3 {P1 P2 P3 : Prop} :
    P1 ∧ (P1 → P2) ∧ (P2 → P3) → P3 := by
  intro h
  rcases h with ⟨h1, h12, h23⟩
  exact h23 (h12 h1)

-- 定理 F4：合取打包的四元链（推广）
theorem chain_conj4 {P1 P2 P3 P4 : Prop} :
    P1 ∧ (P1 → P2) ∧ (P2 → P3) ∧ (P3 → P4) → P4 := by
  intro h
  rcases h with ⟨h1, h12, h23, h34⟩
  exact h34 (h23 (h12 h1))

-- 定理 F5：无限链（任意长节点链，无边界限制）
--   P 0 成立，且每一步 P i ⟹ P (i+1)，则 P n 对任意 n 成立。
theorem chain_unbounded {P : Nat → Prop} (h0 : P 0)
    (hstep : ∀ i, P i → P (i + 1)) (n : Nat) : P n := by
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      exact hstep n ih

-- 定理 F6：有界链（仅要求前 k 步的依赖成立）
--   P 0 成立，且 ∀ i < k, P i ⟹ P (i+1)，则 P k 成立。
theorem chain_bounded {P : Nat → Prop} {k : Nat} (h0 : P 0)
    (hstep : ∀ i, i < k → P i → P (i + 1)) : P k := by
  induction k generalizing P with
  | zero =>
      exact h0
  | succ k ih =>
      apply hstep k (Nat.lt_succ_self k)
      apply ih h0
      intro i hi
      exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self k))

-- 实例哨兵：数值链 0 < 1 < 2 < 3 ⟹ 0 < 3（应用三元链）
example (h01 : 0 < 1) (h12 : 1 < 2) (h23 : 2 < 3) : 0 < 3 :=
  chain3 h01 (fun h => Nat.lt_trans h h12) (fun h => Nat.lt_trans h h23)

-- 实例哨兵：数值链 0 < 1 < 2 < 3 < 4 ⟹ 0 < 4（应用四元链）
example (h01 : 0 < 1) (h12 : 1 < 2) (h23 : 2 < 3) (h34 : 3 < 4) : 0 < 4 :=
  chain4 h01 (fun h => Nat.lt_trans h h12) (fun h => Nat.lt_trans h h23)
    (fun h => Nat.lt_trans h h34)

-- 实例哨兵：有界链（步进仅要求前 5 步）
example : (fun i : Nat => i < 6) 5 := by
  apply chain_bounded (P := fun i : Nat => i < 6) (k := 5)
  · native_decide
  · intro i hi hPi
    exact Nat.succ_lt_succ hi

-- 实例哨兵：无限链
example : (fun i : Nat => i = i) 100 := by
  apply chain_unbounded (P := fun i : Nat => i = i) (n := 100)
  · rfl
  · intro i hi
    rfl

-- 公理审计（预期：全部定理公理为 [propext, Quot.sound] 标准子集或零公理）
#print axioms chain3
#print axioms chain4
#print axioms chain_conj3
#print axioms chain_conj4
#print axioms chain_unbounded
#print axioms chain_bounded

end BSD_F
