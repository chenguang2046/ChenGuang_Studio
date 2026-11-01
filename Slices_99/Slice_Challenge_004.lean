import Mathlib.Computability.Halting

/-!
# Slice_Challenge_004：停机问题不可判定性

目标：在 Lean 4 + mathlib 中形式化验证"不存在判定任意程序是否停机的全功能
判定子"。采用纯逻辑对角线矛盾：程序以 mathlib 的图灵机编码（`Nat.Partrec.Code`）
为对象，停机性以部分函数定义域 `(eval c n).Dom` 表述；核心结论 `halting_problem`
经 Rice 定理（其证明即对角线自指）得出。本文件不引入任何 sorry，不伪造引理，
全部引理均取自 mathlib 或在此直接构造。
-/

namespace SliceChallenge004

open ComputablePred
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- 停机判定谓词：程序编码 `c` 在输入 `n` 上停机，当且仅当部分函数 `eval c n`
    的定义域非空。这是停机性的数学表述，无需引入额外物理模型。 -/
def Halt (c : Code) (n : ℕ) : Prop :=
  (eval c n).Dom

/-- 逻辑对角线内核：任何命题 `P` 都不能与其否定等价。这是所有自指矛盾
    （停机问题、罗素悖论、Cantor 定理）的共同逻辑骨架。 -/
lemma diagonal_contradiction (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h
  by_cases hp : P
  · exact (h.mp hp) hp
  · exact hp (h.mpr hp)

/-- 抽象自指形式：不存在元素 `a` 使谓词 `D` 在 `a` 处满足 `D a ↔ ¬ D a`。 -/
lemma not_exist_self_refuting {α : Type} :
    ¬ (∃ (D : α → Prop) (a : α), D a ↔ ¬ D a) := by
  rintro ⟨D, a, h⟩
  exact diagonal_contradiction (D a) h

/-- 核心定理：停机问题不可判定。
    不存在可计算谓词判定任意程序是否停机（mathlib `halting_problem`）。 -/
theorem halting_undecidable (n : ℕ) :
    ¬ ComputablePred (fun c => Halt c n) := by
  simpa [Halt] using halting_problem n

end SliceChallenge004

/- 公理审计 -/
#print axioms SliceChallenge004.diagonal_contradiction
#print axioms SliceChallenge004.not_exist_self_refuting
#print axioms SliceChallenge004.halting_undecidable
