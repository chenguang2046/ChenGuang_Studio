/-
Copyright (c) 2026 ChenGuang Studio. All rights reserved.
Challenge 021D (第 103 号独立通道切片 · 特例收编与一致性验证)
================================================================================

目标：把早期手搓特例 100–102（Γ₀(1) / Γ₀(p) / Γ₀(p^k)）收编为主干 103 通用指数公式的
      **向下兼容测试用例**：证明通用公式
          index(N) = ∏ p ∈ primeFactors(N), p^{v_p(N)-1} · (p+1)
      在 N = p 处严格化为 p+1（101 号结论），在 N = p^k 处严格化为 p^k + p^{k-1}
      （102 号结论），从而特例不再是游离骨架，而是主干的可执行一致性测试。

承重关系：
  * `universalIndex` 为通用公式的算术骨架，与 `Gamma0N_index_eq` 右端同形；
  * 101 分支（`specialCase_101_fromTrunk`）只经过 `Gamma0N_index_eq` + 纯算术
    `universalIndex_prime`，不回头引用 021B 的 `Gamma0_prime_index`，
    故为**真正的特化检验**（通用框架独立重算出 101 手搓结论）；
  * 102 分支（`specialCase_102_fromTrunk`）同样只经过 `Gamma0N_index_eq` + 纯算术
    `universalIndex_primePow`；但须如实披露：`Gamma0N_index_eq` 的装配链在素数幂
    分量处追溯 021B `Gamma0_primePow_index`（102 手搓定理），故该分支属于
    **装配回归测试**（确认通用公式在 p^k 处不偏离已证分母），而非独立新证。

零 sorry、零新公理；公理审计见 `#print axioms` 输出的三条标准公理。
-/
import Slices_99.Challenge_021C_Index_Main

set_option linter.unnecessarySimpa false

open scoped BigOperators MatrixGroups
open Matrix Matrix.SpecialLinearGroup QuotientGroup

namespace Challenge021Gamma0NIndex

/-! ## ① 通用指数公式的算术骨架 -/

/-- 通用指数公式（103 号主干的算术骨架）：
`index(N) = ∏ p ∈ primeFactors(N), p^{v_p(N)-1} · (p+1)`。 -/
def universalIndex (N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors, (p ^ (N.factorization p - 1) * (p + 1))

/-- 骨架与主干主定理严格同形：主干指数即 `universalIndex`。 -/
theorem Gamma0N_index_eq_universal (N : ℕ) [NeZero N] :
    (gamma0_N N).index = universalIndex N :=
  Gamma0N_index_eq N

/-! ## ② 纯算术特化：N = 1、N = p、N = p^k -/

/-- 平凡端：N = 1 时空乘积为 1（对应 Γ₀(1) = SL(2,ℤ)，指数 1）。 -/
theorem universalIndex_one : universalIndex 1 = 1 := by
  simp [universalIndex]

/-- 素数特化（102 前的 101 号结论）：`universalIndex p = p + 1`。 -/
theorem universalIndex_prime (p : ℕ) [Fact p.Prime] : universalIndex p = p + 1 := by
  have hp : p.Prime := Fact.out
  rw [universalIndex, hp.primeFactors, Finset.prod_singleton, hp.factorization_self]
  norm_num

/-- 素数幂特化（102 号结论）：`universalIndex (p^k) = p^k + p^{k-1}`。 -/
theorem universalIndex_primePow (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    universalIndex (p ^ k) = p ^ k + p ^ (k - 1) := by
  have hp : p.Prime := Fact.out
  rw [universalIndex, Nat.primeFactors_pow (k := k) p hk.ne', hp.primeFactors,
    Finset.prod_singleton]
  rw [Nat.factorization_pow_self hp]
  calc
    p ^ (k - 1) * (p + 1) = p ^ (k - 1) * p + p ^ (k - 1) := by ring
    _ = p ^ ((k - 1) + 1) + p ^ (k - 1) := by rw [pow_succ]
    _ = p ^ k + p ^ (k - 1) := by rw [Nat.sub_add_cancel hk]

/-! ## ③ 交叉验证定理（主干 ⇒ 特例）

以下两条只经 `Gamma0N_index_eq_universal` + 纯算术引理，不复用 021B 的特例定理
作为证明入口：通用框架自己算出 101 / 102 的手搓结论。 -/

/-- **交叉验证（101 号收编）**：103 通用公式代入素数 `p` 得 `p + 1`。
与 101 号切片结论一致；且该结论完全由通用框架导出。 -/
theorem specialCase_101_fromTrunk (p : ℕ) [Fact p.Prime] :
    (gamma0_N p).index = p + 1 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Gamma0N_index_eq_universal]
  exact universalIndex_prime p

/-- **交叉验证（102 号收编）**：103 通用公式代入 `p^k` 得 `p^k + p^{k-1}`。
与 102 号切片结论一致。 -/
theorem specialCase_102_fromTrunk (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    (gamma0_N (p ^ k)).index = p ^ k + p ^ (k - 1) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  rw [Gamma0N_index_eq_universal]
  exact universalIndex_primePow p k hk

/-! ## ④ 特化路径的双重等式（骨架值 = 主干指数 = 手搓结论） -/

/-- 101 的完整收编陈述：骨架值、主干指数、手搓结论三者相等。 -/
theorem specialization_101 (p : ℕ) [Fact p.Prime] :
    universalIndex p = (gamma0_N p).index ∧ (gamma0_N p).index = p + 1 := by
  have hpan := Gamma0N_index_eq_universal p
  exact ⟨hpan.symm, specialCase_101_fromTrunk p⟩

/-- 102 的完整收编陈述：骨架值、主干指数、手搓结论三者相等。 -/
theorem specialization_102 (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    universalIndex (p ^ k) = (gamma0_N (p ^ k)).index ∧
      (gamma0_N (p ^ k)).index = p ^ k + p ^ (k - 1) := by
  have hpan := Gamma0N_index_eq_universal (p ^ k)
  exact ⟨hpan.symm, specialCase_102_fromTrunk p k hk⟩

/-! ## ⑤ 总装式向下兼容陈述 -/

/-- **向下兼容总定理**：通用框架在 N = 1、N = p、N = p^k 三档上同时给出
`1`、`p+1`、`p^k + p^{k-1}`，即 100–102 手搓特例全部被主干覆盖。 -/
theorem trunk_downwardCompatible :
    universalIndex 1 = 1 ∧
      (∀ (p : ℕ), Fact p.Prime → universalIndex p = p + 1) ∧
      (∀ (p k : ℕ), Fact p.Prime → 0 < k → universalIndex (p ^ k) = p ^ k + p ^ (k - 1)) :=
  ⟨universalIndex_one, fun p _ => universalIndex_prime p,
    fun p k _ hk => universalIndex_primePow p k hk⟩

/-- **手搓特例的一致性回执（101 分支）**：通用框架导出的证明与 021B 手搓定理
`Gamma0_prime_index`（101 号原结论的承载体）是同一命题的两条独立证明路径。
本定理显式引用 `Gamma0_prime_index`，故 021B 若改动签名，此处立即编译失败，
构成对 101 特例的回归保护。 -/
theorem crossCheck_101_agreesWithHandRolled (p : ℕ) [Fact p.Prime] :
    specialCase_101_fromTrunk p = Gamma0_prime_index p :=
  Subsingleton.elim _ _

/-- **手搓特例的一致性回执（102 分支）**：通用框架导出的证明与 021B 手搓定理
`Gamma0_primePow_index`（102 号原结论的承载体）在同一命题上汇合，
构成对 102 特例的回归保护。 -/
theorem crossCheck_102_agreesWithHandRolled (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    specialCase_102_fromTrunk p k hk = Gamma0_primePow_index p k hk :=
  Subsingleton.elim _ _

end Challenge021Gamma0NIndex
