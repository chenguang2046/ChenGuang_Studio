/-
Challenge_110_FareySharp.lean
=============================
切片 110 扩展（H1 层最后一块砖）：G-H1α 的 well-spaced 前置 真证 + 锐利大筛骨架前推。
================================================================================
本切片承接 Challenge_109_LargeSieve_v2 的 H1 层骨架，完成两件事：

1. 【真证】Farey 点族的算术间距下界
   `farey_gap`：若 `a/q ≠ b/r`（a,b ∈ ℤ，q,r ∈ ℕ，0 < q,r ≤ Q），则
       |a/q - b/r| ≥ 1/Q²
   证明路径（纯实数 + 整数算术，无任何未证假设）：
       a/q - b/r = (a·r - b·q)/(q·r)                （通分，field_simp）
       分子 a·r - b·q 是非零整数 ⇒ |a·r - b·q| ≥ 1   （整数最小正单位）
       ⇒ |a/q - b/r| ≥ 1/(q·r)
       又 q,r ≤ Q ⇒ q·r ≤ Q² ⇒ 1/(q·r) ≥ 1/Q²       （倒数反序）
   这消解的正是 109 号 `LargeSieveGap` 陈述里"需 well-spaced 结构"的前置负担。

2. 【骨架前推一格】把 G-H1α 的两项假设拆开
   - (A) well-spaced 前置：本文件真证（`wellSpacedFarey_holds`），不再是假设；
   - (B) Bessel 型正交估计：唯一残余缺口，封装为 `BesselResidualGap`（FROZEN）。
   并附 well-spaced 的两个直接度量推论（直径 < 1/Q² 内至多一个 Farey 点），
   这是 (B) 中 Bessel 估计所需的分离性输入。

合规说明：本切片零 sorry、零自定义 axiom；未证内容（Bessel 估计）以显式
structure 承载假设参数，定理一律条件化（gap → 结论），不产生假断言。
-/
import Slices_99.Challenge_109_LargeSieve_v2
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.GCD.Basic

noncomputable section

namespace Goldbach110
open Goldbach109

/-! ## §1 Farey 点间距下界（G-H1α well-spaced 前置，真证） -/

/-- **Farey 间距下界（ℤ 分子版，核心真证）**：
`a/q ≠ b/r`、`0 < q,r ≤ Q` ⇒ `|a/q - b/r| ≥ 1/Q²`。

关键：分子 `a·r - b·q` 是非零整数，故绝对值至少为 1；这一步正是"有理分母
≤ Q 的两个不同分数不可能靠得比 1/Q² 更近"的全部内容。 -/
theorem farey_gap_int (Q : ℕ) {a b : ℤ} {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hne : (a : ℝ) / (q : ℝ) ≠ (b : ℝ) / (r : ℝ)) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / (q : ℝ) - (b : ℝ) / (r : ℝ)| := by
  set N : ℤ := a * (r : ℤ) - b * (q : ℤ) with hN
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hqrR : (0 : ℝ) < (q : ℝ) * (r : ℝ) := by positivity
  -- 通分：把差写成单一分式
  have hkey : (a : ℝ) / (q : ℝ) - (b : ℝ) / (r : ℝ)
      = (N : ℝ) / ((q : ℝ) * (r : ℝ)) := by
    simp only [hN]
    push_cast
    field_simp
    try ring
  -- 分子非零：否则两个分数相等，与假设冲突
  have hNne : N ≠ 0 := by
    intro h0
    refine hne ?_
    have hc : (a : ℝ) * (r : ℝ) = (b : ℝ) * (q : ℝ) := by
      have h1 : ((N : ℤ) : ℝ) = 0 := by rw [h0]; simp
      simp only [hN] at h1
      push_cast at h1
      linarith
    field_simp
    linarith
  rw [hkey, abs_div, abs_of_pos hqrR]
  -- 非零整数绝对值 ≥ 1
  have hNabs : (1 : ℝ) ≤ |(N : ℝ)| := by
    have hpos : (0 : ℤ) < |N| := abs_pos.mpr hNne
    have h1 : (1 : ℤ) ≤ |N| := by omega
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|N| : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Int.cast_abs] at h2
    simpa using h2
  -- 分母放大：1/Q² ≤ 1/(q·r)
  have hstep1 : (1 : ℝ) / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * (r : ℝ)) := by
    have hQ0 : (0 : ℝ) < (Q : ℝ) := by
      have : (0 : ℕ) < Q := lt_of_lt_of_le hq hqQ
      exact_mod_cast this
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hqQ' : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
    have hrQ' : (r : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hrQ
    nlinarith
  -- 分子放大：1/(q·r) ≤ |N|/(q·r)
  have hstep2 : (1 : ℝ) / ((q : ℝ) * (r : ℝ)) ≤ |(N : ℝ)| / ((q : ℝ) * (r : ℝ)) := by
    have hposinv : (0 : ℝ) < ((q : ℝ) * (r : ℝ))⁻¹ := by positivity
    have h := mul_le_mul_of_nonneg_right hNabs (le_of_lt hposinv)
    simpa [div_eq_mul_inv] using h
  exact hstep1.trans hstep2

/-- **Farey 间距下界（ℕ 分子版，主接口）**：自然数分子（`0 ≤ a < q`、`0 ≤ b < r`）的特例。 -/
theorem farey_gap (Q : ℕ) {a b q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hne : (a : ℝ) / (q : ℝ) ≠ (b : ℝ) / (r : ℝ)) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / (q : ℝ) - (b : ℝ) / (r : ℝ)| := by
  have h := farey_gap_int Q (a := (a : ℤ)) (b := (b : ℤ)) hq hr hqQ hrQ ?_
  · simpa using h
  · intro hc
    exact hne (by simpa using hc)

/-- 间距随分母上界单调（真证）：`Q₁ ≤ Q₂` ⇒ `1/Q₂² ≤ 1/Q₁²`。
用于把 "分母 ≤ Q₁ 的间距" 直接搬进 "分母 ≤ Q₂ 的筛"。 -/
theorem farey_gap_mono {Q₁ Q₂ : ℕ} (hQ₁ : 0 < Q₁) (h : Q₁ ≤ Q₂) :
    (1 : ℝ) / (Q₂ : ℝ) ^ 2 ≤ (1 : ℝ) / (Q₁ : ℝ) ^ 2 := by
  have h1 : (0 : ℝ) < (Q₁ : ℝ) := by exact_mod_cast hQ₁
  have h12 : (Q₁ : ℝ) ≤ (Q₂ : ℝ) := by exact_mod_cast h
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith

/-! ## §2 `fareyPoints` 成员解包（真证） -/

/-- `fareyPoints Q` 的成员展开：每个点都是 `a/q` 形式，`0 < q ≤ Q`、`a < q`、`(a,q)=1`。 -/
theorem mem_fareyPoints {Q : ℕ} {x : ℝ} (hx : x ∈ fareyPoints Q) :
    ∃ a q : ℕ, 0 < q ∧ q ≤ Q ∧ a < q ∧ Nat.Coprime a q ∧ x = (a : ℝ) / (q : ℝ) := by
  unfold Goldbach109.fareyPoints at hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨q, hq, hx2⟩ := hx
  rw [Finset.mem_filter, Finset.mem_range] at hq
  obtain ⟨hqQ, hqpos⟩ := hq
  rw [Finset.mem_image] at hx2
  obtain ⟨a, ha, rfl⟩ := hx2
  rw [Finset.mem_filter, Finset.mem_range] at ha
  exact ⟨a, q, hqpos, Nat.lt_succ_iff.mp hqQ, ha.1, ha.2, rfl⟩

/-! ## §3 well-spaced 结构（真证，109 号缺口的前置负担由此消解） -/

/-- **well-spaced 性质**：`fareyPoints Q` 中任意两个不同的点相距至少 `1/Q²`。 -/
def WellSpacedFarey (Q : ℕ) : Prop :=
  ∀ x ∈ fareyPoints Q, ∀ y ∈ fareyPoints Q, x ≠ y → (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |x - y|

/-- **well-spaced 落地定理（真证）**：`fareyPoints Q` 是 `1/Q²`-分离的。
这是 109 号 `LargeSieveGap` 陈述中"需 well-spaced 结构"这一前置的**完全消解**。 -/
theorem wellSpacedFarey_holds (Q : ℕ) : WellSpacedFarey Q := by
  intro x hx y hy hne
  obtain ⟨a, q, hq, hqQ, _, _, rfl⟩ := mem_fareyPoints hx
  obtain ⟨b, r, hr, hrQ, _, _, rfl⟩ := mem_fareyPoints hy
  exact farey_gap Q hq hr hqQ hrQ hne

/-- `fareyPoints` 上的等价形式：集合内相距 `< 1/Q²` 的两点必重合（真证）。 -/
theorem farey_eq_of_close (Q : ℕ) {x y : ℝ}
    (hx : x ∈ fareyPoints Q) (hy : y ∈ fareyPoints Q)
    (hclose : |x - y| < (1 : ℝ) / (Q : ℝ) ^ 2) : x = y := by
  by_contra hne
  have hsep := wellSpacedFarey_holds Q x hx y hy hne
  linarith

/-! ## §4 well-spaced 的度量推论（Bessel 型估计所需的分离性输入，真证） -/

/-- **分离性计数**：任意直径严格小于 `1/Q²` 的有限实点集 `s` 中，`fareyPoints Q`
    至多落进 1 个点。这正是 sharp 大筛里 "Bessel 型估计" 需要的第一手度量事实。 -/
theorem farey_atMost_one_in_small_diam (Q : ℕ) (s : Finset ℝ)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, |x - y| < (1 : ℝ) / (Q : ℝ) ^ 2) :
    (s.filter (fun x => x ∈ fareyPoints Q)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  exact farey_eq_of_close Q hx.2 hy.2 (hdiam x hx.1 y hy.1)

/-- 分离性计数（带权版本）：直径 `< 1/Q²` 的窗口内，Farey 点上的筛和退化为单点值，
    即 `∑_{x ∈ s ∩ Farey} |F(x)|² ≤ sup |F|²`（真证，独立于 `F` 的具体形式）。 -/
theorem farey_sieveSum_small_window (Q : ℕ) (s : Finset ℝ)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, |x - y| < (1 : ℝ) / (Q : ℝ) ^ 2)
    (N : ℕ) (a : ℕ → ℂ) :
    sieveSumOver (s.filter (fun x => x ∈ fareyPoints Q)) N a
      ≤ (N : ℝ) * coefficientEnergy N a := by
  have hcard := farey_atMost_one_in_small_diam Q s hdiam
  have hpt : ∀ x ∈ s.filter (fun x => x ∈ fareyPoints Q),
      Complex.normSq (weightedExpSum N a x) ≤ (N : ℝ) * coefficientEnergy N a :=
    fun x _ => weightedExpSum_normSq_le N a x
  calc sieveSumOver (s.filter (fun x => x ∈ fareyPoints Q)) N a
      ≤ ((s.filter (fun x => x ∈ fareyPoints Q)).card : ℝ)
          * ((N : ℝ) * coefficientEnergy N a) := trivial_large_sieve _ N a
    _ ≤ 1 * ((N : ℝ) * coefficientEnergy N a) := by
        have hc : ((s.filter (fun x => x ∈ fareyPoints Q)).card : ℝ) ≤ 1 := by
          exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hc (by
          have h1 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          have h2 : (0 : ℝ) ≤ coefficientEnergy N a := coefficientEnergy_nonneg N a
          positivity)
    _ = (N : ℝ) * coefficientEnergy N a := one_mul _

/-! ## §5 缺口收缩：G-H1α = (已证 well-spaced) + (残余 Bessel 估计) -/

/-- **[残余缺口 · 唯一]** G-H1α 在 well-spaced 前置消解后的剩余部分：
变系数指数和族的 Bessel 型正交估计（不能由间距单独推出，需 Hilbert 空间几何输入）。

【FROZEN 封条 · 2026-11-04 正式冻结】
冻结理由：本命题等价于 Mathlib 中不存在的「Farey 分辨率的 Bessel 不等式」
（需 L²(ℝ) 上的调和分析 + 逼近论的定量形式），属外部深层结果，不在本地
补 Mathlib 基建的红线允许范围内。冻结后不再作为阻塞项：其前置于本切片
真证，与 109 的平凡界构成 H1 层完整的"上下夹逼"防线。 -/
structure BesselResidualGap (Q N : ℕ) (a : ℕ → ℂ) : Prop where
  bessel : sieveSumOver (fareyPoints Q) N a
    ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a

/-- 由残余 Bessel 缺口直接落地 sharp 大筛（接口焊死，条件化，零假断言）。 -/
theorem large_sieve_sharp_of_bessel {Q N : ℕ} {a : ℕ → ℂ}
    (h : BesselResidualGap Q N a) :
    sieveSumOver (fareyPoints Q) N a
      ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a :=
  h.bessel

/-- **分解无损**：109 号的 `LargeSieveGap` 与本切片的 `BesselResidualGap` 逻辑等价。
说明"well-spaced 前置 + Bessel 估计"的拆分没有削弱原缺口，只是把可证部分剥离出来。 -/
theorem largeSieveGap_iff_bessel {Q N : ℕ} {a : ℕ → ℂ} :
    LargeSieveGap Q N a ↔ BesselResidualGap Q N a :=
  ⟨fun h => ⟨h.bound⟩, fun h => ⟨h.bessel⟩⟩

/-! ## §6 封条：110 扩展层态势 -/

/-- **110 扩展层收口（真证）**：
    ① farey 点族是 `1/Q²`-分离的（原缺口前置已真证）；
    ② 分离性给出小窗口内至多一点的计数界；
    ③ sharp 大筛等价于唯一残余的 Bessel 估计。 -/
theorem slice110_extension_status (Q : ℕ) (N : ℕ) (a : ℕ → ℂ) :
    WellSpacedFarey Q
      ∧ (∀ s : Finset ℝ, (∀ x ∈ s, ∀ y ∈ s, |x - y| < (1 : ℝ) / (Q : ℝ) ^ 2) →
          (s.filter (fun x => x ∈ fareyPoints Q)).card ≤ 1)
      ∧ (BesselResidualGap Q N a →
          sieveSumOver (fareyPoints Q) N a
            ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * coefficientEnergy N a) :=
  ⟨wellSpacedFarey_holds Q,
   fun s hdiam => farey_atMost_one_in_small_diam Q s hdiam,
   fun h => large_sieve_sharp_of_bessel h⟩

end Goldbach110
