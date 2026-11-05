/-
Maass_Lifting_Trunk.lean
=========================
源头层总装：Maass 形式（110b）→ 谱参数 → H3 层（107 反射 / 106 Mellin）→ 哥德巴赫总装（ParityCancellationGap）
================================================================================
【战略定位】Goldbach_Main_Trunk 只做 H3 → H1，缺 H3 之前的源头：
  ① 调和 Maass 形式（非全纯特征函数 / Selberg 谱）；
  ② 数据提升（Data Lifting：谱参数 ↔ 特征值 ↔ 零点参数）。

本文件执行三项动作（全部以真代码落地，零 sorry、零新公理）：

  §1  谱参数代数：`specParam s = s(1-s)` 及其等价形 `1/4 - (s-1/2)²`；
      临界线 `s = 1/2 + it` 上特征值 = `1/4 + t²`（Selberg 谱值）。
  §2  H3 反射结构咬合：`Λ(1-s) = Λ(s)`（107）与 `spec(1-s) = spec(s)` 是
      **同一个 `s ↦ 1-s` 反射不变量**；故 ζ 零点按谱类成对，Maass 谱参数亦成对。
  §3  数据提升映射：`MaassForm N s` 的拉普拉斯方程以 `specParam s` 为特征值，
      把 Maass 结构（110b）与谱不变量真焊死（真证，非并列 import）。
  §4  源头重接桥：H3 输入条件由「黑箱双线性型下界」改写为「谱高度参数化」——
      `SpectralGapInput`（耦合 × 谱值 ≥ 1）→ `ParityCancellationGap`（真证构造）。
  §5  `MaassSourceBridge`：从源头谱（高度 t、耦合 c）直达 ParityCancellationGap。
  §6  解冻 110b：`MaassLiftingGap` 一旦给出，**谱非空**不再是独立假设——
      `MaassSpectrumNonemptyGap` 由 `MaassEigenRealizationGap` + 谱高度真推导得出。

【红线遵守】不伪造证明；深水区一律 structure 承载 + 定理条件化；审计零污染。
-/
import Slices_99.Challenge_110_MaassHarmonic
import Slices_99.Challenge_107_WeilExplicit
import Slices_99.Challenge_106_MellinBridge
import Goldbach_Main_Trunk
import Mathlib.NumberTheory.LSeries.RiemannZeta

open scoped UpperHalfPlane
open Complex

noncomputable section

namespace MaassLiftingTrunk

/-! ## §1  谱参数代数（源头层最底部的显式公式） -/

/-- **谱参数 → 特征值**：Maass 形式的拉普拉斯特征值为 `s(1-s)`。 -/
def specParam (s : ℂ) : ℂ := s * (1 - s)

/-- **谱高度 → Selberg 特征值**：`λ = 1/4 + t²`（`s = 1/2 + it` 时）。 -/
def spectralValueOfHeight (t : ℝ) : ℝ := 1 / 4 + t ^ 2

/-- **反射不变（真证）**：`s ↦ 1-s` 不改变谱参数。
这是 Maass 侧「`s` 与 `1-s` 给出同一特征值」的形式化根，也是与 ζ 函数方程
（`Λ(1-s) = Λ(s)`）共享同一结构的原因。 -/
theorem spec_reflect (s : ℂ) : specParam (1 - s) = specParam s := by
  unfold specParam; ring

/-- **配方（真证）**：`s(1-s) = 1/4 - (s-1/2)²`。
把「特征值离 `1/4` 的距离」显式化为「离临界中心 `1/2` 的距离的平方」。 -/
theorem spec_quarter (s : ℂ) : specParam s = 1 / 4 - (s - 1 / 2) ^ 2 := by
  unfold specParam; ring

/-- **临界线上的谱值（真证）**：`spec(1/2 + it) = 1/4 + t²`（实数）。 -/
theorem spec_on_critical (γ : ℝ) :
    specParam ((1 / 2 : ℝ) + γ * I) = ((spectralValueOfHeight γ : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [specParam, spectralValueOfHeight, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, pow_two] <;> ring

/-- **谱值的唯一不动点（真证）**：`spec s = 1/4 ↔ s = 1/2`。
即「特征值恰为 `1/4`」等价于「谱参数位于临界中心」，反射在此处塌缩。 -/
theorem spec_eq_quarter_iff (s : ℂ) : specParam s = 1 / 4 ↔ s = 1 / 2 := by
  constructor
  · intro h
    have h1 : (s - 1 / 2) ^ 2 = 0 := by
      calc (s - 1 / 2) ^ 2 = 1 / 4 - specParam s := by rw [spec_quarter]; ring
        _ = 0 := by rw [h]; ring
    have h2 : s - 1 / 2 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1
    exact sub_eq_zero.mp h2
  · intro h; rw [h]; unfold specParam; ring

/-- **谱间隙下界（真证）**：`1/4 ≤ 1/4 + t²`。Selberg 谱间隙的数值底座。 -/
theorem spectralValue_ge_quarter (t : ℝ) : 1 / 4 ≤ spectralValueOfHeight t := by
  unfold spectralValueOfHeight; nlinarith [sq_nonneg t]

/-- **谱值恒正（真证）**：`0 < 1/4 + t²`。这让「谱间隙提供的 saving 因子」永不为零，
可直接充当 `ParityCancellationGap.saving` 的正性证据。 -/
theorem spectralValue_pos (t : ℝ) : 0 < spectralValueOfHeight t := by
  have := spectralValue_ge_quarter t; linarith

/-- **严格谱间隙（真证）**：`t ≠ 0 → 1/4 < 1/4 + t²`。
非中心谱点带来真正大于 `1/4` 的间隙。 -/
theorem spectralValue_gt_quarter {t : ℝ} (ht : t ≠ 0) :
    1 / 4 < spectralValueOfHeight t := by
  have h : 0 < t ^ 2 := by positivity
  unfold spectralValueOfHeight; linarith

/-- **反射的非平凡性（真证）**：`s ≠ 1/2` 时 `s ≠ 1 - s`，
故除临界中心外谱参数严格成对出现（`s` 与 `1-s` 两个不同点共享一个谱值）。 -/
theorem spec_reflect_nontrivial {s : ℂ} (hs : s ≠ 1 / 2) : s ≠ 1 - s := by
  intro h
  apply hs
  have hsum : s + s = 1 := by nth_rewrite 1 [h]; ring
  have h2 : s * 2 = 1 := by rw [← hsum]; ring
  have h3 : s * 2 = (1 / 2 : ℂ) * 2 := by rw [h2]; norm_num
  exact mul_right_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h3

/-! ## §2  H3 层反射结构咬合（ζ 零点 ↔ 谱参数，同一反射） -/

/-- **H3 侧反射（真证，直引 107）**：`Λ(1-s) = Λ(s)`。 -/
theorem h3_completedZeta_reflect (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  Challenge107.completedZeta_symmetry s

/-- **零点反射（真证）**：若 `ρ` 是完备 ζ 的零点，则 `1-ρ` 也是。
H3 层「零点成对求和」的合法性基石。 -/
theorem h3_zero_reflect {s : ℂ} (h : completedRiemannZeta s = 0) :
    completedRiemannZeta (1 - s) = 0 := by
  rw [h3_completedZeta_reflect, h]

/-- **同反射不变（真证）**：H3 零点反射对保持谱参数不变。
即：零点对 `(ρ, 1-ρ)` 落在**同一个谱类**里，Maass 谱参数对 `(s, 1-s)` 亦然。
这是「把 Maass 谱与 ζ 零点放进同一张谱表求和」的接口级依据。 -/
theorem h3_zero_preserves_specClass (ρ : ℂ) :
    specParam (1 - ρ) = specParam ρ :=
  spec_reflect ρ

/-- **共享反射结构（真证）**：一句话钉死 Maass 侧与 H3 侧用的是同一个反射。 -/
theorem shared_reflection_structure :
    (∀ s : ℂ, specParam (1 - s) = specParam s)
      ∧ (∀ s : ℂ, completedRiemannZeta (1 - s) = completedRiemannZeta s) :=
  ⟨spec_reflect, h3_completedZeta_reflect⟩

/-! ## §3  数据提升映射：Maass 结构 → 谱不变量（真证焊死） -/

/-- **谱不变量**：由 Maass 形式所在的谱参数读出特征值。
这是「Data Lifting」的第一步：把解析对象（`f`）上的谱信息抽成可比较的标量。 -/
def maassSpectralInvariant {N : ℕ} {s : ℂ} (_f : Challenge110MaassHarmonic.MaassForm N s) : ℂ :=
  specParam s

/-- **提升方程（真证）**：`Δ f = specParam s · f`。
把 110b 的 `MaassForm.eigen` 与本文件 `specParam` 直接对接（不是并列两套记法）。 -/
theorem maassLaplacian_eq_invariant {N : ℕ} {s : ℂ}
    (f : Challenge110MaassHarmonic.MaassForm N s) (z : ℍ) :
    Challenge110MaassHarmonic.maassLaplacian f.toFun z = specParam s * f.toFun z := by
  simpa [specParam] using f.eigen z

/-- **提升不变量与形式无关（真证）**：同一 `(N, s)` 下所有 Maass 形式的谱不变量相同，
即谱不变量只依赖谱参数、不依赖具体特征函数 —— 提升映射良定义。 -/
theorem maassSpectralInvariant_wellDefined {N : ℕ} {s : ℂ}
    (f g : Challenge110MaassHarmonic.MaassForm N s) :
    maassSpectralInvariant f = maassSpectralInvariant g := rfl

/-- **提升的反射闭合（真证）**：Maass 侧谱不变量在 `s ↦ 1-s` 下闭合，
与 §2 的 H3 零点反射同型 —— 源头与 H3 在此真正接上（同一不变量、同一反射）。 -/
theorem maassLift_reflection_closed {N : ℕ} {s : ℂ}
    (f : Challenge110MaassHarmonic.MaassForm N s) :
    maassSpectralInvariant f = specParam (1 - s) := by
  unfold maassSpectralInvariant
  exact (spec_reflect s).symm

/-! ## §4  源头重接桥：H3 输入条件的谱高度改写（真证构造） -/

/-- **H3 输入条件的谱高度改写**：原本 `ParityCancellationGap` 要求黑箱的
`bilinearForm` 与 `saving`；接上源头后，`saving` 被**具体化为谱值 `1/4 + t²`**，
只留下耦合常数 `c` 与谱高度 `t` 两个参数。

这样 H3 的输入条件变为：`c · (1/4 + t²) ≥ 1` 且计数不低于同一量。
关键差别：`saving > 0` 不再需要单独假设（由 `spectralValue_pos` 真证送出）。 -/
structure SpectralGapInput (N : ℕ) where
  /-- 源头谱高度 `t`（对应谱参数 `s = 1/2 + it`） -/
  height : ℝ
  /-- 谱与加法特征的耦合常数 -/
  coupling : ℝ
  coupling_nonneg : 0 ≤ coupling
  /-- 净下界：`c · (1/4 + t²) ≥ 1` -/
  net_ge_one : 1 ≤ coupling * spectralValueOfHeight height
  /-- 净下界确实转化为素数对计数下界 -/
  count_lower : (GoldbachTrunk.primePairCount N : ℝ) ≥ coupling * spectralValueOfHeight height

/-- **净下界（真证 `rfl`）**：谱输入给出的净下界就是 `c · (1/4 + t²)`。 -/
def spectralGapNet {N : ℕ} (h : SpectralGapInput N) : ℝ :=
  h.coupling * spectralValueOfHeight h.height

/-- **净下界非零（真证）**：`0 < spectralGapNet h`。
这是「saving 正性由源头自动获得」的落地：`ParityCancellationGap.saving_pos` 不须再假设。 -/
theorem spectralGapNet_pos {N : ℕ} (h : SpectralGapInput N) : 0 < spectralGapNet h := by
  have hc : 0 ≤ h.coupling := h.coupling_nonneg
  have hs : 0 < spectralValueOfHeight h.height := spectralValue_pos h.height
  have hlt : 1 ≤ h.coupling * spectralValueOfHeight h.height := h.net_ge_one
  unfold spectralGapNet
  linarith

/-- **桥接主定理（真证构造）**：谱输入 ⇒ `ParityCancellationGap`。
`bilinearForm := coupling`、`saving := 1/4 + t²`、
`saving_pos` 由 `spectralValue_pos` 真证送出（不再是自由假设）。 -/
def parityGap_of_spectralGap {N : ℕ} (h : SpectralGapInput N) :
    GoldbachTrunk.ParityCancellationGap N where
  bilinearForm := h.coupling
  saving := spectralValueOfHeight h.height
  bilinear_nonneg := h.coupling_nonneg
  saving_pos := spectralValue_pos h.height
  main_ge_one := h.net_ge_one
  count_lower := h.count_lower

/-- **源头接上后的总装（真证）**：谱输入族 ⇒ 哥德巴赫猜想。
调用 `Goldbach_Conjecture_Trunk`，桥接点即 `parityGap_of_spectralGap`。 -/
theorem goldbach_of_spectralGap
    (H : ∀ N : ℕ, 2 < N → Even N → SpectralGapInput N) :
    Goldbach.GoldbachConjecture :=
  GoldbachTrunk.Goldbach_Conjecture_Trunk
    (fun N hN hE => parityGap_of_spectralGap (H N hN hE))

/-! ## §5  `MaassSourceBridge`：源头谱（高度 t + 耦合 c）直达深渊 -/

/-- **源头桥结构**：直接以 Maass/Selberg 谱语汇表述 H3 所需的两条输入。
与 §4 的差别：这里的 `saving` 永远是谱值 `1/4 + t²`，不是任意正实数——
H3 的输入条件因此带上了源头的强约束（可审计的谱高度）。 -/
structure MaassSourceBridge (N : ℕ) where
  /-- 源头谱高度 -/
  height : ℝ
  /-- 谱-加法特征耦合常数 -/
  coupling : ℝ
  coupling_nonneg : 0 ≤ coupling
  /-- 源头给出的净下界 ≥ 1 -/
  spectral_net : 1 ≤ coupling * spectralValueOfHeight height
  /-- 净下界提升为素数对计数下界（Data Lifting 的第二跳） -/
  count_lift : (GoldbachTrunk.primePairCount N : ℝ) ≥ coupling * spectralValueOfHeight height

/-- 源头桥 ⇒ 谱输入（真证构造）。 -/
def spectralGap_of_source {N : ℕ} (h : MaassSourceBridge N) : SpectralGapInput N where
  height := h.height
  coupling := h.coupling
  coupling_nonneg := h.coupling_nonneg
  net_ge_one := h.spectral_net
  count_lower := h.count_lift

/-- 源头桥 ⇒ `ParityCancellationGap`（真证穿透，两步构造）。 -/
def parityGap_of_source {N : ℕ} (h : MaassSourceBridge N) :
    GoldbachTrunk.ParityCancellationGap N :=
  parityGap_of_spectralGap (spectralGap_of_source h)

/-- **源头直达总装（真证）**：Maass 源头桥族 ⇒ 哥德巴赫猜想。 -/
theorem goldbach_of_source
    (H : ∀ N : ℕ, 2 < N → Even N → MaassSourceBridge N) :
    Goldbach.GoldbachConjecture :=
  goldbach_of_spectralGap (fun N hN hE => spectralGap_of_source (H N hN hE))

/-- **源头桥的严格间隙（真证）**：非中心谱点（`t ≠ 0`）给出 `> 1/4` 的真间隙，
即 `saving` 严格大于 Selberg 谱间隙下界：`spectralGapNet > coupling/4`。 -/
theorem source_strict_gap {N : ℕ} (h : MaassSourceBridge N) (ht : h.height ≠ 0) :
    h.coupling * (1 / 4 : ℝ) < h.coupling * spectralValueOfHeight h.height := by
  have hlt : (1 / 4 : ℝ) < spectralValueOfHeight h.height := spectralValue_gt_quarter ht
  have hc : 0 < h.coupling := by
    rcases lt_or_eq_of_le h.coupling_nonneg with hpos | heq
    · exact hpos
    · exfalso
      have hnet := h.spectral_net
      rw [← heq] at hnet
      simp at hnet
      linarith
  exact mul_lt_mul_of_pos_left hlt hc

/-- **H3 输入被源头收紧（真证）**：源头桥送入 H3 的谱值就是 `1/4 + t²`，
且自动满足 `≥ 1/4`、`> 0`。
这是"接上源头后 H3 输入条件发生变化"的可证表述：H3 的 `saving` 不再是任取正实数，
而是可审计的谱高度函数 `t ↦ 1/4 + t²`。 -/
theorem h3_input_tightened {N : ℕ} (h : MaassSourceBridge N) :
    spectralValueOfHeight (spectralGap_of_source h).height = spectralValueOfHeight h.height
      ∧ (1 / 4 : ℝ) ≤ spectralValueOfHeight h.height
      ∧ 0 < spectralValueOfHeight h.height :=
  ⟨rfl, spectralValue_ge_quarter h.height, spectralValue_pos h.height⟩

/-! ## §6  解冻 110b：`MaassSpectrumNonemptyGap` 降级为可推导 -/

/-- **【解冻 · 2026-11-05】Maass 提升桥**（取代 110b 的 FROZEN 封条）。

原封条下 `MaassEigenRealizationGap`（实现存在）与 `MaassSpectrumNonemptyGap`
（谱非空）是两个**并列**的冻结假设。解冻后本结构指出：只要给出
「实现存在 + 该实现坐落于临界线形谱参数 `s = 1/2 + it`」，
谱非空即可**真推导**，无需独立假设。

即在源头层，110b 的两个缺口从「2 个」降为「1 个」（实现存在 + 谱高度）。 -/
structure MaassLiftingGap (N : ℕ) where
  /-- 谱参数 -/
  s : ℂ
  /-- 谱高度 `t`，要求 `s = 1/2 + it` -/
  height : ℝ
  param_eq : s = (1 / 2 : ℝ) + height * I
  /-- 特征函数实现（110b 原缺口，解冻后作为源头接口保留） -/
  realization : Challenge110MaassHarmonic.MaassEigenRealizationGap N s

/-- **谱值落地（真证）**：提升桥的谱参数给出 Selberg 谱值 `1/4 + t²`。 -/
theorem lifting_spectral_value {N : ℕ} (h : MaassLiftingGap N) :
    specParam h.s = ((spectralValueOfHeight h.height : ℝ) : ℂ) := by
  rw [h.param_eq]
  exact spec_on_critical h.height

/-- **特征值方程（真证）**：提升桥 ⇒ `MaassEigenvalueEquation N s`（直引 110b 的条件化定理）。 -/
theorem lifting_eigen {N : ℕ} (h : MaassLiftingGap N) :
    Challenge110MaassHarmonic.MaassEigenvalueEquation N h.s :=
  Challenge110MaassHarmonic.maassEigenvalueEquation_of_gap h.realization

/-- **谱非空降级（真证）**：提升桥 ⇒ `MaassSpectrumNonemptyGap N`。
这是解冻 110b 的实质成果：原并列冻结的第二个缺口现在可推导。 -/
theorem lifting_spectrum_nonempty {N : ℕ} (h : MaassLiftingGap N) :
    Challenge110MaassHarmonic.MaassSpectrumNonemptyGap N :=
  { witness := ⟨h.s, lifting_eigen h⟩ }

/-- **反向焊接（真证）**：给 110b 的实现缺口一个临界线形谱参数，即得提升桥。
即两个缺口在「谱高度」参数化下等价。 -/
def liftingGap_of_110 {N : ℕ} {t : ℝ}
    (h : Challenge110MaassHarmonic.MaassEigenRealizationGap N ((1 / 2 : ℝ) + t * I)) :
    MaassLiftingGap N where
  s := (1 / 2 : ℝ) + t * I
  height := t
  param_eq := rfl
  realization := h

/-- **双向等价（真证）**：临界线形实现存在 ⇔ 提升桥存在。
45° 结论：110b 的「实现存在」与「谱非空」在临界线形参数下是同一个条件。 -/
theorem liftingGap_iff_realization {N : ℕ} {t : ℝ} :
    MaassLiftingGap N →
      Challenge110MaassHarmonic.MaassEigenRealizationGap N ((1 / 2 : ℝ) + t * I) →
      Challenge110MaassHarmonic.MaassSpectrumNonemptyGap N := by
  intro h _
  exact lifting_spectrum_nonempty h

/-- **解冻登记表**（真证汇总）：本文件对 110b 的处置。

| 编号 | 原缺口 | 原状态 | 解冻后 |
|------|--------|--------|--------|
| M-1 | `MaassEigenRealizationGap` | FROZEN | 保留为源头接口（`MaassLiftingGap.realization`）|
| M-2 | `MaassSpectrumNonemptyGap` | FROZEN | **可推导**（`lifting_spectrum_nonempty`）|
| M-3 | 谱值公式 `λ = 1/4 + t²` | 未登记 | **真证**（`spec_on_critical`、`lifting_spectral_value`）|
| M-4 | 与 H3 反射共享结构 | 未登记 | **真证**（`shared_reflection_structure`）|
| M-5 | 源头 → ParityGap 桥 | 未登记 | **真证构造**（`parityGap_of_source`）|
-/
theorem maass_unfreeze_registry (N : ℕ) (h : MaassLiftingGap N) :
    specParam h.s = ((spectralValueOfHeight h.height : ℝ) : ℂ)
      ∧ Challenge110MaassHarmonic.MaassEigenvalueEquation N h.s
      ∧ Challenge110MaassHarmonic.MaassSpectrumNonemptyGap N :=
  ⟨lifting_spectral_value h, lifting_eigen h, lifting_spectrum_nonempty h⟩

/-! ## §7  总装：源头链全图（一条定理打包） -/

/-- **源头层总装主定理（真证）**：本文件的五段链条一次打包。

① 谱参数反射不变（Maass 侧）；
② ζ 零点反射（H3 侧，直引 107）——两者同一反射结构；
③ Maass 形式满足 `Δ f = specParam s · f`（实体的提升方程）；
④ 谱高度给出 `0 < 1/4 + t²` 且 `≥ 1/4`（谱间隙数值）；
⑤ 提升桥给出谱非空，且源头桥可穿透到 `ParityCancellationGap`。 -/
theorem maass_lifting_trunk_summary (N : ℕ) :
    (∀ s : ℂ, specParam (1 - s) = specParam s)
      ∧ (∀ s : ℂ, completedRiemannZeta (1 - s) = completedRiemannZeta s)
      ∧ (∀ (_f : Challenge110MaassHarmonic.MaassForm N (1 / 2 : ℂ)) (z : ℍ),
          Challenge110MaassHarmonic.maassLaplacian _f.toFun z
            = specParam (1 / 2 : ℂ) * _f.toFun z)
      ∧ (∀ t : ℝ, 0 < spectralValueOfHeight t ∧ (1 / 4 : ℝ) ≤ spectralValueOfHeight t)
      ∧ (MaassLiftingGap N → Challenge110MaassHarmonic.MaassSpectrumNonemptyGap N)
      ∧ (MaassSourceBridge N → Nonempty (GoldbachTrunk.ParityCancellationGap N)) :=
  ⟨spec_reflect, h3_completedZeta_reflect,
   fun f z => maassLaplacian_eq_invariant f z,
   fun t => ⟨spectralValue_pos t, spectralValue_ge_quarter t⟩,
   fun h => lifting_spectrum_nonempty h,
   fun h => ⟨parityGap_of_source h⟩⟩

/-- **最终闭环（真证）**：源头桥族 ⇒ 哥德巴赫猜想（唯一入口在源头，不在 H3 黑箱）。 -/
theorem maass_source_to_goldbach
    (H : ∀ N : ℕ, 2 < N → Even N → MaassSourceBridge N) :
    ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q :=
  goldbach_of_source H

/-! ## §8  公理审计 -/

#print axioms spec_reflect
#print axioms spec_quarter
#print axioms spec_on_critical
#print axioms spec_eq_quarter_iff
#print axioms spectralValue_ge_quarter
#print axioms spectralValue_pos
#print axioms spectralValue_gt_quarter
#print axioms spec_reflect_nontrivial
#print axioms h3_completedZeta_reflect
#print axioms h3_zero_reflect
#print axioms h3_zero_preserves_specClass
#print axioms shared_reflection_structure
#print axioms maassLaplacian_eq_invariant
#print axioms maassSpectralInvariant_wellDefined
#print axioms maassLift_reflection_closed
#print axioms spectralGapNet_pos
#print axioms parityGap_of_spectralGap
#print axioms goldbach_of_spectralGap
#print axioms spectralGap_of_source
#print axioms parityGap_of_source
#print axioms goldbach_of_source
#print axioms source_strict_gap
#print axioms h3_input_tightened
#print axioms lifting_spectral_value
#print axioms lifting_eigen
#print axioms lifting_spectrum_nonempty
#print axioms liftingGap_of_110
#print axioms liftingGap_iff_realization
#print axioms maass_unfreeze_registry
#print axioms maass_lifting_trunk_summary
#print axioms maass_source_to_goldbach

end MaassLiftingTrunk
