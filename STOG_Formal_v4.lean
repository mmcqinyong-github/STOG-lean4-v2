import Mathlib

open MeasureTheory Filter Complex NormedSpace Real InnerProductSpace BigOperators ENNReal
open scoped Topology

set_option autoImplicit true

/-!
# STOG-MetaMorph: Spectral Operator Selection
## 五个核心命题的 Lean 4 形式化框架（v4 修订版）

本文件将论文 Methods 中的命题用 Lean 4 + Mathlib 进行形式化，
并在 **Lean 4.35.0-rc3 + Mathlib** 下实际编译通过（零 `sorry`）。

## v4 修订说明（投稿 NMI 前的诚实性整改）

v3 文件包含 15 个 `sorry`。经逐条核查，除 sorry 之外还存在若干**类型错误**
（文件实际上从未编译通过），以及若干**数学上不成立的陈述**。按"宁可修正陈述、
不虚构造证明"的原则，本轮修订如下：

| 条目 | v3 状态 | v4 处置 |
|------|---------|---------|
| P1 风险分解 | 等式要求 `E_est = 0` 才成立（一般为假） | 修正为两分项**等式**（已证明）+ 三分项**上界**推论（已证明） |
| P2 差分/投影降条件数 | 无条件断言（存在反例） | 按 C1 惯例改为带显式假设的 `Prop` 陈述记录，**不作定理断言** |
| P3 线性读出影响函数无界 | 一般 `w` 下结论不成立；`X` 上无范数 | 样本空间取 `X = ℝ`，对常值 `w = c ≠ 0` **完整证明** |
| P3 中位数影响函数有界 | 一般测度空间上无密度概念 | `Prop` 陈述记录 |
| P3 稳健表示最优性 | 原陈述类型错误（`X` 与 `ℝ` 相减） | 在 `X = ℝ` 上作 `Prop` 陈述记录 |
| P4 门控最优性 | 证明需 TV 距离对偶表示等深层工具 | `Prop` 陈述记录（经验上限定形式已被证伪） |
| P5 Hedge 更新定义 | 2 个 sorry（非负性、归一化） | **完整证明** |
| P5 表示层融合优越性 | 陈述为 `∃ optimal`，平凡可证 | **完整证明**（取 `optimal :=` 表示融合本身） |
| P5 Hedge = 自然梯度流 | 一阶近似被写成精确等式（为假） | 修正为差商 `Tendsto` 形式（导数的本义），**完整证明** |

### 编译期发现并修正的实现层错误（v3 从未通过编译）

1. `ℝ≥0` / `ℝ≥0∞` 记法在只 `open ENNReal` 时未激活，被解析为 `ℝ ≥ 0`
   （`LE Type` 实例缺失）。v4 一律显式写作 `NNReal` / `ENNReal`。
2. Lean 4 中文档注释 `/-- … -/` 不可置于 `variable` 命令之前
   （解析器报 "expected 'lemma'"）。v4 将其改为 `--` 行注释。
3. 全部定义改为**显式参数列表**：v3 依赖 section variable 自动插入的
   隐式参数，导致 `spectralMismatch μ S_X H_i H_star` 这类调用
   报 "Function expected"。
4. `Σ` 是求和记法的保留记号，不能作绑定标识符。v4 改名为 `Sigma`。
5. `conditionNumber` 中的 `inner (T x) x` 缺标量参数，且带证明绑定的
   集合构造 `{… | (x : V) (_ : x ≠ 0)}` 不被接受。v4 改为
   `Set.range` over 非零子类型，并显式写 `inner ℝ`。
6. `∘L` 连续线性映射复合记法不存在，改用 `.comp`。
7. `P.IsSymmetric`（连续线性映射的对称性谓词）不存在于当前 Mathlib，
   改为显式幂等命题参数。
8. `measurable.mul` 应为 `Measurable.mul`；`le_or_lt` 未解析，改用 `by_cases`。
9. `hedgeUpdate` / `GatingRisk` 等使用 `Real.exp` / `integral`，须标 `noncomputable`。
10. `Tendsto (fun η => …) / η` 括号位置错误（对函数作除法）；商已移入 lambda 内。

## v3 修订说明（对应论文第 3 版，保留）

* 论文 v3 将原 "Theorem 1–5" 更名为 **Proposition P1–P5** 并附显式假设集；
  本文件在注释与文档字符串层面对齐该命名（Lean 声明名保持不变以保证兼容）。
* **Proposition P4（门控最优性 / 幅度驱动收益）**：限定形式在幅度平衡实验下被经验证伪
  （E4 v4：幅度比平衡到 1.026 后 oracle 收益由 0.61 降至 0.007；
  v3 的收益完全由 6.53× 幅度差驱动）。形式化陈述本身在其假设下仍然成立，故予以保留。
* **Proposition P5 的几何子条款（对应论文 5a/5b）**：经验证伪，已降级至补充材料（SI）。
* 新增 **Conjecture C1（归因–干预秩一致性）**：经验证伪（Spearman ρ = −0.105），
  仅以陈述形式记录在案（见文件末尾），不作为定理断言。
-/


-- ============================================
-- Proposition P1: Spectral Operator Risk Decomposition
-- 谱算子风险分解
-- ============================================

/-- 由谱密度加权的谱测度 μ_S = μ.withDensity S_X

    注：由 `MeasureTheory.lintegral_withDensity`，对任意非负可测被积函数 g 有
    `∫⁻ g ∂μ_S = ∫⁻ S_X · g ∂μ`；故下述 `spectralMismatch` 的密度展开形式
    与原 withDensity 定义完全相等。 -/
noncomputable def spectralMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S_X : Ω → NNReal) : Measure Ω :=
  μ.withDensity (fun ω => (S_X ω : ENNReal))

/-- 谱失配泛函（论文方程 (2) 的核心项）的密度展开形式：
    ∫ ‖H_i - H*‖² S_X dμ（= ∫ ‖H_i - H*‖² dμ_S） -/
noncomputable def spectralMismatch {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S_X : Ω → NNReal) (H_star H_i : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (‖H_i ω - H_star ω‖ ^ 2) * (S_X ω : ENNReal) ∂μ

/-- 预测风险（论文方程 (1) 的 RHS）：R_i = σ2 + spectralMismatch + E_est -/
noncomputable def predictionRisk {Ω : Type*} [MeasurableSpace Ω]
    (σ2 : NNReal) (μ : Measure Ω) (S_X : Ω → NNReal)
    (H_star H_i : Ω → ℂ) (E_est : NNReal) : ENNReal :=
  (σ2 : ENNReal) + spectralMismatch μ S_X H_star H_i + (E_est : ENNReal)

/-- 真实风险：频域中的均方预测误差 -/
noncomputable def trueRisk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S_X : Ω → NNReal) (H_star H_i : Ω → ℂ)
    (ε : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (‖H_star ω - H_i ω‖ ^ 2) * (S_X ω : ENNReal) ∂μ
  + ∫⁻ ω, ENNReal.ofReal (‖ε ω‖ ^ 2) ∂μ

/-- **Proposition P1（v4 修正版）**: 谱算子风险分解（两分项等式）

假设（v3 显式假设集）：
1. H_star 与 H_i 均属于 L²(μ_S)（论文层面保证各项有限）；
2. 噪声与信号正交（交叉项期望为零）；
3. 噪声的期望功率为 σ2。

结论：真实风险 = 不可约噪声 σ2 + 谱失配。

v4 说明：v3 原结论为与 `predictionRisk`（含 E_est）的**等式**，该等式仅当
`E_est = 0` 时成立，作为一般陈述是假命题。修正后的等式捕捉了分解中可证明的
核心恒等式；含 E_est 的三分项形式以**上界**形式见下一条推论，与论文方程 (1)
的语义一致（估计误差项作为附加非负上界项进入）。 -/
theorem spectral_operator_risk_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S_X : Ω → NNReal) (H_star H_i : Ω → ℂ) (ε : Ω → ℂ)     (σ2 _E_est : NNReal)
    (_h_star : MemLp H_star 2 (spectralMeasure μ S_X))
    (_h_i : MemLp H_i 2 (spectralMeasure μ S_X))
    (_h_orthogonality : ∫⁻ ω,
      ENNReal.ofReal ((star (ε ω) * (H_star ω - H_i ω)).re) ∂(spectralMeasure μ S_X) = 0)
    (h_noise_var : ∫⁻ ω, ENNReal.ofReal (‖ε ω‖ ^ 2) ∂μ = (σ2 : ENNReal)) :
    trueRisk μ S_X H_star H_i ε = (σ2 : ENNReal) + spectralMismatch μ S_X H_star H_i := by
  have hswap : ∀ ω : Ω, ‖H_star ω - H_i ω‖ = ‖H_i ω - H_star ω‖ :=
    fun ω => norm_sub_rev _ _
  have e1 : (∫⁻ ω, ENNReal.ofReal (‖H_star ω - H_i ω‖ ^ 2) * (S_X ω : ENNReal) ∂μ)
      = ∫⁻ ω, ENNReal.ofReal (‖H_i ω - H_star ω‖ ^ 2) * (S_X ω : ENNReal) ∂μ := by
    apply lintegral_congr
    intro ω
    rw [hswap ω]
  unfold trueRisk spectralMismatch
  rw [e1, h_noise_var, add_comm]

/-- **Proposition P1 推论（v4 新增）**: 真实风险以上界形式受三分项预测风险约束

    `trueRisk ≤ σ2 + spectralMismatch + E_est = predictionRisk`。

    这正是论文方程 (1) 的语义：不可约噪声与谱失配之和给出风险的主体，
    估计误差项作为附加非负项给出上界。 -/
theorem true_risk_le_predictionRisk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S_X : Ω → NNReal) (H_star H_i : Ω → ℂ) (ε : Ω → ℂ) (σ2 E_est : NNReal)
    (h_star : MemLp H_star 2 (spectralMeasure μ S_X))
    (h_i : MemLp H_i 2 (spectralMeasure μ S_X))
    (h_orthogonality : ∫⁻ ω,
      ENNReal.ofReal ((star (ε ω) * (H_star ω - H_i ω)).re) ∂(spectralMeasure μ S_X) = 0)
    (h_noise_var : ∫⁻ ω, ENNReal.ofReal (‖ε ω‖ ^ 2) ∂μ = (σ2 : ENNReal)) :
    trueRisk μ S_X H_star H_i ε ≤ predictionRisk σ2 μ S_X H_star H_i E_est := by
  calc trueRisk μ S_X H_star H_i ε
      = (σ2 : ENNReal) + spectralMismatch μ S_X H_star H_i :=
        spectral_operator_risk_decomposition μ S_X H_star H_i ε σ2 E_est
          h_star h_i h_orthogonality h_noise_var
    _ ≤ (σ2 : ENNReal) + spectralMismatch μ S_X H_star H_i + (E_est : ENNReal) :=
        by
        exact le_self_add
    _ = predictionRisk σ2 μ S_X H_star H_i E_est := rfl


-- ============================================
-- Proposition P2: Condition-Number Regularization
-- 条件数正则化
-- ============================================

/-- Rayleigh 商取值集合 {⟪Tx, x⟫ / ‖x‖² : x ≠ 0}

    （v4：v3 用 `{inner (T x) x / ‖x‖^2 | (x : V) (_ : x ≠ 0)}` 的
    带证明绑定集合构造，Lean 不接受；`inner` 亦缺标量参数。
    改为 `Set.range` over 非零子类型。） -/
noncomputable def rayleighValues {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V →L[ℝ] V) : Set ℝ :=
  Set.range fun x : {x : V // x ≠ 0} => inner ℝ (T x.1) x.1 / ‖x.1‖ ^ 2

/-- 条件数 κ(T) = Rayleigh 商之 sSup / sInf

    （v4：v3 中 `conditionNumber Σ h_Σ_pos_def` 多传了一个定义体
    未使用的正定性假设参数，是类型错误；已移除。） -/
noncomputable def conditionNumber {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V →L[ℝ] V) : ℝ :=
  sSup (rayleighValues T) / sInf (rayleighValues T)

/-- 差分后的协方差：D ∘ Sigma ∘ D*

    （v4：连续线性映射复合记法 `∘L` 不存在，改用 `.comp`；
    v3 的参数名 `Σ` 是求和记法的保留记号，改名为 `Sigma`。） -/
noncomputable def diffCovariance {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (Sigma D : V →L[ℝ] V) : V →L[ℝ] V :=
  D.comp (Sigma.comp (ContinuousLinearMap.adjoint D))

/-- **Proposition P2（时间部分）: 差分降低条件数 —— 形式化陈述记录**

数学状态（诚实声明）：该命题作为**无条件**断言不成立——
反例：白噪声谱（谱平坦）下差分反而**增大**条件数；且差分算子有非平凡零空间时
`diffCovariance` 非正定。其成立需要论文 v3 显式假设集所要求的**低频谱集中**前提
（S_Δx(ω) = 2(1-cos ω)S_x(ω) 在 ω→0 处抑制低频能量，
Courant–Fischer 极小极大原理下特征值分布更均匀）。
按 C1 的同一惯例，此处仅以 `Prop` 形式记录其陈述（附显式正则性假设），
**不作定理断言**；完整证明需要 Courant–Fischer 与谱重加权分析，超出本仓库当前范围。 -/
def DifferencingLowersConditionNumber {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (Sigma D : V →L[ℝ] V) (α : ℝ) : Prop :=
  0 < α → Function.Injective D →
  (∀ x, x ≠ 0 → 0 < inner ℝ (Sigma x) x) →
  conditionNumber (diffCovariance Sigma D) ≤ conditionNumber Sigma

/-- 投影后的协方差（v4：`∘L` → `.comp`） -/
noncomputable def projectedCovariance {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (Sigma P : V →L[ℝ] V) : V →L[ℝ] V :=
  P.comp (Sigma.comp P)

/-- **Proposition P2（空间部分）: 静态投影降低条件数 —— 形式化陈述记录**

数学状态（诚实声明）：在数学上正确的版本应比较 range(P) 上的限制算子
（Cauchy 特征值交错给出 κ(PΣP|range) ≤ κ(Σ)）。上式中的
`conditionNumber (projectedCovariance Sigma P)` 定义在全空间上，而 PΣP 在
P⊥ 上为零算子（Rayleigh 商 sInf = 0，除法退化为 0），故上式按其字面
平凡地为真（junk value），**不应**据此获得任何数学信念。
此处保留该记录仅为与论文叙述对齐；有意义的版本（交错不等式）留待后续工作。
不作定理断言。

（v4：`P.IsSymmetric` 谓词在当前 Mathlib 中不存在，改为显式幂等参数。） -/
def StaticProjectionLowersConditionNumber {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (Sigma P : V →L[ℝ] V) : Prop :=
  (P.comp P = P) →
  (∀ x, x ≠ 0 → 0 < inner ℝ (Sigma x) x) →
  conditionNumber (projectedCovariance Sigma P) ≤ conditionNumber Sigma


-- ========================================
-- Proposition P3: Robust Sufficient Statistics
-- 稳健充分统计量
--
-- v4：样本空间取 X = ℝ（一元统计，与 median 读出一致）。
-- v3 中的一般可测空间 X 既无范数结构（‖x‖ 类型错误），
-- 也使 RawReadout 的积分不可类型化。
-- ========================================

/-- ε-污染模型：P_ε = (1-ε)P0 + εQ

    （v4：实数标量经 `ENNReal.ofReal` 进入测度的 ENNReal 标量乘；
    v3 中 `(1-ε) • P0` 以 ℝ 标量乘测度是类型错误。） -/
noncomputable def EpsilonContaminated (P0 Q : Measure ℝ) (ε : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - ε) • P0 + ENNReal.ofReal ε • Q

/-- 影响函数（Gateaux 导数，沿污染路径在 ε=0 处于定义域 [0,1] 内的导数——
    稳健统计标准做法，污染分数 ε 天然取值于 [0,1]）：
    IF(x; T, P) = d/dε [T(P_ε(x))] |_{ε=0}

    （v4：v3 中传给 `EpsilonContaminated` 的 `(by sorry)` 证明义务来自
    其被错误声明却未使用的假设参数，现已随签名修正一并消除。） -/
noncomputable def InfluenceFunction (T : Measure ℝ → ℝ) (P : Measure ℝ) (x : ℝ) : ℝ :=
  derivWithin (fun ε => T (EpsilonContaminated P (Measure.dirac x) ε)) (Set.Icc 0 1) 0

/-- 线性（原始矩）读出：T(P) = ∫ w(x)·x dP(x) -/
noncomputable def RawReadout (w : ℝ → ℝ) (P : Measure ℝ) : ℝ := ∫ x, w x * x ∂P

/-- 稳健读出：中位数。中位数的影响函数有界
    （符号函数除以密度在 median 处之值）。 -/
noncomputable def MedianReadout (P : Measure ℝ) : ℝ :=
  sInf {m | P {x | x ≤ m} ≥ (1 / 2 : ENNReal)}

/-- **线性读出的影响函数闭式**（P3 第一部分的证明基础）：
    对 ε ∈ [0,1]，T(P_ε) = (1-ε)T(P) + ε·w(x₀)·x₀，
    故影响函数 IF(x₀) = w(x₀)·x₀ − T(P)。 -/
theorem raw_readout_influence_function (w : ℝ → ℝ) (P : Measure ℝ) (x₀ : ℝ)
    (h_int : Integrable (fun x => w x * x) P) :
    InfluenceFunction (RawReadout w) P x₀ = w x₀ * x₀ - RawReadout w P := by
  have h_dirac_int : Integrable (fun x => w x * x) (Measure.dirac x₀) :=
    integrable_dirac (a := x₀) (f := fun x => w x * x) enorm_lt_top
  have h_aff : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      RawReadout w (EpsilonContaminated P (Measure.dirac x₀) ε)
      = RawReadout w P + ε * (w x₀ * x₀ - RawReadout w P) := by
    intro ε h0 h1
    have hc1 : ENNReal.ofReal (1 - ε) ≠ ∞ := ENNReal.ofReal_ne_top
    have hc2 : ENNReal.ofReal ε ≠ ∞ := ENNReal.ofReal_ne_top
    have hi1 : Integrable (fun x => w x * x) (ENNReal.ofReal (1 - ε) • P) :=
      h_int.smul_measure hc1
    have hi2 : Integrable (fun x => w x * x) (ENNReal.ofReal ε • Measure.dirac x₀) :=
      h_dirac_int.smul_measure hc2
    unfold RawReadout EpsilonContaminated
    rw [integral_add_measure hi1 hi2]
    rw [integral_smul_measure, integral_smul_measure, integral_dirac]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr h1), ENNReal.toReal_ofReal h0]
    simp only [smul_eq_mul]
    ring
  have h_dh : HasDerivWithinAt
      (fun ε => RawReadout w P + ε * (w x₀ * x₀ - RawReadout w P))
      (w x₀ * x₀ - RawReadout w P) (Set.Icc 0 1) 0 := by
    simpa using
      ((((hasDerivAt_id 0).mul_const (w x₀ * x₀ - RawReadout w P)).const_add
        (RawReadout w P)).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1))
  have hmain : HasDerivWithinAt
      (fun ε => RawReadout w (EpsilonContaminated P (Measure.dirac x₀) ε))
      (w x₀ * x₀ - RawReadout w P) (Set.Icc 0 1) 0 := by
    exact HasDerivWithinAt.congr h_dh (fun ε hε => h_aff ε hε.1 hε.2)
      (h_aff 0 le_rfl (by norm_num))
  unfold InfluenceFunction
  exact hmain.derivWithin ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) 0 (by simp))

/-- **Proposition P3（第一部分，v4 修正版）: 常值线性读出的影响函数无界**

在重尾污染下，线性估计量对任意大振幅敏感。v4 说明：v3 对一般 `w` 断言
无界性，但 `w(x)·x` 对任意 `w` 未必无界（`w` 可衰减）；此处按稳健统计文献
的标准形式取常值权重 `w ≡ c ≠ 0`，此时 IF(x) = c·x − d 关于 |x| 线性无界，
结论以**完整证明**给出。`Integrable (fun x => c * x) P` 为显式假设
（重尾 P 下原始矩积分可能不存在，故必须显式假定）。 -/
theorem raw_influence_unbounded
    (c : ℝ) (hc : c ≠ 0) (P : Measure ℝ)
    (h_int : Integrable (fun x => c * x) P) :
    ¬ ∃ B, ∀ x, ‖InfluenceFunction (RawReadout fun _ => c) P x‖ ≤ B := by
  have hif : ∀ x : ℝ,
      InfluenceFunction (RawReadout fun _ => c) P x = c * x - RawReadout (fun _ => c) P := by
    intro x
    exact raw_readout_influence_function (fun _ => c) P x h_int
  rintro ⟨B, hB⟩
  by_cases hB0 : 0 ≤ B
  · set d := RawReadout (fun _ => c) P with hd
    set t : ℝ := (B + ‖d‖ + 1) / |c| with ht
    have ht_nonneg : 0 ≤ t :=
      div_nonneg (add_nonneg (add_nonneg hB0 (norm_nonneg _)) zero_le_one) (abs_nonneg _)
    have h2 : ‖c * t‖ = |c| * t := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht_nonneg]
    have h3 : |c| * t = B + ‖d‖ + 1 := by
      rw [ht, mul_comm, div_mul_cancel₀ _ (abs_ne_zero.mpr hc)]
    have hnorm : B + 1 ≤ ‖c * t - d‖ := by
      calc B + 1 = |c| * t - ‖d‖ := by rw [h3]; ring
        _ = ‖c * t‖ - ‖d‖ := by rw [h2]
        _ ≤ ‖c * t - d‖ := norm_sub_norm_le _ _
    have hcontra := hB t
    rw [hif t] at hcontra
    linarith
  · have hnonneg := hB 0
    rw [hif 0] at hnonneg
    have : B < 0 := lt_of_not_ge hB0
    have hnorm0 := norm_nonneg (c * 0 - RawReadout (fun _ => c) P)
    linarith

/-- **Proposition P3（第二部分）: 稳健读出的影响函数有界 —— 形式化陈述记录**

中位数、Huber、MAD 等 M-估计量的影响函数在重尾下保持有界。
数学状态（诚实声明）：经典证明需要 P 在 median 处有正密度
（IF(x) = sign(x−m)/(2f(m))），"一般测度空间上有界"不是良定命题。
按 C1 惯例以 `Prop` 记录陈述，**不作定理断言**。 -/
def MedianInfluenceBounded (P : Measure ℝ) : Prop :=
  ∃ B : ℝ, ∀ x : ℝ, ‖InfluenceFunction MedianReadout P x‖ ≤ B

/-- **Proposition P3（综合）: ε-污染下稳健表示的风险最优性 —— 形式化陈述记录**

（v4：v3 原陈述 `‖x - MedianReadout P_ε‖` 中 `x` 与实数中位数相减是类型错误；
此处取 X = ℝ，以实数平方误差写出。） -/
noncomputable def RobustRepresentationOptimal (P0 Q : Measure ℝ)
    (ε : ℝ) (_hε : 0 < ε ∧ ε < 1) : Prop :=
  let P_ε := EpsilonContaminated P0 Q ε
  ∫⁻ x, ENNReal.ofReal ((x - MedianReadout P_ε) ^ 2) ∂P_ε
    < ∫⁻ x, ENNReal.ofReal ((x - RawReadout (fun _ => 1) P_ε) ^ 2) ∂P_ε


-- ========================================
-- Proposition P4: Regime Separability and Gating Optimality
-- 体制可分离性与门控最优性
--
-- v3 经验状态注记：P4 的限定形式（幅度驱动收益主张）在幅度平衡实验下被经验证伪
-- （E4 v4：幅度比平衡到 1.026 后 oracle 收益由 0.61 降至 0.007；
-- v3 的收益完全由 6.53× 幅度差驱动）。形式化陈述在其假设下仍然成立，
-- 幅度相关假设（h_balance）在陈述中保持显式。
-- ========================================

/-- 体制标签：A 与 B -/
inductive Regime | A | B
  deriving DecidableEq

instance : Fintype Regime where
  elems := {Regime.A, Regime.B}
  complete := by intro x; cases x <;> simp

/-- 体制重叠 δ_ST = ∫ min(p(s|A), p(s|B)) ds
    这是总变差距离的对偶表示。 -/
noncomputable def regimeOverlap {S : Type*} [MeasurableSpace S]
    (p_s_given_r : Regime → Measure S) : ENNReal :=
  ∫⁻ s, (min ((p_s_given_r Regime.A).rnDeriv (p_s_given_r Regime.B) s).toNNReal
             ((p_s_given_r Regime.B).rnDeriv (p_s_given_r Regime.A) s).toNNReal : ENNReal)
    ∂(p_s_given_r Regime.A)

/-- 最大风险差距 Δ_max -/
def maxRiskGap (R : Regime → NNReal) : NNReal :=
  max (R Regime.A) (R Regime.B) - min (R Regime.A) (R Regime.B)

/-- 门控函数：根据充分统计量输出两体制权重 -/
abbrev Gate (S : Type*) := S → Fin 2 → ℝ

/-- 贝叶斯最优门控 g*(s) = P(r | s)，使用似然比构造后验概率。 -/
noncomputable def BayesGate {S : Type*} [MeasurableSpace S]
    (p_s_given_r : Regime → Measure S) : Gate S := fun s i =>
  let ratio := (p_s_given_r Regime.A).rnDeriv (p_s_given_r Regime.B) s
  if i = 0 then
    ENNReal.toReal (1 / (1 + ratio))     -- P(A|s)
  else
    ENNReal.toReal (ratio / (1 + ratio)) -- P(B|s)

/-- 门控风险：加权平均各体制风险 -/
noncomputable def GatingRisk {S : Type*} [MeasurableSpace S]
    (p_s_given_r : Regime → Measure S) (R : Regime → NNReal) (g : Gate S) : ENNReal :=
  ∫⁻ s, ENNReal.ofReal (g s 0) * (R Regime.A : ENNReal) ∂(p_s_given_r Regime.A) +
  ∫⁻ s, ENNReal.ofReal (g s 1) * (R Regime.B : ENNReal) ∂(p_s_given_r Regime.B)

/-- **Proposition P4: 门控超额风险受体制重叠控制 —— 形式化陈述记录**

假设（v3 显式假设集）：体制幅度平衡 `h_balance : R A = R B`，
则任何可实现门控 g 的超额风险满足 R(g) − R(g*) = O(δ_ST · Δ_max)。

数学状态（诚实声明）：证明需要总变差距离的对偶表示、
Le Cam 型不等式与 ENNReal 截断减法的精细分析；按 C1 惯例以 `Prop` 记录
陈述，**不作定理断言**。经验状态见节首注记（限定形式已被证伪）。 -/
def RegimeGatingOptimality {S : Type*} [MeasurableSpace S]
    (p_s_given_r : Regime → Measure S) (R : Regime → NNReal) : Prop :=
  ∀ (g : Gate S) (_h_balance : R Regime.A = R Regime.B) (Δ_max : NNReal)
    (_h_Δ : maxRiskGap R ≤ Δ_max),
    GatingRisk p_s_given_r R g - GatingRisk p_s_given_r R (BayesGate p_s_given_r)
      ≤ (Δ_max : ENNReal) * regimeOverlap p_s_given_r


-- ==================================
-- Proposition P5: Function-Space Atlas and Fusion Geometry
-- 函数空间图集与融合几何
--
-- v3 经验状态注记：几何子条款（对应论文 5a/5b，表示层融合优越性等
-- 几何主张）经验证伪，已降级至补充材料（SI）；在线学习子条款 (iii)
-- （Hedge 更新 = 概率单形上自然梯度流的 Euler 离散化）保留于正文。
-- ==================================

/-- 模型族：索引集 + 坐标卡（将输入嵌入到预测函数空间） -/
structure ModelFamily (X : Type*) (F : Type*) where
  index : Type*
  chart : index → (X → F)

/-- 图集：一族模型族 -/
abbrev Atlas (X : Type*) (F : Type*) := List (ModelFamily X F)

/-- 图集光滑性：转移映射是局部微分同胚。

v4 类型修正：坐标卡的值域是预测函数空间 `F`，故转移映射 φ, ψ 的类型为
`F → F`（v3 写作 `X → F`，与 `φ (ψ y)` 的复合不兼容）。此条目仍是
`Prop` 层面的陈述记录，不作定理断言。 -/
def SmoothAtlas {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : Atlas X F) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, i ≠ j →
    ∀ z : F, ∃ U ∈ 𝓝 z, ∃ (φ ψ : F → F),
      ContDiffOn ℝ ⊤ φ U ∧ ContDiffOn ℝ ⊤ ψ U ∧
      (∀ y ∈ U, φ (ψ y) = y) ∧ (∀ y ∈ U, ψ (φ y) = y)

/-- n 维概率向量（概率单形） -/
structure ProbVec (n : ℕ) where
  weights : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  sum_eq_one : ∑ i, weights i = 1

/-- Hedge 指数加权更新
    w_i^{t+1} ∝ w_i^t · exp(-η · ℓ_i^t)
    （v4：两处 sorry——非负性、归一化——已完整证明）

    v4 编译修正：使用 `Real.exp`，故必须标记 `noncomputable`。 -/
noncomputable def hedgeUpdate {n : ℕ} (w : ProbVec n) (losses : Fin n → ℝ) (η : ℝ) : ProbVec n := by
  set raw := fun i => w.weights i * Real.exp (-η * losses i) with hraw
  set total := ∑ i, raw i with htotal
  have h_raw_nonneg : ∀ i, 0 ≤ raw i := fun i =>
    mul_nonneg (w.nonneg i) (Real.exp_pos _).le
  have hsum : (∑ j, w.weights j) = 1 := w.sum_eq_one
  have h_exists : ∃ i, 0 < raw i := by
    have hne : ∃ i, w.weights i ≠ 0 := by
      by_contra hc
      push Not at hc
      have hz : (∑ j, w.weights j) = 0 := Finset.sum_eq_zero fun j _ => hc j
      rw [hsum] at hz
      exact one_ne_zero hz
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, mul_pos (lt_of_le_of_ne' (w.nonneg i) hi) (Real.exp_pos _)⟩
  have h_total_pos : 0 < total := Finset.sum_pos' (fun i _ => h_raw_nonneg i)
    (h_exists.imp fun i hi => ⟨Finset.mem_univ i, hi⟩)
  have hsum_pos : 0 < ∑ i, raw i := by rw [← htotal]; exact h_total_pos
  refine ⟨fun i => raw i / total, fun i => div_nonneg (h_raw_nonneg i) h_total_pos.le, ?_⟩
  rw [← Finset.sum_div, htotal, div_self hsum_pos.ne']

/-- **Proposition P5（几何子条款，对应论文 5a/5b）: 表示层融合 vs 输出层加权**

隐藏表示 h_i(x) 包含比最终输出 y_i(x) 更丰富的结构信息，
因此在表示空间中的线性融合（ridge readout）严格优于输出空间的凸组合。

**经验状态（v3 修订）：该几何子条款经验证伪，已降级至补充材料（SI）。**

v4 说明（诚实声明）：该陈述以 `∃ optimal` 形式量化，允许取
`optimal :=` 表示融合本身而使不等式平凡成立——这正说明此形式化陈述
**无法**捕捉"严格优越性"的本义（需要一个对最优值统一量化的 ∀-形式，
而那需要关于 readout 类结构的额外假设）。此处按原陈述给出**完整证明**，
并将其平凡性如实记录：它与经验证伪相一致——不存在非平凡的纯形式化优越性。 -/
theorem representation_fusion_superiority {n : ℕ} {X F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (experts : Fin n → (X → F))
    (hidden : Fin n → (X → EuclideanSpace ℝ (Fin 256)))
    (_readout : EuclideanSpace ℝ (Fin 256) → F)
    (_h : ∀ i, experts i = _readout ∘ hidden i)
    (w : ProbVec n)
    (W : EuclideanSpace ℝ (Fin 256) →L[ℝ] F) :
    ∀ x : X,
      let outputFusion : F := ∑ i, w.weights i • experts i x
      let reprFusion : F := W (∑ i, w.weights i • hidden i x)
      ∃ optimal : F, ‖reprFusion - optimal‖ ≤ ‖outputFusion - optimal‖ := by
  intro x
  refine ⟨W (∑ i, w.weights i • hidden i x), ?_⟩
  simp

/-- **Proposition P5（在线学习子条款 (iii)）: Hedge 是概率单形上的自然梯度流（v4 修正版）**

在 Shahshahani 度量下，指数加权更新等价于自然梯度下降的欧拉离散化。

v4 说明：v3 原陈述把**一阶展开**写成了**精确等式**（
`w_i^{t+1} = w_i^t − η·w_i^t·(ℓ_i^t − wᵀℓ)`），作为精确等式是假命题
（指数归一化更新含 η² 及更高阶项）。修正为导数（差商极限）的本义形式：

    lim_{η→0} (w_i(η) − w_i(0)) / η = −w_i · (ℓ_i − ∑_j w_j ℓ_j)，

右端即 Shahshahani 自然梯度 `−diag(w)(∇L − wᵀ∇L·1)` 的第 i 分量。
完整证明见下。 -/
theorem hedge_natural_gradient {n : ℕ} (w : ProbVec n) (losses : Fin n → ℝ) (i : Fin n) :
    Tendsto (fun η => ((hedgeUpdate w losses η).weights i - w.weights i) / η)
      (𝓝[≠] 0)
      (𝓝 (-(w.weights i * (losses i - ∑ j, w.weights j * losses j)))) := by
  set wᵢ := w.weights i with hwᵢ
  set L := ∑ j, w.weights j * losses j with hL
  have hsum : (∑ j, w.weights j) = 1 := w.sum_eq_one
  have hval : ∀ η : ℝ, (hedgeUpdate w losses η).weights i
      = wᵢ * Real.exp (-η * losses i) / (∑ j, w.weights j * Real.exp (-η * losses j)) :=
    fun η => rfl
  have hg : HasDerivAt (fun η => -η * losses i) (-losses i) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg.mul_const (losses i)
  have hA : HasDerivAt (fun η => wᵢ * Real.exp (-η * losses i)) (wᵢ * (-losses i)) 0 := by
    have h1 := ((Real.hasDerivAt_exp (-(0 : ℝ) * losses i)).comp 0 hg).const_mul wᵢ
    simpa using h1
  have hB : HasDerivAt (fun η => ∑ j, w.weights j * Real.exp (-η * losses j))
      (∑ j, w.weights j * (-losses j)) 0 := by
    have e1 : (fun η => ∑ j, w.weights j * Real.exp (-η * losses j))
        = ∑ j, (fun η => w.weights j * Real.exp (-η * losses j)) := by
      ext η
      simp [Finset.sum_apply]
    rw [e1]
    have h1 : HasDerivAt (∑ j, (fun η => w.weights j * Real.exp (-η * losses j)))
        (∑ j, w.weights j * (Real.exp (-(0 : ℝ) * losses j) * (-losses j))) 0 := by
      refine HasDerivAt.sum fun j _ => ?_
      have hgj : HasDerivAt (fun η => -η * losses j) (-losses j) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).neg.mul_const (losses j)
      exact ((Real.hasDerivAt_exp (-(0 : ℝ) * losses j)).comp 0 hgj).const_mul _
    have h2 : (∑ j, w.weights j * (Real.exp (-(0 : ℝ) * losses j) * (-losses j)))
        = ∑ j, w.weights j * (-losses j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Real.exp_zero]
    simpa [h2] using h1
  have hB0 : (∑ j, w.weights j * Real.exp (-(0 : ℝ) * losses j)) = 1 := by
    simp [Real.exp_zero, hsum]
  have hquot : HasDerivAt
      (fun η => wᵢ * Real.exp (-η * losses i) / (∑ j, w.weights j * Real.exp (-η * losses j)))
      ((wᵢ * (-losses i) * (∑ j, w.weights j * Real.exp (-(0 : ℝ) * losses j))
        - wᵢ * Real.exp (-(0 : ℝ) * losses i) * (∑ j, w.weights j * (-losses j)))
        / ((∑ j, w.weights j * Real.exp (-(0 : ℝ) * losses j)) ^ 2)) 0 :=
    hA.div hB (by rw [hB0]; exact one_ne_zero)
  rw [hB0] at hquot
  have hneg : (∑ j, w.weights j * (-losses j)) = -L := by
    have e1 : (∑ j, w.weights j * (-losses j))
        = ∑ j, -(w.weights j * losses j) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [e1, Finset.sum_neg_distrib, hL]
  have hval' : (wᵢ * (-losses i) * 1
        - wᵢ * Real.exp (-(0 : ℝ) * losses i) * (∑ j, w.weights j * (-losses j))) / ((1 : ℝ) ^ 2)
      = -wᵢ * (losses i - L) := by
    rw [hneg]
    simp [Real.exp_zero]
    ring
  rw [hval'] at hquot
  have hmain : HasDerivAt (fun η => (hedgeUpdate w losses η).weights i)
      (-wᵢ * (losses i - L)) 0 := by
    refine hquot.congr_of_eventuallyEq ?_
    exact EventuallyEq.of_eq (funext fun η => hval η)
  have hf0' : (fun η => (hedgeUpdate w losses η).weights i) 0 = wᵢ := by
    simpa [Real.exp_zero, hsum] using hval 0
  have hslope := hasDerivAt_iff_tendsto_slope.mp hmain
  simpa [slope_fun_def_field, hf0', hwᵢ, sub_zero, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hslope


-- ==================================
-- Conjecture C1 (Attribution–Intervention Rank Consistency)
-- 归因–干预秩一致性猜想 —— 经验证伪
--
-- v3 新增：论文 v3 引入猜想 C1——按归因分数对专家/窗口排序与按实际干预
-- 效果排序应当一致（Spearman 秩一致）。实测 Spearman ρ = −0.105，
-- 猜想在经验上被证伪。此处仅以 `def` 形式记录其陈述（不作为定理断言，
-- 不声称证明），以便形式化仓库与论文保持同步。
-- ==================================

/-- **Conjecture C1（归因–干预秩一致性），仅陈述，不断言。**

对 `n` 个对象，若对象 `i` 的归因分数不高于对象 `j`，则其干预效果也不高于
`j`（单调秩一致，即正 Spearman 秩相关的定性内容）。

经验状态（v3 修订）：**已证伪**（Spearman ρ = −0.105）。
本表述仅记录；本项目不对其作任何真理性断言。 -/
def attributionInterventionRankConsistent {n : ℕ}
    (attributionScore interventionEffect : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, attributionScore i ≤ attributionScore j →
    interventionEffect i ≤ interventionEffect j
