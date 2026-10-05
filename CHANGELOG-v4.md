# CHANGELOG — Lean4 形式化 v4（投稿 NMI 前诚实性整改，2026-10-06）

## 背景

`STOG-with-mathlib.lean4`（v3）含 15 个 `sorry`。本仓库按"宁可修正陈述、不虚构造证明"
的原则整改为 v4（`STOG-with-mathlib-v4.lean4`），并已通过 **Lean 4.35.0-rc3 + Mathlib
（c20717e）** 编译验证：**0 个 sorry、0 个错误**。

核查中发现 v3 文件**实际上从未编译通过**：除 sorry 外还存在多处类型错误。
下表逐条列出 15 个 sorry 的处置与全部修正。

## 15 个 sorry 的逐条处置

| # | 位置（v3 行号） | v3 内容 | v4 处置 |
|---|---|---|---|
| 1 | L92 | P1 风险分解等式 | **已证明**。陈述修正：与含 `E_est` 的 `predictionRisk` 的等式仅当 `E_est=0` 成立（假命题）；改为两分项等式 `trueRisk = σ² + spectralMismatch` + 上界推论 `true_risk_le_predictionRisk` |
| 2 | L119 | `conditionNumber Σ h_Σ_pos_def` 中的 `(by sorry)` | 定义修正：`h_Σ_pos_def` 未被定义体使用，原写法类型错误；定义改为 `conditionNumber (T : V →L[ℝ] V)`，sorry 随签名修正消除 |
| 3 | L131 | P2 时间部分证明骨架 | 数学上作为无条件断言**为假**（白噪声谱下差分增大条件数）；按 C1 惯例改为 `Prop` 陈述记录 `DifferencingLowersConditionNumber`（附显式假设），**不作定理断言** |
| 4 | L141 | 同 #2（投影版） | 同 #2 签名修正 |
| 5 | L144 | P2 空间部分证明骨架 | 转为 `Prop` 陈述记录 `StaticProjectionLowersConditionNumber`；如实注释：全空间条件数在 P⊥ 上退化（junk value），数学上正确的版本需限制到 range(P)（Cauchy 交错） |
| 6 | L172 | `InfluenceFunction` 中传给 `EpsilonContaminated` 的 `(by sorry)` | `EpsilonContaminated` 的 `hε` 假设参数未在定义体使用（类型错误）；签名修正后 sorry 消除 |
| 7 | L184 | 同 #6 | 同上 |
| 8 | L194 | P3 线性读出 IF 无界 | **已证明**（修正版）：一般 `w` 下结论不成立，`w` 可衰减；取常值 `w ≡ c ≠ 0`，`IF(x) = c·x − d` 无界性给出完整证明（依赖 `raw_readout_influence_function` 闭式） |
| 9 | L206 | P3 中位数 IF 有界 | 一般测度空间上无密度概念，命题不良定；转为 `Prop` 陈述记录 `MedianInfluenceBounded`，**不作定理断言** |
| 10 | L220 | P3 稳健表示最优性 | v3 陈述类型错误（`X` 与 `ℝ` 中位数相减）；样本空间取 `X = ℝ` 后转为 `Prop` 陈述记录 `RobustRepresentationOptimal` |
| 11 | L222 | 同 #10 的证明骨架 | 同上 |
| 12 | L292 | P4 门控最优性证明骨架 | 证明需 TV 距离对偶表示等深层工具；转为 `Prop` 陈述记录 `RegimeGatingOptimality`，**不作定理断言**（注：P4 限定形式已被经验证伪，见论文 v3 注记） |
| 13 | L334–335 | `hedgeUpdate` 非负性与归一化 | **已完整证明**（`Finset.sum_pos'`、`Subtype.coe_injective`、`NNReal.coe_sum` 等） |
| 14 | L357 | P5 表示层融合优越性 | **已证明**：陈述为 `∃ optimal`，取 `optimal :=` 表示融合本身，不等式平凡成立。如实注释：该 `∃` 形式无法捕捉"严格优越性"，与经验证伪一致 |
| 15 | L367 | P5 Hedge=自然梯度流 | v3 把一阶近似写成精确等式（**为假**，含 η² 项）；修正为差商极限（导数本义）：`lim_{η→0}(w_i(η)−w_i(0))/η = −w_i(ℓ_i − ∑wⱼℓⱼ)`，**已完整证明**（HasDerivAt 求和/除法/复合 + `hasDerivAt_iff_tendsto_slope`） |

## 编译环境

- Lean：`leanprover/lean4:v4.35.0-rc3`（经 elan 安装）
- Mathlib：pin 至 commit `c20717eaa791af9dd3f7847f5ba91623bda9ab6b`
- 验证方式：`lake exe cache get` 拉取缓存后 `lake build`，0 错误 0 sorry

## 与论文（v3）叙述的一致性说明

论文 Methods 对 Lean4 的描述为"形式化框架 + 证明骨架"（formalization framework with
proof skeletons）。v4 之后，论文中相应表述建议更新为：

- P1：两份结果（等式 + 上界）均有完整 Lean 证明；
- P3（常值权重情形）、P5（Hedge 更新定义与导数刻画）有完整 Lean 证明；
- P2、P3（median/综合）、P4 以 Lean `Prop` 形式记录陈述（显式假设），与 C1（已证伪猜想）
  的同一惯例处理——这是形式化仓库自身的诚实性纪律，与论文"预注册命题 + 显式假设集 +
  证伪如实报告"的方法论一致。

## GitHub 推送状态

本地提交已完成。远程 `https://github.com/mmcqinyong-github/STOG-lean4-v2.git` 的推送
需要凭据（本机无 SSH 密钥、无 gh CLI），请仓库所有者在本地执行
`git push origin master` 或提供凭据。
