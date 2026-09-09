# Trotter Error 形式化论文完成计划

## 0. 论文定位

本文拟将 `FQP/TrotterError` 描述为对 Childs、Su、Tran、Wiebe、Zhu 的
*A Theory of Trotter Error* 的 Lean 4 + Mathlib 机器核验，而不是把工作包装成一个
“AI 自动证明”项目。

建议标题：

> **A Machine-Checked Formalization of Trotter Error Bounds in Lean 4**

副标题或摘要中说明：

> Formalizing *A Theory of Trotter Error* in Lean 4 and Mathlib

论文网页已经提供了适合引用的公开导航和声明入口：
<https://brycet233.github.io/TrotterError/>。
正文应把网页作为读者查看 Lean 声明和依赖关系的 companion artifact，而不是把网页
本身当作论文内容的替代品。

## 1. 论文的主要贡献

论文应围绕以下三项贡献组织：

1. 在 Lean 内核中核验从时间序指数、一般 product formula、阶条件、误差表示、交换子
   展开到 Trotter error bound 的完整证明链。
2. 精确记录原论文结果在形式化后的数学范围、类型类假设、常数和量词范围。
3. 提取可复用的分析与代数基础设施，包括区间积分、Taylor/迭代导数、有限索引的
   multinomial 展开、有序 `List.prod`、嵌套交换子和指数范数估计。

不要把贡献表述为“证明了一个新的 Trotter 误差定理”。如果没有新的数学推论，论文应
明确这是 faithful machine-checked formalization 和 reusable formal library。

## 2. 形式化范围的冻结

以已推送的 `D:\project\CQM1` 仓库和论文提交时指定的 commit 为唯一 artifact 来源。
核心代码位于 `FQP/TrotterError/`，入口为 `FQP.lean`。

论文应明确说明：

- `ProductFormulaData` 表示有 `Υ` 个 stage、`Γ` 个 summand 的一般 product formula；
- 系数满足 `|a_(υ,γ)| ≤ 1`，每个 stage 带有一个 `Equiv.Perm`；
- 算子族由 `H : Fin Γ → 𝔸` 给出；
- 一般分支工作在完备的带单位范数代数中；
- 反厄米分支额外使用 `StarRing`、`CStarRing`、`StarModule` 等结构；
- 结果对任意阶参数 `p` 给出，但需要 `p ≥ 1` 和 `Υ > 0`；
- 目前不形式化无界生成元、算子定义域、闭算子或一般无限维谱理论；
- Lean 中使用的是抽象代数范数，除非另行建立模型对应，不应直接称为“谱范数”。

应特别核对并在正文中说明论文的右到左乘积约定、`Fin` 的 0-based 索引，以及
`αComm` 与 `αCommConj` 的区别。

## 3. 需要在论文中逐条报告的结果

网页已经列出了主要声明和定义。论文正文用数学语言陈述结果，附表给出 Lean 名称和
网页链接。

| 数学内容 | Lean 入口 | 论文中的作用 |
|---|---|---|
| 时间序指数和 Dyson 展开 | `timeOrderedExp`、`timeOrderedExp_*` | 基础分析框架 |
| 一般 product formula | `ProductFormulaData`、`ProductFormulaData.eval` | 定义 `𝒮(t)` |
| `p` 阶条件 | `ProductFormulaData.IsOrderOf` | 定义高阶公式 |
| 三种误差表示 | `errorType_additive`、`errorType_exponentiated`、`errorType_multiplicative` | 加法、指数化、乘法误差之间的转换 |
| 阶条件等价 | `errorOrderCond_iff` | 将公式阶数转化为 kernel/residual 条件 |
| 单层和多层共轭展开 | `expSMulConj`、`multiConj`、`commutatorExpansion_conj` | 建立交换子余项 |
| 交换子余项范数界 | `norm_commutatorRemainder_le` | 一般分支和反厄米分支的局部估计 |
| 一般 additive Trotter bound | `trotter_error_bound_comm_scaling` | 逐点主界 |
| 一般 additive Big-O | `trotter_error_comm_scaling` | 渐近主定理 |
| 反厄米 additive bound | `trotter_error_bound_comm_scaling_of_skewAdjoint` | 去除指数因子 |
| 反厄米 additive Big-O | `trotter_error_comm_scaling_of_skewAdjoint` | 反厄米渐近主定理 |
| 一般 multiplicative bound | `multiplicative_error_bound_comm_scaling` | 乘法误差逐点界 |
| 反厄米 multiplicative bound | `multiplicative_error_bound_comm_scaling_of_skewAdjoint` | 乘法误差的无指数界 |
| 一阶 prefactor | `firstOrder_bound` | Lie--Trotter 特例 |
| 二阶 prefactor | `secondOrder_bound` | Suzuki 二阶特例 |

主定理至少应写出以下两个显式界。对 `t ≥ 0`，一般分支为

\[
\|\mathcal S(t)-e^{tH}\|
\leq
\frac{2}{p+1}\,\Upsilon^{p+1}\,\alpha_{\mathrm{comm}}^{(p)}
t^{p+1}
\exp\!\left(2t\Upsilon\sum_\gamma\|H_\gamma\|\right),
\]

其中 `H = Σ_γ H_γ`。当所有 `H_γ` 反厄米时，指数因子消失。网页中的 Lean 声明还
给出了相应的 `Filter.atTop` 上的 `IsBigO` 结果，以及 multiplicative error 的对应
版本。

## 4. 论文与原论文的对照审计

制作一张核心对照表，每一行至少包含：

- 原论文的 theorem/lemma/proposition 编号；
- 论文中的数学表述；
- Lean 声明名称；
- 文件和行号；
- 状态：`exact`、`explicit assumption`、`generalized`、`restricted` 或
  `not formalized`；
- 常数是否完全一致；
- 是否增加了完备性、范数、星结构、`p ≥ 1` 或 `Υ > 0` 等显式假设。

重点审计：

1. product formula 的系数和排列；
2. 乘积方向和索引顺序；
3. `IsOrderOf` 对 `O(t^(p+1))` 的定义；
4. `αComm` 与 `αCommConj` 的桥接；
5. `p!`、`Υ^(p+1)`、`2/(p+1)` 和指数因子；
6. 一般分支与反厄米分支的差别；
7. additive 与 multiplicative error 的定义和转换；
8. 逐点界与 `t → ∞` 的 Big-O 结论是否被区分。

只有在确实发现表述不一致时，才声称形式化暴露了原文歧义或遗漏假设；不能预先把
所有新增 Lean 假设描述为原论文错误。

## 5. 正文结构

### 5.1 Introduction

介绍 Trotter product formula、量子模拟中的误差控制，以及机器核验对于常数、量词和
隐藏假设的价值。第一段应先讲数学问题，不要先讲 AI。

### 5.2 Mathematical setting and results

定义 product formula、`p` 阶条件、`αComm`、三种误差和主定理。给出一般分支、反厄米
分支、additive/multiplicative 两类界，并说明 `O` 结论和逐点结论的关系。

### 5.3 Formalization architecture

使用网页中的 dependency graph，按如下依赖顺序说明证明链：

```text
TimeOrderedExp
      ↓
ProductFormula + Calculus
      ↓
ErrorTypes
      ↓
OrderCondition
      ↓
ExpSMulConj + CommutatorExpansion
      ↓
OrderingRemoval
      ↓
CommutatorScaling
      ↓
MainTheorem
```

不要按文件逐个罗列实现细节，而要解释每个层次解决的数学问题。

### 5.4 Comparison with the source paper

放置第 4 节的逐条对照表。这一节应是全文最有说服力的部分。

### 5.5 Reusable infrastructure

说明时间序指数、积分、迭代导数、multinomial、交换子、范数和有序乘积等组件如何
独立于最终 Trotter 定理复用。

### 5.6 AI-assisted development and trust

如保留该节，应准确写明：

- 开发过程中使用的模型始终是 **DeepSeek-V4-Pro**；
- AI 用于证明草稿、API 探索、调试建议和局部重构；
- 数学范围、定理取舍、代码整合和最终核验由作者负责；
- 最终结果以 Lean kernel 检查通过为准。

不要写成“Claude 参与了项目”，也不要把复制来的 `.claude` 工具目录当作 Claude
参与的证据。该目录属于开发环境遗留内容，不是论文贡献的一部分。

### 5.7 Reproducibility

只报告构建 TrotterError 子项目所需的最小信息：仓库 URL、commit、Lean/Mathlib 版本、
入口文件、依赖文件和构建命令。建议在干净环境执行：

```text
lake exe cache get
lake build FQP
lake exe runLinter
lake exe lint-style
```

同时报告 `sorry`、`admit`、`axiom` 和未形式化结果的状态。不要把未实际使用的辅助
脚本或其他项目继承工具写成论文贡献。

### 5.8 Limitations and future work

可列出：

- 无界生成元和算子定义域；
- 更一般的无限维 Hilbert/Banach 算子模型；
- 更高阶具体 splitting formula 的专门误差常数；
- `trotter_number_comm_scaling` 等尚未单独形式化的推论；
- 与量子线路或可计算 Hamiltonian 的具体实例连接。

## 6. 实施阶段和交付物

### 阶段 A：仓库和范围冻结

- [ ] 记录 GitHub URL 和提交 commit；
- [ ] 确认 `FQP/TrotterError` 的公开入口；
- [ ] 确认 Lean、Mathlib 和 Lake 版本；
- [ ] 列出明确不属于论文贡献的仓库内容。

交付物：`artifact manifest` 和一页形式化范围说明。

### 阶段 B：定理和定义清单

- [ ] 从网页和源码建立声明清单；
- [ ] 标出主定理、支撑定理、定义和低阶特例；
- [ ] 为每个声明补充原论文位置和 Lean 文件位置；
- [ ] 核对所有常数和假设。

交付物：论文中的 comparison table 初稿。

### 阶段 C：数学正文

- [ ] 完成 Mathematical setting；
- [ ] 完成 Main results；
- [ ] 写出一般和反厄米两条主证明链；
- [ ] 解释抽象范数代数的范围；
- [ ] 避免把 generic norm 误称为 spectral norm。

交付物：正文第 2--4 节。

### 阶段 D：形式化架构和方法

- [ ] 使用网页 dependency graph；
- [ ] 解释 telescoping、交换子余项和误差转换；
- [ ] 总结可复用基础设施；
- [ ] 加入 DeepSeek-V4-Pro 的准确 provenance 描述。

交付物：正文第 5--7 节。

### 阶段 E：artifact 验证

- [ ] 在干净环境运行 cache/build/linter/style 检查；
- [ ] 固定提交 commit；
- [ ] 检查 GitHub 网页链接和源码链接；
- [ ] 汇总无 `sorry`/`admit`/额外公理的审计结果；
- [ ] 检查网页中的声明名称与提交版本一致。

交付物：可复现性章节和 supplementary artifact 说明。

### 阶段 F：内部审稿和投稿

- [ ] 数学读者检查主定理和常数；
- [ ] Lean 读者检查类型类假设和覆盖范围；
- [ ] 量子模拟读者检查物理动机和反厄米约定；
- [ ] 删除“完整 Trotter 理论”“谱范数”等过强表述；
- [ ] 准备摘要、参考文献、分类和 arXiv 源文件。

## 7. 摘要应包含的事实

摘要建议按以下顺序组织：

1. Trotter error theory 的数学问题和应用背景；
2. 本文在 Lean 4/Mathlib 中形式化的范围；
3. 一般 product formula、交换子标度界以及反厄米分支；
4. 完整证明链和可复用基础设施；
5. GitHub artifact 和机器核验；
6. 尚未覆盖的无界算子或具体应用范围。

AI 不应出现在摘要第一句。若篇幅允许，可在最后一句或方法节中说明 DeepSeek-V4-Pro
辅助开发。

## 8. 最终完成标准

只有满足以下条件，才把论文称为 ready for submission：

- 数学结果、Lean 声明和网页入口逐条对应；
- 主定理的常数、量词和结构假设已人工核对；
- 一般、反厄米、additive、multiplicative 四个分支边界清楚；
- 未形式化的结果明确列出；
- GitHub commit 可从干净环境构建；
- AI provenance 准确且不夸大；
- 论文不依赖读者阅读仓库内部开发工具才能理解贡献。

