# TrotterError 形式化 ↔ 论文对照表（milestone 规划用）

> 数据来源：`C:\Users\Windows11\Downloads\papers\TrotterError\`（论文 LaTeX 源码）
> 与 `D:\p2m-v4331\FQFP\TrotterError\`（v4.33.1 分支源码）。
> 对照依据是**形式化代码自己的 docstring 引用**（65 处），
> 即作者亲手写下的「这个 Lean 声明对应论文哪一条」——这是最权威的映射证据。

---

## A. 论文的编号结果清单（按文件）

### `theory.tex` — 核心理论

| 论文 label | 环境 | 内容 |
|---|---|---|
| `thm:error_type` | Theorem（Types of Trotter error） | 三种误差的显式表达式（additive / exponentiated / multiplicative） |
| `thm:error_order_cond` | Theorem | 阶条件：误差为 $O(\tau^p)$ 的等价刻画 |
| `thm:comm_exp_conj` | Theorem（Commutator expansion of a conjugation of matrix exponentials） | 共轭展开 + 两条范数界（一般 / 反厄米） |
| `thm:trotter_error_comm_scaling` | Theorem（Trotter error with commutator scaling） | **主定理**：additive 与 multiplicative Trotter 误差的渐近界 |
| `cor:trotter_number_comm_scaling` | Corollary | Trotter number 的 commutator scaling |
| `eq:Etau` | equation | $\mathscr E(\tau)$ 的显式式 |
| `eq:pf` | equation | product formula 的一般定义 |
| `eq:unitary_conjugation` | equation | 幺正共轭 |

### `order.tex`

| label | 环境 | 内容 |
|---|---|---|
| `lem:order_cond_deriv` | Lemma | 阶条件与迭代导数在 0 处为零的等价 |
| `lem:monomial` | Lemma | 单项式积分的阶 |
| `prop:order_cond_rule` | Proposition | 阶条件的运算规则 |

### `prelim.tex`

| label | 环境 | 内容 |
|---|---|---|
| `lem:td_Duhamel` | Lemma | 时间序演化的 Duhamel 公式 |
| `lem:interaction_picture` | Lemma | 相互作用绘景 |
| `lem:fte` | Lemma | 时间序演化的基本定理 |
| `lem:time_ordered_norm_bound` | Lemma | 时间序指数的范数界 |
| `cor:time_ordered_distance_bound` | Corollary | 时间序指数之间的距离界 |
| `lem:trotter_error_one_norm_scaling` | Lemma | **一范数标度界** |
| `cor:trotter_number_one_norm_scaling` | Corollary | 一范数下的 Trotter number |
| `eq:trotter_error_one_norm_scaling_bound` | equation | 一范数标度界的具体式 |
| `eq:pf1`, `eq:pf2k` | equation | Lie–Trotter 与二阶 Suzuki 公式 |
| `eq:int_eq` | equation | 时间序指数与迭代积分的关系 |

### `prefactor.tex`

| label | 环境 | 内容 |
|---|---|---|
| `prop:pf1_bound` | Proposition | 一阶（Lie–Trotter）前因子的紧界 |
| `prop:pf2_bound` | Proposition | 二阶（Suzuki）前因子的紧界 |

### `pf2k.tex`

| label | 环境 | 内容 |
|---|---|---|
| `prop:pf4_bound_2term` | Proposition | 四阶公式的 2-term 前因子界 |
| `prop:pf4_bound_3term` | Proposition | 四阶公式的 3-term 前因子界 |

### `app.tex` / `rep.tex` / `type.tex`

| label | 文件 | 内容 |
|---|---|---|
| `eq:alpha_comm_one_norm` | app.tex | 用一范数表示 $\tilde\alpha_{\mathrm{comm}}$（计数论证） |
| `prop:pf-local-obs` | app.tex | 局域可观测量 |
| `lem:relative` | app.tex | 相对界 |
| （`rep.tex`） | rep.tex | commutator scaling 的计算细节；`thm:trotter_error_comm_scaling` 的证明落在这里 |
| `thm:error_type` 的推导 | type.tex | 三种误差的推导 |

---

## B. 对照表：论文结果 → Lean 声明（作者 docstring 自述）

| 论文 label | Lean 声明 | 文件:行 | 状态 |
|---|---|---|---|
| `thm:error_type` (1) | `errorType_additive` | ErrorTypes.lean:517 | ✅ 已形式化 |
| `thm:error_type` (2) | `errorType_exponentiated` | ErrorTypes.lean:542 | ✅ |
| `thm:error_type` (3) | `errorType_multiplicative` | ErrorTypes.lean:560 | ✅ |
| `thm:error_order_cond` | `errorOrderCond_iff` | OrderCondition.lean:761 | ✅ |
| | `errorOrderCond_additive_iff` | OrderCondition.lean:612 | ✅ |
| | `errorOrderCond_exponentiated_iff` | OrderCondition.lean:688 | ✅ |
| | `errorOrderCond_multiplicative_iff` | OrderCondition.lean:726 | ✅ |
| `lem:order_cond_deriv` | `isBigO_norm_iff_iteratedDeriv_lt_eq_zero` | OrderCondition.lean:89 | ✅ |
| `lem:monomial` | `iteratedIntegralMonomial`, `monomial_integral_order` | OrderCondition.lean:415,465 | ✅ |
| `thm:comm_exp_conj` | `commutatorExpansion_conj` | CommutatorExpansion.lean:1468 | ✅ |
| | `commutatorRemainder`（余项定义） | CommutatorExpansion.lean:69 | ✅ |
| `eq:trotter_error_comm_scaling_bound`（p.238–244 两条范数界） | `norm_commutatorRemainder_le` | CommutatorExpansion.lean:915 | ✅ |
| | `norm_commutatorRemainder_le_of_skewAdjoint` | CommutatorExpansion.lean:1035 | ✅ |
| `thm:trotter_error_comm_scaling`（additive，一般） | `trotter_error_bound_comm_scaling` | MainTheorem.lean:429 | ✅ |
| | `trotter_error_comm_scaling`（$=O$ 形式） | MainTheorem.lean:518 | ✅ |
| `thm:trotter_error_comm_scaling`（additive，反厄米） | `trotter_error_bound_comm_scaling_of_skewAdjoint` | MainTheorem.lean:540 | ✅ |
| | `trotter_error_comm_scaling_of_skewAdjoint` | MainTheorem.lean:604 | ✅ |
| `thm:trotter_error_comm_scaling`（multiplicative，一般） | `multiplicative_error_bound_comm_scaling` | MainTheorem.lean:662 | ✅ |
| | `multiplicative_error_comm_scaling` | MainTheorem.lean:753 | ✅ |
| `thm:trotter_error_comm_scaling`（multiplicative，反厄米） | `multiplicative_error_bound_comm_scaling_of_skewAdjoint` | MainTheorem.lean:795 | ✅ |
| | `multiplicative_error_comm_scaling_of_skewAdjoint` | MainTheorem.lean:809 | ✅ |
| `lem:trotter_error_one_norm_scaling` | `trotter_error_one_norm_scaling` | OneNormScaling.lean:259 | ✅ |
| | `trotter_error_bound_one_norm_scaling` | OneNormScaling.lean:238 | ✅ |
| | `trotter_error_one_norm_scaling_of_skew_adjoint` | OneNormScaling.lean:486 | ✅ |
| | `trotter_error_bound_one_norm_scaling_of_skew_adjoint` | OneNormScaling.lean:464 | ✅ |
| `cor:trotter_number_one_norm_scaling` | `trotter_number_one_norm_scaling` | OneNormScaling.lean:619 | ✅ |
| `lem:td_Duhamel` | `timeOrderedExp_duhamel` | TimeOrderedExp.lean:641 | ✅ |
| `lem:interaction_picture` | `timeOrderedExp_interaction_picture` | TimeOrderedExp.lean:675 | ✅ |
| `lem:fte` | `fundamentalTheorem_timeOrderedExp` (+2 变体) | TimeOrderedExp.lean:738,767,778 | ✅ |
| `lem:time_ordered_norm_bound` | `timeOrderedExp_norm_le` | TimeOrderedExp.lean:242 | ✅ |
| | `timeOrderedExp_norm_eq_one_of_skewAdjoint` | TimeOrderedExp.lean:826 | ✅ |
| `cor:time_ordered_distance_bound` | `timeOrderedExp_dist_le` (+2 变体) | TimeOrderedExp.lean:946,1049,1075 | ✅ |
| `eq:int_eq` | `timeOrderedExp_eq_integral` | TimeOrderedExp.lean:322 | ✅ |
| `prop:pf1_bound` | `firstOrder_bound` | Prefactor.lean:224 | ✅ |
| `prop:pf2_bound` | `secondOrder_bound` | Prefactor.lean:620 | ✅ |
| `eq:pf` | `ProductFormulaData`（结构） | ProductFormula.lean:59 | ✅ |
| `eq:pf1` | `lieTrotterData` | Suzuki.lean:84 | ✅ |
| `eq:pf2k` | `suzuki2Data`, `suzukiData`, `suzukiStages` | Suzuki.lean:91,277,264 | ✅ |
| `eq:trotter_error_one_norm_scaling_bound` | `paper_bound_le_target` | OneNormScaling.lean:191 | ✅ |
| `thm:trotter_error_order_cond`（中间桥） | `additiveKernel_eq_commutatorRemainder_sum` | CommutatorScaling.lean:127 | ✅ |

---

## C. 论文中**尚未形式化**的结果（mission 的开发空间）

| 论文 label | 文件 | 内容 | 说明 |
|---|---|---|---|
| `cor:trotter_number_comm_scaling` | theory.tex:283 | commutator scaling 下的 Trotter number | 只有 **一范数**版本形式化了（`trotter_number_one_norm_scaling`）；commutator 版本没有 |
| `prop:order_cond_rule` | order.tex:77 | 阶条件的运算规则（加法/乘法封闭性） | 形式化里有 `orderCond_add`/`orderCond_mul` 等碎片，但未单独对应此命题 |
| `prop:pf4_bound_2term` | pf2k.tex:144 | 四阶公式 2-term 前因子 | 未形式化；**`pf2k.tex` 在 Lean 树中从未被引用** |
| `prop:pf4_bound_3term` | pf2k.tex:159 | 四阶公式 3-term 前因子 | 未形式化（同上）；`sec:prefactor_pf2k` 也无对应 |
| `eq:unitary_conjugation` | theory.tex:132 | 中间 display | 未命名 |
| `eq:one_norm_error_imag` / `eq:one_norm_error_real` | prelim.tex:158,163 | Lemma 6 内的两条特化 | 被一般/反厄米两条 Lean 定理联合覆盖，但标签从未被引用 |
| `eq:alpha_comm_one_norm` | app.tex:80 | 用诱导一范数给 $\tilde\alpha_{\mathrm{comm}}$ 计数上界 | 未形式化（`OneNormScaling` 覆盖的是另一条路径） |
| `prop:pf-local-obs` | app.tex:307 | 局域可观测量应用 | 未形式化 |
| `thm:pf-local`, `thm:pf-power-law`, `thm:pf-electron`, `thm:pf-cluster` | local/power-law/electron/cluster.tex | 各具体物理模型的应用定理 | 未形式化（依赖具体格点/局域哈密顿量模型） |
| `prop:tuv_base`, `prop:tuv_induction`, `lem:sum_scaling`, `lem:commutation_rule` | electron.tex | 电子结构模型的辅助引理 | 未形式化 |
| `lem:norm_delta_H`, `lem:norm_nested_comm` | local-observable.tex | 局域可观测量的范数引理 | 未形式化 |

---

## D. 形式化相对论文的**约定与差异**（写 mission description 时必须交代）

> 以下 1–8 是初版整理的；9–13 由独立交叉核验补充（见 PAPER_MAPPING_full.md §6）。

1. **形式化比论文更一般（这是优势，不是限制）**：论文在矩阵/算子层面陈述，
   用谱范数 $\norm\cdot$；形式化在**完备赋范环** `𝔸`
   （`[NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]`）
   上陈述，用抽象代数范数。
   论文的论证**并不依赖谱范数的特殊性质**——它只用到次乘性
   （$\norm{xy}\le\norm x\norm y$）、$\norm{1}\le1$、完备性（级数与积分收敛）、
   以及反厄米情形下的 $\norm{e^{tA}}=1$。这些性质任何完备赋范代数都有，
   所以**论文的结果对任意完备赋范代数成立**，形式化拿到的是严格更强的定理；
   把 $\mathbb A$ 取成矩阵代数即退回论文原命题。
   叙述时应当说「形式化在抽象范数代数上给出更一般的结果」，
   而**不是**把抽象范数写成需要道歉的差异；同时要说明「此处 $\norm\cdot$ 是代数范数」，
   以免读者误以为在讲谱范数。
2. **未形式化无界生成元**：没有算子定义域、闭算子、无穷维谱理论。
3. **一般公式的表示**：`ProductFormulaData Υ Γ` 表示有 $\Upsilon$ 个 stage、
   $\Gamma$ 个 summand 的一般 product formula，系数满足 `coeff_abs_le_one`（$|a|\le1$），
   每个 stage 带一个 `Equiv.Perm`。
4. **索引约定**：Lean 用 **0-based** `Fin` 索引，论文用 1-based；乘积方向为**右到左**。
5. **阶参数**：结果对任意 $p$ 成立，但需要 $p \ge 1$（`hp : 1 ≤ p`）与 $\Upsilon > 0$（`hΥ : 0 < Υ`）。
6. **反厄米分支**额外需要 `[StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]`
   与 `h_skew : ∀ γ, star (H γ) = -(H γ)`。
7. **两种系数**：`αComm` 与 `αCommConj` 不同，论文里都用 $\alpha_{\mathrm{comm}}$ 记号；
   形式化里 `αCommConj` 是带范数的版本（对应论文的 $\acomm$），
   `αComm` 是另一个（对应 $\tilde\alpha_{\mathrm{comm}}$）。**这是最容易搞错的地方。**
8. **逐点界 vs 渐近界**：论文主定理用 $O(\cdot)$；形式化同时给出了**显式常数的逐点界**
   （`*_bound_*`）和 `Filter.atTop` 上的 `IsBigO` 形式（无 `_bound_`）。两者都形式化了。

9. ⚠️ **prefactor 部分的厄米/反厄米约定是反的。**
   论文用**厄米** $H=\sum_\gamma H_\gamma$ 与实时间演化 $e^{-itH}$；
   形式化（`Prefactor.lean:14-33` 作者自述）改用**反厄米生成元** $K_\gamma$
   （`star (K γ) = -(K γ)`）与 $\exp(t\cdot\sum_\gamma K_\gamma)$。
   对应关系：$H_\gamma \leftrightarrow K_\gamma=-iH_\gamma$、
   $e^{-itH_\gamma}\leftrightarrow\exp(t\cdot K_\gamma)$、
   $[H_\gamma,H_{\gamma'}]\leftrightarrow\lg K_\gamma,K_{\gamma'}\rg$（范数相等），
   **所以常数 $t^2/2$、$t^3/12$、$t^3/24$ 不变**。
   写 Prop 13/14 的 milestone 时必须说清这个翻译。

10. ⚠️ **指数前因子是 2，不是 4。**
    `rep.tex` l.36–44 的中间推导展示的是 $e^{4t\Upsilon\sum\norm{H_\gamma}}$，
    l.44–50 宣布了改进；Lean 的 `trotter_error_bound_comm_scaling` 对应的是**改进后**的
    `thm:trotter_error_comm_scaling` 形式 $e^{2t\Upsilon\sum\norm{H_\gamma}}$。
    （我核对了 `theory.tex:272` 的主定理陈述，确实是 2。）

11. **`[NormOneClass 𝔸]`（$\norm{1}=1$）是显式假设。**
    论文的矩阵自动满足；形式化的 `timeOrderedExp_norm_le`、`norm_eval_le`、
    commutator scaling 系列都显式带着它。`norm_dysonTerm_le_abs` /
    `summable_dysonTerm_abs` 则不需要它。

12. **区间积分是有向的。** 论文假设 $0\le\tau\le t$；
    形式化用有向区间积分，多数陈述对**任意** $t_1,t_2\in\R$ 成立。
    另外「反向区间是逆演化」在论文里是**定义**（prelim.tex l.43），
    在形式化里是**定理**（`TimeOrderedExp.lean:65-68`）。

13. **$O(\cdot)$ 两套约定。** 小 $\tau$ 的 $\OO{}$ → `=O[𝓝 0]`；
    大 $t$ 的 $\cO{}$ → `=O[Filter.atTop]`。因此 `trotter_error_one_norm_scaling`
    用的是 `𝓝 0`，而论文 Lemma 6 写的是 $\cO{}$。
    另外 `cor:trotter_number_one_norm_scaling` 在 Lean 里被改写为
    $r\to\infty$ 时的 $O(r^{-p})$，**不是**论文的 $\epsilon$-精度形式。

14. **`lem:monomial` 只形式化了顺序特化版**（`OrderCondition.lean:415-419`），
    一般形式（每个内层上限是任意更早的变量）作者注明「同样的归纳可给出同阶」。

15. **`suzuki 0` 是 junk identity**；`suzukiData 0 Γ := lieTrotterData Γ` 与它不符，
    `suzuki_eq_eval` 只对 $1\le k$ 陈述（`Suzuki.lean:74,336`）。

16. **`OrderCondition.lean:36-37`**：所有规则都在「光滑生成元」下陈述（对应 order.tex:78 的
    「infinitely differentiable」），但 `orderCond_add`/`orderCond_mul` 不带 `ContDiff` 假设，
    而 `orderCond_deriv_iff`/`_integral_iff`/`_exp_iff` 带。

### D-bis. Lean docstring 中存在**自造引用**（写 milestone 时不要照抄）

已对全部 `*.tex` 用 grep 核实，以下标签**在论文源码中不存在**：

| docstring 里的引用 | 出现位置 | 正确处理 |
|---|---|---|
| `thm:trotter_error_order_cond` | `MainTheorem.lean:45,93`、`CommutatorScaling.lean:127` | 真实标签是 `thm:trotter_error_comm_scaling`；注意 `thm:error_order_cond` 是**另一条**真实定理 |
| `prop:pf1_bound` | `Prefactor.lean:224` | prefactor.tex l.45–50 的 proposition **无 `\label`** |
| `prop:pf2_bound` | `Prefactor.lean:620` | prefactor.tex l.105–114 的 proposition **无 `\label`** |
| `eq:trotter_error_comm_scaling_bound` | `MainTheorem.lean:540` | theory.tex l.273–276 的 display **无 `\label`** |

→ milestone_title 必须用**论文真实编号或明确位置**，不能抄这些自造标签。


---

## E. 建议的 mission 结构

- **`mission_type`**: `ResearchPaper`
- **`main_item_id`（goal）**: `TrotterError.trotter_error_comm_scaling`
  —— 对应 `thm:trotter_error_comm_scaling`，是**最弱而稳定的陈述**
  （$O$ 形式，不会被常数改进推翻）
- **fields**: `mathematical-physics`, `functional-analysis`, `quantum-information`

### milestone 列表（按论文顺序，标题以原文编号开头）

编号已通过**主文件 `\input` 顺序 + 共享计数器**推导确认：
`TrotterErrorTheory.tex` 定义
`\newtheorem{lemma}[theorem]{Lemma}` / `{proposition}[theorem]{Proposition}` /
`{corollary}[theorem]{Corollary}` / `{observation}[theorem]{Observation}`，
即 **Theorem / Lemma / Proposition / Corollary 共用一个计数器**，正文从 1 连续编号；
`theory.tex` 里三条结果用 `\begin{restatable}{theorem}{...}`，同样吃这个计数器。

正文编号序列（已核算）：

```
Lemma 1   lem:td_Duhamel                        prelim.tex
Lemma 2   lem:interaction_picture               prelim.tex
Lemma 3   lem:fte                               prelim.tex
Lemma 4   lem:time_ordered_norm_bound           prelim.tex
Cor 5     cor:time_ordered_distance_bound       prelim.tex
Lemma 6   lem:trotter_error_one_norm_scaling    prelim.tex
Cor 7     cor:trotter_number_one_norm_scaling   prelim.tex
Thm 8     thm:error_type                        theory.tex   (restatable)
Thm 9     thm:error_order_cond                  theory.tex   (restatable)
Thm 10    thm:comm_exp_conj                     theory.tex
Thm 11    thm:trotter_error_comm_scaling        theory.tex   (restatable)  ← 主定理
Cor 12    cor:trotter_number_comm_scaling       theory.tex
Prop 13   prop:pf1_bound                        prefactor.tex
Prop 14   prop:pf2_bound                        prefactor.tex
-- 附录（计数器继续）--
Lemma 15  lem:order_cond_deriv                  order.tex
Lemma 16  lem:monomial                          order.tex
Prop 17   prop:order_cond_rule                  order.tex
```

> ⚠️ **提交前必须核对**：上面的编号是由源码结构推导的，正式提交前应对照
> 已发表版本（arXiv:1912.08854 的 PDF 或期刊版）逐条确认。milestone_title 的
> 硬性规则是「以原文编号开头」，编号错了会被 moderator 退回。

| # | milestone_title | 目标 Lean 声明 | 论文 |
|---|---|---|---|
| 1 | `Lemma 1 — Duhamel formula for time-ordered evolution` | `timeOrderedExp_duhamel` | `lem:td_Duhamel` |
| 2 | `Lemma 3 — fundamental theorem of time-ordered evolution` | `fundamentalTheorem_timeOrderedExp` | `lem:fte` |
| 3 | `Lemma 6 — 1-norm scaling bound for Trotter error` | `trotter_error_one_norm_scaling` | `lem:trotter_error_one_norm_scaling` |
| 4 | `Corollary 7 — Trotter number with 1-norm scaling` | `trotter_number_one_norm_scaling` | `cor:trotter_number_one_norm_scaling` |
| 5 | `Theorem 8 — types of Trotter error` | `errorType_additive` / `_exponentiated` / `_multiplicative` | `thm:error_type` |
| 6 | `Theorem 9 — order conditions of Trotter error` | `errorOrderCond_iff` | `thm:error_order_cond` |
| 7 | `Theorem 10 — commutator expansion of a conjugation of matrix exponentials` | `commutatorExpansion_conj` | `thm:comm_exp_conj` |
| 8 | `Theorem 10 (continued) — norm bounds for the commutator remainder` | `norm_commutatorRemainder_le` / `_of_skewAdjoint` | theory.tex l.237–245（**该 display 无 `\label`**） |
| 9 | `Proposition 13 — tight prefactor for the Lie–Trotter formula` | `firstOrder_bound` | prefactor.tex l.45–50（**该 proposition 无 `\label`**） |
| 10 | `Proposition 14 — tight prefactor for the second-order Suzuki formula` | `secondOrder_bound` | prefactor.tex l.105–114（**无 `\label`**） |
| 11 | `Corollary 12 — Trotter number with commutator scaling`（**尚未形式化**） | — | `cor:trotter_number_comm_scaling` |

**goal 编号已由用户核对确认**：源论文里 Theorem 11 就是 *Trotter error with
commutator scaling*。milestone 编号亦按同一计数器推导（正文共享，
`\newtheorem{lemma}[theorem]{Lemma}`）。

> ⚠️ **`prop:pf1_bound` / `prop:pf2_bound` / `eq:trotter_error_comm_scaling_bound`
> / `thm:trotter_error_order_cond` 这四个标签在论文源码里根本不存在**，
> 是 Lean docstring 里的**自造引用**（已用 grep 对全部 `*.tex` 核实）。
> 写 milestone 时**不能**照抄这些标签，要用论文的真实编号/位置。
> 交叉验证报告见 [PAPER_MAPPING_full.md](PAPER_MAPPING_full.md)（1902 行，独立子代理产出）。

**goal（`main_item_id`）**：`TrotterError.trotter_error_comm_scaling`
—— 对应 **Theorem 11 (`thm:trotter_error_comm_scaling`)**，即论文主定理。

### mission 说明里应点出的「可继续开发」方向

论文里有 **Corollary 12**（`cor:trotter_number_comm_scaling`）——commutator scaling 下的
Trotter number——**尚未形式化**（只形式化了一范数版本 Corollary 7）。这是本 mission
最自然的一个开放目标，也应作为一条 milestone 列入（标注为未完成）。

---

## F. milestone 的 `milestone_description` 原文（逐字摘自论文）

> 规则：milestone_description 用**论文原文的陈述**，**不要**粘贴 Lean 的
> `natural_language_statement`。以下为论文逐字内容（LaTeX 保留，提交时按 JSON 规则把
> 反斜杠写成 `\\`）。

### Lemma 6 — `lem:trotter_error_one_norm_scaling`（prelim.tex:154–166）

> Let $H=\sum_{\gamma=1}^{\Gamma}H_\gamma$ be an operator consisting of $\Gamma$ summands and
> $t\geq 0$. Let $\mathscr{S}(t)=\prod_{\upsilon=1}^{\Upsilon}\prod_{\gamma=1}^{\Gamma}
> e^{ta_{(\upsilon,\gamma)}H_{\pi_{\upsilon}(\gamma)}}$ be a $p$th-order product formula. Then,
> $$\norm{\mathscr{S}(t)-e^{tH}}=\cO{\bigg(\sum_{\gamma=1}^{\Gamma}\norm{H_\gamma}t\bigg)^{p+1}
> e^{t\Upsilon\sum_{\gamma=1}^{\Gamma}\norm{H_\gamma}}}.$$
> Furthermore, if $H_\gamma$ are anti-Hermitian,
> $$\norm{\mathscr{S}(t)-e^{tH}}=\cO{\bigg(\sum_{\gamma=1}^{\Gamma}\norm{H_\gamma}t\bigg)^{p+1}}.$$

### Theorem 8 — `thm:error_type`（theory.tex:57–80）

> Let $H=\sum_{\gamma=1}^{\Gamma}H_\gamma$ be an operator with $\Gamma$ summands. The evolution
> under $H$ for time $t\in\R$ is given by $e^{tH}=e^{t\sum_{\gamma=1}^{\Gamma}H_\gamma}$, which we
> decompose using the product formula
> $\mathscr{S}(t)=\prod_{\upsilon=1}^{\Upsilon}\prod_{\gamma=1}^{\Gamma}
> e^{ta_{(\upsilon,\gamma)}H_{\pi_{\upsilon}(\gamma)}}$. Then,
>
> 1. Trotter error can be expressed in the additive form
>    $\mathscr{S}(t)=e^{tH}+\int_{0}^{t}\mathrm{d}\tau\ e^{(t-\tau)H}\mathscr{S}(\tau)\mathscr{T}(\tau)$,
>    where
>    $\mathscr{T}(\tau)=\sum_{(\upsilon,\gamma)}
>    \prod_{(\upsilon',\gamma')\prec(\upsilon,\gamma)}^{\longrightarrow}
>    e^{-\tau a_{(\upsilon',\gamma')}H_{\pi_{\upsilon'}(\gamma')}}
>    \big(a_{(\upsilon,\gamma)}H_{\pi_{\upsilon}(\gamma)}\big)
>    \prod_{(\upsilon',\gamma')\prec(\upsilon,\gamma)}^{\longleftarrow}
>    e^{\tau a_{(\upsilon',\gamma')}H_{\pi_{\upsilon'}(\gamma')}}
>    -\prod_{(\upsilon',\gamma')}^{\longrightarrow}
>    e^{-\tau a_{(\upsilon',\gamma')}H_{\pi_{\upsilon'}(\gamma')}}H
>    \prod_{(\upsilon',\gamma')}^{\longleftarrow}
>    e^{\tau a_{(\upsilon',\gamma')}H_{\pi_{\upsilon'}(\gamma')}}$;
> 2. Trotter error can be expressed in the exponentiated form
>    $\mathscr{S}(t)=\expT\big(\int_{0}^{t}\mathrm{d}\tau\big(H+\mathscr{E}(\tau)\big)\big)$, where
>    $\mathscr{E}(\tau)=\sum_{(\upsilon,\gamma)}
>    \prod_{(\upsilon',\gamma')\succ(\upsilon,\gamma)}^{\longleftarrow}
>    e^{\tau a_{(\upsilon',\gamma')}H_{\pi_{\upsilon'}(\gamma')}}
>    \big(a_{(\upsilon,\gamma)}H_{\pi_{\upsilon}(\gamma)}\big)
>    \prod_{(\upsilon',\gamma')\succ(\upsilon,\gamma)}^{\longrightarrow}
>    e^{-\tau a_{(\upsilon',\gamma')}H_{\pi_{\upsilon'}(\gamma')}}-H$;
> 3. Trotter error can be expressed in the multiplicative form
>    $\mathscr{S}(t)=e^{tH}(I+\mathscr{M}(t))$, where
>    $\mathscr{M}(t)=\expT\bigg(\int_{0}^{t}\mathrm{d}\tau\
>    e^{-\tau H}\mathscr{E}(\tau)e^{\tau H}\bigg)-I$ with $\mathscr{E}(\tau)$ as above.

### Theorem 9 — `thm:error_order_cond`（theory.tex:103–120）

> Let $H$ be an operator, and let $\mathscr{S}(\tau)$, $\mathscr{T}(\tau)$, $\mathscr{E}(\tau)$,
> and $\mathscr{M}(\tau)$ be infinitely differentiable operator-valued functions defined for
> $\tau\in\R$, such that
> $$\mathscr{S}(t)=e^{tH}+\int_{0}^{t}\mathrm{d}\tau\ e^{(t-\tau)H}\mathscr{S}(\tau)\mathscr{T}(\tau)
> =\expT\bigg(\int_{0}^{t}\mathrm{d}\tau\big(H+\mathscr{E}(\tau)\big)\bigg)=e^{tH}(I+\mathscr{M}(t)).$$
> For any nonnegative integer $p$, the following conditions are equivalent:
> 1. $\mathscr{S}(t)=e^{tH}+\OO{t^{p+1}}$;
> 2. $\mathscr{T}(\tau)=\OO{\tau^p}$;
> 3. $\mathscr{E}(\tau)=\OO{\tau^p}$; and
> 4. $\mathscr{M}(t)=\OO{t^{p+1}}$.

### Theorem 10 — `thm:comm_exp_conj`（theory.tex:221–249）

> Let $A_1,A_2,\ldots,A_s$ and $B$ be operators. Then the conjugation
> $e^{\tau A_s}\cdots e^{\tau A_{2}}e^{\tau A_{1}}Be^{-\tau A_{1}}e^{-\tau A_{2}}\cdots e^{-\tau A_s}$
> $(\tau\in\R)$ has the expansion
> $$e^{\tau A_s}\cdots e^{\tau A_{2}}e^{\tau A_{1}}Be^{-\tau A_{1}}e^{-\tau A_{2}}\cdots e^{-\tau A_s}
> =C_0+C_1\tau+\cdots+C_{p-1}\tau^{p-1}+\mathscr{C}(\tau).$$
> Here, $C_0,\ldots,C_{p-1}$ are operators independent of $\tau$. The operator-valued function
> $\mathscr{C}(\tau)$ is given by
> $$\mathscr{C}(\tau):=\sum_{k=1}^{s}\sum_{\substack{q_1+\cdots+q_k=p\\q_k\neq 0}}
> e^{\tau A_s}\cdots e^{\tau A_{k+1}}
> \cdot\int_{0}^{\tau}\mathrm{d}\tau_2\ e^{\tau_2 A_k}\ad_{A_k}^{q_k}\cdots\ad_{A_1}^{q_1}(B)e^{-\tau_2 A_k}
> \cdot\frac{(\tau-\tau_2)^{q_k-1}\tau^{q_1+\cdots+q_{k-1}}}{(q_k-1)!q_{k-1}!\cdots q_1!}
> \cdot e^{-\tau A_{k+1}}\cdots e^{-\tau A_s}.$$
> Furthermore, we have the spectral-norm bound
> $$\norm{\mathscr{C}(\tau)}\leq\acomm\big(A_s,\ldots,A_1,B\big)\frac{\abs{\tau}^p}{p!}
> e^{2\abs{\tau} \sum_{k=1}^{s}\norm{A_k}}$$
> for general operators and
> $$\norm{\mathscr{C}(\tau)}\leq\acomm\big(A_s,\ldots,A_1,B\big)\frac{\abs{\tau}^p}{p!}$$
> when $A_k$ ($k=1,\ldots,s$) are anti-Hermitian, where
> $$\acomm\big(A_s,\ldots,A_1,B\big):=\sum_{q_1+\cdots+q_s=p}
> \binom{p}{q_1\ \cdots\ q_s}\norm{\ad_{A_s}^{q_s}\cdots\ad_{A_1}^{q_1}(B)}.$$

> milestone 8（Theorem 10 之后的两条范数界）即上式 p.239 与 p.243 两条。

### Theorem 11 — `thm:trotter_error_comm_scaling`（theory.tex:269–282）— **goal**

> Let $H=\sum_{\gamma=1}^{\Gamma}H_\gamma$ be an operator consisting of $\Gamma$ summands and
> $t\geq 0$. Let $\mathscr{S}(t)=\prod_{\upsilon=1}^{\Upsilon}\prod_{\gamma=1}^{\Gamma}
> e^{ta_{(\upsilon,\gamma)}H_{\pi_{\upsilon}(\gamma)}}$ be a $p$th-order product formula. Define
> $\acommtilde=\sum_{\gamma_1,\gamma_2,\ldots,\gamma_{p+1}=1}^\Gamma
> \norm{\big[H_{\gamma_{p+1}},\cdots\big[H_{\gamma_2},H_{\gamma_1}\big]\big]}$.
> Then, the additive Trotter error and the multiplicative Trotter error, defined respectively by
> $\mathscr{S}(t)=e^{tH}+\mathscr{A}(t)$ and $\mathscr{S}(t)=e^{tH}(I+\mathscr{M}(t))$,
> can be asymptotically bounded as
> $$\norm{\mathscr{A}(t)}=\cO{\acommtilde t^{p+1}
> e^{2t \Upsilon\sum_{\gamma=1}^{\Gamma}\norm{H_{\gamma}}}},\quad
> \norm{\mathscr{M}(t)}=\cO{\acommtilde t^{p+1}
> e^{2t \Upsilon\sum_{\gamma=1}^{\Gamma}\norm{H_{\gamma}}}}.$$
> Furthermore, if the $H_\gamma$ are anti-Hermitian, corresponding to physical Hamiltonians,
> we have
> $$\norm{\mathscr{A}(t)}=\cO{\acommtilde t^{p+1}},\quad
> \norm{\mathscr{M}(t)}=\cO{\acommtilde t^{p+1}}.$$

### Corollary 12 — `cor:trotter_number_comm_scaling`（theory.tex:283–290）— **尚未形式化**

> Let $H=\sum_{\gamma=1}^{\Gamma}H_\gamma$ be an operator consisting of $\Gamma$ summands with
> $H_\gamma$ anti-Hermitian and $t\geq 0$. Let $\mathscr{S}(t)=\prod_{\upsilon=1}^{\Upsilon}
> \prod_{\gamma=1}^{\Gamma}e^{ta_{(\upsilon,\gamma)}H_{\pi_{\upsilon}(\gamma)}}$ be a $p$th-order
> product formula. Define $\acommtilde=\sum_{\gamma_1,\gamma_2,\ldots,\gamma_{p+1}=1}^\Gamma
> \norm{\big[H_{\gamma_{p+1}},\cdots\big[H_{\gamma_2},H_{\gamma_1}\big]\big]}$.
> Then, we have $\norm{\mathscr{S}^r(t/r)-e^{tH}}=\cO{\epsilon}$, provided that
> $$r=\cO{\frac{\acommtilde^{1/p}t^{1+1/p}}{\epsilon^{1/p}}}.$$

### 待补原文（提交前必读并逐字摘录）

- **Lemma 1** `lem:td_Duhamel` — `prelim.tex:62`
- **Lemma 3** `lem:fte` — `prelim.tex:94`
- **Corollary 7** `cor:trotter_number_one_norm_scaling` — `prelim.tex:214–230`
- **Proposition 13** `prop:pf1_bound` — `prefactor.tex`
- **Proposition 14** `prop:pf2_bound` — `prefactor.tex`
