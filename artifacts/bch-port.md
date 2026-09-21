# BCH 移植：计划、进度与经验

把 `D:\project\Lean-BCH\BCH`（源，17 个文件 ≈ 108k 行，Lean 4.29.0-rc8）移植进
`D:\project\CQM1\FQFP\BCH`（目标，Lean 4.34.0 / Mathlib v4.34.0），**重写架构与代码风格**，
而不只是搬运。

**当前状态：阶段 1（BCH 核心）、阶段 2（三次/四次/五次项）、阶段 3 的五次项 taylor2 完成。**
`lake build FQFP` ✔（零警告）、`lake exe runLinter` ✔、`lake exe lint-style` ✔，零 `sorry`、零自定义公理、
零 `maxHeartbeats` bump；阶段 1 的定理 `#print axioms` 只剩
`[propext, Classical.choice, Quot.sound]`。五次项的 `_diff_le` 与 taylor2 的四条范数界 +
`bchQuinticTermLinDiff` / `bchQuinticTermTaylor2Remainder` 的定义均已落地；**仍缺**
`bchQuinticTermTaylor2Decomp`（一阶展开恒等式，见 §3.2）。剩余 95k 行的机器生成层未动。

本文合并了原先的三份记录（`bch-port-progress-and-next.md`、
`bch-phase1-log-remainder-continuation.md`、`bch-phase1-complete.md`）。已删去的内容包括：已完成
步骤的逐轮流水账、已被推翻的 `bchWordSum`/`∑ i : Fin m` 系数据形式（含其真实卡点，见 §3.2）、
以及所有指向已删除 `artifacts/bch-audit-round-one/*` 与
`artifacts/bch-phase3-taylor2-word-data.md` 的引用。

---

## 1. 目标文件布局

按**数学陈述**分层，不按源文件分层。行数为当前工作树实测值。

| 文件 | 行数 | 主题 |
|---|---|---|
| `Logarithm.lean` | 1021 | Banach 代数对数；`log (1+·)` 的余项界 |
| `ExpNorm.lean` | 227 | 指数估计：实数与范数代数的 Taylor 余项界 |
| `RealScalar.lean` | 82 | 完备 `ℚ`-代数上的唯一 `ℝ`-代数结构 |
| `WordNorm.lean` | 178 | 词乘积范数（arity-free） |
| `WordExpansion.lean` | 418 | 词展开：二元词模式界、telescoping `_diff` 界、任意字母表词积、加权词表 |
| `NestedCommNorm.lean` | 88 | 嵌套交换子范数 |
| `ChildsBasis.lean` | 163 | Childs 四重交换子基 |
| `BCHElement.lean` | 283 | **结构层**：`bch` 是什么 |
| `BCHCommutator.lean` | 557 | **偏差层**：`bch` 与 `a+b` 差多少 |
| `BCHSymmetric.lean` | 303 | **对称层**：Strang 乘积的误差 |
| `BCHTerms.lean` | 555 | **级数项层**：`bch` 展开的三次/四次/五次项及其范数界 |
| `QuinticRemainder.lean` | 224 | 五次项的一阶 Lipschitz 界（阶段 3 首个完成件） |
| `QuinticTaylor2.lean` | 429 | 五次项 taylor2：`linDiff` / 三块余项的定义 + 四条范数界（**缺** `bchQuinticTermTaylor2Decomp`，见 §3.2） |

依赖链：`Logarithm/ExpNorm → BCHElement → BCHCommutator → BCHSymmetric`；
`WordNorm → WordExpansion → BCHTerms → QuinticRemainder / QuinticTaylor2`。

阶段 1 拆成三个文件的原因：H2 会把 `BCHElement.lean` 推到 1000+ 行；三个文件的主题
（「`bch` 是什么」/「`bch` 与 `a+b` 差多少」/「对称乘积的误差」）边界清楚。阶段 2 单独成
`BCHTerms.lean`：它按「`bch` 的展开系数」组织，与前三层的「误差估计」是两件事。

---

## 2. 阶段 1、2 的源↔目标对照

| 源的声明 / 文件 | 目标 | 备注 |
|---|---|---|
| `LogSeries.lean` 全部 + `Basic:326` 的 `exp∘log` | `Logarithm.lean` | 重定中心到 `1`，去掉定义中的范数；**除**三个 `Complex.log` 互操作引理（`hasSum_logSeriesTerm_complex`、`logOnePlus_complex_eq`、`exp_logOnePlus_complex`）外全部移植 |
| 9 个 `norm_logOnePlus_*` | `norm_log_one_add_sub_logPartialSum_le` + 4 个具体阶 | **参数化**（见 §5.1）；对应目标索引 `n = 0, 2, 3, …, 9` |
| 23 个按 arity 展开的词范数引理 | `List.norm_prod_le` + `WordNorm.lean` 的 `norm_prod_le_ofFn` | arity-free 重写 |
| `Basic:40–216` exp 范数界 | `ExpNorm.lean` | 去重后只留 `TrotterError` 没有的 |
| `Basic:223,251,261,271,176,299,326` | `BCHElement.lean` | 小性条件、`bch`、`exp_bch`、`log_exp_sub_one` |
| `Basic:470` 二次界 `3s²/(2-eˢ)` | `BCHCommutator.lean` | |
| `Basic:612` **H1** `10s³/(2-eˢ)` | `BCHCommutator.lean` | **无心跳 bump**（源带 `maxHeartbeats 16000000`） |
| `Basic:1061` **H2** `300s³` | `BCHSymmetric.lean` | **无心跳 bump**（源带 `6400000`） |
| `Basic:1359,1365` Lie 括号 | `BCHCommutator.lean` | |
| `Basic:1374,1382` Lie 括号形式 | `BCHCommutator.lean`（`lie_eq_commutator`、`norm_bch_sub_add_sub_lie_le`） | 与下面的公开声明列表一致 |
| `norm_bch_sub_add_le'` | **不移植** | 与二次界逐字相同 |
| `LogSeries.lean` 的 `logOnePlus_eq_real` + 手工 `restrictScalars` | `RealScalar.lean` 类型类实例 | |
| `Basic:1397–1670` 三次项族 | `BCHTerms.lean` | def 改名 `bchCubicTerm`（见下） |
| `Basic:1671–1770` 四次项族 | `BCHTerms.lean` | def 改名 `bchQuarticTerm` |
| `Basic:1772–2118` 五次项族（4 组 + 项 + 界） | `BCHTerms.lean` | 组改为词模式数据，见 §3.1；def 改名 `bchQuinticGroup{1,4,6,24}`、`bchQuinticTerm` |
| `Basic:2120–3027` 五次组 `_diff_le` | `QuinticRemainder.lean` | 阶段 3；`_LQ_decomp` 推迟（见 §3.1） |

### 公开声明

- `Logarithm.lean`：`logCoeff`、`norm_logCoeff_le_one`、`logPartialSum`、
  `log_one_add_eq_logPartialSum_add_tsum`、`norm_log_one_add_sub_logPartialSum_le`（主引理）、
  `norm_log_one_add_le`、`norm_log_one_add_sub_le`、`norm_log_one_add_sub_add_sq_le`、
  `norm_log_one_add_sub_add_sq_sub_cube_le`、`logPartialSum_{zero,one,two,three,four}`；
  另有 `logSeries` 族、`log_{one,op}`、`Commute.log*`、`exp_log{,_one_add}` 等（`logSeries` 的
  上游命运见 §5.2）。
- `ExpNorm.lean`：`real_exp_third_order_le_div`、`real_exp_third_order_le_cube`、
  `norm_exp_sub_one_sub_id_le`、`norm_exp_sub_one_sub_id_sub_sq_le`。
- `BCHElement.lean`：`norm_exp_mul_exp_sub_one_lt_one`、`norm_exp_sub_one_lt_one`、`bch`、
  `exp_bch`、`exp_eq_one_of_norm_lt`、`continuousOn_log_one_add`、`log_exp_sub_one`。
- `BCHCommutator.lean`：`norm_bch_sub_add_le`、`norm_bch_sub_add_sub_bracket_le`（H1）、
  `lie_eq_commutator`、`norm_bch_sub_add_sub_lie_le`。
- `BCHSymmetric.lean`：`norm_symmetric_bch_sub_add_le`（H2）。
- `BCHTerms.lean`：三次 `bchCubicTerm`、`bchCubicTerm_smul`、`norm_bchCubicTerm_le`、
  `norm_bchCubicTerm_diff_le`、`bchCubicTerm_LQ_decomp`；四次 `bchQuarticTerm`、
  `bchQuarticTerm_smul`、`norm_bchQuarticTerm_le`、`bchQuarticTerm_LQ_decomp`；五次
  `bchQuinticGroup{1,4,6,24}Words`、`bchQuinticGroup{1,4,6,24}`、
  `bchQuinticGroup{1,4,6,24}_smul`、`bchQuinticTerm`、`bchQuinticTerm_smul`、
  `norm_bchQuinticGroup{1,4,6,24}_le`、`norm_bchQuinticTerm_le`。
  跨层复用的范数辅助（公开）：`norm_mul_sub_mul_le`、`norm_double_commutator_le`、
  `norm_mul_w_mul_le`、`norm_w_mul_mul_le`、`norm_mul_mul_w_le`、`norm_word5_le`。
- `WordExpansion.lean`：二元侧 `wordEval`、`norm_wordEval_le`、`norm_sum_smul_wordEval_le`、
  `norm_sum_wordEval_le`、`wordEval_smul`、`sum_wordEval_smul`、`norm_prod_sub_prod_le`、
  `norm_wordEval_sub_le`、`norm_sum_wordEval_diff_le`；任意字母表侧 `wordProdList`、
  `norm_wordProdList_le`、`norm_sum_smul_wordProdList_le`、`smul_wordProdList`、
  `WeightedWord`、`WeightedWord.eval`、`wordSum`、`wordSum_smul`、`norm_wordSum_le`、
  `norm_wordSum_le_sum_coeff`、`norm_list_sum_le`、`sum_map_const`。
- `QuinticRemainder.lean`：`norm_bchQuinticGroup{1,4,6,24}_diff_le`（常数 10 / 25 / 35 / 5）、
  `norm_bchQuinticTerm_diff_le`（常数 1）。

### 阶段 2 的两条约定（阶段 3 沿用）

1. **`def` 名必须 lowerCamelCase。** Mathlib 的 `defsWithUnderscore` linter 只检查 `def`
   （`Style.lean:557` 先要求 `isDefinition`），`theorem` 不受限——所以 `bch_cubic_term` 这类
   源名必须改写为 `bchCubicTerm`，而定理名仍是源的 `bchCubicTerm_smul`、
   `norm_bchCubicTerm_le`、`bchCubicTerm_LQ_decomp`（Mathlib 先例：`Complex.normSq` 与其
   `normSq_apply`、`norm_compContinuousLinearMap_le`）。
2. **`unusedSectionVars` 靠显式 binder 而不是 `omit`。** 五次项的四个组
   `bchQuinticGroup{1,4,6,24}` 及其范数界只需要 `NormedRing 𝔸`（源亦然），但它们位于
   `NormedAlgebra ℚ 𝔸` 的 section 内；由于本项目禁止 `omit`，改用显式
   `{𝔸 : Type*} [NormedRing 𝔸]` binder 遮蔽 section 变量。

---

## 3. 阶段 3：机器生成层

### 3.1 已完成：arity-free 词 API 与五次项 `_diff_le`

**这是把 95k 行压下来的最大杠杆，且必须在生成器层面做，事后手改不可行。** 生成代码里每个
monomial 分支都重复 `norm_smul_le → norm_Nprod_le → gcongr → ring`，这些全部改成对
`WordNorm.lean` / `WordExpansion.lean` 的单次调用。

付清的第一笔账：五次项四个组的范数界曾为 30 个 5 字母词写 180 行（30 次 `norm_word5_le` +
27 条 `norm_add_le` + 4 次 `linarith only`）；改造后每个是一行
`simpa [bchQuinticGroupN] using norm_sum_wordEval_le bchQuinticGroupNWords a b`。源的对应部分
（`Basic:2120–3027`，约 0.9k 行）为每个 `a`-位置花一个 `calc` 块。

- `WordExpansion.lean` 补齐 `_diff` 侧：`norm_prod_sub_prod_le`（telescoping 原语）、
  `norm_wordEval_sub_le`、`norm_sum_wordEval_diff_le`（组级差分界，常数即该组 a-位置总数），
  以及无权组界 `norm_sum_wordEval_le` 与齐次性 `wordEval_smul` / `sum_wordEval_smul`。
- `BCHTerms.lean` 的四个组是词模式数据（`bchQuinticGroup*Words : Fin m → Fin 5 → Bool`）加
  `Finset.sum`，`_le` / `_smul` 各一行。词表（4 / 10 / 14 / 2）曾与源逐字比对，全部 MATCH。
- `QuinticRemainder.lean`：四个组 `_diff_le`（常数 10 / 25 / 35 / 5）+
  `norm_bchQuinticTerm_diff_le`（常数 1，因 `(1/720)(10 + 4·25 + 6·35 + 24·5) = 440/720 ≤ 1`）。

**代价与偏差**：`_diff_le` 需要 `NormOneClass 𝔸`（源里这三条用 `omit` 去掉了它），因为
telescoping 原语经 `norm_word_le` 归结到 `‖1‖ = 1`；BCH 层的一切本来就带 `NormOneClass`。

**`_LQ_decomp` 伴生引理（有意推迟）**：源把它们写成逐项展开的显式非交换多项式恒等式
（组 1：32 项；组 6：76 项，且带 `set_option maxHeartbeats 3200000`），只能由 `noncomm_ring`
证明。它们只被 `SymmetricSepticPhaseBC` / `SymmetricSepticPieces`（阶段 3 后段）使用，而更早的
`QuinticMixed` / `SexticMixed` / `SepticTaylor` 只需要 `_diff_le` 与 taylor2 余项。因此推迟到
移植那两个消费者时再做；届时先定形状：**逐组显式展开**（忠实于源，但组 6 需处理心跳，本项目
禁止 bump），还是**按词模式生成 W-次数分解**（可能免 bump，但需先看消费者要点什么）。

### 3.2 已落地：五次项 taylor2 余项（`Basic:3028–4830`）

**消费者只用 4 条**：`bchQuinticTermTaylor2Decomp`（恒等式，**仍缺**）、`bchQuinticTermLinDiff` 与
`bchQuinticTermTaylor2Remainder`（定义）、`norm_bchQuinticTermTaylor2Remainder_le`（总界）。源里的
2V / 3V / 4V 三个子块、`taylor2_remainder_split` 及它们的三个界**在 `Basic.lean` 之外无人使用**，
纯属内部脚手架——源为此写了约 1200 行。目标保留三块拆分（因为拆分是 `rfl`、且每块词形一致），
但每块只有一条界。

源的界形状：`≤ (2430/720) M³‖V‖²`，`M = ‖x‖ + ‖V‖ + ‖y‖`；三个子块共用这一形状（常数
`1680/720`、`720/720`、`30/720`）。**常数对齐已核实**：源用的是「每组词数 × 组内最大系数」
而非 `Σ|c|`——`70×24 = 1680`、`30×24 = 720`、`5×6 = 30`，合计 `2430/720` ✓。（生成器另外算出
的 `Σ|c|` 是 `440/384/136/16`，与源的常数无关，仅作诊断。）

**数据与表示（终版）**：数据用 `Fin m → ℚ`（系数，分母 720）与 `Fin m → List (Fin 3)`（模式，
`0 = x`、`1 = V`、`2 = y`），定义是 `bchWordSum` 的一个 `∑`。词数 **75 / 70 / 30 / 5**，与源逐词逐
系数一致，`linDiff` 的 `Σ|c| = 440/720`。旧记录里「改用 `List ℚ` + `List (List (Fin 3))`」的方案
**没有采用**：`Fin` 向量的 `![]` 字面量在默认 `simp` 集下能正常摊平（见「旧方案到底卡在哪」一节），
换成 `List` 只会把 `Fin` 索引的界证明问题换成 `List.getElem` 的界证明问题，收益为零。

**四条范数界的写法（已定型，见 `QuinticTaylor2.lean`）**：全文件只用两条新引理，不展开逐项：

* `sum_abs_le_card_mul_sup'`：`∑ i, |c i| ≤ card ι * (univ.sup' fun i => |c i|)`。这把「一组 `m` 个系数
  的绝对值和」的界归结为「组内最大系数 × 词数」，正是源常数的来源。**不要**用
  `norm_num [<系数 def>]` 直接算 `∑ i : Fin 70`：那会展开 70 项（旧记录里 `Fin.sum_univ_succ` 的写法
  就是这个思路的残留），而且对 `Fin 70 → ℚ` 的 `![]` 字面量并不稳。
* `profile_le`：`M ^ (5 - k) * Vn ^ k ≤ M ^ 3 * Vn ^ 2`（`k ∈ {2,3,4}`，用 `Vn ≤ M`）。字母 profile 本身
  是每块一行 `fin_cases i <;> simp [<词表>] <;> ring_nf ;try simp`。
* 每块一次 `norm_sum_le` + `Finset.sum_le_sum` + `Finset.sum_mul` 即得常数；三条界再合成
  `2430/720`（见文件末的 `norm_bchQuinticTermTaylor2Remainder_le`）。

**已实测的坑（可运行复现见 `artifacts/examples/`）**：

* **`Σ` 不是 `∑`**。生成器曾发射 `≤ Σ i : Fin 70, …`——`Σ` 是 sigma 类型构造子，于是整条 `calc`
  报 `failed to synthesize instance ...` / `invalid 'calc' step, failed to synthesize Trans instance`。
  这类「实例合成失败」错误十有八九是**项的语法形状**不对，不是真的缺实例。
* **`positivity` 判不了 `M ^ 3 * Vn ^ 2`**：`M`、`Vn` 是 `set` 出来的局部定义，`positivity` 不会去
  展开它们，`0 ≤ M` 要显式给。`by positivity` 在这里失败会表现为 `⊢ 0 ≤ ?m`（元变量）。
* **`ring_nf` 会与 `mul_eq_mul_left_iff` 打架**：4V 块最后一个词化简成
  `M * (Vn * (Vn * (Vn * Vn))) = M * Vn ^ 4` 后，`simp` 默认集里的 `mul_eq_mul_left_iff`
  （`c * a = c * b ↔ a = b ∨ c = 0`，**不需要** `c ≠ 0`）把它化成
  `Vn * (Vn * (Vn * Vn)) = Vn ^ 4 ∨ M = 0`，而 `ring`/`ring_nf`/`tauto`/`simp_all`
  **都收不了这个残局**（`simp` 也不再前进）。可行的收尾是 `ring_nf ;try simp`——注意必须是 `;` 而不是
  `<;>`，否则 `lint-style` 报 `Used tac1 <;> tac2 where (tac1; tac2) would suffice`；而
  `<;> try simp` 在 2V/3V 两块（`ring_nf` 已经收尾）会报 `unusedTactic`。
* **`try simp` 不能写成单独一行**：`tac1 <;> tac2` 之后另起一行写 `simp`，会在 2V/3V 的分支上报
  `No goals to be solved`（那时目标已空）。要用 `;try simp` 接在同一行。
* **`longLine` 由 `lake build` 把关**，不是 `lint-style`：`lakefile` 里
  `weak.linter.mathlibStandardSet = true`，行长上限 100。写生成代码时把每行控制在 100 列内是硬约束
  （`QuinticTaylor2.lean` 里用 `set c`/`set w` 给长名字起局部别名，就是为了这个）。

**与生成器的关系（重要）**：`QuinticTaylor2.lean` 的文件头写着 generated by
`scripts/gen_bch_quintic_taylor2.py`，但**两者已不同步**：生成器发射的 2V/3V profile 行是
`<;> ring_nf`，磁盘上是 `<;> ring_nf ;try simp`（见上一条）。这些 `try simp` 属于手工调优，
**不要为了「重新生成」而跑脚本覆盖文件**；脚本可留作数据来源与忠实性交叉核对。若确实要重新生成，
先把生成器对齐到磁盘版本，再逐行 diff。

**待做**：

* `bchQuinticTermTaylor2Decomp`：`bchQuinticTerm (x + V) y - bchQuinticTerm x y =
  bchQuinticTermLinDiff x V y + bchQuinticTermTaylor2Remainder x V y`。被
  `SymmetricSepticPhaseBC`（`septic_d7_P3_C5_lin_poly_eq_taylor2_remainder`）与
  `SymmetricSepticPieces` 使用，是这两个文件的**硬依赖**。源把它写成
  `unfold … ; simp only […] ; match_scalars <;> ring` 并带 `maxHeartbeats 1024000000`——本项目
  禁止 bump，所以这一步需要先定形状（见 §3.3 的开工前提）。

### 3.3 剩余文件与开工前提

| 源 | 行数 | 目标 | 依赖 |
|---|---|---|---|
| `Basic:4830–8714` 双线性二阶差分 + `QuinticMixed.lean` | 5.5k | `QuinticMixed.lean` | 阶段 2 |
| `SmallSDischarge.lean` | 8.4k | 同名 | 阶段 1 |
| `RemainderBounds.lean` | 8.7k | 同名 | SmallSDischarge |
| `Basic:8715–11459` τ⁶ + `SexticMixed.lean` | 8.3k | `SexticMixed.lean` | 阶段 1 |
| `SepticTaylor.lean` | 23.0k | 同名 | 阶段 1 |
| `SymmetricQuinticCore.lean` | 9.8k | 同名 | RemainderBounds, SepticTaylor |
| `SymmetricSepticPhaseBC.lean` | 9.6k | 同名 | SymmetricQuinticCore |
| `SymmetricSepticPieces.lean` | 11.3k | 同名 | PhaseBC |
| `SymmetricSepticAssembly.lean` | 13.0k | 同名 | Pieces, QuinticMixed, SexticMixed |
| `Palindromic.lean` | 5.5k | 同名 | 阶段 1, SymmetricQuinticCore, ChildsBasis |
| `SuzukiSepticMatch{,Words}.lean` | 1.3k | `SuzukiSepticMatch.lean` | Palindromic |
| `Suzuki5Quintic.lean` | 6.8k | 同名 | Palindromic, SuzukiSepticMatch, ChildsBasis |
| `Basic:11460–18070` τ⁷/τ⁸ + Lipschitz | 6.6k | `BCHHigherOrder.lean` | 阶段 1 |
| `Basic:18071–19314` exp 四至九阶余项 + `quartic_identity` + `norm_bch_quartic_remainder_le` | 1.2k | `BCHHigherOrder.lean` | 阶段 2 |

源共 17 个 `.lean`（`Basic`、`LogSeries`、`ChildsBasis` + 14 个生成件），上表逐条覆盖：`Basic`
按行段拆成若干目标，`SymmetricQuintic.lean`（1.3k 的纯聚合模块）的 42k 行内容已先被源自己拆进
`SymmetricQuinticCore` / `PhaseBC` / `Pieces` / `Assembly`，`SuzukiSepticMatchWords.lean` 并入
`SuzukiSepticMatch`。

**开工前必须先解决两件事：**

1. **生成器**：源 `scripts/` 下约 90 个 Python，生成器与独立 CAS 校验器成对出现
   （`gen_bch_quintic_term_taylor2{,_bound}.py`、`gen_bch_sextic_*`、`gen_bch_septic_*`、
   `gen_bch_octic_*`、`gen_d8_*`），`build_safe.sh` 与 `mem_watchdog.sh` 也在。**待确认的只剩
   发射代码对 4.34 的兼容性**：源大量使用 `match_scalars <;> ring`、`noncomm_ring`、
   `dsimp only` 这类对 Mathlib 内部 simp 集敏感的手法。
2. **构建内存**：源已因单模块峰值 RSS 把 42k 行的 `SymmetricQuintic` 拆成 4 个模块，并用
   `scripts/build_safe.sh` 顺序构建（Lake 5 没有 `-j` 节流）。目标仓库必须预先规划同样的拆分，
   不能等到 OOM。

---

## 4. 仍然适用的设计约定

1. **`bch` 用中心化 `log` 定义，不引入 `logOnePlus`。**
   `bch a b := log (exp a * exp b)`（源写 `logOnePlus (exp a * exp b - 1)`）。这样
   `exp_bch` 就是 `exp_log` 一行，源里手写的 `1 + (y - 1)` 消去不再需要；`log_exp_sub_one`
   的直接形式是 `log (exp a) = a`。**不要**保留 `logOnePlus x := log (1 + x)` 的薄别名
   —— 第二个家，且源的每次使用都能写成 `log (1 + x)` 或 `log y`。
2. **标量接口只有 `ℚ`；`ℝ` 是证明内部的局部实例。**
   `NormedSpace.exp` 与 `FQFP.log` **都不带标量域参数**（两者都是 `ℚ`-级数 + junk 值），
   所以 BCH 层的 statement 只用
   `[NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]`。
   `Logarithm.lean` 的 ODE 论证需要 `NormedAlgebra ℝ 𝔸`，在证明里用
   `have : NormedAlgebra ℝ 𝔸 := normedAlgebraReal 𝔸`（`RealScalar.lean`）临时引入。
   这样假设更弱，且不产生 `unusedSectionVars` 警告。
   **`WordNorm`/`WordExpansion` 的标量域是 `[NormedField 𝕂]`（不是源的 `RCLike 𝕂`）**：
   `RCLike ℚ` 不存在，而 BCH 层的一切都在 `ℚ` 上，`RCLike` binder 会让缩放引理在唯一需要它的
   地方无法使用。`RealScalar.lean` 原有的 `NormedAlgebra.coe_rat_smul`（`(q : ℝ) • a = q • a`）
   已删除：它的 ℝ-smul 被文件内 `attribute [local instance] normedAlgebraReal` 烧死，任何用
   `have/letI` 引入 ℝ-结构的调用点都点不着它。
3. **一个 `𝔸`，一个命名空间。** 全部在 `namespace FQFP.BCH`；源的 `namespace BCH` 不沿用。
   `LieRing.ofAssociativeRing` 用 `attribute [local instance]` 局部打开（与
   `ChildsBasis.lean`、`NestedCommNorm.lean` 一致），且必须在**用到 `⁅·,·⁆` 的 section 内**
   声明，否则不可用。
4. **重复的定义不移植。** 目标库已有的（`TrotterError.norm_exp_le`、
   `ExpNorm.norm_exp_sub_one_le`、`ExpNorm.norm_exp_sub_sum_le`、`RealScalar` 全套）以及源里
   逐字重复的孪生定理，都不再抄一遍——docstring 指向即可。
5. **用 section 边界代替 `omit`/`include 𝕂`。** 目标不许出现 `omit`。（审核后 `WordNorm.lean`
   已按此重写：按所需结构拆 section，12 处 `omit` 全部消失。）
6. **`norm_*_rat` 这类单例辅助不要留。** `‖(4 : ℚ)‖ = 4` 之类的引理只服务一个调用点，直接写
   `by simp [← Rat.norm_cast_real]`（或 `rw [← Rat.norm_cast_real]; norm_num`）即可。曾经有
   `norm_{four,six,twentyFour,sevenTwenty}_rat` 四个引理，已删并原地内联；删的时候记得检查
   `BCHTerms.lean` 之外的调用点（`QuinticRemainder.lean` 里还有四处）。

---

## 5. 技术经验

### 5.1 参数化，而不是按阶展开

源 `LogSeries.lean` 有 9 个 `norm_logOnePlus_*`（1 个不带减项 + 8 个 `sub…sub_le`），是同一个证明
在逐阶上的重复（每个阶还要配一个 `summable_logSeriesTerm_shiftK` 与 `…_eq_tsum`）。目标用**一个**
参数化引理：

```lean
theorem norm_log_one_add_sub_logPartialSum_le (x : 𝔸) (n : ℕ) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - logPartialSum 𝔸 n x‖ ≤ ‖x‖ ^ n * (1 - ‖x‖)⁻¹
```

**索引约定**（踩过坑，别再改）：`logPartialSum 𝔸 n x` 的 `n` 是**第一个被省略的项的次数**，
所以 `n = 0 → 0`、`n = 1 → 0`（常数项系数 `(-1)/0 = 0`）、`n = 2 → x`、`n = 3 → x - x²/2`。
这与 `Summable.sum_add_tsum_nat_add n` 的切分点一致——用别的约定会导致 `rw` 接不上。

**界的形式**：`‖x‖^n * (1-‖x‖)⁻¹`，**不是** `‖x‖^n/(n+1) * (1-‖x‖)⁻¹`。对首项 `cₙ xⁿ`
（系数 `1/n`）有 `1/n ≤ 1/(n+1)` 是**假的**（`n=1` 时 `1 ≤ 1/2`）。

### 5.2 `linarith`/`nlinarith` 的性能：实测数据与两条规则

源的 H1 带 `maxHeartbeats 16000000`、H2 带 `6400000`；目标 AGENTS.md 禁止这类 bump。
用 Lean 自带 profiler 定位过：

```lean
set_option trace.profiler true in
set_option trace.profiler.useHeartbeats true in
set_option trace.profiler.threshold 500 in
private lemma bch_cubic_real_core …
```

**根因不是整条定理慢，而是单个 `linarith` 家族在乘积/三次多项式上炸**：

```
timeout at «Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss.getTableauImp»
  (maximum number of heartbeats 200000 has been reached)
```

**规则 1：纯代数事实用 Mathlib 现成引理，不要交给 `nlinarith` 搜。**

`BCHCommutator.lean` 里最贵的一行是 AM-GM，占整个引理的 **52%**：

```
bch_cubic_real_core                    132,368,707 heartbeats  (改前)
  have ht_le : α * β ≤ s ^ 2 / 4         68,550,095
    nlinarith [sq_nonneg (α - β)]        68,183,145
      nlinarithExtras: 17,543,776 / adding product terms: 16,294,175
```

`nlinarith` 会用**全部局部假设**做「假设两两相乘」的搜索；这个引理的上下文有 ~20 条含
`Real.exp` 原子的假设，每条乘积假设在预处理时又展开成很多单项式。
Mathlib 自带这条 AM-GM（`Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:700`）：

```lean
four_mul_le_sq_add (a b : R) : 4 * a * b ≤ (a + b) ^ 2
```

于是改成纯 `calc` + 一次 `linarith only`，成本降到可忽略：

```lean
have ht_le : α * β ≤ s ^ 2 / 4 := by
  have h : 4 * (α * β) ≤ s ^ 2 := by
    calc 4 * (α * β) = 4 * α * β := by ring
      _ ≤ (α + β) ^ 2 := four_mul_le_sq_add α β
      _ = s ^ 2 := by rw [← hs]
  linarith only [h]
```

**规则 2：必须用 `linarith`/`nlinarith` 时，一律写 `linarith only [...]`。**

`linarith` 默认扫**整个上下文**；在 `Real.exp` 原子 + 乘积假设的环境里，即使只证
`s⁴/2 ≤ s³/2` 也要几百万心跳（预处理要把每条假设 ring-归一化）。

`bch_cubic_real_core` 的改进链：

| 改动 | heartbeats |
|---|---|
| 改前 | 132,368,707 |
| 用 `four_mul_le_sq_add` 取代那行 `nlinarith` | 64,914,331（−51%） |
| `hRB7` 的两个 `linarith` → `linarith only` | 58,834,647（−56%） |
| 全引理 `linarith` → `linarith only [...]` | **32,854,795（−75%）** |

墙钟：`BCHCommutator.lean` ~16s → 13s，`BCHSymmetric.lean` ~10s。
**心跳数的收益远大于墙钟**，因为心跳决定的是「会不会超时/需不需要 bump」。

配套的第三条（结构层面）：把实数算术抽成独立的 `private lemma`
（`bch_cubic_real_core`、`symmetric_bch_real_core`、`symmetric_bch_scale_bounds`），
statement 只含纯实数命题、`𝔸` 不出现；每个估计用显式 `calc` +
`mul_le_mul*`/`add_le_add`/`pow_le_pow_left₀`/`div_le_div_of_nonneg_left`/`div_le_iff₀` 链证，
只把最后的**线性**求和留给 `linarith`。

**`linarith only` 的语义坑**：它**完全不用**局部上下文（也不自动补 `sq_nonneg`）。
所以「`Real.add_one_le_exp s : 1 + s ≤ eˢ` 推出 `1 ≤ eˢ`」必须写成
`linarith only [Real.add_one_le_exp s, hs_nn]`——漏了 `hs_nn : 0 ≤ s` 就失败。

### 5.3 其他坑一览

- **`have` 而不是 `haveI`**：`linter.style.haveILetI` 要求 Prop 目标下用 `have`；Lean 4 的
  `have : C := …`（`C` 是 class）确实会注册为局部实例。
- **`set x := e with hx` 的 `hx : x = e`**：`rw [hx]` 把 `x` 展成 `e`；`rw [← hx]` 是反方向。
  写反了**不报错**，只是静默不生效，随后 `exact` 失败、显示原始目标——很容易误判。
  `α`、`β`、`s` 这类透明局部定义通常**不需要 rw**，靠 defeq 就能 `exact` 匹配。
- **强制转换的 elaborate 陷阱**：`((k + n : ℕ) : ℚ)` 在期望类型为 `ℚ` 时会 elaborate 成
  `↑k + ↑n`（cast 插在每个变量上），与库引理里的 `↑(k+n)` 不是同一个项，`rw` 匹配不上。
  解法是引入 `logCoeff : ℕ → ℚ`，让索引始终以 **ℕ** 传给函数，整类问题消失。
- **`norm_pow` 需要 `‖1‖ = 1`**（`NormOneClass`）；裸 `NormedRing` 只有 `norm_pow_le'`
  （要求 `0 < n`），零情形要单独处理。
- **`‖(2 : ℚ)‖`/`‖(2 : ℚ)⁻¹‖` 的 `norm_num` 无效**（报 `‖2‖ = 2` 未解决）：要
  `rw [← Rat.norm_cast_real]; norm_num`（或 `simp [← Rat.norm_cast_real]`）。
- **`Real.norm_exp_sub_one_sub_id_le`** 在 `Mathlib/Analysis/Complex/Exponential.lean:456`，
  是 `_root_.Real.…`（由 ℂ 版 `exact_mod_cast` 得到）；配合 `Real.norm_eq_abs` +
  `abs_of_nonneg` 使用。
- **`real_exp_third_order_le_cube` 的 `5/6` 阈值是数值上方便的**，不是最尖锐的；
  `s < log 2` 先转成 `s < 5/6`（证明：`2 ≤ 1 + 5/6 + (5/6)²/2 ≤ exp(5/6)`）。
- **`Real.exp_add` 的方向**：`exp (x+y) = exp x * exp y`，要把 `exp α * exp β` 变成
  `exp s` 得用 `←`；且 `rw` 不会自动展开 `(exp α - 1) * (exp β - 1)`，需要先写一个 `ring`
  恒等式把它化成 `exp α * exp β - …`。
- **写文件**：拆分/生成文件时 `WriteAllLines` 会写 CRLF，`lint-style` 报错；用 .NET
  `UTF8Encoding($false)` 且手动把 `\r\n` 换成 `\n`（`lake exe lint-style --fix` 对行尾**无效**）。
  **不要用 `Set-Content`/`Get-Content -Raw` 改 Lean 文件**（破坏 UTF-8 的 `‖` 等字符）；
  用 `[System.IO.File]::ReadAllLines/WriteAllLines` 或 `edit` 工具。
- **`simp only` 会关掉 simp 的默认集，遇到字面量要当心**（见 §3.2，复现见
  `artifacts/examples/vec-cons-simplification.lean`）：向量字面量 `![-1, 4, -6, 4, -1]`
  上的 `get`，靠的是默认集里的 `Matrix.cons_val_zero` / `Matrix.cons_val_succ`。所以
  `simp only [<数据 def>]` 化简不动它（残局 `⊢ ↑(![-1, …] 0) = -1`），而 `simp [<数据 def>]`
  一条过。要保留 `simp only` 就显式补 `Matrix.cons_val_zero/succ`（`simp?` 会给出完整清单），
  或者干脆换 `List`（`List.getElem_cons_*` 是真 simp 引理）。写生成代码时这是个反复踩的点：
  **发射 `simp only` 之前先确认它在完整 `simp` 下成立**，否则会得到「展开后没人收尾」的残局。
- **`decide` 不能判 `ℝ` 命题**：`Real.decidableLE` 经 `Classical.choice` 定义，`decide` 展开后
  卡在 `Classical.choice` 上（报错会明说）。`decide` 只对 `ℕ`/`ℤ`/`ℚ`/`Bool`/`List` 上的
  可计算目标可靠，例如「词表里 `a`-位置的总数 = 10」。
- **`Rat.norm_cast_real` 只认 `ℚ`**：形状是 `‖(↑q : ℝ)‖ = ‖q‖`（`q : ℚ`）。`ℤ` 经 `Int.cast`
  直接进 `ℝ` 的话（`‖↑↑z‖`）这条套不上，要先降到 `ℚ`。
- **`List.getElem` 的界证明会进目标**：`getElem w ⟨i, by decide⟩` 化简后会露出
  `decide (2 < w.length)`，与已展开的 `true` 对不上，`simp only` 报
  `Application type mismatch ... @Eq Bool (decide (2 < w.length)) true`。索引改用
  `match` 式访问函数或 `nameWords[i.val]'(…)` 形式即可。

---

## 6. 仓库状态与待办

- **工作树的改动**（本次会话）：
  - `FQFP/BCH/BCHTerms.lean`：删掉 `norm_{four,six,twentyFour,sevenTwenty}_rat` 与两个不再需要的
    import，调用点改用 `simp [← Rat.norm_cast_real]`（见 §4.6）。
  - `FQFP/BCH/QuinticRemainder.lean`：上面那次删除留下的四处悬空调用（`norm_four_rat`、
    `norm_six_rat`、`norm_twentyFour_rat`、`norm_sevenTwenty_rat`）已按同一写法内联修好。
  - `FQFP/BCH/QuinticTaylor2.lean`：taylor2 一线从「只有数据、缺界」推到「定义 + 四条范数界」，
    见 §3.2；`bchQuinticTermTaylor2Decomp` 仍缺。
  - `scripts/gen_bch_quintic_taylor2.py`：与磁盘文件**已不同步**（2V/3V 的 profile 行差
    `;try simp`），保留作数据来源与交叉核对，不要直接跑它覆盖文件（见 §3.2 末）。
  - `artifacts/examples/`：新增几个可运行的勘察脚本（`taylor2-*.lean`、`vec-cons-simplification.lean`）。
  - `artifacts/bch-audit-round-one/` 下的两个比对脚本已从工作树删除；其中的结论（词表 MATCH、
    常数对齐）已收进本文。
- **`.lake` 构建残留已清理**：原先有 `FQFP/BCH/LogOnePlus`、`FQFP/BCH/ScratchProbe`、
  `FQFP/NormedSpace/LogOnePlus`、`FQFP/Spike/*` 等已删除模块的陈旧 olean（上一轮失败尝试的
  痕迹）。现在 `FQFP/` 下每个 `.lean` 都有对应 olean、每个 olean 都有对应 `.lean`，双向核对为空。

- **`Logarithm.lean` 的上游命运**：该文件的代数半部分与 `NormedSpace.log`
  （[mathlib4#43670](https://github.com/leanprover-community/mathlib4/pull/43670)）重复，pin 一过
  就应删除。已核实目标 checkout 是 `v4.34.0`（`5ed2965256`，2026-09-15），全树搜索 `logSeries`
  **零命中**，`Mathlib/**/Logarithm*.lean` **不存在**——即该 PR 尚未进入目标 pin，
  `FQFP/BCH/Logarithm.lean` 仍是必需的本地实现。下次 Mathlib bump 时做机械替换：删 vendored
  代数层 + 改名 `FQFP.log → NormedSpace.log`。
- **版本漂移**：源在 Lean 4.29.0-rc8，目标 v4.34.0。阶段 1/2 的手写移植顺利（漂移可控），但
  生成代码大量使用 `match_scalars <;> ring`、`noncomm_ring`、`dsimp only` 这类对 Mathlib 内部
  simp 集敏感的手法（源 `CLAUDE.md` 记了 7 条此类技巧）。**生成代码的移植成本很可能远高于它的
  行数比例。**
- 每次提交前的验收（顺序不可省）：

  ```
  lake exe cache get
  lake build FQFP
  lake exe runLinter
  lake exe lint-style
  ```

  **注意工具链的覆盖范围**：`lake exe runLinter` 是 **Batteries 的驱动**
  （`mathlib/lakefile.lean` 的 `lintDriver := "batteries/runLinter"`，其 `opts := {}`），
  **不打开** `linter.mathlibStandardSet`；`lake exe lint-style` 只跑 4 个 TextBased linter
  （不含行长）。真正会让 `longLine`/`maxHeartbeats`/`emptyLine`/`header` 等 Mathlib 标准集
  生效的是 **`lake build`**（lakefile 的 `[leanOptions] weak.linter.mathlibStandardSet = true`）。
  单文件复核可用 `lake env lean "-Dlinter.mathlibStandardSet=true" FQFP\BCH\X.lean`。
