# BCH 移植：计划、进度与经验

把 `D:\project\Lean-BCH\BCH`（源，17 个文件 ≈ 108k 行，Lean 4.29.0-rc8）移植进
`D:\project\CQM1\FQFP\BCH`（目标，Lean 4.34.0 / Mathlib v4.34.0），**重写架构与代码风格**，
而不只是搬运。

**当前状态：阶段 1（BCH 核心）、阶段 2（三次/四次/五次项）、阶段 3 的五次项
（含 `bchQuinticTermTaylor2Decomp`，见 §3.2）全部完成。** 验收全绿：`lake build FQFP`（零警告）、
`lake exe runLinter`、`lake exe lint-style`；零 `sorry`、零自定义公理、零 `maxHeartbeats` bump，
`#print axioms` 只剩 `[propext, Classical.choice, Quot.sound]`。

**下一步就看 §3.3 那张表**：`SmallSDischarge.lean`（8.4k 行）是全表唯一只依赖阶段 1、可以立刻
开工的大块；`bchQuinticTermTaylor2Decomp` 完成后，`QuinticMixed` / `SexticMixed` /
`SymmetricSeptic*` 整条链（约 57k 行）的前置已解除。

---

## 1. 目标文件布局

按**数学陈述**分层，不按源文件分层。行数为当前工作树实测值。

| 文件 | 行数 | 主题 |
|---|---|---|
| `Logarithm.lean` | 1021 | Banach 代数对数；`log (1+·)` 的余项界 |
| `ExpNorm.lean` | 227 | 指数估计：实数与范数代数的 Taylor 余项界 |
| `RealScalar.lean` | 82 | 完备 `ℚ`-代数上的唯一 `ℝ`-代数结构 |
| `WordNorm.lean` | 178 | 词乘积范数（arity-free） |
| `WordExpansion.lean` | 396 | 词展开：二元词模式界、telescoping `_diff` 界、任意字母表词积、顺序保持的子集展开 |
| `NestedCommNorm.lean` | 88 | 嵌套交换子范数 |
| `ChildsBasis.lean` | 163 | Childs 四重交换子基 |
| `BCHElement.lean` | 283 | **结构层**：`bch` 是什么 |
| `BCHCommutator.lean` | 557 | **偏差层**：`bch` 与 `a+b` 差多少 |
| `BCHSymmetric.lean` | 303 | **对称层**：Strang 乘积的误差 |
| `BCHTerms.lean` | 981 | **级数项层**：`bch` 展开的三次/四/五/六/七/八次项及其范数界 |
| `QuinticRemainder.lean` | 224 | 五次项的一阶 Lipschitz 界 |
| `QuinticTaylor2.lean` | 282+ | 五次项 taylor2：**四组 × 子集** 的片段定义、`Decomp`、四条范数界 |

依赖链：`Logarithm/ExpNorm → BCHElement → BCHCommutator → BCHSymmetric`；
`WordNorm → WordExpansion → BCHTerms → QuinticRemainder / QuinticTaylor2`。
阶段 1 拆三个文件是因为 H2 会把 `BCHElement.lean` 推到 1000+ 行，而三者的主题
（「`bch` 是什么」/「差多少」/「对称乘积的误差」）边界清楚。

---

## 2. 源↔目标对照（只列不直观的）

| 源 | 目标 | 备注 |
|---|---|---|
| `LogSeries.lean` 全部 + `Basic:326` | `Logarithm.lean` | 重定中心到 `1`，去掉定义中的范数；**不移植**三个 `Complex.log` 互操作引理 |
| 9 个 `norm_logOnePlus_*` | `norm_log_one_add_sub_logPartialSum_le` | **参数化成一个**（见 §5.1） |
| 23 个按 arity 展开的词范数引理 | `List.norm_prod_le` + `norm_prod_le_ofFn` | arity-free 重写 |
| `Basic:612` **H1** `10s³/(2-eˢ)` | `BCHCommutator.lean` | 源带 `maxHeartbeats 16000000`，目标**无 bump** |
| `Basic:1061` **H2** `300s³` | `BCHSymmetric.lean` | 源带 `6400000`，目标**无 bump** |
| `Basic:1397–1770` 三次/四次项族 | `BCHTerms.lean` | def 改名 `bchCubicTerm` / `bchQuarticTerm`（见 §2.2） |
| `Basic:1772–2118` 五次项族（4 组 + 项 + 界） | `BCHTerms.lean` | 组改为词模式数据（见 §3.1） |
| `Basic:2120–3027` 五次组 `_diff_le` | `QuinticRemainder.lean` | `_LQ_decomp` 推迟（见 §3.1） |
| `Basic:3028–4830` taylor2 | `QuinticTaylor2.lean` | 见 §3.2 |
| `norm_bch_sub_add_le'` | **不移植** | 与二次界逐字相同 |
| 源里逐字重复的孪生定理、目标已有的（`TrotterError.norm_exp_le` 等） | **不移植** | docstring 指向即可 |

### 2.1 各文件的核心公开声明（改名前先看这里）

- `Logarithm.lean`：`logCoeff`、`norm_logCoeff_le_one`、`logPartialSum`、
  `norm_log_one_add_sub_logPartialSum_le`（主引理）、`norm_log_one_add{,_sub,_sub_add_sq,_sub_add_sq_sub_cube}_le`、
  `logPartialSum_{zero,one,two,three,four}`、`exp_log{,_one_add}`。
- `ExpNorm.lean`：`real_exp_third_order_le_{div,cube}`、`norm_exp_sub_one_sub_id{,_sub_sq}_le`。
- `BCHElement.lean`：`bch`、`exp_bch`、`log_exp_sub_one`、`continuousOn_log_one_add`、
  `norm_exp{_mul_exp}_sub_one_lt_one`、`exp_eq_one_of_norm_lt`。
- `BCHCommutator.lean`：`norm_bch_sub_add_le`、`norm_bch_sub_add_sub_bracket_le`（H1）、
  `lie_eq_commutator`、`norm_bch_sub_add_sub_lie_le`。
- `BCHSymmetric.lean`：`norm_symmetric_bch_sub_add_le`（H2）。
- `BCHTerms.lean`：三次 `bchCubicTerm` + `_smul` / `norm_*_le` / `_diff_le` / `_LQ_decomp`；
  四次同构；五次 `bchQuinticGroup{1,4,6,24}Words`、`bchQuinticGroup{1,4,6,24}`、`bchQuinticTerm`
  及其 `_smul` / `norm_*_le`。跨层复用的范数辅助：`norm_mul_sub_mul_le`、
  `norm_double_commutator_le`、`norm_mul_w_mul_le`、`norm_w_mul_mul_le`、`norm_mul_mul_w_le`、
  `norm_word5_le`。
- `WordExpansion.lean`：二元侧 `wordEval`、`norm_wordEval_le`、`norm_sum{_smul}_wordEval_le`、
  `wordEval_smul`、`sum_wordEval_smul`、`norm_prod_sub_prod_le`、`norm_wordEval_sub_le`、
  `norm_sum_wordEval_diff_le`；任意字母表侧 `wordProdList`、`norm_wordProdList_le`、
  `norm_sum_smul_wordProdList_le`、`smul_wordProdList`。
- `QuinticRemainder.lean`：`norm_bchQuinticGroup{1,4,6,24}_diff_le`（常数 10/25/35/5）、
  `norm_bchQuinticTerm_diff_le`（常数 1）。

### 2.2 两条命名/接口约定（阶段 3 沿用）

1. **`def` 名必须 lowerCamelCase。** `defsWithUnderscore` linter 只查 `def`，`theorem` 不受限——
   所以 `bch_cubic_term` 要改成 `bchCubicTerm`，而定理名保留源的 `bchCubicTerm_smul`、
   `norm_bchCubicTerm_le`（Mathlib 先例：`Complex.normSq` / `normSq_apply`）。
2. **`unusedSectionVars` 靠显式 binder，不用 `omit`**（本项目禁止 `omit`）。五次项四个组只需要
   `NormedRing 𝔸`，却位于 `NormedAlgebra ℚ 𝔸` 的 section 内，于是用
   `{𝔸 : Type*} [NormedRing 𝔸]` 显式遮蔽 section 变量。

---

## 3. 阶段 3：机器生成层（95k 行）

### 3.1 已完成：arity-free 词 API

**这是把 95k 行压下来的最大杠杆，且必须在生成器层面做，事后手改不可行。** 生成代码里每个
monomial 分支都重复 `norm_smul_le → norm_Nprod_le → gcongr → ring`，全部换成对 `WordNorm` /
`WordExpansion` 的单次调用：五次项四个组的范数界从 180 行变成每行
`simpa [bchQuinticGroupN] using norm_sum_wordEval_le bchQuinticGroupNWords a b`。

**代价**：`_diff_le` 需要 `NormOneClass 𝔸`（源用 `omit` 去掉了），因为 telescoping 原语经
`norm_word_le` 归结到 `‖1‖ = 1`；BCH 层本来就带 `NormOneClass`。

**`_LQ_decomp` 有意推迟**：源写成逐项展开的显式非交换多项式恒等式（组 1：32 项，组 6：76 项且带
`maxHeartbeats 3200000`），只能由 `noncomm_ring` 证。只有 `SymmetricSepticPhaseBC` /
`SymmetricSepticPieces` 用它。届时先定形状：**逐组显式展开**（忠实于源，但组 6 有心跳问题），
还是**按词模式做 W-次数分解**（可能免 bump，需先看消费者要点什么）。

### 3.2 五次项 taylor2：`bchQuinticTermTaylor2Decomp` 已完成

```lean
bchQuinticTerm (x + V) y - bchQuinticTerm x y
  = bchQuinticTermLinDiff x V y + bchQuinticTermTaylor2Remainder x V y
```

它是 `SymmetricSepticPhaseBC`（`septic_d7_P3_C5_lin_poly_eq_taylor2_remainder`）与
`SymmetricSepticPieces` 的**硬依赖**。源写成 `unfold … ; simp only […] ; match_scalars <;> ring`
并带 `maxHeartbeats 1024000000`。

**难点与方案见 `artifacts/quintic-taylor2-route.md`（必读）。** 一句话：
`Finset.prod_add` 及其全部同族引理只对 `CommSemiring` 成立，右端**重排了字母**，在非交换环上
是错的；BCH 的 `𝔸` 必须非交换，所以「按子集展开再重排系数」这条路数学上不成立（曾提交的
`FQFP/BCH/QuinticExpansion.lean` 带 `[CommRing 𝔸]`，因此无法调用，已删）。正确形态是**按 snoc
归纳、保持字母顺序**的展开：`WordExpansion.wordProdList_add`，在
`artifacts/examples/quintic-expansion-spike.lean` 中先验证过、随后搬进 `WordExpansion.lean`（`[Semiring 𝔸]`，无
`omega`/`sorry`，axioms 只剩三条）。

**最终形态（终版，别再改）**：`BCHTerms.lean` 的四组 `Fin 5 → Bool` 词表**原样保留**，
`QuinticTaylor2.lean` 的片段定义为「四组 × 该词 `a`-位置的 `k`-子集」的嵌套和：

* `bchQuinticGroupSubsets words k x V y`：一组内所有词的 `powersetCard k` 之和；
* `bchQuinticSubsetPiece k x V y`：`(720)⁻¹ • bchQuinticBracket (四组分别在 k 处的和)`，
  `bchQuinticBracket v1 v4 v6 v24 = -v1 + 4•v4 - 6•v6 + 24•v24` 逐字镜像 `bchQuinticTerm` 内层；
* `LinDiff = piece 1`，`Remainder{2V,3V,4V} = piece 2/3/4`，`Remainder = 2V+3V+4V`（`rfl`）。

不再有 `Fin 75/70/30/5` 的平坦字面量表，也不再有 `bchWordSum`：片段是**从
`bchQuinticTerm` 经已证明的 `wordProdList_add` 推导出来的**，所以不存在转写错误，
也不需要「逐项核对 180 个词」。

**只需两条引理**：

* `sum_powerset_eq_sum_powersetCard`：`card ≤ 4` 时
  `∑ t ∈ s.powerset, f t = ∑ k ∈ range 5, ∑ t ∈ s.powersetCard k, f t`；
* `bracket_sum`：`bracket (∑A) (∑B) (∑C) (∑D) = ∑ k, bracket (A k) (B k) (C k) (D k)`。

**四条范数界（`1680/720`、`720/720`、`30/720`，合计 `2430/720`）**：词形统一（`k` 个 `V`、
`5-k` 个来自 `{x,y}`），所以 `norm_wordProdList_le` + 字母界 `![M, Vn, M]` 直接给
`M^(5-k)·Vn^k`，再用 `Vn ≤ M` 松到 `M³·Vn²`——**没有 `fin_cases`**。词数 12 个数
（k=2 时 12/24/30/4，k=3 时 8/11/10/1，k=4 时 2/2/1/0）由 `decide` 算出。

**独立校验器**（`scripts/check_quintic_taylor2_pieces.py`）：不读片段定义，从 `BCHTerms.lean`
解析四组词表、从 `git show HEAD:FQFP/BCH/QuinticTaylor2.lean` 解析旧表，自己枚举
「每个词 × `a`-位置的每个非空 `k`-子集」重建四个片段并逐 `(词, 系数)` 比对。结果全绿
（75/70/30/5，共 180 项）。用法见脚本 docstring。

### 3.3 剩余文件与开工前提

| 源 | 行数 | 目标 | 依赖 |
|---|---|---|---|
| `SmallSDischarge.lean` | 8.4k | 同名 | **阶段 1/2 + 六/七/八次项前置（见下，已完成）** |
| `Basic:4830–8714` + `QuinticMixed.lean` | 5.5k | `QuinticMixed.lean` | taylor2 `Decomp` |
| `Basic:8715–11459` + `SexticMixed.lean` | 8.3k | `SexticMixed.lean` | 阶段 1 |
| `SepticTaylor.lean` | 23.0k | 同名 | 阶段 1 |
| `RemainderBounds.lean` | 8.7k | 同名 | SmallSDischarge |
| `SymmetricQuinticCore.lean` | 9.8k | 同名 | RemainderBounds, SepticTaylor |
| `SymmetricSepticPhaseBC.lean` | 9.6k | 同名 | SymmetricQuinticCore |
| `SymmetricSepticPieces.lean` | 11.3k | 同名 | PhaseBC |
| `SymmetricSepticAssembly.lean` | 13.0k | 同名 | Pieces, QuinticMixed, SexticMixed |
| `Palindromic.lean` | 5.5k | 同名 | 阶段 1, SymmetricQuinticCore, ChildsBasis |
| `SuzukiSepticMatch{,Words}.lean` | 1.3k | `SuzukiSepticMatch.lean` | Palindromic |
| `Suzuki5Quintic.lean` | 6.8k | 同名 | Palindromic, SuzukiSepticMatch, ChildsBasis |
| `Basic:11460–18070` τ⁷/τ⁸ + Lipschitz | 6.6k | `BCHHigherOrder.lean` | 阶段 1 |
| `Basic:18071–19314` 四至九阶余项 + `quartic_identity` | 1.2k | `BCHHigherOrder.lean` | 阶段 2 |

（`SymmetricQuintic.lean` 是 1.3k 的纯聚合模块，其 42k 行内容源自己已拆进
`SymmetricQuinticCore` / `PhaseBC` / `Pieces` / `Assembly`；`SuzukiSepticMatchWords.lean` 并入
`SuzukiSepticMatch`。）

### 3.3bis `SmallSDischarge.lean` 的真实依赖与难度（本轮实测，修正上表上一版的说法）

上一版把它标成「只依赖阶段 1、可立刻开工」——**不对**。实测（`Select-String` 计数）：

* 它用了 `bch_sextic_term`（20 处）、`bch_septic_term`（13 处）、`bch_octic_term`（4 处），
  三者的定义分别在 `Basic.lean:8732 / 11478 / 14221`，即上表映射到 `SexticMixed.lean` 与
  `BCHHigherOrder.lean` 的两段**尚未移植**的区域。所以开工前有一层约 300 行的前置：
  三个 k 次项的词表 + 各自的范数界（`norm_bch_*_term_le`，分别在 Basic:8822 / 12437 / 15162）。
  **好消息**：三个定义都很小（34 / 134 / 130 行；28 / 126 / 124 个单项式，分母 1440），
  范数界就是 `norm_sum_wordEval_le` / `norm_sum_smul_wordProdList_le` 的一次应用——正是阶段 1/2
  已有的形态。
* **难点集中且形状已知**：29 处 `maxHeartbeats`，其中最狠的四处是
  `pieceB_sextic_decomp` 1.0e9、`pieceB_septic_decomp` 2.0e9、`pieceB_octic_decomp` 8.2e9、
  `norm_I2_residual_inner_le` 1.0e9——全是**非交换多项式恒等式**，与刚做完的
  `bchQuinticTermTaylor2Decomp` 同型，正好是本轮新增的 `wordProdList_add` + 子集索引能处理的
  东西。其余 25 处是 4e6–1.3e8 的伸缩/分解引理。
* 另有 18 处 `omit`（本项目禁止）、17 处 `match_scalars`、48 处 `noncomm_ring`，以及全程
  `RCLike 𝕂`（目标约定是陈述用 `ℚ`、`ℝ` 只在证明里局部引入，见 §4.2）。**8.4k 行不能按行数
  线性外推。**

建议的分片顺序（每片独立可验收）：
**P0** 六/七/八次项前置（**已完成**：`bchSexticTerm` / `bchSepticTerm` / `bchOcticTerm` + `norm_bch*Term_le`，28/126/124 项，分母 1440/30240/120960，见 `BCHTerms.lean`；生成+校验器 `scripts/gen_bch_higher_terms.py`）→ **P1** 纯恒等式 `{quintic,sextic,septic,octic,nonic}_pure_identity`
（源自己已有 `_cleared` 的整数放大版本，正好用来拆小 `noncomm_ring` 目标）→
**P2** 伸缩与 `I1/I2` 残差分解 → **P3** `pieceB_*_decomp`（1e9–8e9 那四处）→
**P4** `norm_bch_{sextic,septic,octic}_remainder_le`。

**开工前提（两件硬约束）**：

1. **生成代码的兼容性**：源 `scripts/` 下约 90 个 Python（生成器 + 独立 CAS 校验器成对）。
   生成代码大量用 `match_scalars <;> ring`、`noncomm_ring`、`dsimp only` 这类对 Mathlib 内部
   simp 集敏感的手法（源 `CLAUDE.md` 记了 7 条）。**生成件的移植成本很可能远高于它的行数比例**，
   评估工期时不要按行数线性外推。
2. **构建内存**：源已因单模块峰值 RSS 把 42k 行的 `SymmetricQuintic` 拆成 4 个模块，并用
   `build_safe.sh` 顺序构建（Lake 5 没有 `-j` 节流）。目标仓库必须**预先**规划同样的拆分，
   不要等到 OOM。

---

## 4. 设计约定（改代码前必读）

1. **`bch` 用中心化 `log` 定义，不引入 `logOnePlus`。** `bch a b := log (exp a * exp b)`
   （源写 `logOnePlus (exp a * exp b - 1)`）。于是 `exp_bch` 就是 `exp_log` 一行。
   不要保留 `logOnePlus x := log (1 + x)` 的薄别名——第二个家。
2. **标量接口只有 `ℚ`；`ℝ` 是证明内部的局部实例。** BCH 层 statement 只用
   `[NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]`；`Logarithm.lean`
   的 ODE 论证需要 `NormedAlgebra ℝ 𝔸`，在证明里用
   `have : NormedAlgebra ℝ 𝔸 := normedAlgebraReal 𝔸`（`RealScalar.lean`）临时引入。
   **`WordNorm`/`WordExpansion` 的标量域是 `[NormedField 𝕂]`，不是源的 `RCLike 𝕂`**：
   `RCLike ℚ` 不存在，`RCLike` binder 会让缩放引理在唯一需要它的地方无法使用。
3. **一个 `𝔸`，一个命名空间。** 全部在 `namespace FQFP.BCH`。`LieRing.ofAssociativeRing` 用
   `attribute [local instance]` 局部打开，且必须在**用到 `⁅·,·⁆` 的 section 内**声明。
4. **用 section 边界代替 `omit`/`include`**（禁止 `omit`）。`WordNorm.lean` 已按此重写，
   12 处 `omit` 全部消失。
5. **`norm_*_rat` 这类单例辅助不要留。** `‖(4 : ℚ)‖ = 4` 直接写
   `by simp [← Rat.norm_cast_real]`。曾经的 `norm_{four,six,twentyFour,sevenTwenty}_rat`
   四个引理已删并原地内联。

---

## 5. 技术经验

### 5.1 参数化，而不是按阶展开

源 `LogSeries.lean` 的 9 个 `norm_logOnePlus_*` 是同一个证明在逐阶上的重复（每阶还要配一个
`summable_logSeriesTerm_shiftK` 与 `…_eq_tsum`）。目标用**一个**参数化引理：

```lean
theorem norm_log_one_add_sub_logPartialSum_le (x : 𝔸) (n : ℕ) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - logPartialSum 𝔸 n x‖ ≤ ‖x‖ ^ n * (1 - ‖x‖)⁻¹
```

**索引约定**（踩过坑，别再改）：`n` 是**第一个被省略的项的次数**，所以 `n = 0 → 0`、
`n = 1 → 0`、`n = 2 → x`、`n = 3 → x - x²/2`。这与 `Summable.sum_add_tsum_nat_add n` 的切分点一致，
换别的约定 `rw` 就接不上。

**界的形式**是 `‖x‖^n * (1-‖x‖)⁻¹`，**不是** `‖x‖^n/(n+1) * (1-‖x‖)⁻¹`：对首项系数 `1/n`，
`1/n ≤ 1/(n+1)` 是假的。

### 5.2 `linarith`/`nlinarith` 的性能：两条规则

源的 H1/H2 各带一个巨大的 `maxHeartbeats`；AGENTS.md 禁止 bump，用 profiler 定位到根因：
**不是整条定理慢，而是单个 `linarith` 家族在乘积/三次多项式上炸**
（`SimplexAlgorithm.Gauss.getTableauImp` 超时），因为它会用**全部局部假设**做两两相乘的搜索，
而 BCH 的上下文有 ~20 条含 `Real.exp` 原子的假设。

* **规则 1：纯代数事实用 Mathlib 现成引理，不要交给 `nlinarith` 搜。** AM-GM 用
  `four_mul_le_sq_add`（`Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean`），改前那一行占整个
  引理 **52%** 的心跳。
* **规则 2：必须用时一律写 `linarith only [...]`。** 它**完全不用**局部上下文、也不自动补
  `sq_nonneg`，所以「`Real.add_one_le_exp s` 推出 `1 ≤ eˢ`」必须写
  `linarith only [Real.add_one_le_exp s, hs_nn]`——漏了 `hs_nn` 就失败。

改动链（`bch_cubic_real_core`）：132M → 用 `four_mul_le_sq_add` → 65M → 关键 `linarith` 换
`linarith only` → 59M → 全引理 `linarith only` → **33M**。配套的结构手段：把实数算术抽成只含纯实数
命题的 `private lemma`，`𝔸` 不出现；每个估计用显式 `calc` 链，只把最后的线性求和留给 `linarith`。

### 5.3 其它会反复踩的坑

* **`Σ` 不是 `∑`。** `Σ i : Fin 70, …` 是 sigma 类型构造子，会让整条 `calc` 报
  `failed to synthesize instance` / `invalid 'calc' step, failed to synthesize Trans instance`。
  这类错误十有八九是**项的语法形状**不对，不是真缺实例。
* **`positivity` 判不了 `set` 出来的局部定义**：`0 ≤ M`（`M := ‖x‖+‖V‖+‖y‖`）要显式给；
  失败表现为 `⊢ 0 ≤ ?m`。
* **`simp` 默认集里的 `mul_eq_mul_left_iff`**（`c * a = c * b ↔ a = b ∨ c = 0`，**不需要**
  `c ≠ 0`）会把 `M * _ = M * _` 化成析取式，`ring` / `ring_nf` / `tauto` / `simp_all` 都收不了。
  可行的收尾是 `ring_nf ;try simp`——必须是 `;` 不是 `<;>`（否则 `lint-style` 报
  `Used tac1 <;> tac2 where (tac1; tac2) would suffice`），也不能把 `simp` 另起一行
  （已收敛的分支会报 `No goals to be solved`）。
* **`longLine` 由 `lake build` 把关**，不是 `lint-style`（`weak.linter.mathlibStandardSet`，
  上限 100 列）。长名字的定理里用 `set c` / `set w` 起局部别名就是为了这个。
* **`simp only` 会关掉 simp 的默认集，遇到字面量要当心**：向量字面量 `![-1, 4, -6, 4, -1]` 上的 `get`
  靠默认集里的 `Matrix.cons_val_zero` / `Matrix.cons_val_succ`，所以 `simp only [<数据 def>]` 化简
  不动它（残局 `⊢ ↑(![-1, …] 0) = -1`），而 `simp [<数据 def>]` 一条过。
* **`Rat.norm_cast_real` 只认 `ℚ`**（形状 `‖(↑q : ℝ)‖ = ‖q‖`）。`ℤ` 经 `Int.cast` 直接进 `ℝ` 套不上。
* **`decide` 不能判 `ℝ` 命题**（`Real.decidableLE` 经 `Classical.choice`，展开后卡住）。
  **而且它同样判不了 `ℚ`**（上一版这里写的「`ℚ` 可靠」是错的，P0 实测纠正）：
  `Rat.instDecidableLe` 落在 `Rat.blt` 上，而 `Rat.blt` / `Rat.num` / `Rat.den` 都不做
  kernel 归约，所以连 `example : (1:ℚ)/2 ≤ 3/4 := by decide` 都失败，形如
  `∀ i : Fin 126, (c i).num.natAbs ≤ 216` 的 `ℕ` 命题也同样卡在 `(c i).num` 上。
  **`decide` 只对不含 `ℚ`/`ℝ` 的可计算目标可靠**（`ℕ`/`ℤ`/`Bool`/`List`，以及
  `Finset.card` 这类计数式）。含 `ℚ` 的数值事实一律交给 `norm_num`。
* **`norm_num` 不能求 `∑ i : Fin m, f i` 的和**（`f` 是向量字面量时它把 `f` 展成字面量、
  却留下未化简的 `∑`）。要显式展开：`simp only [<表 def>, Fin.sum_univ_succ,
  Fin.sum_univ_zero, ← Rat.norm_cast_real, Real.norm_eq_abs]` 再 `norm_num`；`←
  Rat.norm_cast_real` 这一条不能省，否则残局是 `‖1440‖⁻¹ + … ≤ 1`。
  **但 126/124 项的展开会超过 `simp` 默认的 `maxRecDepth`**（报错是
  `maximum recursion depth has been reached`，不是心跳超时）。`BCHTerms.lean` 的
  `norm_bchSepticTerm_le` / `norm_bchOcticTerm_le` 因此带一条
  `set_option maxRecDepth 8000 in`——这是**有限的 tactic 递归深度**，不是搜索/心跳预算，
  且已在原处写明理由。若要彻底去掉它，就得把系数表按「系数值分组」（像五次项的四个组那样）
  而不是「平坦表 + 系数向量」；代价是约 30 个额外的组定义。
* **`List.getElem` 的界证明会进目标**：`getElem w ⟨i, by decide⟩` 化简后露出
  `decide (2 < w.length)`，与已展开的 `true` 对不上。索引用 `nameWords[i.val]'(…)` 形式绕开。
* **`have` 而不是 `haveI`**：`linter.style.haveILetI` 要求 Prop 目标下用 `have`。
* **写文件**：`WriteAllLines` 会写 CRLF，`lint-style` 报错；用 .NET `UTF8Encoding($false)` 并手动把
  `\r\n` 换成 `\n`（`lake exe lint-style --fix` 对行尾无效）。**不要用
  `Set-Content`/`Get-Content -Raw` 改 Lean 文件**（破坏 UTF-8 的 `‖`）。

---

## 6. 仓库状态与验收

- 每次提交前的验收（顺序不可省）：

  ```
  lake exe cache get
  lake build FQFP
  lake exe runLinter
  lake exe lint-style
  ```

  **工具链的覆盖范围容易误判**：`lake exe runLinter` 是 Batteries 的驱动，**不打开**
  `linter.mathlibStandardSet`；`lake exe lint-style` 只跑 4 个 TextBased linter，**不含行长**。
  真正让 `longLine`/`maxHeartbeats`/`emptyLine`/`header` 生效的是 **`lake build`**（lakefile 的
  `[leanOptions] weak.linter.mathlibStandardSet = true`），所以 `build` 的警告也要清零。
  单文件复核：`lake env lean "-Dlinter.mathlibStandardSet=true" FQFP\BCH\X.lean`。

- **`Logarithm.lean` 的上游命运**：其代数半部分与 `NormedSpace.log`
  （[mathlib4#43670](https://github.com/leanprover-community/mathlib4/pull/43670)）重复。目标 pin
  `v4.34.0` 尚未包含该 PR（全树搜 `logSeries` 零命中），所以本地实现仍必需。下次 bump 时做机械
  替换：删 vendored 代数层 + 改名 `FQFP.log → NormedSpace.log`。

- **版本漂移**：源 Lean 4.29.0-rc8，目标 v4.34.0。手写移植顺利，生成件是风险集中点（见 §3.3）。
