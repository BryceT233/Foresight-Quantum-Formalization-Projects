# BCH 移植：计划、进度与经验

把 `D:\project\Lean-BCH\BCH`（源，17 个文件 ≈ 108k 行，Lean 4.29.0-rc8）移植进
`D:\project\CQM1\FQFP\BCH`（目标，Lean 4.34.0 / Mathlib v4.34.0），**重写架构与代码风格**，
而不只是搬运。

**当前状态：阶段 1（BCH 核心）、阶段 2（三次/四次/五次项）完成。** `lake build FQFP` ✔、
`lake exe runLinter` ✔、`lake exe lint-style` ✔，零 `sorry`、零自定义公理、零 `maxHeartbeats`
bump；阶段 1 的定理 `#print axioms` 只剩 `[propext, Classical.choice, Quot.sound]`。
阶段 3（机器生成层）未开始（见 §3）。

本文合并了原先的三份记录（`bch-port-progress-and-next.md`、
`bch-phase1-log-remainder-continuation.md`、`bch-phase1-complete.md`），删去了已过时的规划内容。

---

## 1. 目标文件布局

按**数学陈述**分层，不按源文件分层。

| 文件 | 行数 | 主题 |
|---|---|---|
| `Logarithm.lean` | 1034 | Banach 代数对数；`log (1+·)` 的余项界 |
| `ExpNorm.lean` | 230 | 指数估计：实数与范数代数的 Taylor 余项界 |
| `RealScalar.lean` | 83 | 完备 `ℚ`-代数上的唯一 `ℝ`-代数结构 |
| `WordNorm.lean` | 179 | 词乘积范数（arity-free） |
| `WordExpansion.lean` | 243 | 二元词模式、加权词和的分组界、`_diff` 界（telescoping） |
| `NestedCommNorm.lean` | 92 | 嵌套交换子范数 |
| `ChildsBasis.lean` | 165 | Childs 四重交换子基 |
| `BCHElement.lean` | 287 | **结构层**：`bch` 是什么 |
| `BCHCommutator.lean` | 573 | **偏差层**：`bch` 与 `a+b` 差多少 |
| `BCHSymmetric.lean` | 315 | **对称层**：Strang 乘积的误差 |
| `BCHTerms.lean` | 591 | **级数项层**：`bch` 展开的三次/四次/五次项及其范数界 |
| `QuinticRemainder.lean` | 233 | 五次项的一阶 Lipschitz 界（阶段 3 首个文件） |

依赖链：`Logarithm/ExpNorm → BCHElement → BCHCommutator → BCHSymmetric`；
`WordNorm → WordExpansion → BCHTerms → QuinticRemainder`。

阶段 1 拆成三个文件的原因：H2 会把 `BCHElement.lean` 推到 1000+ 行；三个文件的主题
（「`bch` 是什么」/「`bch` 与 `a+b` 差多少」/「对称乘积的误差」）边界清楚。阶段 2 单独成
`BCHTerms.lean`（712 行）：它按「`bch` 的展开系数」组织，与前三层的「误差估计」是两件事。

---

## 2. 阶段 1、2 已完成：源↔目标对照

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
| `Basic:1772–2118` 五次项族（4 组 + 项 + 界） | `BCHTerms.lean` | def 改名 `bchQuinticGroup{1,4,6,24}`、`bchQuinticTerm` |

**阶段 2 的两条约定**（与阶段 1 的差异，供阶段 3 沿用）：

1. **`def` 名必须 lowerCamelCase。** Mathlib 的 `defsWithUnderscore` linter 只检查 `def`
   （`Style.lean:557` 先要求 `isDefinition`），`theorem` 不受限——所以 `bch_cubic_term` 这类
   源名必须改写为 `bchCubicTerm`，而定理名仍是源的 `bchCubicTerm_smul`、
   `norm_bchCubicTerm_le`、`bchCubicTerm_LQ_decomp`（Mathlib 先例：`Complex.normSq` 与其
   `normSq_apply`、`norm_compContinuousLinearMap_le`）。
2. **`unusedSectionVars` 靠显式 binder 而不是 `omit`。** 五次项的四个组 `bchQuinticGroup{1,4,6,24}`
   及其范数界只需要 `NormedRing 𝔸`（源亦然），但它们位于 `NormedAlgebra ℚ 𝔸` 的 section 内；
   由于本项目禁止 `omit`，改用显式 `{𝔸 : Type*} [NormedRing 𝔸]` binder 遮蔽 section 变量。

### 阶段 1 的公开声明

- `Logarithm.lean`：`logCoeff`、`norm_logCoeff_le_one`、`logPartialSum`、
  `log_one_add_eq_logPartialSum_add_tsum`、`norm_log_one_add_sub_logPartialSum_le`（主引理）、
  `norm_log_one_add_le`、`norm_log_one_add_sub_le`、`norm_log_one_add_sub_add_sq_le`、
  `norm_log_one_add_sub_add_sq_sub_cube_le`、`logPartialSum_{zero,one,two,three,four}`。
- `ExpNorm.lean`：`real_exp_third_order_le_div`、`real_exp_third_order_le_cube`、
  `norm_exp_sub_one_sub_id_le`、`norm_exp_sub_one_sub_id_sub_sq_le`。
- `BCHElement.lean`：`norm_exp_mul_exp_sub_one_lt_one`、`norm_exp_sub_one_lt_one`、`bch`、
  `exp_bch`、`exp_eq_one_of_norm_lt`、`continuousOn_log_one_add`、`log_exp_sub_one`。
- `BCHCommutator.lean`：`norm_bch_sub_add_le`、`norm_bch_sub_add_sub_bracket_le`（H1）、
  `lie_eq_commutator`、`norm_bch_sub_add_sub_lie_le`。
- `BCHSymmetric.lean`：`norm_symmetric_bch_sub_add_le`（H2）。

### 阶段 2 的公开声明（`BCHTerms.lean`）

- 三次：`bchCubicTerm`、`bchCubicTerm_smul`、`norm_bchCubicTerm_le`、
  `norm_bchCubicTerm_diff_le`、`bchCubicTerm_LQ_decomp`。
- 四次：`bchQuarticTerm`、`bchQuarticTerm_smul`、`norm_bchQuarticTerm_le`、
  `bchQuarticTerm_LQ_decomp`。
- 五次：`bchQuinticGroup1`、`bchQuinticGroup4`、`bchQuinticGroup6`、`bchQuinticGroup24`、
  `bchQuinticTerm`、`bchQuinticTerm_smul`、`norm_bchQuinticTerm_le`。

阶段 3 复用的范数辅助（审核后已从 `private` 提升为公开）：`norm_mul_sub_mul_le`、
`norm_double_commutator_le`、`norm_mul_w_mul_le`、`norm_w_mul_mul_le`、`norm_mul_mul_w_le`、
`norm_word5_le`；`smul_five_fold` 仍是 `BCHTerms.lean` 的私有辅助。

---

## 3. 待做

### 3.1 阶段 3：机器生成层（≈95k 行，真正的成本中心）

| 源 | 行数 | 目标 | 依赖 |
|---|---|---|---|
| `Basic:2120–3027` 五次组 `_diff_le`（**已完成**）+ `_LQ_decomp`（推迟，见下） | 0.9k | `QuinticRemainder.lean`（已建） | 阶段 2 |
| `Basic:3028–4830` `bch_quintic_term_lin_diff` + taylor2 余项 `{,_2V,_3V,_4V}` | 1.8k | `QuinticRemainder.lean` | 阶段 2 |
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

**开工前必须先解决三件事：**

1. **生成器**：已确认存在——源 `scripts/` 下约 90 个 Python，生成器与独立 CAS 校验器成对出现
   （`gen_bch_quintic_term_taylor2{,_bound}.py`、`gen_bch_sextic_*`、`gen_bch_septic_*`、
   `gen_bch_octic_*`、`gen_d8_*`），`build_safe.sh` 与 `mem_watchdog.sh` 也在。**待确认的只剩
   发射代码对 4.34 的兼容性**：源大量使用 `match_scalars <;> ring`、`noncomm_ring`、
   `dsimp only` 这类对 Mathlib 内部 simp 集敏感的手法。
2. **构建内存**：源已因单模块峰值 RSS 把 42k 行的 `SymmetricQuintic` 拆成 4 个模块，并用
   `scripts/build_safe.sh` 顺序构建（Lake 5 没有 `-j` 节流）。目标仓库必须预先规划同样的拆分，
   不能等到 OOM。
3. **arity-free 重写的机会**：生成代码里每个 monomial 分支都重复
   `norm_smul_le → norm_Nprod_le → gcongr → ring`，这些应当全部改成对 `WordNorm.lean` /
   `WordExpansion.lean` 的单次调用。**这是把 95k 行压下来的最大杠杆，且必须在生成器层面做，
   事后手改是不可行的。**

   阶段 2 量过这笔账，阶段 3 开工前又付清了一次：五次项四个组的范数界曾为 30 个 5 字母词写
   180 行（30 次 `norm_word5_le` + 27 条 `norm_add_le` + 4 次 `linarith only`）；改造后每个是
   一行 `simpa [bchQuinticGroupN] using norm_sum_wordEval_le bchQuinticGroupNWords a b`。

   **本轮已完成**：

   * `WordExpansion.lean` 补齐了 `_diff` 侧：`norm_prod_sub_prod_le`（telescoping 原语）、
     `norm_wordEval_sub_le`、`norm_sum_wordEval_diff_le`（组级差分界，常数即该组 a-位置总数），
     以及无权组界 `norm_sum_wordEval_le` 与齐次性 `wordEval_smul` / `sum_wordEval_smul`。
   * `BCHTerms.lean` 的四个组改成词模式数据（`bchQuinticGroup*Words : Fin m → Fin 5 → Bool`）
     加 `Finset.sum`，`_le` / `_smul` 各一行；词表已用
     `artifacts/bch-audit-round-one/_check_quintic_words.py` 与源逐字比对（4 / 10 / 14 / 2 全 MATCH）。
   * `QuinticRemainder.lean`：四个组 `_diff_le`（常数 10 / 25 / 35 / 5）+ `norm_bchQuinticTerm_diff_le`
     （常数 1，因 `(1/720)(10 + 4·25 + 6·35 + 24·5) = 440/720 ≤ 1`）。

   **代价与偏差**：`_diff_le` 现在需要 `NormOneClass 𝔸`（源里这三条用 `omit` 去掉了它），因为
   telescoping 原语经 `norm_word_le` 归结到 `‖1‖ = 1`；BCH 层的一切本来就带 `NormOneClass`。

   **`_LQ_decomp` 伴生引理（有意推迟）**：源把它们写成逐项展开的显式非交换多项式恒等式
   （组 1：32 项；组 6：76 项，且带 `set_option maxHeartbeats 3200000`），只能由 `noncomm_ring`
   证明。它们只被 `SymmetricSepticPhaseBC` / `SymmetricSepticPieces`（阶段 3 后段）使用，
   而更早的 `QuinticMixed` / `SexticMixed` / `SepticTaylor` 只需要 `_diff_le` 与 taylor2 余项。
   因此推迟到移植那两个消费者时再做；届时先定形状：**逐组显式展开**（忠实于源，但组 6 需处理
   心跳，本项目禁止 bump），还是**按词模式生成 W-次数分解**（可能免 bump，但需先看消费者要点什么）。

   **`Basic:3028–4830`（`lin_diff` + taylor2 余项，1.8k 行）的勘察结论**（本轮完成，实现待下轮）：

   * **消费者只用 4 条**：`bch_quintic_term_taylor2_decomp`（恒等式）、`lin_diff` 与
     `taylor2_remainder`（定义）、`norm_bch_quintic_term_taylor2_remainder_le`（总界）。
     2V / 3V / 4V 三个子块、`taylor2_remainder_split` 与它们的三个界**在 `Basic.lean` 之外无人
     使用**，纯属内部脚手架——源为此写了约 1200 行（每项一条 `..._eq_sum` + `...Term_norm_le`）。
     按现在的词 API 这整块可以不要，总界由组引理直接给出。
   * **源的界形状**：`≤ (2430/720) M³‖V‖²`，`M = ‖x‖ + ‖V‖ + ‖y‖`；三个子块共用这一形状
     （常数 `1680/720`、`720/720`、`30/720`）。若用「每词 ≤ `M³‖V‖²`」的粗界加最大系数 `1/30`，
     得 `105/30 = 3.5`，比源的 `3.375` 弱 3.7%；要精确对齐需按 V 的个数分类并用各组的 `Σ|c|`。
   * **`WordExpansion.lean` 本轮补上了字母表无关的 API**：`wordProdList`（模式为 `List κ`）、
     `norm_wordProdList_le`、`norm_sum_smul_wordProdList_le`。动机有两条：Taylor 余项的词在
     **三**字母 `{x, V, y}` 上，二元的 `wordEval` 覆盖不到；且模式必须是 `List` 而不是 `Fin n → κ`
     ——`wordProdList` 的定义方程是 `rfl`，具体模式按定义约简，而 `wordEval` 的
     `if (v i) then a else b` 会卡成 `if true = true then a else b`（`simp only [↓reduceIte]`
     与 `simp only [cond_true]` 在该语境下都不触发，`abel`/`noncomm_ring` 于是把它当成与 `a`
     不同的原子）。已实测通过：`x*x*V*V*y = wordProdList ![x,V,y] [0,0,1,1,2]` 由
     `simp only [wordProdList, mul_one]; noncomm_ring` 一次解决；`Fin` 求和展开本身也可行
     （`Fin.sum_univ_succ` + `Fin.sum_univ_one` + `Finset.univ_eq_empty`/`Finset.sum_empty`）。
   * **下一步**：改造 `gen_bch_quintic_term_taylor2.py`（194 行，已通读）：它已用非交换多项式算出
     `lin_diff`（75 词）与 `taylor2_remainder`（105 词）；只需把 `emit_def` 改成发射模式数据
     （`List (Fin 3)` 字面量）与系数数据，加 `∑` 形式定义，`taylor2_decomp` 用「展开求和 +
     `noncomm_ring`」证明，总界用 `norm_sum_smul_wordProdList_le` 一行。

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

---

## 5. 技术经验（阶段 2/3 会反复用到）

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
  `rw [← Rat.norm_cast_real]; norm_num`。
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

---

## 6. 风险

1. **版本漂移。** 源在 Lean 4.29.0-rc8，目标 v4.34.0。阶段 1 的手写移植顺利（说明漂移可控），
   但生成代码大量使用 `match_scalars <;> ring`、`noncomm_ring`、`dsimp only` 这类对 Mathlib
   内部 simp 集敏感的手法（源 `CLAUDE.md` 记了 7 条此类技巧）。**生成代码的移植成本很可能
   远高于它的行数比例。**
2. **`Logarithm.lean` 的最终命运。** 该文件的代数半部分与 `NormedSpace.log`
   （[mathlib4#43670](https://github.com/leanprover-community/mathlib4/pull/43670)）重复，
   pin 一过就应删除。已核实目标 checkout 是 `v4.34.0`(`5ed2965256`, 2026-09-15)，全树搜索
   `logSeries` **零命中**，`Mathlib/**/Logarithm*.lean` **不存在**——即该 PR 尚未进入目标 pin，
   `FQFP/BCH/Logarithm.lean` 仍是必需的本地实现。下次 Mathlib bump 时做机械替换：删 vendored
   代数层 + 改名 `FQFP.log → NormedSpace.log`。
3. **已归档的设计记录。** `artifacts/log-upstream-alignment.md`、
   `artifacts/abstractions/LogOnePlus.md`、`artifacts/exp-log-plan.md`、
   `artifacts/rat-to-real-scalars.md` 已从工作树删除、但在 `HEAD` 中完好。它们是
   `Logarithm.lean` / `ExpNorm.lean` / `RealScalar.lean` 的设计依据（对齐 #43670 的接口决策、
   `log` 中心在 `1`、定义不需要范数、"shim 试过又删掉了"）。**要继续保留就
   `git checkout HEAD -- artifacts/`；否则本文 §4 与代码 docstring 已覆盖其结论性内容。**

---

## 7. 仓库状态与待办

- 阶段 1、阶段 2 的改动**已提交**（`a946626`、`c1b774e`、`33c578b`）。工作树当前有审核修复
  （见 `artifacts/bch-audit-round-one/bch-code-review.md` 的「修复记录」）：`FQFP.lean`（+1 import）、
  `FQFP/BCH/` 下 10 个文件、新增 `FQFP/BCH/WordExpansion.lean` 与仓库根的 `LICENSE`。
- 遗留文件 `xxxxyyyytest.lean` 已删除（`xxxxyyyytest1.lean` 早已不在）。
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
