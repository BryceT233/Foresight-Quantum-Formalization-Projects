# BCH 移植：计划、进度与经验

把 `D:\project\Lean-BCH\BCH`（源，17 个文件 ≈ 108k 行，Lean 4.29.0-rc8）移植进
`D:\project\CQM1\FQFP\BCH`（目标，Lean 4.34.0 / Mathlib v4.34.0），**重写架构与代码风格**，
而不只是搬运。

**当前状态：阶段 1（BCH 核心）完成。** `lake build FQFP` ✔、`lake exe runLinter` ✔、
`lake exe lint-style` ✔；阶段 1 的全部定理 `#print axioms` 只剩
`[propext, Classical.choice, Quot.sound]`，零 `sorry`、零自定义公理、零 `maxHeartbeats` bump。
阶段 2/3 未开始（见 §3）。

本文合并了原先的三份记录（`bch-port-progress-and-next.md`、
`bch-phase1-log-remainder-continuation.md`、`bch-phase1-complete.md`），删去了已过时的规划内容。

---

## 1. 目标文件布局

按**数学陈述**分层，不按源文件分层。

| 文件 | 行数 | 主题 |
|---|---|---|
| `Logarithm.lean` | 1014 | Banach 代数对数；`log (1+·)` 的余项界 |
| `ExpNorm.lean` | 229 | 指数估计：实数与范数代数的 Taylor 余项界 |
| `RealScalar.lean` | 92 | 完备 `ℚ`-代数上的唯一 `ℝ`-代数结构 |
| `WordNorm.lean` | 177 | 词乘积范数（arity-free） |
| `NestedCommNorm.lean` | 93 | 嵌套交换子范数 |
| `ChildsBasis.lean` | 165 | Childs 四重交换子基 |
| `BCHElement.lean` | 285 | **结构层**：`bch` 是什么 |
| `BCHCommutator.lean` | 549 | **偏差层**：`bch` 与 `a+b` 差多少 |
| `BCHSymmetric.lean` | 312 | **对称层**：Strang 乘积的误差 |

依赖链：`Logarithm/ExpNorm → BCHElement → BCHCommutator → BCHSymmetric`。

阶段 1 拆成三个文件的原因：H2 会把 `BCHElement.lean` 推到 1000+ 行；三个文件的主题
（「`bch` 是什么」/「`bch` 与 `a+b` 差多少」/「对称乘积的误差」）边界清楚。

---

## 2. 阶段 1 已完成：源↔目标对照

| 源的声明 / 文件 | 目标 | 备注 |
|---|---|---|
| `LogSeries.lean` 全部 + `Basic:326` 的 `exp∘log` | `Logarithm.lean` | 重定中心到 `1`，去掉定义中的范数 |
| 8 个 `norm_logOnePlus_sub…le` | `norm_log_one_add_sub_logPartialSum_le` + 4 个具体阶 | **参数化**（见 §5.1） |
| 23 个按 arity 展开的词范数引理 | `WordNorm.lean` 1 个引理 | arity-free 重写 |
| `Basic:40–216` exp 范数界 | `ExpNorm.lean` | 去重后只留 `TrotterError` 没有的 |
| `Basic:223,251,261,271,176,299,326` | `BCHElement.lean` | 小性条件、`bch`、`exp_bch`、`log_exp_sub_one` |
| `Basic:470` 二次界 `3s²/(2-eˢ)` | `BCHCommutator.lean` | |
| `Basic:612` **H1** `10s³/(2-eˢ)` | `BCHCommutator.lean` | **无心跳 bump**（源带 `maxHeartbeats 16000000`） |
| `Basic:1061` **H2** `300s³` | `BCHSymmetric.lean` | **无心跳 bump**（源带 `6400000`） |
| `Basic:1359,1365` Lie 括号 | `BCHCommutator.lean` | |
| `Basic:1374,1382` Lie 重复件 | **不移植** | 与原定理逐字相同 |
| `norm_bch_sub_add_le'` | **不移植** | 与二次界逐字相同 |
| `LogSeries.lean` 的 `logOnePlus_eq_real` + 手工 `restrictScalars` | `RealScalar.lean` 类型类实例 | |

### 阶段 1 的公开声明

- `Logarithm.lean`：`logCoeff`、`norm_logCoeff_le_one`、`logPartialSum`、
  `log_one_add_eq_logPartialSum_add_tsum`、`norm_log_one_add_sub_logPartialSum_le`（主引理）、
  `norm_log_one_add_le`、`norm_log_one_add_sub_le`、`norm_log_one_add_sub_add_sq_le`、
  `norm_log_one_add_sub_add_sq_sub_cu_le`、`logPartialSum_{zero,one,two,three,four}`。
- `ExpNorm.lean`：`real_exp_third_order_le_div`、`real_exp_third_order_le_cube`、
  `norm_exp_sub_one_sub_id_le`、`norm_exp_sub_one_sub_id_sub_sq_le`。
- `BCHElement.lean`：`norm_exp_mul_exp_sub_one_lt_one`、`norm_exp_sub_one_lt_one`、`bch`、
  `exp_bch`、`exp_eq_one_of_norm_lt`、`continuousOn_log_one_add`、`log_exp_sub_one`。
- `BCHCommutator.lean`：`norm_bch_sub_add_le`、`norm_bch_sub_add_sub_bracket_le`（H1）、
  `lie_eq_commutator`、`norm_bch_sub_add_sub_lie_le`。
- `BCHSymmetric.lean`：`norm_symmetric_bch_sub_add_le`（H2）。

---

## 3. 待做

### 3.1 阶段 2：Suzuki 三次系数 + 五次余项（≈700 行，手写）

源 `Basic.lean:1387–2100` → 目标 `FQFP/BCH/SuzukiCubic.lean`。内容：`bch_cubic_term`
（源 `Basic:1393` 的 `(1/12)([a,[a,b]] + [b,[b,a]])`）、齐次性
`bch_cubic_term (c•a) (c•b) = c³ • bch_cubic_term a b`、`bch_quintic_term`、四组范数界、
`norm_bch_quintic_remainder_le`。依赖：阶段 1。

之后才可能有 `Palindromic.lean`（源 5.5k 行），其中含
`IsSuzukiCubic p ↔ 4p³ + (1-4p)³ = 0`（源 `Palindromic:1362`）与 `suzukiP`。
`ChildsBasis.lean` 已就位，所以 `Palindromic` 的 Childs 依赖已满足。

### 3.2 阶段 3：机器生成层（≈95k 行，真正的成本中心）

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
| `Basic:11460–19314` τ⁷/τ⁸ + Lipschitz | 7.9k | `BCHHigherOrder.lean` | 阶段 1 |

**开工前必须先解决三件事：**

1. **生成器**：源用 `scripts/gen_*.py`（CAS 校验 + Lean 发射）。需确认脚本是否随源仓库保留、
   以及它发射的目标 Lean/Mathlib 版本是否还是 4.34。
2. **构建内存**：源已因单模块峰值 RSS 把 42k 行的 `SymmetricQuintic` 拆成 4 个模块，并用
   `scripts/build_safe.sh` 顺序构建（Lake 5 没有 `-j` 节流）。目标仓库必须预先规划同样的拆分，
   不能等到 OOM。
3. **arity-free 重写的机会**：生成代码里每个 monomial 分支都重复
   `norm_smul_le → norm_Nprod_le → gcongr → ring`，这些应当全部改成对 `WordNorm.lean` 的
   `norm_smul_word_le` / `norm_word_le` 的单次调用。**这是把 95k 行压下来的最大杠杆，
   且必须在生成器层面做，事后手改是不可行的。**

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
3. **一个 `𝔸`，一个命名空间。** 全部在 `namespace FQFP.BCH`；源的 `namespace BCH` 不沿用。
   `LieRing.ofAssociativeRing` 用 `attribute [local instance]` 局部打开（与
   `ChildsBasis.lean`、`NestedCommNorm.lean` 一致），且必须在**用到 `⁅·,·⁆` 的 section 内**
   声明，否则不可用。
4. **重复的定义不移植。** 目标库已有的（`TrotterError.norm_exp_le`、
   `ExpNorm.norm_exp_sub_one_le`、`ExpNorm.norm_exp_sub_sum_le`、`RealScalar` 全套）以及源里
   逐字重复的孪生定理，都不再抄一遍——docstring 指向即可。
5. **用 section 边界代替 `omit`/`include 𝕂`。** 目标不许出现 `omit`。

---

## 5. 技术经验（阶段 2/3 会反复用到）

### 5.1 参数化，而不是按阶展开

源 `LogSeries.lean` 有 8 个 `norm_logOnePlus_sub…sub_le`，是同一个证明在 `n = 1..8` 上的重复
（每个阶还要配一个 `summable_logSeriesTerm_shiftK` 与 `…_eq_tsum`）。目标用**一个**参数化引理：

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

- 阶段 1 的改动**全部未 commit**：修改 `FQFP.lean`（+3 import）、`FQFP/BCH/ExpNorm.lean`、
  `FQFP/BCH/Logarithm.lean`；新建 `FQFP/BCH/{BCHElement,BCHCommutator,BCHSymmetric}.lean`。
- 工作树里 `xxxxyyyytest.lean`、`xxxxyyyytest1.lean` 是遗留文件，应删除或归档。
- 每次提交前的验收（顺序不可省）：

  ```
  lake exe cache get
  lake build FQFP
  lake exe runLinter
  lake exe lint-style
  ```
