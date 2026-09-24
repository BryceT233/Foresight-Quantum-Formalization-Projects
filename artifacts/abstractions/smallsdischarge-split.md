# `SmallSDischarge.lean` 拆分勘察 + degree-8 可行性实测

勘察人：abstraction agent。**本轮未改动 `FQFP/` 下任何文件**；所有结论来自
`lake env lean` 与 Python 实跑（探针与生成器在 `scratch/`，结论保留后即删）。

本轮要回答两个问题：

1. `SmallSDischarge.lean`（现 **1627 行**，冷编译 ~115 s）该怎么切开，让没做完的部分
   （degree-8 恒等式 + 余项记账链）在新文件里做？
2. degree-8 恒等式（源 `nonic_pure_identity`）按现有形状能不能落地？墙在哪？

---

## 0. 结论摘要（先看这段）

| 问题 | 结论 |
|---|---|
| 现 `SmallSDischarge.lean` 是什么？ | 只有源 `SmallSDischarge.lean` 的**纯恒等式**那一半（degree 4/5/6/7），加一层表基建；76 条源声明没有对应物。 |
| 文件为什么长？ | 1479 行正文里**约 1540 行是生成的字面数据**（七个整数字面规范形 719 行 + `dynkin7Norm` 822 行定义）。 |
| 拆分的切法 | **按「每度一条恒等式 + 一个共享工具箱」切**（§4）。工具箱是唯一的新增文件；degree 4–7 各自成文件；degree-8 一个文件；余项链按主题簇另开 3 个文件。 |
| **本轮做完了什么？** | §5：工具箱 + degree 4/5/6/7 四个文件已落地，`SmallSDischarge.lean` 从 1627 行降到 **47 行**（只剩聚合与余项链占位），degree-7 的字面规范形**全部删除**、改用增量 collapse。验收全绿、25/25 条陈述逐字未变。**代价：恒等式侧冷编译 115 s → 95 s，其中 degree-7 从 ~11 s 涨到 47 s（§5.4，原因未定）。** |
| degree-8 数学成立吗？ | **成立**（§2，Python 独立复算）：`L·(Dynkin 侧) − L·bchOcticTerm` 在全部 2⁸ = 256 个字上系数为 0，有效支撑 124 = `bchOcticTerm` 的项数。 |
| degree-8 按 degree-7 的形状能落地吗？ | **按「块」切分可以**（7 条 `decide` 全过，整文件 11 s）；**按 degree-7 的旧「生成整数字面规范形」不可以**——256 行的字面 `def` 在默认预算下**超 200k 心跳**（§3.2）。本轮新增的增量 collapse（§5.2）回避了这一点。 |
| 需要换 K 吗？ | **不需要**。`K = 210` 覆盖到 degree 8：`210⁸ = 3782285936100000000` 被 `120960`（`bchOcticTerm` 的公分母）、`20160`、`288` 等整除（§2.2）。`WordAlgebra.lean` 文档里「degree 9/10 要重新考虑 K」的说法对 degree 8 不适用。 |
| 下一步该做什么？ | `DynkinReeOctic.lean`（degree-8，§6.4）：先把 `bchOcticTermWords/Coeffs` 换成表，再照 degree-7 的形状加一块。若要先回收 §5.4 的 36 s，两条候选都记在那里。 |

---

## 1. 现状盘点（实测）

### 1.1 本树 `FQFP/BCH` 的 16 个文件

| 文件 | 行数 | 冷编译代价相关事实 |
|---|---|---|
| `SmallSDischarge.lean` | 1627 | `.olean.private` 2.62 MB；冷编译 ~115 s |
| `BCHTerms.lean` | 992 | degree-5 的四组保持 `Fin m → Fin 5 → Fin 2`（有位置索引消费者） |
| `QuinticTaylor2.lean` | 490 | |
| 其余 13 个 | 63–816 | |

### 1.2 `SmallSDischarge.lean` 的内部分区（按 `grep` 实测行号）

| 行段 | 内容 | 行数 |
|---|---|---|
| 61–78 | 工具箱前言 | 18 |
| 80–114 | 环级 `bchZ`、`bchT2`…`bchT7` | 35 |
| 116–148 | `bchTTable : (k : ℕ) → KTab` | 33 |
| 150–210 | `evalKTab_bchTTable_{one…seven}`（7 条桥） | 61 |
| 212–254 | degree-4：`quintic_pure_identity{_cleared}` | 43 |
| 256–385 | degree-5：`bchW5`/`bchY35`/`bchY45` + 5 张表 + 桥 + `dynkin5Tab` + 一条 `decide` + `sextic_pure_identity` | 130 |
| 387–586 | degree-6：同上形（4 个 `bchY*`、5 张表、`dynkin6Tab`、`decide`、`septic_pure_identity`） | 200 |
| 588–789 | degree-7 环级件 + 表 + 7 条桥（**无字面规范形**） | 202 |
| **790–1508** | **七个字面规范形**（`w7Norm` 66 / `y37Norm` 64 / `y47Norm` 74 / `y57Norm` 74 / `y67Norm` 66 / `z7Norm` 75 / `septicNorm`＝`bchSepticTermTable` 复用） | **719** |
| 1510–1591 | `septicNorm`、`dynkin7Tab`、7 条 `collapseK_*`（`rfl`）、`dynkin7Norm`（822 行定义）、`decide` | 82（+ 定义体 822） |
| 1593–1625 | `evalKTab_dynkin7Tab_eq_dynkin7Norm`、`…_eq_zero`、`octic_pure_identity` | 33 |

**「生成的字面数据」≈ 1540 行 ≈ 全文件 95%。** 真正的数学陈述与证明 ≈ 90 行。

### 1.3 与源的差距（沿用并复核 `artifacts/abstractions/wordalgebra-int.md` §「与源的差距」）

源 80 条声明，**76 条在本树没有对应物**：

| 家族 | 源 | 本树 |
|---|---|---|
| `quintic_pure_identity(_cleared)` / `sextic_` / `septic_` / `octic_`（degree 4–7） | ✅ | ✅ |
| `nonic_pure_identity`（degree 8） | ✅ | ❌ |
| `pow{n}_sub_zpow{n}_telescope`（n=3..8）与 `norm_pow{n}_…_le` | ✅ | ❌ |
| `y{m}_sub_z{m}_sub_…_decomp` 整梯 + `norm_*` | ✅ | ❌ |
| `I1/I2_residual_decomp_eq`（含 septic/octic/nonic 变体）与 `norm_I*` | ✅ | ❌ |
| `R_eq_neg_deg5_residual` / `R_plus_T5_…` 四代 | ✅ | ❌ |
| `norm_bch_{quintic,sextic,septic,octic}_remainder_large_s_le` | ✅ | ❌ |
| `pieceB_{sextic,septic,octic,nonic}_decomp` | ✅ | ❌ |

**纯恒等式的消费者已经查清（实测 `grep _pure_identity`）**：

| 恒等式 | 源里的消费者 |
|---|---|
| `quintic_pure_identity`（deg 4） | `norm_bch_quintic_remainder_le`（`convert`，源 1183）、四个 `pieceB_*_decomp` |
| `sextic_pure_identity`（deg 5） | `pieceB_sextic/septic/octic/nonic_decomp` |
| `septic_pure_identity`（deg 6） | `pieceB_septic/octic/nonic_decomp` |
| `octic_pure_identity`（deg 7） | `pieceB_octic/nonic_decomp` |
| `nonic_pure_identity`（deg 8） | `pieceB_nonic_decomp`（源 8379：`have hNonic := nonic_pure_identity 𝕂 a b`，8379–8380 与其它四条一起进 `linear_combination`） |

也就是说：**degree-8 恒等式是 `pieceB_nonic_decomp` 的硬依赖**，与其余四条同级——这是它必须做的理由，
而且它的形状必须与源一致（`W8`/`y3_8`…`y7_8` 的写法直接出现在 `pieceB_nonic_decomp` 的 `let` 链与
`intro` 里，源 8352–8372）。

---

## 2. degree-8 的数学：实测成立

生成器与校验器：`scratch/gen_deg8_full.py`、`scratch/check_deg8_identity.py`。

### 2.1 恒等式的形状（源 `nonic_pure_identity`，degree 8）

```
½·W8 + ⅓·(y³)₈ − ¼·(y⁴)₈ + ⅕·(y⁵)₈ − ⅙·(y⁶)₈ + ⅐·(y⁷)₈ − ⅛·z⁸ − C₈ = 0
```

`W8 = 2·y_d8 − (y²)_d8`；`C₈ = bchOcticTerm`。（源把 `2·y_d8` 的 9 个单项式与 `(y²)_d8` 的 7 个乘积写在 `W8` 里，所以表侧就是 `2 • bchTTable 8` 减去 7 条 `mulKTab` 链——与 degree-7 的 `w7Tab` 同形。）

### 2.2 字表规模（Python 独立复算，`scratch/gen_deg8_full.py` 输出）

| 块 | 原始行数 | 支撑 | `L = 840` 下的整乘子 |
|---|---|---|---|
| `w8Tab` | 156 | 93 | 420 |
| `y38Tab` | 819 | 219 | 280 |
| `y48Tab` | 2241 | 255 | −210 |
| `y58Tab` | 3400 | 256 | 168 |
| `y68Tab` | 2928 | 256 | −140 |
| `y78Tab` | 1344 | 256 | 120 |
| `z8Tab` | 256 | 256 | −105 |
| `octicTab` | 124 | 124 | −840 |
| **合计** | **11144** | — | — |

与 `artifacts/abstractions/wordalgebra-int.md` §4.2 的读数（11268 / 逐块 9,147,819,2241,3400,2928,1344,256）**一致**（本文的 11144 少 124，因为把 `bchOcticTerm` 单列为一块而不是并入 `y1`）。

### 2.3 消去成立（独立校验）

```
raw rows          : 11144
Dynkin support    : 0 words (after term)
bchOcticTerm      : 124 words
merged nonzero    : 0
OK: the degree-8 cancellation identity holds word by word.
```

**`K = 210` 够用**：`210⁸ = 3782285936100000000`，`120960 | 210⁸`（`120960 = 2⁷·3³·5·7`），所以
`bchOcticTerm` 的系数 `c/120960` 清成整数 `c · 31268898281250`。同理 `20160`、`5040`、`288`、`144` 都整除。
（`WordAlgebra.lean` 模块文档里「degree 9 或 10 不该在不动 `K` 的情况下尝试」的警告是**对 degree 8 之后的**，degree 8 本身不需要动它。）

### 2.4 顺带确认的一件事

`bchOcticTerm` 目前是**唯一一个还用「词数组 + 有理系数数组」的项**（`bchOcticTermWords`/`bchOcticTermCoeffs`，`BCHTerms.lean:821/887`）。degree-6/7 的对应物都已按「数据住在它所定义的项的家」改成 `KTab`
（`bchSexticTermTable` / `bchSepticTermTable`）。**degree-8 的第一步与 degree-7 完全一样**：把这两个数组换成
`bchOcticTermTable : KTab`（124 行整数字面量），`bchOcticTerm a b := evalKTab a b bchOcticTermTable`，
`norm_bchOcticTerm_le` 改走 `ratTab`。两者在本树都**零消费者**（实测：`bchOcticTermWords`/`Coeffs` 只出现在
`BCHTerms.lean` 自身），所以是安全的。

---

## 3. degree-8 的墙：实测读数

### 3.1 按「块」切分的 kernel collapse：**全部通过**

探针 `scratch/deg8_pieces.lean`（生成器 `scratch/gen_deg8_probe.py`）把八块表逐字镜像本树的 degree-7
写法，然后每块一条

```lean
set_option maxRecDepth 100000 in
example : (collapseK y58Tab).all (fun p => p.2 == 0) = false := by decide
```

**七条全部通过，整文件 11 s。** 也就是说 `collapseK` 的 kernel 归约对 3400 行 / 256 支撑是**可行**的——
这与 `wordalgebra-int.md` §4.2「degree-8 的 y4/y5/y6 三块仍超时」**并不矛盾**：那次的失败点在「把 3400 行折成
256 行的**字面**表」这个项构造上，而不是在归约本身（见 §3.2）。

### 3.2 真正的墙：**256 行的字面 `def`**

探针 `scratch/deg8_literal.lean`：

| 形状 | 结果 |
|---|---|
| `def lit64 : KTab := [ 64 行字面量 ]` | ✅ |
| `def lit256 : KTab := List.replicate 256 (...)` | ✅ |
| `def lit256explicit : KTab := [ 256 行字面量 ]` | ❌ **超 200k 心跳**（`«synthesize pending MVars»`，报在 `def` 那一行） |

而在完整 dry run（`scratch/deg8_full.lean`，13130 行）里，**第一个 256 行的 `*Norm` 字面 `def` 就超时了**，
后续 `collapseK pieceTab = pieceNorm := rfl` 全部退化成 `Not a definitional equality` 的连锁错误。

**根因判定**：不是归约慢，是**把 256 行 × 17 位整数的字面表装进环境**这件事本身超预算。degree-7 的
`dynkin7Norm` 有 822 行却过得去，说明预算是**按 `def` 的项整体**算的，而不是按行数线性——822 行**同一度**
的短行（每行 7 个字母）与 256 行**8 字母 + 大整数**处在不同量级。（这一条需要下一轮用 `set_option diagnostics`
或 profiler 钉死，但工程上的结论已经够了：**不要写 256 行的字面规范形**。）

### 3.3 绕法：增量 collapse，**一个字面规范形都不写**

`WordAlgebra` 已经有 `evalKTab_collapseK : evalKTab (collapseK t) = evalKTab t`，但缺**合并律**。
补两条纯 `List` 引理（小、零风险）即可把一次大 collapse 拆成「逐块 collapse + 累加」：

```lean
theorem collapseK_append (s t : KTab) : collapseK (s ++ t) = collapseAuxK t (collapseK s)
theorem collapseAuxK_append (s t acc : KTab) :
    collapseAuxK (s ++ t) acc = collapseAuxK t (collapseAuxK s acc)
```

于是 degree-8 的系数比对变成**九步**，每步只见一块（≤3400 行）与一个 ≤256 行的累加器：

```
collapseK dynkin8Tab   -- dynkin8Tab 写成「八块 ++ 第九块」的右结合 __树__
  = collapseAuxK 其余 (collapseAuxK dynkin8First (collapseK sexticFirst))   -- 每步一条 rw
  …
  → 最终 256 行，再一条 decide
```

**收益**：degree-8 文件里**不再出现任何字面规范形**（degree-7 的 1540 行生成数据在这里是 0 行），
代价是 9 条小引理式 + 两条 `collapseK_append`。**这条路线还能反过来给 degree-7 减重**（§4.3）。

---

## 4. 拆分设计

### 4.1 唯一需要新增的「结构性」文件：共享工具箱

degree 4–7 目前**共用**同一批声明，必须有一个家：

```lean
-- FQFP/BCH/DynkinReeToolbox.lean   (新文件, ~150 行)
-- 数学内容：y = exp a · exp b − 1 的分次件 T_k，以及 Dynkin/Ree 形式的公共记号
def bchZ  (a b) := a + b                                    -- 只要 [Add]
def bchT2 … bchT7                                            -- [Semiring] [Algebra ℚ]
def bchTTable : (k : ℕ) → KTab                               -- 数据的家
lemma evalKTab_bchTTable_one … _seven                        -- 7 条桥
```

`quintic_pure_identity_cleared` / `quintic_pure_identity`（degree 4）也放这里：它只有 43 行，
而且**刻意走 `noncomm_ring` 而不是表格路线**（陈述在裸 `[Ring 𝔸]` 上，`evalKTab` 需要 `[Algebra ℚ 𝔸]`），
所以给它单开一个文件不值得。

### 4.2 度 → 文件映射（每度一条恒等式）

| 新文件 | 内容 | 源里的名字 | 估行数（拆分后） |
|---|---|---|---|
| `DynkinReeToolbox.lean` | §4.1 + degree-4 恒等式 | `quintic_pure_identity{,_cleared}` | ~190 |
| `DynkinReeQuintic.lean` | degree-5（`bchW5`/`bchY35`/`bchY45` + 表 + 桥 + `decide`） | `sextic_pure_identity` | ~135 |
| `DynkinReeSextic.lean` | degree-6 | `septic_pure_identity` | ~205 |
| `DynkinReeSeptic.lean` | degree-7（**字面规范形按 §4.3 处理**） | `octic_pure_identity` | 202 + 数据 |
| `SmallSDischarge.lean` | **余项记账链**（另一整半） | `norm_bch_*_remainder_*` … | 见 §4.4 |

命名说明：**按「这条恒等式的次数」命名，不按源里 `octic_pure_identity` 的名字命名**——源的名字比它证的
次数**小 1**（`octic_` 证 degree 7），这是源的一个历史错位，`artifacts/abstractions/wordalgebra-int.md`
§0quater 已经决定「源是唯一真理，保留原名」，所以**定理名保留源的，文件名用次数**。每个文件的 docstring
里写明「本文件的 `octic_pure_identity` 证 degree-7 的消去，名字沿用源」。

### 4.3 degree-7 的字面规范形：移出去，或删掉

两条路，本轮实测支持后者：

* **(a) 移到 `DynkinReeSepticData.lean`**：纯数据文件（~1540 行 `def` + 7 条 `rfl`），
  `DynkinReeSeptic.lean` import 它。**零技术风险**，`SmallSDischarge` 立刻瘦到 ~200 行，
  但冷编译总代价不变。
* **(b) 按 §3.3 的增量 collapse 重写**：删掉全部七个字面规范形与 `dynkin7Norm`，
  改成「逐块 collapse + 累加」，最后一条 `decide`。**得到 degree-8 要用的形状**（等于顺手把
  degree-8 的技术点先在 degree-7 上验证一遍），并把 ~1540 行生成数据换成 ~30 行引理。
  风险：`decide` 的预算要重新量（已知 1040 行的单块过、3400 行没过，而增量型每步 ≤1040 行）。

**建议 (b)，并把它当作 degree-8 的前置**：degree-8 反正必须走增量型（§3.2 的墙），
先在 degree-7 上把形状跑通，degree-8 就只是「照抄 + 加一块」。

### 4.4 余项记账链（源 787–8382，约 7.6k 行）的分簇

按数学主题分三个文件，每个都能独立开工（依赖关系是线性的）：

| 新文件 | 源行段 | 内容 | 源行数 |
|---|---|---|---|
| `BCHRemainderTelescope.lean` | 1719–3014 + 4294–7806 | `pow{n}_sub_zpow{n}_telescope`、`norm_pow{n}_…_le`、`y{m}_sub_z{m}_sub_…_decomp` 整梯及其范数 | ~4.0k |
| `BCHResidualDecomp.lean` | 3015–4131 | `I1/I2_{septic,octic,nonic}_residual_decomp_eq`、`R_eq_neg_deg5_residual` 四代、`norm_I1_*_RHS_le` | ~1.1k |
| `BCHPieceBDecomp.lean` | 7807–8382 + 787–1718 | `pieceB_{sextic,septic,octic,nonic}_decomp` 与非小-s 的 `norm_bch_*_remainder_large_s_le` | ~1.5k |

（`787–1718` 的四条 `norm_bch_*_remainder_large_s_le` 与 `pieceB_*_decomp` 放在一起，因为它们互为上下游。）

### 4.5 拆分后的依赖图

```
BCHTerms ─┬─> DynkinReeToolbox ─┬─> DynkinReeQuintic ─> DynkinReeSextic ─> DynkinReeSeptic
          │                     │                                            │
          │                     └────────────────────────────────────────────┴─> DynkinReeOctic (degree 8)
          └─> BCHRemainderTelescope ─> BCHResidualDecomp ─> BCHPieceBDecomp (SmallSDischarge)
                                                            ↑
                        DynkinRee{Quintic,Sextic,Septic,Octic} ┘
```

**无环**：恒等式侧只依赖 `DynkinReeToolbox`（+ 同度的前一度）；余项侧依赖全部恒等式。这也正是
`artifacts/abstractions/wordalgebra-int.md` §0quater 记下的「当初必须分文件的原因」的最终形态。

---

## 5. 施工记录（本轮已落地：拆分 + degree-7 增量 collapse）

用户拍板：degree-7 的规范形**按增量 collapse 重写**（§4.3 的 (b)），本轮范围**只做纯恒等式侧的
拆分**（工具箱 + degree 4/5/6/7 分文件）。以下全部实跑。

### 5.1 落地内容

| 文件 | 行数 | 内容 |
|---|---|---|
| `FQFP/BCH/DynkinReeToolbox.lean` | 200 | `bchZ`、`bchT2`…`bchT7`、`bchTTable` + 7 条桥、degree-4 的 `quintic_pure_identity{_cleared}` |
| `FQFP/BCH/DynkinReeQuintic.lean` | 145 | degree-5：`bchW5`/`bchY35`/`bchY45` + 4 张表 + 4 条桥 + `dynkin5Tab` + 一条 `decide` + `sextic_pure_identity` |
| `FQFP/BCH/DynkinReeSextic.lean` | 195 | degree-6：同形 + `septic_pure_identity` |
| `FQFP/BCH/DynkinReeSeptic.lean` | 309 | degree-7：环级件 + 7 张表 + 7 条桥 + **增量 collapse** + `octic_pure_identity` |
| `FQFP/BCH/SmallSDischarge.lean` | 47 | **只剩聚合 + 余项链的占位文档**（2790 → 47 行的正文） |
| `FQFP/BCH/WordAlgebra.lean` | 312（+22） | 新增 `collapseAuxK_append`、`collapseK_append` |

`FQFP.lean` 未改：`SmallSDischarge` 现在 `public import` 四个 `DynkinRee` 模块，
而它们又各自 `public import` 前一度，所以四个新模块都已在伞内（已由 `lake build FQFP` 实检）。

### 5.2 degree-7 的新形状（实测）

七个字面规范形（719 行）与 `dynkin7Norm`（822 行定义）**全部删除**，换成七个**命名的累加阶段**：

```lean
def dynkin7Acc1 : KTab := collapseK (smulKTab 210 w7Tab)
def dynkin7Acc2 : KTab := collapseAuxK (smulKTab 140 y37Tab) dynkin7Acc1
…
def dynkin7Norm : KTab := collapseAuxK (smulKTab (-420) septicTab) dynkin7Acc6
```

**两个必须记住的实测点**：

1. **阶段必须命名成 `def`，不能写成七层嵌套的 `collapseAuxK` 一项**。嵌套版在
   `def dynkin7Norm` 的声明头就 `whnf` 超 200k 心跳；拆成七个 `def` 后每个阶段都在预算内。
   原因与 `DynkinReeToolbox.lean` 里「piece 命名成 `def` 而不是 `let`」完全同源：
   `whnf`/`isDefEq` 每进一层就把整棵嵌套项重算一遍。
2. **最后一条比对用 `decide +kernel`，不是 `decide`**。`decide`（默认求值器）在
   `dynkin7Norm` 上仍 `whnf` 超 200k 心跳；`decide +kernel` 走内核自己的归约，通过。
   **没有 `maxHeartbeats` bump**；`maxRecDepth 100000` 是遍历 ~1000 层 `List.cons` 的
   tactic 递归深度限制，理由写在原处。

累加链的桥（`evalKTab_dynkin7Tab_eq_dynkin7Norm`）也实测通过：
`rw [dynkin7Tab]; simp only [collapseK_append]` 把链折成七个 `collapseAuxK`，再
`rw [← dynkin7Acc1, …, ← dynkin7Norm]` 认出各阶段。（`rw [dynkin7Acc1]` 用**正向**会失败——
目标是 `collapseK (smulKTab 210 w7Tab)` 而等式左边是 `dynkin7Acc1`。）

### 5.3 验收（全部实跑）

| 项 | 结果 |
|---|---|
| `lake build FQFP` | ✅ **零警告**（8966 jobs） |
| `lake exe runLinter FQFP` | ✅ `Linting passed for FQFP` |
| `lake exe lint-style` | ✅ exit 0 |
| 陈述逐字不变 | ✅ `scratch/check_split_statements.py`：**25/25 条恒等式陈述一致**（按去空白后的 name + binders + type 比对，从 `863a502` 的旧文件读原文） |
| `#print axioms` | ✅ 五条 `*_pure_identity` 与三条 `evalKTab_dynkin*Tab_eq_zero` 都只剩 `[propext, Classical.choice, Quot.sound]`；`dynkin7Norm_all_zero` 只剩 `[propext]`；两条 `collapse*_append` **零公理** |

### 5.4 代价：degree-7 变慢了（要记账）

冷编译实测（逐个删 olean 后 `lake build`）：

| 文件 | 冷编译 |
|---|---|
| `DynkinReeToolbox.lean` | 14.6 s |
| `DynkinReeQuintic.lean` | 12.4 s |
| `DynkinReeSextic.lean` | 21.4 s |
| `DynkinReeSeptic.lean` | **47.1 s** |
| 恒等式侧合计 | **95 s**（拆前 `SmallSDischarge` 整文件 ~115 s） |

degree-7 单文件从约 11 s 涨到约 47 s。三个候选原因，**都还没定**：

* 累加链的 kernel 归约是 7 段顺序计算，`decide +kernel` 要把整条链走完——而旧的
  「逐块 `rfl` 折成字面表 + 一条 `decide`」是 7 次独立的小归约 + 1 次 128 行的判定，
  总量可能更小；
* `rw [dynkin7Tab]; simp only [collapseK_append]` 在 ~3400 行表上跑了 6 次接缝；
* 对照读数还不干净：同一文件先后测到 77 s 与 47 s，需要 `set_option trace.profiler` 钉死。

**下一步若要回收这 36 s**，优先试 two 条：(i) 给 `dynkin7Acc{1..6}` 的 `decide +kernel`
做成逐阶段的 `example`，看时间分布在哪一段；(ii) 把「逐块 `rfl` 折成字面表」这一半保留在
degree-7（它过），只把 `dynkin7Norm` 也写成字面表——即退回 §4.3 的 (a)，代价是 degree-8 要另想
办法（§3.2 的 256 行字面 `def` 墙仍然在，且现在有了 `decide +kernel` 这个新工具，degree-8 也许
能直接走增量型而不必付这次的钱）。

---

## 6. 施工顺序

1. ~~**`DynkinReeToolbox.lean`**~~：✅ 已完成（§5.1）。
2. ~~**`DynkinReeQuintic.lean` / `DynkinReeSextic.lean`**~~：✅ 已完成。
3. ~~**degree-7 的规范形**~~：✅ 已按 (b) 重写。
4. **`DynkinReeOctic.lean`**（degree-8，新工作）：
   a. `BCHTerms.lean`：`bchOcticTermWords/Coeffs` → `bchOcticTermTable : KTab`（124 行）+ `bchOcticTerm := evalKTab …` + `norm_bchOcticTerm_le` 走 `ratTab`；
   b. `bchTTable 8` + `evalKTab_bchTTable_eight`；
   c. 环级 `bchW8`、`bchY38`…`bchY78`；表 `w8Tab`、`y38Tab`…`y78Tab`、`z8Tab`、`octicTab` + 桥；
   d. `dynkin8Tab`（`L = 840`）+ §3.3 的增量 collapse + `nonic_pure_identity`。
5. **余项链三文件**（§4.4）：按簇开工，逐簇验收。这一步的工程量远大于 1–4，且里面才出现
   `RCLike 𝕂` / `Real.exp` / `Real.log`。

---

## 7. 本轮探针（在 `scratch/`，不进版本库）

| 复现方式 | 验的是什么 | 结论 |
|---|---|---|
| `python scratch/gen_deg8_full.py` | degree-8 八块表的原始行数 / 支撑 / `L = 840` 乘子 / 消去 | §2.2–2.3 |
| `python scratch/check_deg8_identity.py` | 从 `BCHTerms.lean` 解析 `bchOcticTermWords/Coeffs` 并清成整数，逐字核对 | §2.3 成立 |
| `lake env lean scratch/deg8_pieces.lean` | 八块各自的 `decide` collapse | 全过，11 s |
| `lake env lean scratch/deg8_y58Tab.lean` | 单块（3400 行）的 `decide` collapse 墙钟 | 16 s |
| `lake env lean scratch/deg8_literal.lean` | 64 / 256 行字面 `def` | 64 ✅、`replicate 256` ✅、**256 行字面 ❌** |
| `lake env lean scratch/deg8_full.lean` | 完整 dry run（八块 + 八条 `rfl` + 一条 `decide`） | 卡在第一个 256 行 `*Norm` 的 `def` 上 → §3.2 |
| `python scratch/check_split_statements.py` | 拆分前后 25 条恒等式陈述逐字比对 | 25/25 一致（§5.3） |
| `python scratch/wa_probe.lean`（`lake env lean`） | `collapseK_append` / `collapseAuxK_append` 的小例冒烟 | 通过；注意 `collapseK` 边走边「前插」，左边有重复字时左侧发生合并 |
| `scratch/SmallSDischarge.orig.lean` | 拆分前的原文副本（83846 字节） | 供回看，**不进版本库** |

`scratch/` 在 `.gitignore` 里，不进构建也不进 `lint-style`。
