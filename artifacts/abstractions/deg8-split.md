# degree-8 的墙与暂缓决定

勘察人：abstraction agent。§1–3 是实测：所有读数来自 `lake env lean <probe>` 的实跑，勘察时
工作树未被改动（探针只存在于已删除的 `scratch/`）。§4–5 是后续的处置记录：degree 8 已决定暂缓，
`DynkinReeOctic.lean` 与它的生成器已删除，§5 留下重启所需的全部规格。工作树当前状态：
`lake build FQFP` ✅ 零警告（`DynkinRee*` 四个模块已从源码编译通过，见 §6）。

---

## 0. 结论摘要

| 问题 | 结论 |
|---|---|
| degree-8 现在的形状卡在哪？ | **不是内核，也不是心跳**：是 **elaborator 的 `whnf`**。累加链深到 4 层时，一条最普通的 `rfl`（`(collapseK …).length = 256`）就在**默认 200k 心跳**上超时。 |
| 为什么 degree-7 能过、degree-8 不能？ | 不是「8 层链」本身，而是**每一片要大 4 倍、链长 8 层**；`whnf` 在这里是**深度敏感**的。degree-7 的 7 层链在定义它的模块里要 33.9 s 类型检查（实测见 §5.1），degree-8 翻倍后就是现在的「>10 分钟不出结果」。 |
| `smallsdischarge-split.md` §3.2 那条「**256 行字面 `def` 超默认预算**」还对吗？ | **不对，是误诊。** 真因是 `maxRecDepth`（tactic 递归深度），不是心跳：256 行字面表在**默认预算**下配 `set_option maxRecDepth 100000` 直接过；224 行连 `maxRecDepth` 都不用改。 |
| 那 degree-8 是不是就能照 degree-7 写？ | 不能照抄。**片太大**：`(y⁵)₈` 这一片 3400 行，单独一次 `decide` 就要 **498 s**。 |
| 真正可用的形状 | **把片切小**（每块 ≤ ~800 行，沿乘积边界切，天然且便宜），**每块独立 collapse 成一行一个词的规范形**，再用一个**浅的合并树**把这些 256 行表合起来。 |
| 关键读数（本轮实测） | 见 §2 表。 |

---

## 1. 实测读数

全部在 `lake env lean` 下、默认 200k 心跳，`set_option maxRecDepth 100000` 只在数据级
`decide +kernel` 上（理由同 degree-7：遍历 ~256 层 `List.cons` 的 tactic 递归深度，不是搜索/心跳预算）。

| 探针（`scratch/`，已删，可复现） | 量的是什么 | 读数 |
|---|---|---|
| `lit_64 … lit_224` | 字面 `KTab` 的规模上限 | 64/96/128/160/192/224 行**全部通过**（~7.2–7.7 s，几乎只有 import 成本） |
| `lit_depth` | 256 行字面表 | **默认 `maxRecDepth` → `maximum recursion depth has been reached`；加 `maxRecDepth 100000` → 过**。全程无心跳问题。 |
| `primitives` | 单片 collapse + 两表合并 | `collapseK (smulKTab 420 w8Tab)`✅、`collapseK (smulKTab (-105) z8Tab)`✅、`collapseAuxK n2 n1`✅（三个都是 256 行表，~23 s 含 import） |
| `leaf_n1` (156 行片) | 单片 collapse | **7.9 s** ✅ |
| `leaf_n7` (256 行片) | 单片 collapse | **12.3 s** ✅ |
| `leaf_n8` (`bchOcticTermTable`, 124 行) | 单片 collapse | **21.6 s** ✅ |
| `leaf_n2` (`(y³)₈`, 819 行) | 单片 collapse | **17.3 s** ✅ |
| `leaf_n4` (`(y⁵)₈`, 3400 行) | 单片 collapse | **498.6 s** ✅（过了，但不可接受） |
| `chunked` (`(y⁵)₈` 的前 8 个乘积, ~800 行) | 切小后单片 collapse | **17.4 s** ✅ |
| `chain_depth` (4 层累加链，全是 256 行表) | 链深 | **`rfl` 在 `whnf` 上超 200k 心跳** ❌ |
| `leaves.lean`（八片各一条 `decide`，一个文件） | 全量 | 10 分钟未出结果（被 n4 拖住） |
| `scratch_deg8_chain.lean`（完整 8 层链） | 现状形状 | >10 分钟无输出（内存 8.7–10.8 GB 间 GC 抖动，即在做有用功但太慢） |

### 1.1 成本模型（实测拟合）

单片 collapse 的 `decide +kernel` 代价近似

    ≈ (片内行数) × 256      -- 内核为取 256 个词各重跑一遍折叠

的证据是：同一条 `all` 判据下，800 行 17 s、3400 行 499 s；行数涨 4.25×，时间涨约 29×。
无论是线性还是超线性，**工程阈值是清楚的：单片超过约 1000 行就该切**。

### 1.2 为什么 `chain_depth` 是决定性的

`chain_depth` 里没有任何大数据：四层累加器全是 256 行表，可最外层那条
`example : acc1.length = 256 := rfl` 就超时。**这排除了「行数」作为根因**，把矛头指向
`collapseAuxK` 的嵌套深度——也就是 `DynkinReeOctic.lean` docstring 里已经写对的
「一条嵌套的 `collapseAuxK` 项会在每个外层 `whnf` 上被重算」。degree-8 只是把这条曲线推到了
默认预算之外。

---

## 2. 方案：切小 + 浅合并树

### 2.1 形状

```
                                   decide +kernel（256 行，便宜）
                                            ▲
              merge₃ = collapseAuxK m₇ (collapseAuxK m₆ m₅)   ← 全 256 行表，浅
                        ▲                            ▲
        merge₂ = collapseAuxK m₄ m₃        merge₂' = collapseAuxK m₂ m₁
             ▲              ▲                    ▲            ▲
        leaf m₃        leaf m₄             leaf m₁        leaf m₂      ← 每片单独 collapse
             ▲              ▲                    ▲            ▲
        chunk₃         chunk₄              chunk₁        chunk₂        ← ≤ ~800 行，沿乘积边界切
```

* **叶子**：把八片各自沿**乘积边界**切成 ≤ ~800 行的小块（`(y⁵)₈` 35 个乘积切 5 块、
  `(y⁴)₈` 36 个乘积切 4 块、`(y⁶)₈` 21 个乘积切 3 块…），每块一条
  `def mᵢ : KTab := collapseK (smulKTab c chunkᵢ)` 加一条
  `decide +kernel` 的「mᵢ 是一行一个词」判据。切法是 `List.take`/`drop` 乘积列表 +
  一个 `rows (l : List KTab) := l.foldr (· ++ ·) []`（本轮 `chunked.lean` 已实测这条路可跑）。
* **合并**：`collapseAuxK` 从右往左合并这些 256 行表，**树形**而不是线性——树深控制在 3–4，
  每一步的两个操作数都是 256 行表，所以每一步都便宜。
* **收口**：把 `collapseK dynkin8Tab` 用 `collapseK_append` 逐块归约到树根
  （`DynkinReeSeptic.lean` 的 `evalKTab_dynkin7Tab_eq_dynkin7Norm` 那套照搬），最后一条
  `decide +kernel`。

### 2.2 为什么这样能过

* 每条 `decide` 的操作数从「3400 行」降到「≤ 800 行」，按 §1.1 的 256× 因子直接降一个量级；
* 树上每个内部节点都是**已经是一行一个词**的表，`collapseAuxK` 在两个 256 行表上展开是线性的；
* 链深被限制在 3–4 层（`chain_depth` 已经告诉我们 4 层在**有 512 行操作数**时会超时，所以
  树的每一层只合并 256 行表——这一点必须在实现时逐层复核，必要时树再宽一点、浅一点）。

### 2.3 仍要复核的三件事

1. **树深的上限**：`chain_depth` 显示 4 层带 256 行操作数在 `rfl` 上超时，但那条是 `rfl`
   （要 elaborator 直接 `whnf`），而 `decide +kernel` 走内核。实现时要量「3 层 / 4 层 / 5 层树」
   各自的墙钟，取最浅且够宽的。
2. **文件预算**：约 18–20 条 `decide`，每条 10–20 s，degree-8 文件冷编译会到 ~3–5 分钟。
   这是这条路的真实代价，写进 docstring。
3. **行的顺序不影响正确性**：切块合并得到的规范形与线性折叠的规范形**行序不同**，
   但 `dynkin8Norm_all_zero` 只要求「所有系数为零」，与行序无关，所以安全。

---

## 3. 对既有笔记的更正

`artifacts/abstractions/smallsdischarge-split.md`（已删除）§3.2 写着：

> `def lit256explicit : KTab := [ 256 行字面量 ]` → ❌ **超 200k 心跳**（`synthesize pending MVars`）

本轮实测这条**不成立**：同一份 256 行字面表在默认心跳下直接过，错的是 `maxRecDepth`
（报错文本 `maximum recursion depth has been reached` 与心跳超时是两条不同的信息）。
`DynkinReeSeptic.lean` 的 docstring 里「256 行字面表本身就超预算」的表述也应据此更正
（`DynkinReeOctic.lean` 已随 degree-8 一并删除，见 §4）。

**但这不改变结论**（切小仍然必需）：单片 3400 行的 `decide` 要 498 s，`whnf` 对链深敏感，
这两条是本轮真正测出来的墙。

---

## 4. 决定：degree-8 暂缓，本轮已撤回

**结论：degree 8 暂不做。`DynkinReeOctic.lean`、它的生成器、以及只服务它的 `T₈` 都已删除。**

说清楚这个决定的依据，因为「超 maxHeartbeats」这个说法需要一个限定：

* **这个文件从来没有编译成功过一次。** 最后一次尝试（本轮复核）得到的是 **12 条
  `unknownIdentifier`**（`dynkin8Y3a` … `dynkin8Y6c` 被前向引用，`DynkinReeOctic.lean:247-261`
  用到了 348–493 行才定义的 fragment），`maxHeartbeats` 那类报错是**次级连锁**
  （`545/575/584/588/643/664`）。同时 `FQFP/` 下 `set_option maxHeartbeats` **零命中**——
  现在这个形状里没有任何心跳 bump 可超。
* 所以「很多次尝试最终总会超过心跳」这句，准确的落点是 §1.2 那条：**`whnf` 在 4 层嵌套
  `collapseAuxK` 上超 200k 心跳**（`chain_depth` 探针，操作数全是 256 行表），根因是链深与
  「每片大 4 倍」，不是 `decide` 的心跳。§2 的浅合并树正是针对它设计的，但**树根那两条
  `decide +kernel` 的总工程量从未被测过**——因为文件没能编译到那里。
* 因此诚实的记录是：**§2 的形状在逻辑上完整、理由充分，但可行性未经验证**。不是「试了很多次
  都撞墙」，而是「还没跑到能量墙的那一步就死在结构错误上」。

### 4.1 删掉/保留的清单

| 项 | 处置 | 理由 |
|---|---|---|
| `FQFP/BCH/DynkinReeOctic.lean`（800 行，未跟踪） | **删** | 八次纯恒等式的证明，即是考不过的那部分 |
| `scripts/gen_degree8_tables.py` | **删** | 只服务该文件；且自身有两处错（§4.2） |
| `DynkinReeToolbox` 的 `bchT8`、`bchTTable 8`、`evalKTab_bchTTable_eight` | **删** | 只服务 `W8 = 2T₈ − (y²)₈`，没有第二个消费者 |
| `DynkinReeToolbox` docstring 里 `T₂ … T₈` / `… DynkinReeOctic.lean` 的措辞 | **改回** | 现在的真相是 `T₂ … T₇` |
| `BCHTerms` 的 `bchOcticTermTable` + `bchOcticTerm` + `norm_bchOcticTerm_le` | **留** | `C₈` 的**定义**与范数界，是结构层内容，不消耗任何证明预算；余项链（`bch-port.md` §3.3 的最大剩余块）需要它 |
| `WordAlgebra` 的 `evalKTab_eq_zero_of_collapseK` | **留** | 通用落地引理，只要求 `collapseK t = u` 且 `u` 全零 |

`bchOcticTerm` 留在**表形式**（`KTab`，124 行，与六次/七次同构）。它原本是
`∑ i, bchOcticTermCoeffs i • wordEval ![a, b] (bchOcticTermWords i)`（`Fin 124 → Fin 8 → Fin 2`
词数组 + `Fin 124 → ℚ` 系数数组），迁移已完成且工作树里**没有** `bchOcticTermWords` /
`bchOcticTermCoeffs` 残留。把它留着，是为了将来做余项链时不用重做这次迁移。

### 4.2 生成器本身的两处错（若重启，先修这两条）

1. **合并树的形状与 §2 相反。** `gen_degree8_tables.py:341-346` 的循环从 `names[0]` 出发逐个
   `collapseAuxK nxt cur`，产出的是**深度 16 的线性链**；而 §1.2/§2.2 的结论是每层只能合并
   两个 256 行表、树深 3–4。手写的那棵树反而是对的（逐项核对：`M1..M8` + `N1..N4` + `P1`,`P2`
   + 根 = 15 个内部节点、16 个叶子，平衡二叉树）。**不能直接跑这个生成器。**
2. **它读不出乘积序列。** `read_body(text, "y38Tab")` 期望拿到 `(…) ++ (…)` 的乘积链，但文件里
   那四张表已经被**已缩放**的 fragment 顶掉（`y38Tab := dynkin8Y3a ++ dynkin8Y3b`），
   所以它会在读取处就失败。修法是让生成器**负责整段**：按依赖顺序先发射未缩放 fragment
   （`y3a : KTab := …`）、再发射已缩放 fragment、再发射 `y38Tab := y3a ++ y3b`。

`--check` 用的静态检查本身是对的，值得保留：乘积数 21/35/35/21、每个乘积括号平衡、fragment
重组回原乘积序列、整份文件括号平衡。

---

## 5. 未完成的规格（重启时的起点）

### 5.1 degree-7 的代价记录（已删笔记里唯一有长期价值的数据）

* `octic_pure_identity` 所在的 `DynkinReeSeptic.lean`，**在定义它的模块里**类型检查要
  **33.9 s**，而 elaboration 只有 **153 ms**（`lake env lean --profile`）。把文件截到最后两条
  声明之前，41 s → 7.7 s。
* 同一段证明**从已编译模块 import 后重跑只要 1.3 s**。
* 诊断：贵的是内核在定义模块内部把整条 `collapseAuxK` 链归约出来（`dynkin7Norm_all_zero`），
  不是 tactic、也不是五条桥接引理（合计 0.7 s）。**增量折叠消掉了字面表，却把那次唯一的归约
  挪进了最紧的预算里。**

这是 degree-8 最该先量的量：§2 的形状把「一次大归约」换成「16 条 fragment 级 `decide` + 树根
1 条」，**总归约量是涨了还是跌了，没有数据**。

### 5.2 数学规格（源 `SmallSDischarge.lean:457-616`，逐字已核对）

恒等式（`W8 = 2·y_d8 − (y²)_d8`）：

    ½·W8 + ⅓·(y³)_d8 − ¼·(y⁴)_d8 + ⅕·(y⁵)_d8 − ⅙·(y⁶)_d8 + ⅐·(y⁷)_d8 − ⅛·z⁸ − C₈ = 0

其中 `z = a + b`，`C₈ = bchOcticTerm a b`，且：

| 量 | 正合分解数 | 说明 |
|---|---|---|
| `(y³)_d8` | 21 | `8 = k₁+k₂+k₃`，每个 `kᵢ ≥ 1`，按字典序，写作 `z`/`T₂…T₆` 之积 |
| `(y⁴)_d8` | 35 | 四个正部 |
| `(y⁵)_d8` | 35 | 五个正部 |
| `(y⁶)_d8` | 21 | 六个正部 |
| `(y⁷)_d8` | 7 | 七个正部 |
| `(y⁸)_d8` | 1 | **就是 `z⁸`**（`kᵢ ≥ 1` 且和为 8，八部只有全 1） |

`Tₖ` 是 `y = exp a * exp b − 1` 的 `k` 次部。`W8` 的展开式与上表六块的显式乘积都摆在
`Lean-BCH/BCH/SmallSDischarge.lean:457-616`，那条证明带源自己的
`set_option maxHeartbeats 128000000`。

### 5.3 整数化的乘子（源 `SmallSDischarge.lean:432-786`）

表上的比对必须先把 `ℚ` 系数清成整数（`ℚ` 没有内核归约；`K = 210`，`120960 | 210⁸`）。
恒等式整体乘 `lcm(1, …, 8) = 840`：

| 项 | `ℚ` 系数 | × 840 后 |
|---|---|---|
| `W8` | `1/2` | `420` |
| `(y³)_d8` | `1/3` | `280` |
| `(y⁴)_d8` | `−1/4` | `−210` |
| `(y⁵)_d8` | `1/5` | `168` |
| `(y⁶)_d8` | `−1/6` | `−140` |
| `(y⁷)_d8` | `1/7` | `120` |
| `z⁸` | `−1/8` | `−105` |
| `C₈` | `−1` | `−840` |

§2 的 16 个 fragment 就是把右侧这八个数按「3–5 个乘积一片」切开、各自带自己的整乘子得到的，
顺序为「`C₈`, `z⁸`, `(y⁷)₈`, `(y⁶)₈`×3, `(y⁵)₈`×5, `(y⁴)₈`×2, `(y³)₈`×2, `W8`」，
`W8` 在最内层（它是最大的单片）。

### 5.4 重启的顺序

1. 修 §4.2 的两条，让生成器能重新产出一份文件（或手工按 §4.2 第 2 条的依赖顺序重排）；
2. **先只编到 `evalKTab_dynkin8Tab` 为止**（16 条 `decide` 暂时注掉），确认结构层通过；
3. 再逐条量 16 条 fragment `decide` 与树根 `dynkin8Tree_all_zero` 的墙钟与峰值内存
   （§1 记录过 8.7–10.8 GB 抖动，这条要盯）；
4. 树根超预算就把树放宽（每层只合并 256 行表）；总代价超预算，就回到 §5.1 那条结论上重新设计
   ——**是「分片」还是「换表示」，这是重启时要先回答的问题**；
5. 接进构建：把四个 `DynkinRee*` 模块 import 进某个根模块，`lake build FQFP` / `runLinter` /
   `lint-style` 全绿。

---

## 6. 撤回后的验收记录

```
lake build FQFP                                   8961 jobs  ✅ 零 warning
lake build FQFP.BCH.SmallSDischarge                5 模块     ✅ 83 s（当时尚在）
lake build FQFP.BCH.DynkinReeSeptic                4 模块     ✅ 删除 SmallSDischarge 后复验
lake env lean -Dlinter.mathlibStandardSet=true     ✅ 零 warning
lake exe runLinter                                 ✅ passed（含四个 DynkinRee 模块）
lake exe lint-style                                ✅ exit 0
```

**一个坑，值得记住：`lake env lean <file>` 不会重编它的 import。** 改完 `DynkinReeToolbox.lean`
之后直接 `lake env lean DynkinReeSeptic.lean`，用的是**旧的** `.olean`——看起来「严格 lint 通过」，
实际验证的是修改前的代码。判别方法是比时间戳（源码比 `.olean` 新就是没编）。真正的验证命令是

```
lake build FQFP.BCH.DynkinReeSeptic      # 或任一 DynkinRee 模块
```

它会把四个模块从源码编一遍（83 s，其中 `DynkinReeSeptic` 42 s，与 §5.1 的画像吻合）。

`SmallSDischarge.lean` 已删除：拆分后它只剩聚合 import 与 docstring，degree-8 撤回后连聚合的对象
都没有了。这四个 `DynkinRee*` 模块因此**不在任何构建图里**，验证只能按模块名 `lake build`；
要接回根模块是另一个决定（会加编译时间）。


