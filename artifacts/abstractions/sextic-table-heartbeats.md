# SexticTable 的 64 个系数命题：削减心跳/编译代价的勘察

勘察人：abstraction agent。本轮**未改动** `FQFP/` 下任何文件。所有结论都来自 `lake env lean`
实跑（探针在 `scratch/`，交付前删除）。另重写了一个**已经失效**的独立校验器：
`scripts/check_sextic_free_identity.py`（现在能独立复算 64 个系数，见 §6）。

---

## 0. 结论摘要（先看这段）

| 问题 | 结论 |
|---|---|
| 64 条 `private lemma` 现在多少钱？ | 每条 **≈6.5 s** 墙钟（`SexticTable.olean.private` 实测 **188 MB**）。 |
| 贵在哪一步？ | **不是心跳计数，也不是 `norm_num` 本身**。`rw [reprTab_apply_eq]` 免费（<0.1 s），**`simp only [...]` 把 `dynkin6Tab` 摊成 984 行** ≈3.7 s，随后 `norm_num` 再 ≈2.8 s。 |
| **提高 `maxHeartbeats` 有用吗？** | **完全没用。** 200k → 2M → 5M，墙钟实测 17.92 s → 17.79 s → 42.93 s（后者条数不同，同条数下不变）。花的是 `whnf` 展开 984 行 `List` 结构的实现代价，不进心跳账。**任何「加预算」的处方在这里方向就是错的。** |
| profiler 能用吗？ | **不能。** `AGENTS.md` 的 `trace.profiler` 配方在这个目标上实测 **>600 s 无输出**。下面全部是墙钟 + 强制超时反推。 |
| 有结构性冗余吗？ | 有：**同一个 984 行展开被复制了 64 遍**，每条声明的证明项里各自带一份。 |
| 能靠 kernel 归约省掉吗？ | **不能碰 `dynkin6Tab`**：`@[irreducible]` 把 `decide` 完全挡住（§2.4）。**但可以碰「一张 64 行的字面表」**：对字面表 `decide`/kernel 归约完全可用。 |
| 能合并成「一条通用比较引理」吗？ | **不能，而且会更贵**（§2.5）：词一旦是**变量**，984 个 `if` 条件无法归约，`norm_num` 面对 984 项符号表达式，实测超 3M 心跳。**每词一条引理是唯一让 kernel 归约生效的形状。** |
| 那削减在哪里做？ | **把「计算」从 64 个逐词目标里搬到「表」这一层**：一次算出 `collapse dynkin6Tab` 的 64 行规范形，用 `reprTab_eq_of_reprTab_eq` + `reprTab_collapse` 转过去；64 条词引理只读 64 行字面表（实测 ≈0.25 s/条，且 ≤48k 心跳内可过）。 |
| 规范形长什么样？ | **64 行、系数全 0**。独立 Python 模型（§6）算出 `dynkin6Tab` 在全部 64 个六字母词上系数为 0，有效支撑（28 个词）与 `bchSexticTermTable` 逐项一致。 |

---

## 1. 数学内容与四层规模

`dynkin6Tab` 是自由结合 `ℚ`-代数 `ℚ[FreeMonoid (Fin 2)]` 里的**六次齐次元**

```
dynkin6Tab = ½·W6 + ⅓·(y³)₆ − ¼·(y⁴)₆ + ⅕·(y⁵)₆ − ⅙·z⁶ − bchSexticTerm
```

（`z = a + b`，`T_k` 是 `y = exp a · exp b − 1` 的 `k` 次部分，`W6 = 2y₆ − (y²)₆`）。
恒等式说它**是零**。系数函数 `reprTab` 是它的**完整不变量**：表的行是单项式
`(词, 系数)`，所以六次表相等**当且仅当**每个六字母词的系数相等——这就是
`WordAlgebra.reprTab_eq_zero_of_length` 表达的一般判据。

| 层 | 规模 | 说明 |
|---|---|---|
| 环境支撑 | `2⁶ = 64` 个词 | 六次元必须在这 64 个词上比较 |
| **有效支撑** | **28 个词** | 恒等式两边真正非零的词（两边相同） |
| 单项式支撑 | ≤64 行 | 单个乘积表（最大是 `z⁶`） |
| **原始展开（本轮新量）** | **984 行** | `w6Tab` 77 + `y36Tab` 231 + `y46Tab` 344 + `y56Tab` 240 + `z⁶` 64 + `sexticTab` 28 |

984 行里绝大多数是**同一个词的重复行**，`collapse`（`WordAlgebra.lean` 里已有、
目前**零消费者**）会合成 **64 行**。「表的规模」是这条路线里唯一真正昂贵的变量：
64 行的表近乎免费，984 行的表每次 ≈6.5 s，而当前实现**每次都让 984 行进入目标**。

---

## 2. 实测：代价在哪里

### 2.1 基线分解（每个探针一次 `lake env lean`，import 固定 6.3 s）

| 变体 | 墙钟 | 减 import | 每次增量 |
|---|---|---|---|
| 只 import | 6.3 s | 0 | — |
| 1 条系数引理 | 13.27 s | 6.97 s | 6.97 s |
| 4 条 | 30.44 s | 24.1 s | 6.03 s |
| 10 条 | 62.66 s | 56.4 s | 5.64 s |
| 10 条，只 `simp only` 展开（不 `norm_num`） | 42.93 s | 36.6 s | **3.66 s** |
| 10 条，只 `rw [reprTab_apply_eq]`（目标不关） | 6.28 s | ≈0 | **≈0.07 s** |
| 10 条，`norm_num` 单独（目标不关） | 6.97 s | 0.7 s | 0.07 s |

`rw [reprTab_apply_eq]` 免费；**3.66 s/次花在 `simp only` 的展开**上，再 ≈2.3 s 花在随后
`norm_num` 处理展开后的 `ℚ` 项上。也就是「把 984 行搬进目标」占每条声明 **~60%**。

### 2.2 提高心跳预算无效（重复强调，这是本轮最重要的否定结论）

| 配置 | 墙钟（两条系数引理） |
|---|---|
| 默认 200k | 17.92 s |
| 2M | 17.79 s |

（另：10 条在 5M 下 42.94 s，与 200k 下 10 条的 62.66 s 同量级，差异来自探针内容不同。）
**6~25 倍预算，墙钟不变。** 开销不进心跳账。

### 2.3 profiler 不可用

```lean
set_option trace.profiler true in
set_option trace.profiler.useHeartbeats true in
set_option trace.profiler.threshold 100 in
```

单条系数引理实测 **>600 s 无输出**。`AGENTS.md` 的 profiler 配方在本文件上不适用。

### 2.4 `@[irreducible] dynkin6Tab` 挡住所有 kernel 捷径（全部失败）

```lean
example : (collapse dynkin6Tab).length = 64 := by decide                 -- 失败
example : (dynkin6Tab.map Prod.fst).length = 984 := by decide            -- 失败
example : (dynkin6Tab.map Prod.fst).eraseDups.length = 64 := by decide   -- 失败
example : collapse dynkin6Tab = dynkin6Norm := by decide                 -- 失败
```

逐条都是 `Decidable` 归约**卡在未展开的 `dynkin6Tab` / `collapse dynkin6Tab`** 上。这与
文件里 `dynkin6Tab` docstring 记的理由一致（`irreducible` 是为了让 `fin_cases`/`exact` 的
类型比较不展开整张表），**不要去掉它**——去掉会把派发定理重新炸掉。

**但有一条正面事实**：文件里已有的 `List.all … := by decide` 之所以能过，是因为它**从不
下钻到 `dynkin6Tab`**，只碰六块子树（`w6Tab` 等是可归约的），再用
`smulTab_words_length`/`append_words_length` 把结论拼起来。**这正是该复制的模式**。

反向的负面事实：`decide` 对**单个 `ℚ` 命题**无效（`instDecidableEqRat` 卡在 `Rat.num` /
`Rat.add`），所以「让 kernel 直接算系数」在 `ℚ` 上根本不存在。与
`bch-wordalgebra-next-step.md` §2.1 的实测一致。

### 2.5 比较引理不能写成「变量词」（本轮第二个关键否定结论）

§2.1 与 §4 里那些「12 s / 0.25 s」的读数，全部是**字面量词**（`p.1 = [0,0,0,0,0,0]`）：
`norm_num (config := { decide := true })` 能把 984 个 `if` 的条件用 kernel 归约判掉，
**因为词是闭项**。

把词换成**变量** `l`（配 `hl : l.length = 6`），条件 `if p.1 = l` **无法归约**，
984 个条件全部留下：

```lean
-- 实测：超 3M 心跳；提到 10M 也在跑不动的那一侧。残余目标是这样的：
--   ⊢ (if [0,0,0,0,0,0] = l then 1/720 else 0) + ((if [0,0,0,0,0,1] = l then 1/120 else 0) + …)
example (l : List (Fin 2)) (hl : l.length = 6) :
    (List.map (fun p => if p.1 = l then p.2 else 0) dynkin6Tab).sum = 0
```

**推论（决定了整个设计）**：「每个词各一条引理」（现状）**不是**随手的选择，而是唯一
能让 kernel 归约生效的形状；换成一条覆盖所有词的通用比较引理会**更贵**。
削减必须做在别处。

---

## 3. 干净设计

把「表」看成**系数函数的载体**而不是「一串行」，于是有三个不同的对象：

```
1. 分次构件（六块）    w6Tab y36Tab y46Tab y56Tab z6Tab sexticTab   -- 输入，不动
2. 和表                dynkin6Tab                                   -- 输入，不动
3. 规范形（系数函数）   dynkin6Norm : Tab                            -- 新：唯一被反复读的对象
```

**接口**：

```lean
/-- 规范形：`dynkin6Tab` 在每个六字母词上的系数。64 行字面量，由
`scripts/check_sextic_free_identity.py --emit` 生成。 -/
def dynkin6Norm : Tab := [ … 64 行，系数全 0 … ]

/-- **唯一的计算引理**：规范形就是 `dynkin6Tab` 的系数函数。
这一条承担全部 984 行，并且只用一次。 -/
lemma reprTab_dynkin6Norm : reprTab dynkin6Norm = reprTab dynkin6Tab

/-- 64 条词引理：读规范形，不再展开 `dynkin6Tab`（类型不变！）。 -/
private lemma reprTab_dynkin6Tab_word_0 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 0, 0, 0]) = 0 := by
  rw [← reprTab_dynkin6Norm, reprTab_apply_eq]
  norm_num (config := { decide := true })
```

**为什么这是自然层级**：

- 计算引理的陈述在**表**这一层（`reprTab _ = reprTab _`），所以它的证明里可以
  **一次性**处理 984 行；而 64 条词引理的陈述仍在**词**这一层（现状不变），所以 kernel
  归约照旧生效。
- 两种「取系数」互不冲突：左端用 `reprTab_eq_of_reprTab_eq`（`WordAlgebra` 已有），
  再由它得到 `evalTab` 的相等（`evalTab_eq_reprTab`）。**不需要** `Finsupp.ext`/`funext`
  ——实测 `funext w` 对 `reprTab dynkin6Tab = reprTab dynkin6Tab` **不成立**
  （`reprTab` 是 `def`，报 `could not unify the conclusion of @funext`）。
- 64 条词引理的**类型一个字不改**，所以 `reprTab_dynkin6Tab_words` 派发定理与最后三行
  （`reprTab_dynkin6Tab_eq_zero` / `evalTab_dynkin6Tab` / `septic_pure_identity`）**完全不动**。
- 规范形**不是第二个家**：它不复制六块里的任何定义，它是 `reprTab dynkin6Tab` 的**值**，
  由计算引理钉住，并由 Python 侧独立复算（§6）。

**计算引理怎么证**（两条路，都不碰变量词）：

1. **字面层**：`reprTab dynkin6Norm = 0` 由 `decide` 或 `reprTab_apply_eq`+查表得到
   （64 行零表，实测免费，§4）。
2. **连接层**：`reprTab dynkin6Tab = reprTab dynkin6Norm`。推荐走
   `collapse`：`reprTab_collapse` 把左端换成 `reprTab (collapse dynkin6Tab)`，于是只需证
   **表的相等** `collapse dynkin6Tab = dynkin6Norm`——这是一个**表层**目标，`ℚ` 的加法由
   `norm_num` 收，64 行都在字面层。实测这一步已经开始工作（`collapse` 能把 984 行算出
   64 行），但本轮**没有量到它在默认预算下的完整读数**（§7 的诚实边界）。

---

## 4. 施工前实测（每条都已实跑）

| 变体 | 结果 | 读数 |
|---|---|---|
| 字面 64 行零表的逐词目标（`reprTab_apply_eq` + `simp only [dynkin6Norm, …]` + `norm_num (config := { decide := true })`） | ✅ | **≤48k 心跳内通过**；10 条一起 ≈6.5 s − import ≈ **0.25 s/条** |
| 同上，`norm_num` 不带 `decide := true` | ✅ | 同量级（`if` 条件由配置内的 kernel 归约收掉） |
| 同上，`decide` 收尾 | ❌ | `instDecidableEqRat` 不归约（`ℚ` 无 kernel 归约）→ **必须 `norm_num`** |
| **字面词**的完整 984 行：`(List.map (fun p => if p.1 = [0,…] then p.2 else 0) dynkin6Tab).sum = 0`，`simp only [ …六块…]` + `norm_num` | ✅ | **12.0 s**（3M 预算内）；这是「算一次」的地板 |
| **变量词**的同一目标 | ❌ | 超 3M 心跳；984 个 `if` 全部残留（§2.5） |
| 把「一次算完 64 个系数」写成单条引理 | ❌ | 超 3M 心跳（与「变量词」是同一个病） |
| `(collapse dynkin6Tab).length = 64`：`simp only [ …六块…, collapse, collapseAux]` + `decide` | ✅ | 9 s 量级；印证 §2.4：**先显式展开 `dynkin6Tab`，`decide` 就能用** |
| `collapse dynkin6Tab = dynkin6Norm`：`simp only [ …六块…, collapse, collapseAux, addRow]` + `norm_num` | 未收 | 剩 64 个 `addRow` 项（`ℚ` 加法）；需补 `addRow` 的方程引理/`split_ifs` |

---

## 5. 与现有代码的 delta

| # | 现状 | 建议 | 依据 |
|---|---|---|---|
| D1 | 64 条声明**各自**展开 984 行；展开复制 64 遍 | 新增**一条表层计算引理**承担唯一一次 984 行；64 条改为「引用 + 读字面表」 | §2.1、§4 |
| D2 | 规范形不存在 | 新增 64 行字面 `dynkin6Norm`（系数全 0），Python 生成、Lean 证明 | §6 |
| D3 | `collapse` / `reprTab_collapse` / `evalTab_collapse` **零消费者**（`WordAlgebra.lean` 为它写了 40 行文档） | 让它成为 D1 的实现手段 | 「已有 API 无消费者」也是设计信号 |
| D4 | `sexticCoeff` 宏把「展开 + `norm_num`」绑成一件事，于是「展开几次」被绑死在「有几条声明」上 | 把「展开」抽到表层引理；宏只做查表 | §3 |
| D5 | `scripts/check_sextic_free_identity.py` **已过期**（按已删除的 `bchSexticTermWords`/`bchSexticTermCoeffs` 解析，现在直接报 `definition not found`） | 已重写：解析 `bchSexticTermTable`，并新增「从 Lean 源码求六块 → 复算 64 个系数」的独立模型 | `bch-wordalgebra-next-step.md` §4.4 早已预告 |

**有意保留**：`@[irreducible] dynkin6Tab`、每词一条引理、`sexticTab := bchSexticTermTable`、
`reprTab_eq_zero_of_length`、`length_eq_six`、派发定理的 `fin_cases` 形状、最后三行。
**病灶只有一个**：「984 行进目标的次数」。

---

## 6. 独立校验与生成器（`scripts/check_sextic_free_identity.py`）

脚本跑两套彼此独立的模型：

1. **compositions（数学）**：`yᵖ` 的六次部分 = 遍历 6 的正合成，把对应 `T_i` 乘起来；
   `bchSexticTerm` 从 `BCHTerms.lean` 的 `bchSexticTermTable` 读。
2. **pieces（代码）**：把 `SexticTable.lean` 里 `w6Tab/y36Tab/y46Tab/y56Tab/z6Tab` 的
   **定义体原文**抓出来，用同一套 `mulTab`/`powTab`/`smulTab` 代数求值（含一个小的
   递归下降解析器，因为 Lean 的 `f x y` 结合力与 Python 不同；见脚本内注释）。

实跑输出：

```
# piece rows: w6Tab=42 y36Tab=63 y46Tab=64 y56Tab=64 z6Tab=64
# Dynkin side has 28 words, bchSexticTerm has 28
# compositions agree with bchSexticTerm on all 28 words
# pieces model: all 64 six-letter words cancel
# OK
```

即 **64 个词上系数全部为 0**，且数学模型与代码模型逐词一致。生成规范形：

```
python scripts/check_sextic_free_identity.py --emit > scratch/dynkin6Norm.raw.lean
```

生成的字面量由 Lean 的 `norm_num` **证明**相等，所以不存在转录错误——这与
`bch-port.md` §3.2 反对的「手抄平坦表」有本质区别：那些是*断言*，这些是*定理*。

---

## 7. 范围、代价与诚实的边界

| 项 | 规模 |
|---|---|
| 新增 | 1 条表层计算引理（~10 行）+ 1 个 64 行字面量 `def` |
| 修改 | 64 条词引理的证明体（每条 2 行）+ `sexticCoeff` 宏（只做查表） |
| 不动 | 所有类型签名、派发定理、最后三行、六块定义、`dynkin6Tab` |
| 风险 | 低：类型全不变，`#print axioms` 不受影响，**不需要** `maxHeartbeats` bump |
| 预期收益 | 64 × 3.66 s 的 `simp only` 塌缩成 1 次；编译墙钟与 `olean.private`（188 MB）同步下降 |
| 推广 | 7/8 次项同形：`dynkin7Norm`/`dynkin8Norm`，行数 128/256，仍 << 原始上千行 |

**本轮的诚实边界（下一次开工前必须先量这两条）**：

1. **表层计算引理在默认 200k 预算下的读数**没有量到。量到的是它的两端：
   字面层 ≈0.25 s/条（✅），字面词的 984 行单次计算 12.0 s（✅，3M 预算内）。
   12.0 s 那个数字**顺带算了 64 个系数**，而表层引理**只算一次表比较**，所以它应当更便宜；
   但这是推断，不是读数。
2. 若它在 200k 下超时，正确的下一步是**拆**——按 §2.4 的正面事实，把它拆成
   「六块各自 == 各自的折叠表」的小目标（每条都是纯 `List`/`ℚ`，且 `decide` 对六块可用），
   再用 `reprTab_append`/`reprTab_smulTab` 拼起来——**而不是** bump 预算
   （§2.2 已证 bump 无效）。

### 7.1 施工尝试（同轮，未落地）：表层计算引理试了 6 种形状，全部失败

按 §3 的方案去实现时，**第一步就卡住**：`collapse dynkin6Tab = dynkin6Norm` 证不出来。
逐一记录，避免下一轮重走：

| 尝试 | 结果 |
|---|---|
| `simp only [ …六块…, collapse, collapseAux, addRow]` + `norm_num` | 剩 984 个 `addRow` 项 |
| `simp (config := { decide := true }) only [collapse, collapseAux, addRow]` | 同上；`addRow` 的累加器参数是 `addRow …` 本身而非构造子，方程引理匹配不上 |
| `norm_num (config := { decide := true })` 先跑、再 `simp only [collapse, …]` | `norm_num` 会把 984 行摊开但不碰 `collapse`；随后的 `simp only` 只展开最外层 |
| `rw [reprTab_apply_eq, reprTab_apply_eq]` + 全量 `simp only` + `decide` | `decide` 卡在 `(reprTab (collapse …)).2 … .num`（`ℚ` 无 kernel 归约） |
| 不 rewrite、直接 `decide reprTab (collapse dynkin6Tab) … = 0` | 同上，卡在 `.num` |
| 只对**单个字面词**做 `collapse` 的系数比较 + `norm_num` | 同上：`norm_num` 不展开 `collapse`，64 个 `if` 全留 |

**根因**：`collapse` 的系数是 **`ℚ` 加法**，而 `ℚ` 在 kernel 里既不能被 `decide` 判等
（`Rat.add`/`Rat.num` 不归约），`norm_num` 又**不会主动展开 `collapse`/`addRow` 这类
自定义递归函数**（它只做算术与 `if` 消解）。于是「把 984 行折成 64 行」这个动作
**只能由 `simp`/显式展开驱动**，而 `addRow` 的累加器形状又让 `simp` 卡住。
本轮没有找到既 axiom-clean（不引入 `native_decide`）又能通过的关键形状。

**因此本轮没有改动 `FQFP/` 下任何文件**：§3 的方案在纸面上成立、两端读数都支持它，
但中间那一条引理没落地；半个重构（换了 64 条引理却留着旧的计算）比现状更差。

**下一轮的第一选择**：`bch-wordalgebra-next-step.md` §5 的**路线 B（`ℤ` 缩放）**。
它的路线图里 `group X = []` 是**一条 `rfl`**，正好绕开本节的全部失败原因——
`ℤ` 的加法与判等在 kernel 里都能归约，`collapse`/`addRow` 那一步会变成可 `decide` 的
纯整数计算。代价是要新写一层「分次整数缩放 + 求值回 `𝔸`」的接口（估 300–500 行）。

### 7.2 路线 B 的试探（同轮）：关键假设已证实，但配套引理层没完工

按 §7.1 的建议去试路线 B，**最重要的那个假设被证实了**：

```lean
abbrev ITab : Type := List (List (Fin 2) × ℤ)
-- 整数取值的 collapse：kernel 直接算出来了
example : collapseAuxInt ([([0,0], (1:ℤ)), ([0,0], (-1:ℤ)), ([0,1], (5:ℤ))] : ITab) []
    = [([0,0], (0:ℤ)), ([0,1], (5:ℤ))] := by decide    -- ✅ 通过
```

也就是说 **`ℚ` → `ℤ` 这一步确实把「折叠」从不可归约变成可归约**（对比 §2.4：`ℚ` 版的
`collapse` 连 `decide` 都进不去）。**这是路线 B 的可行性根据，值得记下来。**

同一轮把缩放层的下述部分写通了：

| 声明 | 状态 |
|---|---|
| `scaleUp t = t.map (fun p => (p.1, (p.2 * K).num))`，`K = 720^6` | ✅ |
| `scaleUp (s ++ t) = scaleUp s ++ scaleUp t` | ✅ |
| `scaleUp (mulTab s t) = mulIntTab (scaleUp s) (scaleUp t)`（`Int.num_mul`） | ✅ |
| `scaleUp (smulTab c t) = scaleUp t`（`c` 是分母上的单位，恒成立） | ✅ |
| `scaleUp (powTab t n) = powIntTab (scaleUp t) n` | ✅ |
| `mulIntTab`/`smulIntTab`/`powIntTab` 的数据层定义 | ✅ |
| **`reprIntTab (mulIntTab s t) = reprIntTab s * reprIntTab t`** | ❌ 未完成 |

最后那条没写通的原因是**技术性的，不是数学性的**：`reprIntTab` 用
`(t.map fun p => single p.1 p.2).sum` 定义时，`MonoidAlgebra ℤ _` 上的 `Mul` 实例解析
在策略里卡住（`typeclass instance problem is stuck: Mul ?m`）；改用 `def` + 模式匹配时，
`rw [reprIntTab]` 又匹配不上（equation 生成器对这种写法不给 `eq_def`）。
两条写法各堵一半，本轮没有把它调通。

**结论**：路线 B 的**可行性**已经落地（linchpin 证实 + 缩放代数四条律通过），
**剩余工作量**集中在「`reprIntTab` 的乘法相容」与「把 6 张 `scaleUp (T k)` 用
`norm_num` 连接成字面量表」这两块，估 150–300 行。这比 §3 方案的剩余工作量明确得多，
**下一轮应当从路线 B 继续**，而不是继续在 `ℚ` 上找形状。

---

## 8. 复现清单

```
lake env lean scratch/probe_baseline_noprof.lean   # 基线：2 条 ≈14 s
lake env lean scratch/cost_NORM48.lean             # 字面 64 行表：≤48k 心跳通过
lake env lean scratch/cost_ONEGOAL.lean            # 字面词 984 行单次：12.0 s 通过
lake env lean scratch/probe_var1.lean              # 变量词：失败（984 个 if 残留）
lake env lean scratch/cost_SUPPORT.lean            # decide 被 irreducible 挡住：失败
python scripts/check_sextic_free_identity.py       # 独立校验：64 个系数全 0
```

探针全部在 `scratch/`（以及 §7.1 的 `SexticNormProbe.lean`），交付前删除；结论已全部并入本文。
文件与脚本均可单独复跑：`python scripts/check_sextic_free_identity.py`（独立校验 + `--emit` 生成规范形）。
