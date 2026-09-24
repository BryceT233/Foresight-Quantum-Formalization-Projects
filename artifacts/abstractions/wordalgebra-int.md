# `ℚ` → `ℤ`：`WordAlgebra` 整数表层的勘察、设计与实测

勘察人：abstraction agent。本轮**改动了 `FQFP.lean` 一行**（把 `SexticTable` 从伞里剔除，见 §0bis），
其余全部结论来自 `lake env lean` 实跑（探针在 `scratch/`，交付前删除）。

本轮要回答的问题：**`artifacts/bch-wordalgebra-next-step.md` §5 的「路线 B」（用 `ℤ` 取代 `ℚ`）
到底能不能让 `decide` 把 degree-6 恒等式算掉、从而削减编译时间？** 结论是**能，而且比预期的更强**；
但 degree-7/8 撞的是另一堵墙（心跳，不是 `ℚ`），需要按「合成项」而不是「整块」切分。

---

## 0. 结论摘要

| 问题 | 结论 |
|---|---|
| `lake build FQFP` 会编译未被 import 的模块吗？ | **不会。** 实测：在 `FQFP/BCH/` 放一个没人 import 的 `ZZBuildProbe.lean`，`lake build FQFP` 不生成它的 olean。所以从伞里删掉一行**确实**把它移出默认构建（§0bis）。 |
| `SexticTable` 值多少钱？ | **冷编译 147 s**（`lake build FQFP.BCH.SexticTable` 实测），`olean.private` **188 MB**。 |
| `ℤ` 取代 `ℚ` 之后，degree-6 恒等式怎么证？ | **一条 `rfl`。** 整张 984 行的表在 kernel 里折成 64 行、系数全 0（§4，实测）。 |
| 代价？ | 检查一次 ≈**11 s**（加上 import/定义 ≈17 s 一个文件），`maxRecDepth ≥ 5000`（现行 `SexticTable.lean` 已经在用 100000）。**不需要** `maxHeartbeats` bump。 |
| 标度怎么取？ | 用**词长**承载标度：一行 `(w, c)` 表示 `(c / K ^ w.length) • w`，`K = 210 = 2·3·5·7`。这样乘法自动相容，**不需要**分次指标（§3）。 |
| 有理系数 ½…⅙ 怎么办？ | **先乘穿**：`dynkin_d` 的标量是 `1/2 … 1/d`，先乘 `L = lcm(1..d)` 变成整数 30/20/-15/12/-10/-60，再做 `K`-标度。这一步是上一轮 probe 失败的根因（§3.2）。 |
| 上一轮卡住的 `reprIntTab (mulIntTab s t) = …`？ | **绕开 `Finsupp` 就完成了**：直接在 `MonoidAlgebra` 里做，`scratch/ktab_api.lean`（≈140 行）**零错误编译通过**（§5）。 |
| degree-7/8 呢？ | 数学上**成立**（独立复算：degree-7 有效支撑 126、degree-8 124，与源里的项数完全一致）；one-shot kernel 检查**超 200k 心跳**；按「每块一个目标」切分后 **degree-7 通过**（最大块 1040 行），**degree-8 仍有 3 个最大块（3400/2928/2241 行）超时**，需要再切一层（§4.3、§7）。 |

---

## 0bis 本轮已落地的改动

`FQFP.lean`：删掉 `public import FQFP.BCH.SexticTable`，原位留一段说明为什么。

验收（实跑）：

| 命令 | 结果 |
|---|---|
| `lake build FQFP`（删 import + 删 `SexticTable.*` olean 后） | **25.3 s**，`SexticTable olean rebuilt? False` |
| `lake build FQFP.BCH.SexticTable`（冷） | 147 s（这就是被移出的代价） |

`SexticTable.lean` 是**叶子**：全树只有 `FQFP.lean` import 它，`septic_pure_identity` 也**零消费者**
（`SmallSDischarge.lean` 只在注释里提到它）。所以剔除是安全的，而且 `scripts/lint-style.lean`
按**目录**枚举模块（`modulesUnder "FQFP"`），仍然会给它做 style 检查。

**这一步只是临时措施。** 下文的迁移落地之后 `SexticTable` 已经装回伞里（§0ter）。

---

## 0ter 施工记录：`ℚ` → `ℤ` 迁移**已落地**

用户拍板：**表的唯一之家取 `ℤ`**、**不保留 `MonoidAlgebra ℚ (FreeMonoid (Fin 2))` 这一层**。
本轮按此实施完毕，四个文件 + 一个脚本。

### 落地内容

| 文件 | 改动 |
|---|---|
| `FQFP/BCH/WordAlgebra.lean` | **重写**：`KTab`/`evalKTab`/`ratTab` + `mulKTab`/`smulKTab`/`powKTab`/`collapseK` 与全部相容引理（≈240 行）。删掉了整个 `ℚ` 表层：`wordAlgebraLift`、`freeGen`、`mono`、`evalTab`、`reprTab`、`coeff_*`、`Tab`、`FreeMonoid` 相关，共约 450 行。不再 import `MonoidAlgebra` / `FreeMonoidInstances`。 |
| `FQFP/BCH/BCHTerms.lean` | `bchSexticTermTable : KTab`（28 行整数字面量）；`bchSexticTerm a b := evalKTab a b bchSexticTermTable`；`norm_bchSexticTerm_le` 改走 `ratTab`（`WordExpansion.lean` **一行未改**，它的范数引理本来就是裸类型 `List (List (Fin 2) × ℚ)`）。 |
| `FQFP/BCH/SexticTable.lean` | **重写**（757 → 304 行）：`T : (k : ℕ) → KTab`、六块表、六个 `evalKTab_*` 桥、`dynkin6Tab`、**一条 `decide`** 收掉整个系数比对。删掉 64 条 `reprTab_dynkin6Tab_word_*`、`reprTab_dynkin6Tab_words`、`length_eq_six`、`reprTab_eq_zero_of_length`、`sexticCoeff` 宏、`@[irreducible] dynkin6Tab`、`maxRecDepth 100000`。 |
| `FQFP/BCH/FreeMonoidInstances.lean` | 现在**无人 import**（它服务的正是被删掉的那一层）。文件与文档保留（两个 `FreeMonoid` 实例是独立的 Mathlib 空缺），docstring 加了 `## Status` 一节说明；仍在伞里，照常构建与 lint。 |
| `scripts/check_sextic_free_identity.py` | 解析改成整数字面量 + `mulKTab`/`powKTab`/`smulKTab`，独立模型换上 `×60` 的整数标量；删掉已无对应物的 `--emit`（`dynkin6Norm` 不再存在）。实跑仍通过。 |

### 验收（全部实跑）

| 项 | 结果 |
|---|---|
| `lake build FQFP`（伞里含 `SexticTable`） | ✅ |
| `lake exe runLinter FQFP` | ✅ `Linting passed for FQFP` |
| `lake exe lint-style` | ✅ exit 0 |
| `#print axioms septic_pure_identity` | `[propext, Classical.choice, Quot.sound]` ✅（无 `native_decide`） |
| `#print axioms collapseK_dynkin6Tab_all_zero` | `[propext]` ✅ |

### 收益（实测）

| 量 | 迁移前（`ℚ`） | 迁移后（`ℤ`） |
|---|---|---|
| `SexticTable` 冷编译 | **147 s** | **11.2 s**（`touch` 后经伞重建） |
| `SexticTable.olean.private` | **188 MB** | **0.87 MB** |
| degree-6 系数比对的声明数 | 64 条 `private lemma` + 1 条派发 + 1 条判据 | **1 条 `decide`** |
| `maxRecDepth` | 100000（文件级） | **10000**（单条声明局部） |
| `maxHeartbeats` | 未 bump | 未 bump |
| `SexticTable.lean` 行数 | 757 | 304 |

### 施工中发现的形状（写下来供 7/8 次项复用）

1. **T 桥的配方**（`evalKTab a b (T k) = bchT k a b`）：
   `rw [T, bchT k]` → `simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons,
   List.sum_nil, add_zero, List.prod_cons, List.prod_nil, mul_one, pow_succ, mul_assoc]` →
   `norm_num` → `abel`。`pow_succ` + `mul_assoc` 把 `bch` 侧的 `a ^ n` 右结合化，
   与 `List.prod` 的形状对齐；`norm_num` 负责 `K`-因子与有理系数的相消。`k = 1` 不需要后两步。
2. **块桥的配方**（`evalKTab a b w6Tab = bchW6 a b`）：
   `simp only [<块定义>, bch*, bchZ, evalKTab_append, evalKTab_smulKTab, evalKTab_mulKTab]` →
   `simp only [evalKTab_T1, …, evalKTab_T6, bchZ]` → `simp only [smul_add, smul_smul]` →
   `norm_num` → `abel`。
   **`y36Tab`/`y46Tab`/`y56Tab` 只用到前两行**——因为 T 桥已经把 `K`-因子消掉，
   两边逐字相同，`simp only` 直接以 `rfl` 收尾。别照抄多出来的 `smul_add, smul_smul; norm_num`：
   那会报 "No goals to be solved"（本轮的实测）。
3. **`dynkin6Tab` 的标量账**：`evalKTab_smulKTab` 之后左端是 `Σ (c:ℚ) • …`，右端是
   `60 • (½•… + …)`；用一条 `show … from by module` 把右端归一成左端形状，再 `norm_num; abel`。
4. **`60 • x = 0 → x = 0`**：`smul_eq_zero.mp` + `norm_num` 排除 `60 = 0`。
5. **`dynkin6Tab` 不要标 `irreducible`**：旧文件标它是因为 64 条引理的类型比较会反复展开整张表；
   现在只有一条 `decide` 需要展开它，标上反而挡住 `decide`。

---

## 0quater 施工记录（第 2 步：合并 `SexticTable` 进 `SmallSDischarge` + 重构 degree-5 恒等式）

用户的两条指令：**把 `SexticTable.lean` 融合进 `SmallSDischarge.lean`**；
**重构 `sextic_pure_identity`**（勘察后确认指的是 **degree-5** 那条：`SmallSDischarge:153` 的
`sextic_pure_identity` 证的是 degree 5，degree 6 那条叫 `septic_pure_identity`；
这个差一位的名字**是源项目的**——`Lean-BCH/BCH/SmallSDischarge.lean:104` 的 `sextic_pure_identity`
定义 `T₂,T₃,T₄,W5`，`:162` 的 `septic_pure_identity` 定义到 `T₅`，所以按「源是唯一真理」保留原名）。

### 合并

| 项 | 处理 |
|---|---|
| `FQFP/BCH/SexticTable.lean` | **删除**（304 行），内容并入 `SmallSDischarge.lean` |
| 伞 `FQFP.lean` | 删掉 `public import FQFP.BCH.SexticTable` |
| 命名空间 | `FQFP.BCH.SexticTable` → `FQFP.BCH` |
| 表格 `T` | → **`bchTTable`**（与环级的 `bchT2 … bchT5` 区分） |
| T 桥 | `evalKTab_T1 … _T6` → **`evalKTab_bchTTable_one … _six`** |
| 六块表/桥 | `w6Tab`/`y36Tab`/`y46Tab`/`y56Tab`/`z6Tab`/`sexticTab` 及其 `evalKTab_*` 名字不变 |
| 新增 import | `SmallSDischarge` 现在 import `FQFP.BCH.WordAlgebra`（无环：`WordAlgebra` 只依赖 Mathlib） |

`bchTTable` 现在放在环级工具箱之后，degree-4/5/6 三条恒等式共用它——这也正是当初必须分文件的原因
（`SexticTable` 需要用这里的 `bchZ`/`bchT k`，于是只能反过来 import）。

### degree-5 恒等式的重构

原来：`simp only [<展开 30 个单项式>]; noncomm_ring; module`。
现在与 degree-6 完全同形：

| 新增声明 | 内容 |
|---|---|
| `w5Tab` / `y35Tab` / `y45Tab` / `z5Tab` | `bchW5` / `bchY35` / `bchY45` / `bchZ^5` 的整数表 |
| `bchQuinticTermTable`（**在 `BCHTerms.lean`**） | **30 行字面量**：`bchQuinticTerm` 的四个 `Finset.sum` 组按 `-K⁵/720, K⁵/180, -K⁵/120, K⁵/30` 铺开（由 `scratch/gen_quintic_table.py` 从 `bchQuinticGroup*Words` 生成）。放在 `bchQuinticTerm` **旁边**，与 `bchSexticTermTable`/`bchSexticTerm` 同一规则：**数据住在它所定义的项的家**。 |
| `evalKTab_{w5Tab,y35Tab,y45Tab,z5Tab}` | 四条桥（在 `SmallSDischarge`） |
| `evalKTab_bchQuinticTermTable` | 第五条桥（**在 `BCHTerms.lean`**，紧邻表格） |
| `dynkin5Tab` | `30w5 + 20y35 − 15y45 + 12z5 − 60·quintic`（即 `60 ×` 左端） |
| `evalKTab_dynkin5Tab` / `collapseK_dynkin5Tab_all_zero` / `evalKTab_dynkin5Tab_eq_zero` | 与 degree-6 同形的三条 |
| `sextic_pure_identity` | 陈述**一字未改**，证明换成「表格为零 → 除以 60」 |

**degree-5 的表规模**：`dynkin5Tab` 原始 **310 行** → 折叠成 **32 行**（= `2^5`，满支撑）。
degree-6 仍是 984 → 64。两条 `decide` 都不是空真：`z5Tab`/`z6Tab` 单独折叠后并非全零（负向对照）。

### 一条经验（写下来给 7/8 复用）

`evalKTab_quinticTab` 的桥**不再需要 `noncomm_ring`**：只要 `simp only` 里补上
`List.length_cons, List.length_nil`（`evalKTab` 里有 `(K:ℚ) ^ p.1.length`），
系数相消由 `norm_num` 承担，最后 `module` 归一。用 `noncomm_ring` 反而会失败——
它把系数交给 `ring`，而 `ring` 证不出 `↑(-1 • 567236250) * 210⁻¹ ^ 5 = -1/720`。
另外 `evalKTab_w5Tab` 需要把环级 `bchT5` 加进 simp 集：`bchW5` 把 `2·T₅` **写成显式幂**，
而表侧给出的是 `2 • bchT5 a b`；反过来 `bchT2/bchT3/bchT4` **不能**展开，
因为 `bchW5` 里它们出现在乘积中，展开会引入需要分配的乘积。

### 验收

| 项 | 结果 |
|---|---|
| `lake build FQFP` | ✅（合并文件经伞重建 **11 s**） |
| `lake exe runLinter FQFP` / `lake exe lint-style` | ✅ / exit 0 |
| `SmallSDischarge.olean.private` | 2.62 MB |
| `#print axioms sextic_pure_identity`（degree 5） | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms septic_pure_identity`（degree 6） | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms collapseK_dynkin5Tab_all_zero` | `[propext]` |
| 非空真 | `collapseK dynkin5Tab` = 32 行，`collapseK dynkin6Tab` = 64 行 |

**7/8 的模板已经就位**：`bchTTable`（共享）+ 每度的分块表 + `dynkinDTab` + 一条 `decide`。
按度-7/8 的实测（§4.2），degree-7 需要把 `decide` 按「块」切分，degree-8 还要再切到「合成项」。

### degree-7 第 1 步（已做）：项的数据换成表

勘察时发现 degree-7/8 与 degree-5 **相反**、与 degree-6 **相同**：

| | `bchSepticTermWords/Coeffs`（d=7） | `bchOcticTermWords/Coeffs`（d=8） | `bchQuinticGroup*`（d=5） |
|---|---|---|---|
| 家外的消费者 | **0** | **0** | `QuinticRemainder` 89 / `QuinticTaylor2` 68 |
| 结论 | 表**取代**数组 | 表可以取代 | 表只能**追加** |

`norm_bchSepticTerm_le` / `norm_bchOcticTerm_le` 在全树也**零消费者**，所以它们改走 `ratTab`
不会影响任何下游。

已落地（`BCHTerms.lean`）：`bchSepticTermWords` + `bchSepticTermCoeffs` → **`bchSepticTermTable`**
（126 行，由 `scratch/gen_septic_table.py` 从源数组生成并校验：126 个字互异、恰好是非纯 7 字母字）；
`bchSepticTerm a b := evalKTab a b bchSepticTermTable`；`norm_bchSepticTerm_le` 改走 `ratTab`。
验收：`lake build FQFP` ✅、`runLinter` ✅、`lint-style` exit 0 ✅、
`#print axioms norm_bchSepticTerm_le` = 三条标准公理；`bchSepticTermTable` 实检
`length = 126`、`eraseDups.length = 126`、全为 7 字母。

**这消掉了 degree-7 最大的一个风险**：源把 `bchSepticTerm` 写成 `Fin 126` 上的 `∑`；
若保留数组、只加一张表，桥就得把 126 项 `∑` 展开成单项式，很可能撞心跳。
改成「表即定义」之后 `bchSepticTerm` 与表逐字相同，桥是 `rfl`，**根本不需要展开**。

**剩余（degree-7 第 2 步，未做）**：`bchTTable` 补 `k = 7`；环级 `bchW7`、`bchY37`、`bchY47`、
`bchY57`、`bchY67`（照源 `octic_pure_identity` 的形状）；它们的表与桥；`dynkin7Tab`；
`octic_pure_identity`（源名）。唯一的新问题仍是**心跳**：one-shot `decide` 在 degree-7 超 200k，
要按「块」切分（§4.2 已验证可行，最大块 1040 行）。

### degree-7 第 2 步（已做）：恒等式 + 按块切分的系数比对

同一提交里落地：`bchTTable 7`；环级 `bchT6`/`bchT7`（`bchW6` 顺势改成 `2 • bchT6 a b - …`，
degree-6 的 `y₆` 从此只有一个家）；`bchW7`、`bchY37`、`bchY47`、`bchY57`、`bchY67`
（= 源的 `octic_pure_identity` 里 `W7` 与 `y3_7 … y6_7`，按 7 的正合成字典序，连续 1 段收成 `z^k`）；
它们的 `KTab` 与桥；`dynkin7Tab`；`octic_pure_identity`。清分母用 `L = lcm(1..7) = 420`
（乘子 `210, 140, −105, 84, −70, 60, −420`）。

**切分（本轮唯一的新技术点）**：one-shot `decide` 在 degree-7 超 200k 心跳，所以
**按块切分**——七块各自在**自己的目标**里 `rfl` 折成字面规范形（`collapseK_w7Tab` …），
再把折叠后的表拼成 `dynkin7Norm`（822 行），最后一条 `decide` 折它（128 行）。
两块都是 **`List` 事实**，所以切分是**可靠的**：规范形作为数据为零 ⇒ 它在**任意** `𝔸` 里求值为零。
（这一点排除了「逐字系数」路线：那条需要自由代数的线性无关性，在任意 `𝔸` 里是**假**的。）

验收：`octic_pure_identity` / `collapseK_dynkin7Norm_all_zero` 的 `#print axioms` 分别是
三条标准公理 / `[propext]`；`collapseK dynkin7Norm` = **128 行**（满支撑，非空真），
`dynkin7Norm` = 822 行，负向对照 `z7Tab` 单独折叠后非全零。

**代价（要记住）**：`SmallSDischarge.lean` 现在的冷编译约 **115 s**（degree-7 之前约 20 s）。
主要来自七条 `rfl` 规范形（最大块 1040 行）与那条 `decide`。文件也涨到 ~1620 行（约 850 行是
生成的字面规范形）。如果嫌贵，可选：把规范形拆到单独文件（只在需要时构建），或把字面表换成
「按合成项」再细一层的切分（degree-8 反正必须这么做）。

### 与源 `SmallSDischarge.lean` 的差距（实查）

源文件 80 条声明，我们 95 条（多出来的是表基建），其中 **76 条源声明在本树没有对应物**。
本文件**只有纯恒等式这一半**：

| 家族 | 源 | 本树 |
|---|---|---|
| `quintic_pure_identity(_cleared)` / `sextic_` / `septic_` / `octic_`（degree 4/5/6/7） | ✅ | ✅ |
| `nonic_pure_identity`（degree 8） | ✅ | ❌ |
| `pow{n}_sub_zpow{n}_telescope`（n=3..8）与 `norm_pow{n}_…_le` | ✅ | ❌ |
| `y{m}_sub_z{m}_sub_…_decomp` 整梯 + 其 `norm_*` | ✅ | ❌ |
| `I1/I2_residual_decomp_eq`（含 septic/octic/nonic 变体）与 `norm_I*` | ✅ | ❌ |
| `R_eq_neg_deg5_residual` / `R_plus_T5_…` 四代 | ✅ | ❌ |
| `norm_bch_{quintic,sextic,septic,octic}_remainder_large_s_le` | ✅ | ❌ |
| `pieceB_{sextic,septic,octic,nonic}_decomp` | ✅ | ❌（只在注释里被引用） |

也就是说：**纯恒等式是「代数」的一半，剩下那半是「余项记账」**——`y^m − z^m` 的逐度望远镜分解
与残差范数界，里面才出现 `RCLike 𝕂` / `Real.exp` / `Real.log`。我们下面每一条 `*_pure_identity`
都是那些定理的**输入**，而它们目前都还没有消费者。

### `bchQuinticTermTable` 上移到 `BCHTerms.lean`；以及 degree-5 的旧结果**不能**被取代

用户提出：`quinticTab` 该不该放进 `BCHTerms.lean`？5 次的旧结果该不该都被它取代？

**前半：应该，已做。** 表格是项的*数据*，规则与 degree-6 完全一致
（`bchSexticTermTable` 就住在 `bchSexticTerm` 旁边）。改名 `quinticTab` → **`bchQuinticTermTable`**，
连同桥 `evalKTab_bchQuinticTermTable` 一起搬进 `BCHTerms.lean` 的 `bchQuinticTerm` 之后；
`SmallSDischarge` 只保留四条分块桥。`BCHTerms` 本来就 import `WordAlgebra`，没有新增依赖。

**后半：不能，而且一条都不能删。** 与 degree-6 的区别在**消费者**：

| | degree-6 的旧数据 | degree-5 的旧数据 |
|---|---|---|
| 旧形式 | `bchSexticTermWords : Fin 28 → Fin 6 → Fin 2` + `bchSexticTermCoeffs : Fin 28 → ℚ` | 四个 `bchQuinticGroup*Words : Fin m → Fin 5 → Fin 2` + `bchQuinticGroup*`（`Finset.sum`）+ `bchQuinticTerm` |
| 消费者 | **只有 `bchSexticTerm` 自己** | `QuinticRemainder.lean`（`bchQuinticGroup` 89 处）、`QuinticTaylor2.lean`（68 处）、`bchQuinticTerm_smul`、四条 `norm_bchQuinticGroup*_le` |
| 结论 | 表**取代**数组（现已全树零引用） | 表是**追加**，不是替代 |

三条硬约束（实测的，不是推测）：

1. **`bchQuinticTerm` 不能改写成 `evalKTab a b bchQuinticTermTable`**：
   `QuinticTaylor2.bchQuinticTerm_eq_bracket` 是一条 **`rfl` 见证**，断言
   `bchQuinticTerm a b = (720)⁻¹ • bchQuinticBracket (G1) (G4) (G6) (G24)`
   ——它依赖 `bchQuinticTerm` 的定义**就是**那个四组加权组合。改成表格求值会让这条 `rfl` 失效。
2. **`bchQuinticGroup*Words` 必须保留 `Fin m → Fin 5 → Fin 2` 的形状**：
   `QuinticRemainder` 的 `card_sum_bchQuinticGroup*Words`（按位置数 `0` 的个数：10/25/35/…）与
   `norm_sum_binWord_diff_le (v := bchQuinticGroup*Words)` 都是**按位置索引**的。
   表格是 `List (List (Fin 2) × ℤ)`，没有位置索引。
3. **四条 `norm_bchQuinticGroup*_le` 与四组结构本身有数学内容**：
   权重 `-1, +4, -6, +24` 正好是四组的系数，`QuinticTaylor2.norm_bchQuinticSubsetPiece_le` 的
   `hc1/hc4/hc6/hc24` 假设块把 4/10/14/2 四个组大小写死。表化会丢掉这层分解。

因此 degree-5 与 degree-6 的**不对称是有意的**，理由写在 `bchQuinticTermTable` 的 docstring 里，
以免下一轮误以为是漏做。要真正统一，得先回答一个更大的问题
（`bch-wordalgebra-next-step.md` §4.3 已列）：是保留四组、还是把 `QuinticTaylor2`/`QuinticRemainder`
整套换成 `List` 索引版范数原语。那是独立的一步，不在本轮的「重构 degree-5 恒等式」范围内。

### degree-3 / degree-4 能不能按同样的方法重做？——不能（3），不必（4）

勘察结论（`scratch/cubic_quartic_tables.py` 实算）：

| | `bchCubicTerm` | `bchQuarticTerm` |
|---|---|---|
| 定义形式 | **闭式括号式** `(1/12)([a,[a,b]] + [b,[b,a]])` | **闭式括号式** `-(1/24)[b,[a,[a,b]]]` |
| 展开成字表 | 6 个字（`2^3` 中的 6 个），系数 `-1/6, 1/12` | 4 个字（`2^4` 中的 4 个），系数 `±1/12, ±1/24` |
| 消去恒等式 | **没有**（本 port 的 `*_pure_identity` 从 degree 4 起） | 有：`quintic_pure_identity`（degree 4） |
| 恒等式现在怎么证 | —— | `unfold bchQuarticTerm; simp only […]; module`，**不需要任何 bump** |
| 字表/组数据的消费者 | 只有 `bchCubicTerm` 自己 | 只有 `bchQuarticTerm` 自己 |

**为什么 5/6 值得、3/4 不值得**：5/6 的表是**数据**——degree-6 的旧 `bchSexticTermWords/Coeffs`
（`Fin 28 → Fin 6 → Fin 2` + 系数数组）**零外部消费者**，degree-5 的四个组位数组是**范数/余项界
的索引对象**。3/4 的项本来就是**闭式括号式**，展开成 6/4 个字是**派生**的，没有任何东西消费它；
给它配一张表就是「派生数据的第二个家」，正是 abstraction 规则反对的形状。

**两条不能动的边界**：

1. **`bchCubicTerm` / `bchQuarticTerm` 的定义不能改成表。** 括号式是论文的形式，而且
   `bchCubicTerm_smul`、`bchCubicTerm_LQ_decomp`、`bchQuarticTerm_LQ_decomp`、`norm_*_le`
   都是**按括号结构**写的。这与 degree-6 的情形正相反：那里的旧数组形式没有任何结构消费者，
   所以表可以**取代**它。
2. **`quintic_pure_identity_cleared` 永远进不了表格路线**：它陈述在裸 `[Ring 𝔸]` 上
   （标量是 `Nat` 值，刻意不用 `ℚ`），而 `evalKTab` 需要 `[Algebra ℚ 𝔸]`。
   所以即使把 degree-4 的 `quintic_pure_identity` 表化，家族里仍会留一条非表的证明，
   「完全统一」本来就达不到。

**建议**：degree-3 什么都不做；degree-4 的 `quintic_pure_identity` 可以表化，
但收益**只有家族一致性，编译时间是零收益**（现证不需要 bump），代价约 120 行
（`T₄`、`(y²)₄`、`(y³)₄`、`z⁴` 四张分块表 + `bchQuarticTermTable` 4 行 + 五条桥 + `dynkin4Tab` + 一条 `decide`）。
7/8 的模板已经由 degree-5/6 验证过，不需要靠 degree-4 做练习。

---

## 1. 数学内容

`FreeMonoid (Fin 2)` 上的自由结合代数 `ℚ⟨a, b⟩ ≅ ℚ[FreeMonoid (Fin 2)]`。令
`y = exp a · exp b − 1 = Σ_{k≥1} T_k`，其中 `T_k = Σ_{n=0}^{k} aⁿb^(k−n)/(n!(k−n)!)`。
由 `log(1 + y) = Σ_{k≥1} (−1)^{k+1} y^k / k` 与 BCH 的级数展开，

> **degree-`d` 恒等式**：`Σ_{k=1}^{d} (−1)^{k+1}/k · (y^k)_d = bch⟨d⟩Term`（`(·)_d` 取 `d` 次齐次部分）。

- `d = 6` 时左端即 `½W6 + ⅓y3₆ − ¼y4₆ + ⅕y5₆ − ⅙z⁶`（因为 `½W6 = y₆ − ½(y²)₆`），右端是
  `bchSexticTerm` —— 这正是 `SexticTable.lean` 证的那条。
- `d = 7, 8` 的右端分别是 `bchSepticTerm`（126 项）、`bchOcticTerm`（124 项），**尚未形式化**。

这是一条**纯恒等式**：它只用到自由代数的结合律与 `ℚ` 的域运算，跟范数、完备性、`𝔸` 都无关。
所以它应当被「在数据层算掉」，而不是被「在环层用 `noncomm_ring` 展开」——`bch-port.md` §3.3quater
里 1.0e9 / 8.2e9 的心跳就是后者。

**齐次性与支撑**：degree-`d` 的元只落在长度为 `d` 的字上，共 `2^d` 个（`d=6,7,8` 时为 64/128/256）。
`dynkin_d` 的**有效支撑**（真正非零的字）恰好等于右端的项数：**28 / 126 / 124**（§4 实测），
但 `(y^k)_d` 的单项式是满支撑，所以**比较坐标系必须是 `2^d`**，不能用 28/126/124 去缩小范围。

---

## 2. 为什么 `ℚ` 不行、`ℤ` 行

### 2.1 kernel 归约的边界（沿用并复核上一轮的实测）

| 命题 | `rfl` / `decide` | 说明 |
|---|---|---|
| `(2 : ℚ) * 3 = 6` | ✗ | `Rat` 的运算不归约 |
| `decide ((1:ℚ)/2 = 2/4) = true` | ✗ | `instDecidableEqRat` 卡在 `Rat.num` / `Rat.add` |
| `(2 : ℤ) * 3 = 6` | ✓ | |
| `List.filter (fun z : ℤ => z ≠ 0) [1, 0, 2] = [1, 2]` | ✓ | `ℤ` 的加/乘/判等**全部** kernel 可归约 |
| `List (Fin 2)` 的相等 | ✓ | 词相等由结构递归判定 |

所以「把 984 行折成 64 行、看系数是不是 0」这个动作，在 `ℚ` 上根本不存在可归约的引擎
（`norm_num` 是唯一的引擎，而它一次只吃小表达式）；在 `ℤ` 上它就是一个纯数据结构计算。

### 2.2 但 `ℤ` 只是必要条件，不是充分条件：**心跳墙仍然在**

`rfl` 的归约发生在 elaborator 的 `isDefEq`/`whnf` 里，**是要记心跳的**（这一点与
`sextic-table-heartbeats.md` §2.2「bump 无效」的结论不矛盾：那里 bump 无效是因为大头在
`simp only` 把 984 行搬进目标，而那是**项构造**的代价）。实测边界：

| 规模 | 一条目标能不能过默认 200k 心跳 |
|---|---|
| `d=6`：984 行 × 64 支撑 | **能**（≈11 s） |
| `d=7`：3390 行 × 128 支撑 | **不能** |
| `d=7`：切到「每块一个目标」，最大块 1040 行 | **能** |
| `d=8`：切到「每块一个目标」，最大块 3400 / 2928 / 2241 行 | **不能**（其余块能） |

**经验阈值：一条目标的原始展开 ≈1000–2000 行以内。**

---

## 3. 干净设计

### 3.1 从数学出发的对象

「表」是**系数函数的载体**：`KTab := List (List (Fin 2) × ℤ)`，一行 `(w, c)` 代表
`(c / K ^ |w|) • w`。

**为什么标度用词长而不是一个分次字段**：两个标度表相乘时，系数相乘、
词相接——只要 `K ^ |l₁ ++ l₂| = K ^ |l₁| · K ^ |l₂|`（即 `List.length_append` + `pow_add`），
乘法就自动相容。**标度不是额外的数据结构，它内蕴在词里**，所以不需要 `d` 指标、
不需要齐次性不变量、也不需要任何校验。这是本设计里最省事的一点。

`K = 210 = 2·3·5·7`：`K^d` 整除 degree-`d` 表出现的**所有**分母
（`T_d` 的 `1/d!`、`bchSexticTermTable` 的 `1440`、septic 的 `30240`、octic 的 `120960`，
在 `d ≤ 8` 时都整除 `K^d`；生成器里有断言）。

### 3.2 有理标量必须先乘穿（**上一轮 probe 失败的根因**）

`dynkin_d` 的标量是 `½, ⅓, …, 1/d`。它们**不能**在 `K`-标度之后施加：`K`-标度后的
`z⁶` 表系数是 `K⁶`，再乘 `K⁶/6` 就会得到 `K¹²`-标度（本轮的第一个 probe 就是这么错的，
表现为「折叠后 28 个非零」）。

正确顺序是：**先把整条恒等式乘穿 `L = lcm(1..d)`**，标量变成整数，再做 `K`-标度。

```
dynkin_d = Σ_{k=1}^{d} (−1)^{k+1}/k · (y^k)_d − bch⟨d⟩Term
L · dynkin_d = Σ_{k=1}^{d} (−1)^{k+1}·(L/k) · (y^k)_d − L · bch⟨d⟩Term
```

`d = 6`：`L = 60`，标量 `30, −20, 20, −15, 12, −10, −60`；
`d = 7`：`L = 420`；`d = 8`：`L = 840`。

于是**表层的标量全是整数**，`smulKTab : ℤ → KTab → KTab` 就够了。

### 3.3 类型层次与签名

```
KTab := List (List (Fin 2) × ℤ)                    -- 唯一的表类型（ℤ 值，词长标度）

evalKTab : KTab → MonoidAlgebra ℚ (FreeMonoid (Fin 2))   -- 表的「意义」
  --  Σ p, (p.2 / K ^ p.1.length) • of (ofList p.1)

unitKTab : KTab
mulKTab  : KTab → KTab → KTab           -- 词相接、整数系数相乘
smulKTab : ℤ → KTab → KTab              -- 只有整数标量
powKTab  : KTab → ℕ → KTab
addRowK  : (List (Fin 2) × ℤ) → KTab → KTab
collapseAuxK / collapseK : KTab → … → KTab -- 支撑规范化（一词一行）
```

相容引理（**§5 已全部实跑通过**）：

```lean
evalKTab_append     : evalKTab (s ++ t) = evalKTab s + evalKTab t
evalKTab_mulKTab    : evalKTab (mulKTab s t) = evalKTab s * evalKTab t
evalKTab_smulKTab   : evalKTab (smulKTab c t) = (c : ℚ) • evalKTab t
evalKTab_powKTab    : evalKTab (powKTab t n) = evalKTab t ^ n
evalKTab_collapseK  : evalKTab (collapseK t) = evalKTab t
evalKTab_eq_zero_of_all_beq :
    t.all (fun p => p.2 == 0) = true → evalKTab t = 0
```

连接层（小目标，`d ≤ 8`）：

```lean
TK : (k : ℕ) → KTab                    -- T_k 的整数表，1/(n!(k−n)!) → K^k/(n!(k−n)!)
evalKTab_TK : evalKTab (TK k) = bchT k (mono [0] 1) (mono [1] 1)     -- k = 1 … d 各自一条
-- 六块（degree 6）：w6I y36I y46I y56I z6I sexticI，各自的 evalKTab = bchW6 / bchY36 / …
```

主定理的形状（degree 6）：

```lean
theorem evalKTab_dynkin6I : evalKTab dynkin6I = 0        -- dynkin6I = 60 · dynkin6（见表）
theorem dynkin6_eq_zero : (½•bchW6 + … − bchSexticTerm) = 0
  -- 由 `60 • x = 0 → x = 0`（ℚ-模里 60 可逆）得到
theorem septic_pure_identity {𝔸} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : … = 0
  -- 同现行证明：rw [← wordAlgebraLift_dynkin6, …, map_zero]
```

---

## 4. 实测读数

### 4.1 degree-6：一条 `rfl` 收掉整条恒等式

探针 `scratch/int_probe.lean`（生成器 `scratch/gen_int_probe.py`），
六块表**逐字**镜像 `SexticTable.lean` 的定义，只是系数换成 `K⁶ × 有理系数`：

```
#eval (dynkin6I.map Prod.fst).length   →  984      -- 与 ℚ 版完全一致
#eval (collapseI dynkin6I).length      →   64
example : (collapseI dynkin6I).length = 64 := by decide                          ✓
example : (collapseI dynkin6I).all (fun p => p.2 == 0) = true := by decide       ✓
example : List.filter (fun p => p.2 ≠ 0) (collapseI dynkin6I) = [] := rfl        ✓
example : (collapseI z6I).all (fun p => p.2 == 0) = false := by decide           ✓（非空检查）
```

| 变体 | 墙钟 |
|---|---|
| 只放定义（import + 展开数据） | 6.1 s |
| 定义 + 一条 `rfl`，**Lean 默认 `maxRecDepth`** | 6.1 s，**失败**：`maximum recursion depth` |
| 定义 + 一条 `rfl`，`maxRecDepth 5000` | 17.0 s ✓ |
| 定义 + 一条 `rfl`，`maxRecDepth 20000` / `100000` | 16.8 s / 16.7 s ✓ |

也就是说：**检查本身的代价 ≈11 s**，而 `maxRecDepth` 的墙与 `ℚ` 版是**同一堵**
（现行 `SexticTable.lean` 已经在用 `set_option maxRecDepth 100000`），
5000 就够、且**不需要**任何 `maxHeartbeats`。

对照现行实现：**SexticTable 冷编译 147 s、64 条系数引理各 ≈6.5 s、`olean.private` 188 MB**
（见 `sextic-table-heartbeats.md` §2.1）。**预期收益 ≈6–9×，且 `.olean.private` 应降到很小
（整条证明就是一个 `rfl`，不再有 64 份 984 行展开）。**

### 4.2 degree-7/8：数学成立，一条目标不够

生成器 `scratch/gen_int_deg.py` 用**真实数据**（从 `BCHTerms.lean` 解析 `bchSepticTermWords/Coeffs`、
`bchOcticTermWords/Coeffs`）建表：

```
#eval (lhsI.map Prod.fst).length   d=6:   984   d=7:  3390   d=8: 11268
#eval (collapseI lhsI).length      d=6:    64   d=7:   128   d=8:   256
```

| 度 | one-shot（一条 `rfl`/`decide`） | 按「每块 `(y^k)_d` 一个目标」切分 |
|---|---|---|
| 6 | ✓（≈11 s） | ✓ |
| 7 | ✗ 超 200k 心跳 | **✓ 全部通过**（19 个检查，整文件 134 s） |
| 8 | ✗ 超 200k 心跳 | ✗：`y⁴/y⁵/y⁶` 三块（2241/3400/2928 行）仍超时，其余通过 |

逐块的原始行数（`scratch/sizes.py`）：

```
d=6: y1:7   y2:70   y3:231  y4:344  y5:240  y6:64
d=7: y1:8   y2:104  y3:456  y4:952  y5:1040 y6:576  y7:128
d=8: y1:9   y2:147  y3:819  y4:2241 y5:3400 y6:2928 y7:1344 y8:256
```

阈值与 §2.2 一致：**1040 行过，2241 行不过**。所以 degree-8 需要把「块」再切到
**合成项**（每个 `mulTab` 链 ≤128/256 行）一层（§7）。

**顺带得到一个独立校验**：`dynkin_d` 的有效支撑在 `d = 6, 7, 8` 时为 **28 / 126 / 124**，
与 `bchSexticTerm` / `bchSepticTerm` / `bchOcticTerm` 的项数**逐一吻合**，
并且两边在全部 `2^d` 个字上系数相等（`scratch/degrees.py`）。degree-7/8 的恒等式
（尚未形式化）在数值上已被独立确认。

### 4.3 `decide` 与 `rfl` 等价，纯 kernel 也需要 `maxRecDepth`

`decide` 与 `rfl` 在本问题上是同一条归约（`decide` 多一层 `of_decide_eq_true`）。
「纯 kernel 就不受 `maxRecDepth` 限制」是**错的**——`rfl` 的 `isDefEq` 同样受它约束（§4.1）。

---

## 5. 上一轮卡点的实测破除：`KTab` 的 API 层

`sextic-table-heartbeats.md` §7.2 记录：`reprIntTab (mulIntTab s t) = reprIntTab s * reprIntTab t`
没写通，原因是 `Finsupp`/`MonoidAlgebra ℤ` 上的 `Mul` 实例解析卡住。
**绕开 `Finsupp` 之后这道墙不存在**：在 `MonoidAlgebra` 里、用与现行有理层**同样的归纳**，
`scratch/ktab_api.lean`（≈140 行）**零错误编译通过**，包含：

`rat_div_mul_div`、`kmono_add`、`kmono_mul`、`evalKTab_{nil,cons,append}`、
`evalKTab_mul_single`、`evalKTab_mulKTab`、`evalKTab_smulKTab`、`evalKTab_singleton`、
`evalKTab_unitKTab`、`evalKTab_powKTab`、`evalKTab_addRowK`、`evalKTab_collapseAuxK`、
`evalKTab_collapseK`、`evalKTab_eq_zero_of_rows`、`evalKTab_eq_zero_of_all_beq`。

关键一步只有一处用到 `K`：

```lean
lemma rat_div_mul_div (c₁ c₂ : ℤ) (a b : ℕ) :
    (c₁ : ℚ) / (K : ℚ) ^ a * ((c₂ : ℚ) / (K : ℚ) ^ b)
      = ((c₁ * c₂ : ℤ) : ℚ) / (K : ℚ) ^ (a + b) := by
  rw [div_mul_div_comm, ← pow_add, Int.cast_mul]
```

`evalKTab_addRowK` 的合并分支需要 `Int.cast_add` + `add_div` + `kmono_add`（`add_smul`）；
`evalKTab_smulKTab` 需要 `smul_smul` + `Int.cast_mul` + `mul_div_assoc`。
**这就是全部的技术含量**——没有 bridge code，没有实例 hack。

---

## 6. 与现有代码的 delta

先量清楚：**`WordAlgebra.lean` 的表层在全树的消费者只有两个文件。**

| 声明 | 消费者（除 `WordAlgebra.lean` 自身） |
|---|---|
| `Tab`（类型） | `BCHTerms.lean:586`（`bchSexticTermTable`）、`SexticTable.lean` |
| `evalTab` | `BCHTerms.lean:800`、`SexticTable.lean` |
| `wordAlgebraLift` | `BCHTerms.lean:797/800`、`SexticTable.lean` |
| `mono` `mulTab` `smulTab` `powTab` `collapse` `reprTab` `freeGen` `coeff_mono*` | **只有 `SexticTable.lean`** |

也就是说：**除了 `bchSexticTerm` 的定义与它的范数界，整个 `ℚ` 表层只服务于 `SexticTable.lean`**，
而那个文件正是要被重写的。`WordExpansion.lean` 的 `norm_sum_smul_binTab_le` 用的是**裸类型**
`List (List (Fin 2) × ℚ)`（不是 `Tab`），且 `WordExpansion.lean` **不 import `WordAlgebra.lean`**，
所以它**不需要改**——只需要一个把 `KTab` 变成 `List (List (Fin 2) × ℚ)` 的重标度函数。

| # | 现状 | 建议 | 依据 |
|---|---|---|---|
| D1 | `Tab := List (List (Fin 2) × ℚ)`，系数不可 kernel 归约 | 换成 `KTab := List (List (Fin 2) × ℤ)`（词长标度），**是表的唯一之家** | §2.1、§3.1 |
| D2 | `bchSexticTermTable : Tab`（28 行有理字面量） | 改成整数字面量 `: KTab`；有理数据由 `KTab.toRat`（`c ↦ c/K^\|w\|`）**导出** | 「一个对象一个家」；`norm_num` 28 行即可证 `toRat` 的取值 |
| D3 | `bchSexticTerm a b := wordAlgebraLift a b (evalTab …)` | `:= wordAlgebraLift a b (evalKTab …)`（同形） | 接口不变 |
| D4 | `norm_bchSexticTerm_le` 用 `(bchSexticTermTable.map ‖·‖).sum ≤ 1` | 同一句，作用于 `bchSexticTermTable.toRat` | `WordExpansion` 的引理是裸类型，不用改 |
| D5 | `WordAlgebra.lean` 的 `ℚ` 表层（`mono`/`evalTab`/`reprTab`/`coeff_*`/`evalTab_*`/`collapse`/…，约 450 行） | 删掉，换成 `KTab` 层（≈200 行，§5 已跑通） | 唯一消费者是 `SexticTable.lean` |
| D6 | `SexticTable.lean`：`T`、六块、64 条 `private` 系数引理 + `sexticCoeff` 宏 + `@[irreducible] dynkin6Tab` + `maxRecDepth 100000` | 重写：六块改成 `KTab` 整数表；64 条引理**整体删除**，换成「逐块 `rfl` + 一次 `decide`」；`maxRecDepth` 降到 5000 即可 | §4.1 |
| D7 | `scripts/check_sextic_free_identity.py` 解析 `bchSexticTermTable` 的**有理**字面量 | 改成解析整数字面量（该脚本已被上一轮改过一次，这次同样要跟） | §8 |

**有意保留**：`wordAlgebraLift`（自由代数的泛性质，是「表 → `𝔸`」的唯一通道）、
`wordAlgebraLift_mono`、六块的 `evalTab_*` 桥的形状、`septic_pure_identity` 的陈述与证明收尾。

**明确删掉**：64 条 `reprTab_dynkin6Tab_word_*`、`reprTab_dynkin6Tab_words`、
`length_eq_six`、`reprTab_eq_zero_of_length`、`@[irreducible] dynkin6Tab`、
`set_option maxRecDepth 100000`、`mono_sq/mono_cube/…/smul_mono_eq/ofList_pair`。
**没有任何一条会变成「需要新写的等价物」**——它们全部是被 `rfl` 取代的计算脚手架。

---

## 7. 范围、代价与风险

| 项 | 估值 |
|---|---|
| 新增 | `WordAlgebra.lean` 的 `KTab` 层 ≈200 行（§5 的探针已是它的草稿） |
| 修改 | `BCHTerms.lean`：`bchSexticTermTable`（28 行数据）+ `bchSexticTerm` + 1 行范数证明 |
| 重写 | `SexticTable.lean`：757 行 → 估 200 行（数据 + 桥 + 一条 `rfl`） |
| 删除 | `WordAlgebra.lean` 的 `ℚ` 表层（≈450 行）、`SexticTable.lean` 的 64 条引理 |
| 脚本 | `scripts/check_sextic_free_identity.py` 的解析 |
| 预期收益 | `SexticTable` 147 s → **≈20 s**；`olean.private` 188 MB → 预计 ≪ 10 MB；`FQFP.lean` 可以**把 `SexticTable` 装回去** |
| 风险 | **低**：`maxHeartbeats` 不 bump；`maxRecDepth` 只需 5000（现行 100000）；`#print axioms` 不变（无 `native_decide`） |

**两个决策（已由用户拍板，并在 §0ter 落地）**：

1. **表的唯一之家 = `ℤ`**（上文的 (a)）：`KTab` 是数据的家，有理数据由 `ratTab` 导出
   （施工时用的名字是 `ratTab`，不是 `toRat`）。`norm_bchSexticTerm_le` 因此走
   `ratTab bchSexticTermTable` + 原有的 `norm_sum_smul_binTab_le`，`WordExpansion.lean` 一行未改。
2. **不保留 `MonoidAlgebra ℚ (FreeMonoid (Fin 2))`**（上文的 (b)）：`evalKTab a b : KTab → 𝔸`
   直接落在目标代数里，`wordAlgebraLift` 与整个自由代数层被删除。恒等式的证明链条变成
   「数据层一条 `decide` → `evalKTab_collapseK` → `evalKTab_eq_zero_of_all_beq`」，
   不再经过 `map_zero`。

**忠实性边界（施工时守住的线）**：把 ℚ 系数**数据**换成 ℤ 系数数据是**同一元素的换一种呈现**
（元素是 `(1/K^|w|) •` 整数表），不是弱化。因此
`bchSexticTerm`、`norm_bchSexticTerm_le`、`septic_pure_identity` 的**陈述一字未改**，
论文里的分母 `1440` 只是搬到了 `ratTab` 与范数界那一侧。`#print axioms` 也仍只有三条标准公理。

**degree-7/8 的后续路线**（本轮只做到「知道墙在哪」）：
把切分单位从「块 `(y^k)_d`」降到「**合成项**」——每个 `mulKTab` 链的原始表 ≤ `2^d` 行，
逐个折成**固定字序的满 `2^d` 行字面量表**（§3 的「环境支撑」），
然后整条恒等式就是这些满表按整数标量相加，一次 `decide`。
按 `d = 8` 的数据（最大块 3400 行、64 个合成项）估计每步 ≤10^5 次整数运算，**远在预算内**。
`WordAlgebra.lean` 的 `K` 是唯一需要跟着改的常数（`d ≤ 8` 时 `K = 210` 够用）。

---

## 8. 复现清单

```
python scratch/gen_int_probe.py                  # degree-6 探针
lake env lean scratch/int_probe.lean             # 一条 rfl：✓（含 maxRecDepth 5000 的对照）
python scratch/gen_int_deg.py 6 7 8              # 真实数据的 degree-6/7/8 探针
lake env lean scratch/int_deg6.lean              # ✓；deg7/deg8 超心跳（这就是墙）
python scratch/gen_int_split.py 6 7 8            # 按块切分
lake env lean scratch/int_split7.lean            # ✓（deg8 仍有 3 块超时）
lake env lean scratch/ktab_api.lean              # KTab API 全通过（≈140 行）
python scratch/model_check.py                    # 有理/整数模型逐字一致，且都相消
python scratch/degrees.py                        # degree 6/7/8 独立复算：28 / 126 / 124
python scratch/sizes.py                          # 逐块原始行数
python scripts/check_sextic_free_identity.py     # 独立校验器（已改指整数表，仍通过）
lake build FQFP                                  # 全树冷编译 86.7 s
```

`scratch/` 里保留的是**可复用的生成器与独立校验器**：`ktab_api.lean`（新 `WordAlgebra` 整数层
的草稿，已搬进 `FQFP/BCH/WordAlgebra.lean`）、`gen_int_deg.py` / `gen_int_split.py`
（degree-7/8 的生成器雏形）、`gen_int_probe.py`、`model_check.py`、`degrees.py`、`sizes.py`，
以及产出库里字面量的三个生成器 `gen_quintic_table.py`、`gen_septic_table.py`、`gen_deg7.py` +
`gen_deg7_norms.py`。一次性的诊断探针（`int_*.lean`、`bridge_probe.lean`、`axioms.lean`、
`dbg.py`、`cmp.py`、`mkvariants.py`）在迁移落地后已删除。

**`scratch/` 全部不进版本库**（`.gitignore` 里有 `/scratch/`）：本文所有 `scratch/...` 路径都是
**当前工作副本**里的文件，fresh clone 里没有。`scratch/` 也不在 `FQFP/` 下，既不进构建也不进
`lint-style`（后者按 `FQFP`/`_spike` 两个目录枚举模块）。因此**库里那批生成的字面量**
（`bchQuinticTermTable`、`bchSepticTermTable`、degree-7 的环级件/表/规范形）在仓库内没有生成脚本，
只有本文记录的算法；要重生成得先照本节把脚本写回来。

---

## 9. 一句话回答用户的问题

**「用 `ℤ` 取代 `ℚ` 能不能用 `decide` 归约、从而加速命题编译？」——能，而且不是小幅加速，
本轮已经落地（§0ter）：**

- degree-6 恒等式的**全部 984 行计算 + 64 个系数比较**塌缩成**一条 `decide`**：
  `SexticTable` 147 s → **11.2 s**，`.olean.private` 188 MB → **0.87 MB**，
  文件 757 → 304 行；
- 全树冷编译 **86.7 s**（迁移前仅 `SexticTable` 一个文件就要 147 s），
  所以 `SexticTable` 已经**装回伞里**，不再需要 §0bis 那个临时剔除；
- `maxHeartbeats` 不用碰，`maxRecDepth` 10000 就够（原 100000）；
- 上一轮卡住的 API 层（`reprIntTab` 的乘法相容）**绕开 `Finsupp` 后跑通**，
  并且按用户的决定**整个自由代数层被删除**——`evalKTab a b : KTab → 𝔸` 直接落在目标代数里；
- `bchSexticTerm` / `norm_bchSexticTerm_le` / `septic_pure_identity` 的**陈述一字未改**，
  `#print axioms` 仍是三条标准公理；
- degree-7/8 数学上同样成立（有效支撑 126/124，与源里项数逐一吻合），
  但需要把 kernel 检查按**合成项**切分——这是「下一步」而不是「不可行」。
