# 用 `wordAlgebraLift` + 系数函数重构 `BCHTerms.lean`：下一步勘察

勘察人：abstraction agent。本轮**未改动 `FQFP/` 下任何文件**；所有结论都来自 `lake env lean`
实跑（探针在 `scratch/`，结论保留后即删）。本轮也纠正了 `artifacts/bch-port.md` 与
`SmallSDischarge.lean` 里几处**已经过期**的说法。

---

## 0. 结论摘要（先看这段）

| 问题 | 结论 |
|---|---|
| 当前树里唯一的 `sorry` 在哪？ | `SmallSDischarge.lean:210`，即 degree-6 的 `septic_pure_identity`。`lake build FQFP` 成功，只有这一条警告。**它就是下一步。** |
| `WordAlgebra.lean` 现在能直接用吗？ | **不能。** 它没有任何 **`𝔸` 值**的求值引理，也没有 `+`/`⊗` 与系数函数的相容引理；`wordAlgebraLift` 在全树**零消费者**。这一层目前是孤岛。 |
| 为什么不能在 `ℚ` 上直接算？ | **`ℚ` 完全没有 kernel 归约**（实测 `example : (2:ℚ) * 3 = 6 := rfl` 失败）。所以「算完再看是不是空表」在 `ℚ` 上不可能；`norm_num` 是唯一引擎，而它在**单个 ~1300 项的 `ℚ` 和**上就超 200k 心跳。 |
| 那 `ℤ` 呢？ | **`ℤ` 可以 kernel 归约**（`(2:ℤ)*3 = 6 := rfl`、`List.filter (· ≠ 0) [1,0,2] = [1,2] := rfl` 都过）。这是战略备选（§5 路线 B）。 |
| 支撑集该选多大？ | **degree-6 的 64 个字**。实测：整个 Dynkin 侧的有效支撑**恰好 28 个字**（与 `bchSexticTerm` 相同），但 `z⁶` 一类单项式是满支撑，所以**比较所需的最小充分支撑是 64**；而**每个单项式自己的表都 ≤ 64 行**（最大是 `z⁶` 的 64 行）——这正是「分组/支撑」应当钉在哪一级。 |
| 下一步该怎么做？ | ① 先补 `WordAlgebra` 的桥（§4.1，小、零风险）；② 再按**「逐单项式规范化 + 逐字比对」**证 `septic_pure_identity`（§4.2）；③ 然后才谈 `BCHTerms` 的表重构（§4.3）。 |

---

## 0bis 施工记录（§4.1「补桥」已完成）

`FQFP/BCH/WordAlgebra.lean`（+92/−59）、`FQFP/BCH/SexticTable.lean`、`FQFP/BCH/FreeMonoidInstances.lean`。
验收：`lake build FQFP`（仅剩 `SmallSDischarge.lean:201` 那条**既有**的 `sorry` 警告）、
`lake exe runLinter FQFP`、`lake exe lint-style` 全绿；五条新声明的
`#print axioms` 都只剩 `[propext, Classical.choice, Quot.sound]`。

| 声明 | 内容 |
|---|---|
| `Tab`（`abbrev Tab : Type := List (List (Fin 2) × ℚ)`） | 表的**唯一之家**，从 `SexticTable.lean` 上移；本文件内 16 处手写的 `List (List (Fin 2) × ℚ)` 全部改用它 |
| `wordAlgebraLift_mono` | `wordAlgebraLift a b (mono l q) = q • (l.map ![a,b]).prod`——**𝔸 值求值的桥**；`l = [0]/[1]`、`q = 1` 即两个生成元 |
| `wordAlgebraLift_evalTab` | `wordAlgebraLift a b (evalTab t) = (t.map fun p => p.2 • (p.1.map ![a,b]).prod).sum` |
| `reprTab_append` | `reprTab (s ++ t) = reprTab s + reprTab t`（纯 `List` 归纳，不经过 `MonoidAlgebra`） |
| `reprTab_eq_coeff` | `reprTab t = (evalTab t).coeff` |
| `reprTab_smulTab` | `reprTab (smulTab c t) = c • reprTab t` |

同时：删掉 `wordAlgebraLift_injective` 及其两个 `private` 依赖（`freeGenerators`、
`wordAlgebraLift_free_eq_symm`）与随之失去用途的 `import Mathlib.Algebra.FreeAlgebra`；
`SexticTable.T` 补上 `| 6 => …`（7 行，`1/(n!(6−n)!)`）；模块文档里补了「`ℚ` 无 kernel 归约」
与「正向传输不需要单射」两段实测说明。冒烟测试（`wordAlgebraLift a b (evalTab (T 1)) = a + b`
从 `SexticTable.T_one` 转过来、`reprTab` 的加性/齐性）通过后已删。

**未做**（有意）：`reprTab_mulTab`。`Finsupp` 上没有 `Mul` 实例（`MonoidAlgebra` 才是那个环），
`MonoidAlgebra.coeff_mul` 又是逐点形式，所以这条要么换陈述形式、要么绕 `ofCoeff`。它对 §4.2 的
「逐单项式展开、逐字 `norm_num`」不是必需的，先不加，等真的要「把表代数搬进 `Finsupp` 代数」
（§5 路线 B 会遇到）时再定形状。

**顺带修掉的既有违规**：`FreeMonoidInstances.lean:66` 的 `by omega` 改成 `by lia`
（`AGENTS.md`：本库 `omega`-free，且禁 `omega`）。

---

## 0ter 施工记录（第 2 步：表基建 + 定义的自然一般性；四次 commit）

`e810e05`（第 1 步的桥）→ `323417f`（degree-6 表 + collapse 层）→ `fbed7cc`（定义降到自然一般性）
→ `49aebde`（六块表的自由代数桥）。每步都 `lake build FQFP` + `runLinter` + `lint-style` 全绿。

### 已落地

| 声明 | 内容 |
|---|---|
| `unitTab` / `powTab` / `evalTab_powTab` / `evalTab_singleton` | 表的幂（`z⁶` 这类分次件需要） |
| `addRow` / `collapseAux` / `collapse` + `reprTab_{addRow,collapseAux,collapse}` / `evalTab_collapse` | **支撑规范化**：合并判据只比较**词**相等，所以可 kernel 归约 |
| `w6Tab` / `y36Tab` / `y46Tab` / `y56Tab` / `z6Tab` / `sexticTab` / `dynkin6Tab` | degree-6 左端六块各自的表与整体 |
| `evalTab_{w6Tab,y36Tab,y46Tab,y56Tab,sexticTab}` | 每张表**就是**它镜像的环表达式（纯 `simp only`，无 `norm_num`、无 bump） |
| `mono_pair_eq_freeGen` | `![mono [0] 1, mono [1] 1] = freeGen` |

### 本轮的两条实测结论

1. **`collapse` 可 kernel 归约，整张 degree-6 表也算得动**：
   `example : (collapse dynkin6Tab).length = 64 := by decide` 直接过。也就是说合并过程不需要
   任何 `ℚ` 判定，支撑能在 kernel 层被钉到 64 个字。这是 §3 那张表能落地的机制。
2. **`bchSexticTerm` 原先的 `[NormedRing 𝔸]` 是硬阻塞**：自由词代数不是赋范环，所以
   `bchSexticTerm (mono [0] 1) (mono [1] 1)` 根本不是合法项。已按「定义降到自然一般性」放松
   （见 §4.5），此后 `evalTab_sexticTab` 就是一次 `simp only`。

### 剩下的（第 2 步收尾）与一个必须定的形状

`evalTab dynkin6Tab = 0` 的**逐字比对**卡在一处：`sexticTab` 目前是
`List.ofFn fun i : Fin 28 => (List.ofFn (bchSexticTermWords i), bchSexticTermCoeffs i)`，
它的**行只能在 kernel 里归约，`simp only` 归约不动**（`bchSexticTermWords i j` 不是 simp 能拆的
形状；实测 `bchSexticTermWords 27 = ![1,1,1,1,0,0] := rfl` 过，但 `simp only` 拆不开）。
而 `List.ofFn` 形式与「28 行字面量表」**不是 defeq**（实测 `rfl` 失败），所以两条路只能选一条：

* **(a) 把 `bchSexticTerm` 的表当字面量**：即 §4.3 的 Phase B——`bchSexticTermWords/Coeffs`
  换成一张 28 行的 `bchSexticTermTable : Tab`，`bchSexticTerm a b := wordAlgebraLift a b (evalTab …)`。
  这样 `sexticTab` 与它就是同一个对象（桥变成 `rfl`），逐字比对直接可做；代价是重做
  `norm_bchSexticTerm_le`（需要一条 `List` 索引版的范数原语，§7 已列为缺口）。
* **(b) 保留双数组，另证一条 `List.ofFn` ↔ 字面量的识别引理**：28 步 `List.ofFn_succ'` +
  `rfl` 级向量归约。不动 `BCHTerms`，但多一条脆弱的引理。

**倾向 (a)**，而且它同时就是 §4.3 要做的事；用户已明确「优秀架构优先，旧代码可以改」。
七次/八次项（126 / 124 行）将来照抄同一形状。

**逐字比对的形状**（两条都需要）：`reprTab_collapse` 把目标降到 `collapse dynkin6Tab`
（64 行），`reprTab_apply_eq` 给出每行系数，`norm_num` 收尾（§2.2 实测 64 行量级秒级）。
`collapse dynkin6Tab` 的展开约 983 行，实测在文件级 `maxRecDepth 20000` 下秒级通过；
若最后仍需它，按 §2.3 用**文件级并写明理由**。

### §4.5 本轮新增的架构决定

`bchCubicTerm` / `bchQuarticTerm` / `bchQuinticTerm` / `bchQuinticGroup{1,4,6,24}` /
`bchSexticTerm` / `bchSepticTerm` / `bchOcticTerm` 都**不需要** `NormedRing`（范数只在范数界里
用得到）。已按自然层级改写为显式 binder：Ring+Algebra / Semiring / Semiring+Algebra。
定理保持原有范数假设不动，调用点靠 `NormedRing → Ring/ Semiring`、`NormedAlgebra → Algebra`
自动满足。这条与 §4.1 的「Tab 唯一之家」是同一类动作：**让接口停在它数学上真正需要的地方**。

---

## 0quater 施工记录（第 2 步完成：degree-6 恒等式证完，零 `sorry`）

`bchSexticTerm` 已按路线 (a) 改成表定义（`bchSexticTermTable` + `wordAlgebraLift`），
`septic_pure_identity` 在 `SexticTable.lean` 证完。全树零 `sorry`、零 `maxHeartbeats`，
axioms 只剩三条。

**两个卡点，都是实测逼出来的，都值得记下来**：

1. **64 个系数必须各写一条声明，不能合在一个 `fin_cases` 里。** 单条目标约 4 秒、在默认预算内
   （§2.2 的探针已证），但合在一个命题里时**证明项**变成 64 份 ~1000 行展开，kernel 检查
   （`whnf`）超 200k 心跳。拆成 64 条 `private lemma` 后每条项很小，派发定理只是 64 个引用。
   重复的三步走收在一个 `sexticCoeff` 宏里，所以 64 条各占一行。
2. **`@[irreducible] dynkin6Tab` 是必需的。** 派发定理要用 `fin_cases`/`exact` 比较含
   `dynkin6Tab` 的**类型**；若 `whnf`/`isDefEq` 能展开它，每次类型比较都会把整张 ~1000 行的表
   拉进来（实测 `isDefEq` 超 200k 心跳）。标成 `irreducible` 后类型比较是语法级的，
   而需要展开的地方（`sexticCoeff` 宏、`unfold dynkin6Tab`）照常展开。

**系数比对的组织**（可原样复制到七/八次项）：

| 声明 | 内容 |
|---|---|
| `dynkin6Tab_rows_length` | 每块用 `List.all` 一次读出行长（`decide`，只碰词不碰系数），再用 `append_words_length`/`smulTab_words_length` 合成整表——**从不展开整表** |
| `reprTab_eq_zero_of_length`（`WordAlgebra`） | 一般判据：行都是 `n` 字母词的表，只要在每个 `n` 字母词上系数为 0 就是 0 |
| `length_eq_six` | 长度为 6 的 `List` 就是六个字母 |
| `reprTab_dynkin6Tab_word_0…63` | 64 条系数目标，各一条 `private lemma`，body 是 `sexticCoeff` |
| `reprTab_dynkin6Tab_words` | 派发：`fin_cases` 六个字母后 64 个 `exact` |
| `reprTab_dynkin6Tab_eq_zero` / `evalTab_dynkin6Tab` / `septic_pure_identity` | 三行套用 |

`maxRecDepth 100000` 只出现在 `SexticTable.lean` 的比对段，理由写在原处：那是遍历 ~1000 层
`List.cons` 的 tactic 递归深度，不是搜索/心跳预算。

---

## 1. 目标与现状

`FQFP/BCH/` 现在 17 个文件，`WordAlgebra.lean`（366 行）与 `SexticTable.lean`（162 行）是上一阶段
新建的表层基建，已注册进 `FQFP.lean`。它们要解决的问题写在 `WordAlgebra.lean` 的模块文档里：
degree-6 及以上的纯恒等式在抽象非交换环里做 `noncomm_ring` 会撞心跳天花板
（`bch-port.md` §3.3quater：源 `pieceB_septic_decomp` bump 1.0e9，最高 8.2e9）。

### 1.1 已经落地的东西（实测可编译）

`WordAlgebra.lean`：`wordAlgebraLift`、`wordAlgebraLift_injective`、`freeGen`、`mono`、
`mono_mul`、`prod_eq_mono`、`wordEval_gen`、`coeff_mono`/`coeff_smul_mono`/`coeff_mono_mul`/
`coeff_mono_sum`/`coeff_mono_list`、`evalTab`、`mulTab`、`smulTab`、`evalTab_*` 一族、
`reprTab`、`evalTab_eq_reprTab`、`evalTab_eq_of_reprTab_eq`、`reprTab_apply_eq`。

`SexticTable.lean`：`Tab`、`T : (k : ℕ) → Tab`（**只到 5**）、`mono_sq`/`mono_cube`/`mono_pow_four`/
`mono_pow_five`、`smul_mono_eq`、`T_one`…`T_five`、`Z_mul_T5`、`T2_mul_T4`。

### 1.2 还缺什么（本轮新查出来的）

1. **`WordAlgebra` 没有 `𝔸` 值求值引理。** 缺的正是：
   ```lean
   theorem wordAlgebraLift_mono (a b : 𝔸) (l : List (Fin 2)) (q : ℚ) :
       wordAlgebraLift a b (mono l q) = q • (l.map ![a, b]).prod
   theorem wordAlgebraLift_evalTab (a b : 𝔸) (t : Tab) :
       wordAlgebraLift a b (evalTab t) = (t.map fun p => p.2 • (p.1.map ![a, b]).prod).sum
   ```
   没有它们，`bchSexticTerm a b := wordAlgebraLift a b (evalTab table)` 这种定义**无法推理**
   （连范数界都陈述不出）。注意 `wordEval_gen` 是**反方向**（把 `wordEval` 搬进 `MonoidAlgebra`），
   不能替代。
2. **`reprTab` 与表运算的相容引理缺两条**：
   ```lean
   theorem reprTab_append (s t : Tab) : reprTab (s ++ t) = reprTab s + reprTab t
   theorem reprTab_mulTab (s t : Tab) : reprTab (mulTab s t) = reprTab s * reprTab t
   theorem reprTab_smulTab (c : ℚ) (t : Tab) : reprTab (smulTab c t) = c • reprTab t
   ```
   （`evalTab` 侧的对应物已经有了，但系数函数侧没有。）
3. **`Tab` 的定义目前住在 `SexticTable.lean`**（第 63 行），而 `WordAlgebra.lean` 里到处写
   `List (List (Fin 2) × ℚ)`。一个数学对象应该只有一个家：`Tab` 应上移到 `WordAlgebra`。
4. **`SexticTable.T` 到 5 就断了**（`| _ => []`），degree-6 需要 `T 6`（7 行）。
5. `wordAlgebraLift_injective` 及其两个 `private` 依赖（`freeGenerators`、
   `wordAlgebraLift_free_eq_symm`）**没有消费者**。正向传输（自由代数 → `𝔸`）只需要同态性质，
   不需要单射。要么留着当文档，要么删掉——但别再往上加东西。
6. `SmallSDischarge.lean:15` 指向 `bch-port.md §3.3bis`，**该节已在 `c992573 refactor` 里被删**；
   `bch-port.md:85` 指向 `artifacts/word-representation-decision.md` 与
   `artifacts/fin2-migration-result.md`，**这两个文件不存在**；`bch-port.md:287-292` 说
   `norm_bchSepticTerm_le`/`norm_bchOcticTerm_le` 带 `set_option maxRecDepth 8000 in`，
   而 `BCHTerms.lean` 现在**一条 `set_option` 都没有**。同一个 commit 还删掉了
   `artifacts/free-word-coeff-api-audit.md`（第四轮勘察全文）、`artifacts/quintic-taylor2-route.md`、
   两个 `artifacts/examples/*.lean` 与 7 个 `scripts/*.py`。**文档损失需要补回来**，否则下一轮还会重走。

---

## 2. 本轮实测：`ℚ` 到底能做什么、不能做什么

这一节是本轮最重要的产出。所有条目都是 `lake env lean` 实跑结论。

### 2.1 kernel 归约的边界

| 命题 | `rfl` | 说明 |
|---|---|---|
| `(2 : ℚ) * 3 = 6` | **失败** | `Rat` 的运算一律不归约 |
| `((1:ℚ)/2 + 1/3).num = 5` | **失败** | `.num` 也不归约 |
| `decide ((1:ℚ)/2 = 2/4) = true` | **失败** | `DecidableEq ℚ` 不归约 |
| `List.filter (fun q : ℚ => q ≠ 0) [1/2, 0, 1/3] = [1/2, 1/3]` | **失败** | 同上 |
| `(2 : ℤ) * 3 = 6` | **通过** | |
| `List.filter (fun z : ℤ => z ≠ 0) [1, 0, 2] = [1, 2]` | **通过** | |
| `decide (([0,1,0] : List (Fin 2)) = [0,1,0]) = true` | **通过** | 词相等可 kernel 归约 |
| `List.filter (fun p : List (Fin 2) × ℚ => p.1 = [0,1,0]) [...] = [...]` | **通过** | 谓词只碰词，值不碰 |

**推论**：凡是「按词分组 / 按词筛选」的数据运算，只要不判 `ℚ` 的等零，就能被 kernel 或 `decide`
直接算掉；凡是「把 `ℚ` 算成数」的动作，只能交给 `norm_num`。

### 2.2 `norm_num` 的吞吐（这是心跳天花板的真身）

| 形状 | 结果 |
|---|---|
| 单个 **1281 项** `ℚ` 左结合和 | **超 200k 心跳**（`«synthesize pending MVars»`） |
| 一个 **1280 行**的*字面量*表 `def`（`List (List (Fin 2) × ℚ)` 字面量） | **`def` 本身就超 200k 心跳**，写不出来 |
| **64 行**字面量表 + 64 个逐字 `rw [reprTab_apply_eq]; norm_num [表]` | **全绿**，秒级 |

也就是说：**「把大表摊平再逐字 `norm_num`」这条路两头都堵**——大表写不出来，写出来也 `norm_num`
不动。**表必须由小表组合而成，且每个 `norm_num` 只能看见一个小表达式。**

### 2.3 展开深度的墙：`maxRecDepth`（不是心跳）

用 `++` 串起 N 份 12 行字面量表，再 `rw [reprTab_apply_eq]; simp only [<定义>, List 词法]; norm_num`：

| N（行数） | 默认选项 | 文件级 `set_option maxRecDepth 20000` |
|---|---|---|
| 4（48 行） | 通过 | 通过 |
| 10（120 行） | 通过 | 通过 |
| 26（312 行） | **失败**（`maximum recursion depth`） | 通过 |
| 40（480 行） | **失败** | 通过 |
| 100（1200 行） | **失败** | 通过 |
| 250（3000 行） | **失败** | 通过（整文件 ~19 秒） |

两点要注意：
* 这是**递归深度**限制，不是心跳预算。`AGENTS.md` 只禁 `maxHeartbeats` bump，`maxRecDepth`
  是「项本身就有几千层 `::`」时的正当手段（旧代码就用过 8000）。但**更好的做法是让任何一次
  化简都不超过 ~120 行**——这正是 §3 支撑集的动机。
* `set_option maxRecDepth 20000 in <example>` 这种**局部写法在本轮实测里没生效**，文件级才生效。
  如果最终要用它，必须文件级并写明理由。

### 2.4 degree-6 Dynkin 侧的真实尺寸（`scratch/size_report.py`）

| 量 | 值 |
|---|---|
| LHS 的单项式个数 | **38**（`½W6` 的 7 个字 + 5 个 `y²` 项 + `⅓y³` 10 项 + `-¼y⁴` 10 项 + `⅕y⁵` 5 项 + `-⅙z⁶`） |
| 原始展开总行数 | **956** |
| **单个单项式的最大行数** | **64**（`z⁶`）；其次是 `y⁵` 的 5 项各 48 行、`y⁴` 的 36 行 |
| degree-6 字的总数（环境支撑） | **64**（`2⁶`） |
| **LHS 的有效支撑** | **28 个字**，与 `bchSexticTerm` 的 28 个**完全相同**（`scripts/check_sextic_free_identity.py` 复跑确认：`# tables agree on all 28 words`） |

**这就是支撑集的答案**：环境支撑是 64，有效支撑是 28，而**每一个单项式自己都 ≤ 64 行**。
只要「每个单项式先按词分组、再相加」，**任何一次折叠都不会超过 128 行**——落在默认
`maxRecDepth` 之内（§2.3：120 行通过）。**956 行的原始展开永远不必被造出来。**

### 2.5 一次性摊平是行不通的（Probe7）

我按真实数据（38 个单项式、`T 1..T 6`、逐单项式 `group`、平衡的 `++` 树）建了一个探针：

* **好消息**：`group`（只比较词、系数用 `ℚ` 加法搬着走）**是 kernel 可归约的**——
  `example : (group (T 1 ++ T 1)).length = 2 := by decide` 直接过。这说明支撑集钉在
  「表 → 分组表」这一步是**可行且免费**的。
* **坏消息**：如果**把所有 `m_i` 定义都塞进同一个 `norm_num [...]`**，让一个目标里同时展开整棵
  塔并算完 38 个单项式的系数，**超 200k 心跳**（`timeout at simp` / `timeout at isDefEq`）。

结论：**不能一个目标干完整个恒等式**。必须「每个单项式一个小目标、每个字一个小目标」地拆开——
这既是 `AGENTS.md`「重复意味着缺 API」的反面（这里是「大目标意味着缺切分」），也是 §3 支撑集的
直接后果。

---

## 3. 支撑集：钉在哪一级

「支撑集」在这条路线里有三层，必须区分清楚，否则一定选错：

| 层 | 对象 | 该选多大 | 依据 |
|---|---|---|---|
| **环境支撑** | 一个 degree-`k` 齐次元的系数函数所在的字集 | `2^k`（degree-6 是 **64**） | 齐次性；比较两个 degree-6 元必须覆盖全部 64 个字 |
| **有效支撑** | 恒等式**两边真正非零**的字集 | **28** | 实测：Dynkin 侧 = `bchSexticTerm` 的 28 个字 |
| **单项式支撑** | 一个单项式（乘积表）的行数 | **≤ 64** | 实测：最大是 `z⁶` 的 64 行；其余 ≤ 48 |

**可施工的取法**：把**环境支撑 64 个字**作为唯一的「比较坐标系」，把**单项式支撑**作为唯一的
「计算单元」。具体地：

* 不做「先把 38 个单项式乘成 956 行的大表、再逐字算」——那会同时碰到 §2.2 和 §2.3 两堵墙；
* 而是**每个单项式在自己的 ≤64 行支撑上先算完**（一个小目标），**再按 64 个字的坐标系相加**
  （折叠时每步 ≤128 行，落在默认深度内）；
* 28 这个「有效支撑」是**结果**，不是**前提**：它由 `z⁶` 这类满支撑单项式相消得来，
  所以不能用它来缩小比较范围。它的用处是**校验**（Python 侧的独立校验器已经这么做了），
  以及在 `BCHTerms` 重构后作为 `bchSexticTermTable` 的定义域。

---

## 4. 推荐的下一步

### 4.1 第一步：补 `WordAlgebra.lean` 的桥（小、零风险、所有路线都要）

一次性做完，之后 `BCHTerms` 的表重构才有地基：

1. 把 `Tab` 从 `SexticTable.lean` 上移到 `WordAlgebra.lean`（唯一之家），全树改用 `Tab`。
2. 补 `𝔸` 值求值层：
   * `wordAlgebraLift_of : wordAlgebraLift a b (MonoidAlgebra.of ℚ _ (FreeMonoid.ofList l)) = (l.map ![a,b]).prod`
   * `wordAlgebraLift_mono : wordAlgebraLift a b (mono l q) = q • (l.map ![a,b]).prod`
   * `wordAlgebraLift_evalTab : wordAlgebraLift a b (evalTab t) = (t.map fun p => p.2 • (p.1.map ![a,b]).prod).sum`
   * 推论：`wordAlgebraLift a b (evalTab t) = 0 ↔ evalTab t = 0` 之类**不要**加（那是单射方向），
     正向只需要 `map_zero`。
3. 补系数函数与表运算的相容：
   * `reprTab_append`、`reprTab_mulTab`、`reprTab_smulTab`
   * `reprTab_eq_iff` 不需要；有 `reprTab_apply_eq` 就够。
4. 决策并记录：`wordAlgebraLift_injective` 留还是删（无消费者）。**倾向删**——它连同两个
   `private` 依赖是「反向传输」的残留，而本路线只走正向（见被删的第四轮勘察 §3.2 的论证）。
5. `SexticTable.T` 补 `T 6`；`T` 的 `_ => []` 兜底要保留（否则 `T 7` 没法用）。

### 4.2 第二步：证掉唯一的 `sorry`（degree-6 `septic_pure_identity`）

**目标**：`SmallSDischarge.lean:201-210`。按 §3 的支撑集取法，证明形状是

```
在 ℚ[FreeMonoid (Fin 2)] 的 (mono [0] 1) (mono [1] 1) 处
  ½W6 + ⅓y3₆ - ¼y4₆ + ⅕y5₆ - ⅙z⁶ = bchSexticTermTable 的求值
→ 对 wordAlgebraLift a b 取像
→ 𝔸 里的恒等式
```

施工单元（每个都是小目标）：

1. **单项式级**（38 个，每个 ≤64 行）：把 `T i` 的积写成表，逐 **字** 求系数。
   推荐形态是**每个单项式一条引理**，例如
   ```lean
   theorem z6_coeff (l : List (Fin 2)) : ... -- 不行，l 是变量
   ```
   ——不行，`l` 必须是具体字。所以落地形态是**每个单项式 × 每个字一个小 `have`/`example`**
   或者**每个单项式一条「分组表 = 字面量分组表」的引理**（后者行数少得多：38 条引理，
   每条 ≤64 行）。两条都行；先做后者（38 个小目标），因为它顺带给出可复用的规范形。
   注意：字面量分组表由脚本生成、由 `norm_num` **证明**相等，所以**不存在转写错误风险**——
   这与 `bch-port.md` §3.2 反对的「手抄平坦表」有本质区别（那些是*断言*，这些是*定理*）。
2. **相加级**：用 `reprTab_group`（分组不改系数函数）与 `reprTab_append` 把 38 个规范形
   折成一张 ≤64 行的表；**每步都 `group`**，所以每步 ≤128 行。
3. **逐字级**：64 个字，每个字一个 `rw [reprTab_apply_eq]; norm_num`，右端是 ≤38 项的 `ℚ` 和。
4. **传输级**：用 §4.1 的 `wordAlgebraLift_evalTab` + `map_zero` 回到 `𝔸`，替掉 `sorry`。

**必须避免的形状**（本轮都实测失败过）：
* 把恒等式写成一个目标，靠 `noncomm_ring`/`norm_num` 一次收掉（源的老路，就是心跳天花板本身）；
* 把 38 个单项式的定义塞进一个 `norm_num [...]`（Probe7：超 200k 心跳）；
* 用一张 956 行（或 1280 行）的字面量表（§2.2：`def` 都写不出来）。

**验收**：`lake build FQFP` 零 `sorry`；`lake exe runLinter`、`lake exe lint-style`；
`#print axioms septic_pure_identity` 只剩三条。**不需要** `maxHeartbeats`，**应尽量不需要**
`maxRecDepth`（§3 的取法就是为了这个）；如果确实需要，按 §2.3 用文件级并写明理由。

### 4.3 第三步：`BCHTerms.lean` 的表重构（有前置）

**先别动 `BCHTerms.lean`。** 理由是实测出来的：`bchQuinticTerm` 的四组
（`bchQuinticGroup{1,4,6,24}` / 四张 `Fin 5 → Fin 2` 词表）在下游有**位置索引**的硬消费者：

* `QuinticTaylor2.lean`：`bchQuinticGroupSubsets`（`Fin m` + `Fin 5` 双重索引，L70-73）、
  `bchQuinticTerm_eq_bracket`（**`rfl` 见证**，L148-151）、四个 `card_group*`
  （`fin_cases i <;> decide`，L126-143）、`norm_bchQuinticSubsetPiece_le` 的
  `hc1/hc4/hc6/hc24` 假设块（L441-451，把 4/10/14/2 四个组大小写死）。
* `QuinticRemainder.lean`：四个 `card_sum_bchQuinticGroup*Words`（`decide`，L53-70）与
  `norm_sum_binWord_diff_le (v := bchQuinticGroup*Words)`（L90/110/133/153）。

这些**不是改名能解决的**：`norm_sum_wordEval_le` / `norm_sum_binWord_diff_le` /
`sum_prod_map_smul` 都是 `ι → Fin n → Fin 2` 索引的，表是 `List (List (Fin 2) × ℚ)`，
需要**新的 `List` 索引版范数原语**（顺带一提，这三个引理在 `BCHTerms.lean` 之外**没有消费者**，
所以是「扩展」而不是「另起一套」）。

所以顺序应该是：

1. §4.1 的桥 + §4.2 的 degree-6（拿到心跳/形状读数，确认形状可推广）；
2. **degree-7/8 用同一形状再走一遍**（`T 7`/`T 8`、`octic_pure_identity`、`nonic_pure_identity`）；
   这一步是「形状可推广」的真正检验，成本比 degree-6 高一个量级（单项式支撑到 128/256 行，
   可能就需要 §5 路线 B 或 `maxRecDepth`）；
3. 有了可推广的形状，**再**做 `BCHTerms` 的表化，并且**先回答一个决策点**：
   * **(a) 保留四张五次表**（最小改动：`bchQuinticBracket`、`hc1..hc24`、四个 `_diff_le` 都存活，
     只需把 `Fin`-索引换成 `List`-索引）；
   * **(b) 合并成一张 30 行表**（`norm_bchQuinticSubsetPiece_le` 变成一条加权单和，
     `norm_bchQuinticTerm_diff_le` 的 64 行四段估计压成一条；但 `bchQuinticTerm_eq_bracket`
     这个 `rfl` 会消失，`sextic_pure_identity` 的 `simp only` 集要重建）。
     `bch-port.md` §3.3 已经把四次项/五次项的分组称为「数学上有意义」——`-1, +4, -6, +24`
     这四个权重正好是四组的系数绝对值，所以 **(a) 在数学上更忠实**，我倾向 (a)。

### 4.4 第四步：文档与脚本

* 把第四轮勘察（`artifacts/free-word-coeff-api-audit.md`，`c992573` 删掉的 541 行）与本文件合起来
  重新落盘；`bch-port.md` 补 §3.3bis 的替代节，删掉/修正 §3.3quater 与 §5.3 里
  `maxRecDepth 8000`、`gen_bch_higher_terms.py`、`check_quintic_taylor2_pieces.py`、
  `word-representation-decision.md`、`fin2-migration-result.md` 这些**指向不存在文件**的引用。
* `scripts/check_sextic_free_identity.py` 现在靠正则解析 `bchSexticTermWords` /
  `bchSexticTermCoeffs`（L151-162），**表化之后会直接报 `definition not found`**，要同步改成解析表。
* `SmallSDischarge.lean:15` 的 §3.3bis 引用要改。

---

## 5. 两条备选路线（如果你觉得 §4.2 的生成件太多）

### 路线 B：整数缩放 + 一条 `rfl`（战略备选，能一次解决 6/7/8 次项）

核心观察：`ℚ` 不能 kernel 归约，但 `ℤ` 能。取 `K = 60`（`K^k` 覆盖所有分母：`60^6` 被
`2,3,4,5,6,24,18,60,360,1440,6!` 整除），把齐次 degree-`d` 的自由代数元表示成
**`ℤ` 值的「`K^d` 缩放系数函数」**，于是一个 degree-`d₁` 元乘 degree-`d₂` 元就是
**无除法的整数卷积**（`K^{d₁}·K^{d₂} = K^{d₁+d₂}`），标量 `c ∈ ℚ` 变成整数 `c·K^d`。

这样一来：
* 整条 degree-6 计算全是 `Int.add`/`Int.mul` + 词相等，**全部 kernel 可归约**；
* 用 §2.5 已经验证的 `group`（这次带除零，因为 `DecidableEq ℤ` 可归约）：
  **`group X = []` 是一条 `rfl`**，不需要任何 `norm_num`，也就没有心跳问题；
* 7 次、8 次项是同一套代码——源里最狠的四个 bump（1e9 / 2e9 / 8.2e9）会整体消失。

代价：要新写一层「分次整数缩放多项式 + 求值回 `𝔸`」的接口（估 300–500 行），
并且要挨个证 `bchT k`/`bchZ` 的缩放表示引理（每个都很小）。这是**唯一**能让 7/8 次项
也免于 `maxRecDepth`/生成件的路线。**建议在 §4.2 完成后立刻评估是否转向它。**

### 路线 A：接受 `maxRecDepth`（最省事，但只到一定程度）

就是 §2.3 的实测结果：文件级 `set_option maxRecDepth 20000` 能让 3000 行表的
`simp only [...] ; norm_num` 通过（~19 秒）。缺点是它把「展开深度」这堵墙往后推而不是拆掉，
7/8 次项会再撞上，而且 `AGENTS.md` 的「No Elaboration Hacks」精神上不欢迎。
只应在 §4.2 的切分之后**仍然**需要时，作为**有理由的、文件级的**兜底。

---

## 6. 本轮的探针（已删，结论保留）

探针建在 `scratch/`，交付前已删除（沿用本项目「探针已删、结论保留」的惯例）。下表记录
**每个探针验的是什么、怎么复现**，以便下一轮不必重测：

| 复现方式 | 验的是什么 | 结论 |
|---|---|---|
| 直接写 `example : (2:ℚ)*3 = 6 := rfl` 等（§2.1 表格逐条） | `ℚ`/`ℤ`/`List (Fin 2)` 的 kernel 归约边界 | §2.1 |
| 一个 1281 项 `ℚ` 左结合和 + `norm_num` | `norm_num` 吞吐上限 | 超 200k 心跳 |
| 一个 1280 行 `List (List (Fin 2) × ℚ)` 字面量 `def` | 字面量表能否写出来 | **`def` 本身就超 200k 心跳** |
| 64 行字面量表 + 64 个 `rw [reprTab_apply_eq]; norm_num [表]` | 支承集较小时的逐字目标 | 全绿，秒级 |
| N 份 12 行字面量表用 `++` 串联（N = 4/10/26/40/100/250），`simp only [<定义>, List 词法]; norm_num` | 展开深度上限；`maxRecDepth` 的作用 | 默认 120 行通过、312 行失败；文件级 `maxRecDepth 20000` 下 3000 行通过（整文件 ~19 秒） |
| 镜像 `check_sextic_free_identity.py` 的模型统计 LHS | 单项式个数 / 行数 / 各层支撑 | §2.4 |
| 按真实数据建 38 个单项式 + `group` + 平衡 `++` 塔，先 `decide` 行数，再把全部 `m_i` 塞进一个 `norm_num` | 一次性摊平是否可行 | `decide` 能算 `group`（kernel 可归约）；一次性摊平**超 200k 心跳** |

`scripts/check_sextic_free_identity.py` 复跑输出：
`# Dynkin side has 28 words, bchSexticTerm has 28` / `# tables agree on all 28 words`。
