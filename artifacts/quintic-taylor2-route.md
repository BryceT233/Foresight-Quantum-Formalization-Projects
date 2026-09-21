# `bchQuinticTermTaylor2Decomp`：旧路线为何死、新路线为何活

本轮结论。落地代码：`FQFP/BCH/WordExpansion.lean`（顺序保持展开）与 `FQFP/BCH/QuinticTaylor2.lean`（片段与 `Decomp`）。

---

## 1. 旧路线（`Finset.prod_add` / 子集展开）在数学上不可能成立

被删掉的 `FQFP/BCH/QuinticExpansion.lean` 里 `taylorProdSplit` / `prodAdd_const` /
`prodAdd_const_at_s` 的 section 变量是

```lean
variable {𝔸 : Type*} [CommRing 𝔸] {n : ℕ}
```

**`CommRing` 是必须的，不是随手写的**：`Finset.prod_add` 本身就在
`Mathlib/Algebra/BigOperators/Ring/Finset.lean` 的 `section CommSemiring` 里
（第 107 行开 section，`prod_add` 在第 171 行）。原因是它的右端

```lean
∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * ∏ i ∈ s \ t, g i
```

把**所有 `f` 因子挪到前面、所有 `g` 因子挪到后面**。在非交换环这直接是错的：取
`s = {0,1}`，`0 < 1`，

* 左边 `(f₀+g₀)(f₁+g₁) = f₀f₁ + f₀g₁ + g₀f₁ + g₀g₁`
* 右边 `f₀f₁ + g₀f₁ + g₁f₀ + g₁g₀`

差在 `f₀g₁` vs `g₁f₀`。

BCH 的 `𝔸` 是 `NormedRing`——算子代数，**非交换是本质的**，不能加 `CommRing`。所以那条路线
的三条引理虽然能编译，但在任何 `𝔸` 上都无法调用：它们是关于另一个数学对象的定理。这不是
「还没证完」，是「方向错了」。

同一文件里的 `prod_add_ordered`（第 205 行）同样在 `CommSemiring` section 内，而且**它的
结论本身就是交换版**：它把 `g i` 放在左乘积的左边，即
`g i * (∏ j < i, …)`；保持顺序的正确形式应该是 `(∏ j < i, …) * g i * ∏ j > i, …`。
所以 Mathlib 里**没有**可用的非交换乘积展开引理。

源 `Basic.lean` 的 `bch_quintic_term_taylor2_decomp` 之所以能写成
`match_scalars <;> ring`（带 `maxHeartbeats 1024000000`），正是因为它**不做**这种重组：
它在显式单项式链上让 `noncomm_ring` 逐项对齐。目标不用 `noncomm_ring`，就必须自己造出
「保持顺序」的展开。

---

## 2. 新路线：按 snoc 归纳的顺序保持展开（已进库）

引理已落在 `FQFP/BCH/WordExpansion.lean`（`[Semiring 𝔸]`，无 `omega`、无 `sorry`，
`#print axioms` = `[propext, Classical.choice, Quot.sound]`；先用
`artifacts/examples/quintic-expansion-spike.lean` 验通，随后搬进库，spike 已删）：

```lean
/-- `a`-字母的绝对位置。 -/
def wordAPositions (w : List (Fin 2)) : Finset ℕ :=
  (Finset.range w.length).filter fun j => w[j]? = some 0

/-- 把 `s` 中位置上的 `a` 换成 `c` 得到的三元词（`0=a, 1=c, 2=b`）。 -/
def wordSubstA (w : List (Fin 2)) (s : Finset ℕ) : List (Fin 3) :=
  (List.range w.length).map fun j => if j ∈ s then 1 else if w[j]? = some 0 then 0 else 2

/-- **顺序保持展开**。 -/
theorem wordProdList_add (w : List (Fin 2)) (a c b : 𝔸) :
    wordProdList ![a + c, b] w
      = ∑ s ∈ (wordAPositions w).powerset, wordProdList ![a, c, b] (wordSubstA w s)
```

配套（同文件）：

* `wordProdList_eq_prod_map`（`wordProdList letters l = (l.map letters).prod`）、
  `wordProdList_append`；
* `wordEvalPattern`（`Fin n → Bool` → `List (Fin 2)`，`true ↦ 0`）与
  `wordProdList_wordEvalPattern`（`wordEval` 的和 = `wordProdList` 的和）——四组到词 API 的桥；
* `wordProdList_substA_empty`（`wordProdList ![x,y] w = wordProdList ![x,V,y] (wordSubstA w ∅)`）
  ——`k = 0` 那个片段的塌缩。

五条关键设计（踩点，别改）：

1. **归纳走 snoc**（`List.reverseRecOn`，`l ++ [k]`），不走 cons。`List.range l.length` 在
   追加一个字母后**就是**新 `range` 的前缀，位置下标不需要 `+1` 平移。走 cons 的话
   `Finset ℕ` 位置全体要平移，`s.erase` / `insert` 的簿记会翻倍。
2. **乘积用 `List.prod`，不用 `Finset.prod`。** `Finset.prod_range_succ` 要求 `CommMonoid`
   （它的证明结尾就是 `simp only [mul_comm, …]`，见
   `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:536`）；非交换要用
   `List.range_succ` + `List.map_append` + `List.prod_append`。
3. **和用 `Finset.sum`**：`Finset.sum_powerset_insert` 只管加法（`AddCommMonoid`），
   在非交换环上完全可用。这是把「集合簿记」和「非交换」拆开的关键。
4. **不要在证明里写 `have hf : … = …` 然后 `rw [hf]`。** 从 `wordSubstA` 定义里展开出来的
   `fun j => …` 与手写 lambda 的隐式 `Decidable` 实例项不同，`rw`/`simp only` **匹配不上**
   （打印出来一模一样）。要用 `congr 1` 让**目标自己的** lambda 出现在子目标里，再用
   `List.map_congr_left` 逐点证。本轮在这里卡了 3 轮。
5. `fin_cases k`（`k : Fin 2`）会把 `k` 换成 `(fun i => i) ⟨0, ⋯⟩`，与字面量 `[0]` 不
   `rw` 匹配；用 `obtain rfl | rfl := (by fin_cases k <;> simp : k = 0 ∨ k = 1)`。

---

## 3. 用它证 `bchQuinticTermTaylor2Decomp` 的方案

目标陈述（源 `Basic.lean:3228`）：

```lean
bchQuinticTerm (x + V) y - bchQuinticTerm x y
  = bchQuinticTermLinDiff x V y + bchQuinticTermTaylor2Remainder x V y
```

### 3.1 实际落地的设计：「四组 × 子集」，不引入 30 词统一索引

原计划（把四组拼成 30 词表，再用 `Fin.sum_univ_add` 拆）**没有采用**：拼接表要
`Fin.append` + 三次 `Fin.sum_univ_add`，还要额外证明「拼接表与四组词表逐项一致」，而收益只是
一个 `Fin 30` 索引。实际做法保留源的四组结构，只加一个镜像 `bchQuinticTerm` 内层括号的辅助：

```lean
def bchQuinticBracket [Ring 𝔸] [Algebra ℚ 𝔸] (v1 v4 v6 v24 : 𝔸) : 𝔸 :=
  -v1 + (4 : ℚ) • v4 - (6 : ℚ) • v6 + (24 : ℚ) • v24

def bchQuinticGroupSubsets [Semiring 𝔸] {m : ℕ} (words : Fin m → Fin 5 → Bool) (k : ℕ)
    (x V y : 𝔸) : 𝔸 :=
  ∑ i : Fin m, ∑ s ∈ (wordAPositions (wordEvalPattern (words i))).powersetCard k,
    wordProdList ![x, V, y] (wordSubstA (wordEvalPattern (words i)) s)

def bchQuinticSubsetPiece [Ring 𝔸] [Algebra ℚ 𝔸] (k : ℕ) (x V y : 𝔸) : 𝔸 :=
  (720 : ℚ)⁻¹ • bchQuinticBracket
    (bchQuinticGroupSubsets bchQuinticGroup1Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup4Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup6Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup24Words k x V y)
```

`bchQuinticTerm a b = (720)⁻¹ • bracket (G1 a b) (G4 a b) (G6 a b) (G24 a b)` 是 `rfl`
（括号体逐字复制 `bchQuinticTerm` 的内层表达式），所以片段与 `bchQuinticTerm` 的形状天然对齐。
`bchQuinticGroupSubsets` 只需要 `[Semiring 𝔸]`；片段因为有减号与标量乘，用
`[Ring 𝔸] [Algebra ℚ 𝔸]`。

### 3.2 「不要减掉空集项」——把 `k = 0` 也做成一个片段

计划里写的是「`T = ∅` 那一项正是 `bchQuinticTerm x y`，两边相消」。实现时**不需要相消**：
`wordProdList_add` 给的是**整个** `powerset` 上的和，而 `powerset` 本身按 `card` 无遗漏地分成
`k = 0..5`：

```lean
theorem bchQuinticTerm_add_eq_sum_pieces (x V y : 𝔸) :
    bchQuinticTerm (x + V) y = ∑ k ∈ Finset.range 5, bchQuinticSubsetPiece k x V y

theorem bchQuinticSubsetPiece_zero (x V y : 𝔸) :
    bchQuinticSubsetPiece 0 x V y = bchQuinticTerm x y
```

`bchQuinticSubsetPiece_zero` 用 `Finset.powersetCard_zero` 与 `wordProdList_substA_empty`
（`WordExpansion.lean`，本轮新增）把 `k = 0` 的整条和塌成 `wordProdList ![x, y]`。于是

```lean
rw [bchQuinticTerm_add_eq_sum_pieces, Finset.sum_range_succ ×4, Finset.sum_range_one,
    bchQuinticSubsetPiece_zero]
unfold …; abel
```

就是 `Decomp`——比「减去空集项」少一次 `Finset.sum_erase` 类簿记，而且 `∑_{k∈range 5}` 正是
`Finset.sum_range_succ` 直接可拆的形状。

分工上：`card ≤ 4`（没有全 `a` 的词）**只**用在

```lean
sum_powerset_eq_sum_powersetCard :
    ∑ t ∈ s.powerset, f t = ∑ k ∈ Finset.range 5, ∑ t ∈ s.powersetCard k, f t
```

（`Finset.sum_fiberwise_of_maps_to` + `Finset.powersetCard_eq_filter`，10 行）；
代数部分**只**用一条

```lean
bracket_sum : bracket (∑A) (∑B) (∑C) (∑D) = ∑ k, bracket (A k) (B k) (C k) (D k)
```

（`simp only [bchQuinticBracket, Finset.smul_sum, ← Finset.sum_neg_distrib,
← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`）。
**全程没有 `noncomm_ring`，没有 `maxHeartbeats` bump。**

三条踩点（已写进文件注释，别重蹈）：

* 片段的标量必须写 `[Algebra ℚ 𝔸]` 而不是 `[SMul ℚ 𝔸]`：`Finset.smul_sum` 要求
  `DistribSMul ℚ 𝔸`，只给 `SMul` 时 `rw [Finset.smul_sum]` 报的是「找不到 pattern」
  而不是缺实例，极易误判成方向写反。
* 四组到 `wordProdList` 的桥是 `wordProdList_wordEvalPattern`（本轮加进 `WordExpansion.lean`），
  不必逐组写四条：`sum_ofFn_wordEval_eq` 一条 `Finset.sum_congr` 就够。
* `∑ k ∈ range 5, piece k` 要先 `Finset.sum_range_succ` 拆到 `k = 0` 露出来，
  `rw [bchQuinticSubsetPiece_zero]` 才能匹配——直接 `rw` 无法把 `bchQuinticSubsetPiece k`
  和 `bchQuinticSubsetPiece 0` 对上。

### 3.3 四条范数界的形式与常数

`bchQuinticGroupSubsets` 的词形是统一的：`s ∈ powersetCard k` ⇒ 词里恰有 `k` 个字母 `1`（`V`）、
`5-k` 个字母属于 `{0,2}`（`x`、`y`）。于是

* `norm_wordProdList_le` 取字母界 `![M, Vn, M]`（`M = ‖x‖+‖V‖+‖y‖`、`Vn = ‖V‖`）直接给出
  `≤ M^(5-k) · Vn^k`，**完全不需要 `fin_cases`**；
* 词数 = `∑ i, ((wordAPositions …).card).choose k`（`Finset.card_powersetCard`），
  12 个数（4 组 × 3 个 `k`）由 `decide` 直接算出；
* `M^(5-k)·Vn^k ≤ M³·Vn²`（`k ≥ 2`，用 `Vn ≤ M`）收尾。

实算的词数表（`decide` 核对）：

| k | group1 (×1) | group4 (×4) | group6 (×6) | group24 (×24) | 合计 | 系数和 |
|---|---|---|---|---|---|---|
| 2 | 12 | 24 | 30 | 4 | **70** | `384/720` |
| 3 | 8 | 11 | 10 | 1 | **30** | `136/720` |
| 4 | 2 | 2 | 1 | 0 | **5** | `16/720` |

三行的系数和都**小于**源常数（`1680/720`、`720/720`、`30/720`），所以定理陈述保留源常数
（下游 `10000·s^9` 那条链的算术不变），而证明走精确加权和——比源的「词数 × 最大系数」更紧。
合计 `1680+720+30 = 2430`，`2430/720`，与源一致。

### 3.4 独立核对（已做，通过）

旧表（`Fin 75/70/30/5` 的字面量表）是手工从源反推的，所以必须独立核对。新定义是
**从 `bchQuinticTerm` 经已证明的 `wordProdList_add` 推导出来的**，所以原则上不存在转写错误；
但为了不依赖「原则上」，仍然做了一次**独立校验器**
`scripts/check_quintic_taylor2_pieces.py`：

* 它**不读** `QuinticTaylor2.lean` 的片段定义；
* 从 `BCHTerms.lean` 解析四组 `Fin 5 → Bool` 词表，从 `git show HEAD:FQFP/BCH/QuinticTaylor2.lean`
  解析**旧表**（旧表是逐词逐系数对着源核对过的）；
* 自己枚举「每个词 × 其 `a`-位置的每个非空 `k`-子集」重建四个片段，逐 `(词, 系数)` 比对。

结果（`python scripts/check_quintic_taylor2_pieces.py <old_qt2.lean>`）：

```
rebuilt piece sizes:  k = 1 : 75   k = 2 : 70   k = 3 : 30   k = 4 : 5
k = 1 : OK (75 terms, 75 distinct words)
k = 2 : OK (70 terms, 70 distinct words)
k = 3 : OK (30 terms, 30 distinct words)
k = 4 : OK (5 terms, 5 distinct words)
total terms k = 1..4 : 180
RESULT: OK
```

（校验收到的第一个差异是**脚本**的符号约定写错：`bchQuinticTerm` 的第 1、3 组系数是 `-1`、`-6`，
不是 `+1`、`+6`。修脚本后全绿——这也说明这类校验器的价值。）


---

## 4. 与 `bch-port.md` §3.2 的关系

`bch-port.md` §3.2 把难点描述为「两套表示」的成因分析，并给出「统一表示」或「加桥接引理」
两个选项。本轮的修正是：

* 难点**不是**表示不统一，而是**非交换**：`Finset.prod_add` 一类工具在非交换环上不成立，
  所以任何「先按子集展开、再重排系数」的方案都会撞墙；
* 「统一表示」的方向仍然对，但**统一的目标形态是「四组 × `a`-位置的子集」**，而不是按
  `Fin 5 → Bool`、`Fin 30` 核心词表或 `Fin 75/70/30/5` 的平坦表；
* 桥接引理与本方案**不冲突**：§3.1 的 `bchQuinticBracket` + `sum_ofFn_wordEval_eq`
  就是桥接，而且只需要 `Finset.sum` 拆分，不需要展开。

## 5. 实施状态

见 `FQFP/BCH/QuinticTaylor2.lean` 的文件注释。`bchQuinticTermTaylor2Decomp` 已证明
（`lake build FQFP` 零警告、`runLinter` / `lint-style` 全过）；四条范数界（§3.3）
为最后一块。

