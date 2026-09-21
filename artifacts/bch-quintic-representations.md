# 五次项的两套表示：成因、核对与统一方案

## 1. 为什么会有两套表示

**源里只有一套**：`Basic.lean` 的 `bch_quintic_group_{1,4,6,24}` 是逐字的显式单项式链
（`a * a * a * a * b + a * b * b * b * b + b * a * a * a * a + b * b * b * b * a`），
**源完全没有词数据**。taylor2 一线在源里同样是显式的 `+`-链（75 + 105 项），恒等式用
`match_scalars <;> ring` 证。

目标是分两批移植的，两批的**需求不同**，于是各自选了当时最顺手的表示：

| | 表示 | 为什么 |
|---|---|---|
| `BCHTerms.lean`（阶段 2） | `Fin 5 → Bool` 词模式 + `Finset.sum` + `wordEval` | 范数界要走 `WordExpansion` 的 arity-free 组引理 `norm_sum_wordEval_le`，它的输入就是二元字母表 `{a, b}` 的词模式。这一步把源 180 行的逐项估计压成四行 |
| `QuinticTaylor2.lean`（阶段 3） | `Fin 3` 模式 + `Fin m → ℚ` 系数 + `bchWordSum` | 被展开的对象是 `bchQuinticTerm (x + V) y`，字母表是 `{x, V, y}`；而且界要按「词内 V 的个数」分块，每块 coefficient × 词数 就是源常数 |

所以两套表示不是数学上的两种东西，而是**移植顺序的痕迹**：先有了「按二元词模式求和的
`bchQuinticTerm`」，后有「按三字母词模式求和的 taylor2」。`Decomp` 之所以难，正是因为它要
把这两个 `Finset.sum` 对上。

**代价评估**：源用显式链时，这个恒等式是 `match_scalars <;> ring` 一句话——但代价是界只能
逐项做（源为此写 1200 行，还带 `maxHeartbeats 1024000000`）。目标选了词数据，赚到了界，代价
就是 `Decomp` 需要一次索引重组。

## 2. 核对：两套表示描述的是同一批单项式

从源反推四个组的 30 个核心词与系数（`0 = a`、`2 = b`），与目标 taylor2 的
`linDiff / 2V / 3V / 4V` 四块数据交叉核对，结果：

* **逐词逐系数 0 mismatch**；
* **30 个核心词全覆盖**；
* `linDiff` 恰好取每个核心词的每个 `x`-位置一次（75 = `Σ_{w} #x(w)`）；
* 每块内 `#V` 恒定（2 / 3 / 4）；
* 每个核心词在四块里的出现次数分别是 `#x(w) choose k`，总多重数 **5**；
* `Σ|c| = 176`，与五次项界常数一致。

即：**taylor2 的四块数据就是这批核心词的展开，没有第五种东西。**

## 3. 统一方案

**把 `bchQuinticTerm` 的定义与 taylor2 侧统一到同一种 `Finset.sum` 形状**，`Decomp` 就退化为
系数级恒等式 + 一次索引重组，`noncomm_ring` 完全不需要。

### 3.1 数据（已排序，组即索引集合）

`Fin 30 → Fin 5 → Fin 3`，`0 = a`、`2 = b`：

```
[0,0,0,0,2] [0,0,0,2,0] [0,0,0,2,2] [0,0,2,0,0] [0,0,2,0,2] [0,0,2,2,0]
[0,0,2,2,2] [0,2,0,0,0] [0,2,0,0,2] [0,2,0,2,0] [0,2,0,2,2] [0,2,2,0,0]
[0,2,2,0,2] [0,2,2,2,0] [0,2,2,2,2] [2,0,0,0,0] [2,0,0,0,2] [2,0,0,2,0]
[2,0,0,2,2] [2,0,2,0,0] [2,0,2,0,2] [2,0,2,2,0] [2,0,2,2,2] [2,2,0,0,0]
[2,2,0,0,2] [2,2,0,2,0] [2,2,0,2,2] [2,2,2,0,0] [2,2,2,0,2] [2,2,2,2,0]
```

系数（分母 720）：

```
[-1, 4, 4, -6, -6, -6, 4, 4, -6, 24, -6, -6, -6, 4, -1,
 -1, 4, -6, -6, -6, 24, -6, 4, 4, -6, -6, -6, 4, 4, -1]
```

四个组的索引集合（**不是连续区间**）：

| 组 | 系数 | 索引 |
|---|---|---|
| 1 | `-1` | `0, 14, 15, 29` |
| 4 | `+4` | `1, 2, 6, 7, 13, 16, 22, 23, 27, 28` |
| 6 | `-6` | `3, 4, 5, 8, 10, 11, 12, 17, 18, 19, 21, 24, 25, 26` |
| 24 | `+24` | `9, 20` |

### 3.2 三条核心引理

1. **分配律基元**（一次、一处，`WordExpansion.lean`）：
   `wordProdList (Function.update f i v) w = ∑ s : Finset (Finset.Icc 0 (n-1)), …` ——
   更实用的形状是把模式 `w : Fin n → κ` 按**子集** `s ⊆ univ` 展开：
   对固定的基模式 `w₀` 与字母替换 `f`，
   `wordProdList letters (w₀ at f) = ∑_{s ⊆ positions} …`。
   每个五次词只有 5 个字母，所以这是 ≤ 32 项的有限和，全部由 `Finset.sum` 的分配律给出。

2. **`bchQuinticTerm` 的展开**：
   `bchQuinticTerm (x + V) y - bchQuinticTerm x y`
   `= ∑_{w} (c_w/720) • (wordProdList ![x+V,V,y] w - wordProdList ![x,V,y] w)`
   —— 这是 `Finset.sum_sub_distrib` + `smul_sub`，不需要分配律。
   注意 `bchQuinticTerm (x+V) y` 里 `1` 位置的字母不变，只有 `0` 位置的 `x` 变成 `x + V`。

3. **逐词展开 + 系数核对**：
   `wordProdList ![x+V,V,y] w - wordProdList ![x,V,y] w`
   `= ∑_{∅ ≠ s ⊆ {i | w i = 0}} wordProdList ![x,V,y] (w 在 s 处置 V)`
   （`x + V` 代入后，选 `x` 的分支给出原来的词、选 `V` 的分支给出置 `V` 的词；减去原词正好
   抵消 `s = ∅` 项）。右边按 `#V` 分类就是 `linDiff + 2V + 3V + 4V` 的形状。

`Decomp` 于是 = 引理 2 + 引理 3 + 「同一模式的两条路径系数相同」，后者是 `Finset.sum`
的重组（`Finset.sum_biUnion` / `Finset.sum_bij`），**不需要 `noncomm_ring`**。

### 3.2bis 引理 1 的确切形状与卡点（已试过多轮，务必先读）

`Finset.prod_add`（`Algebra/BigOperators/Ring/Finset.lean:171`）的形状是

```
∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * ∏ i ∈ s \ t, g i
```

**第一坑：`t = ∅` 那一项是 `∏ i, g i`，不是 `∏ i, f i`。** 要减掉的 `∏ i, f i` 是
**`t = univ`** 那一项（`s \ t = ∅`）。早先「减掉空集项」的写法全部作废。

**第二坑（最关键，来回错了五轮）：两个因子的支撑集方向。** 把它放到 Taylor 替换上，
位置分两类，而**增量并不支撑在 `sᶜ` 上**：

* `i ∈ s`（词里是 `x`）：`letters i = x + V`，即 `f i = x`，`g i = V`；
* `i ∉ s`（词里是 `y`）：`letters i = y`，即 `f i = y`，`g i = 0`。

所以 **`f` 在整条词上都不为零**，`g` 支撑在 `s` 上。有了这个，`prod_add` 的 summand
`(∏ i ∈ t, f i) * ∏ i ∈ univ \ t, g i` 是：

* `t ⊆ s` 时：`univ \ t ⊇ sᶜ`，而 `sᶜ` 上 `g = 0`……**但 `univ \ t` 还含 `s \ t`，那里 `g = V`**，
  所以这个因子**一般不是 `1`**；
* 真正干净的说法是：**该 summand 当且仅当 `t ⊄ s` 时为 `0`**（此时 `t` 里有 `i ∉ s`，而那里
  `f i = y`？——不，`f i = y ≠ 0`）。**这就是我反复搞错的地方。**

**本轮的净结论（避免下轮重蹈）**：

* `prod_add` 的 summand 是 `(∏ i ∈ t, f i) * ∏ i ∈ (univ \ t), g i`；要减掉的 `∏ i, f i` 是
  **`t = s`**（在 `s` 上的展开里）那一项。**不要**再去「减空集项」，也不要减 `t = univ`。
* **`Finset.prod_ite` 是这条路的正确入口**，它直接把
  `∏ i, if i ∈ s then x+V else y` 拆成 `(∏ i ∈ s, x+V) * ∏ i ∈ univ \ s, y`，
  **完全绕开了之前反复出错的 `prod_sdiff` 方向问题**。
* 真正需要减去的恒等式**只在 `s` 上**：
  `∏ i ∈ s, (x+V) - ∏ i ∈ s, x = ∑_{∅≠t⊆s} (∏ i ∈ t, (x+V)) * (∏ i ∈ s\t, x)`。
  `sᶜ` 上的因子 `∏ i ∈ sᶜ, y` 两边都有，先提出来即可。**不要在 `univ` 上做这个减法。**
* 已验证并落地的三条（`FQFP/BCH/QuinticExpansion.lean`，`lake build` 零警告）：
  `taylorProdSplit`、`prodAdd_const`、`prodAdd_const_at_s`。
* **卡点**：把 `s.powerset.erase s`（或 `t ≠ s` 的 filter）与
  `s.powerset.filter (t.Nonempty ∧ t ≠ s)` 对上的那一步 membership 簿记。`Finset.sum_erase_add`
  要求 `a ∈ s`，`Finset.sum_eq_single` 的"例外情形"是**第三个**参数且顺序是
  `(fun b _ hb => f b = 0) (fun ha => f a = 0)`——这两点本轮都踩过。
* **下轮做法**：把 `erase_powerset` 那条**纯集合等式**
  `s.powerset.erase s = s.powerset.filter (fun t => t.Nonempty ∧ t ≠ s)`
  单独写成一个小引理并用 `ext` 打穿（`mem_erase`/`mem_filter`/`mem_powerset` 三者交互，
  建议用 `simp only [...]` 后 `constructor` 分方向手写，不要 `tauto`），再拼总式。

### 3.3 波及范围

* `BCHTerms.lean`：五次项的四个组改为由 30 词表加索引集合定义；`bchQuinticTerm` 改成对
  30 词的 `Finset.sum`；`_smul`、`norm_bchQuinticGroup*_le`、`norm_bchQuinticTerm_le` 需要跟着
  重写（组界仍是「系数上界 × 词数」形状，常数不变）。
* `QuinticRemainder.lean`：四个 `_diff_le` 与 `norm_bchQuinticTerm_diff_le` 依赖原组定义，
  需要重证（或改成按索引集合的 filter 形状）。
* `QuinticTaylor2.lean`：只是新增 `Decomp`，数据不动。

**建议顺序**：先加分配律基元（1）并验通，再做（2）+（3），最后才动 `BCHTerms.lean` 的定义。
在（2）+（3）验通之前不要改 `BCHTerms.lean`——那是把已经验收的 555 行暴露出去。
