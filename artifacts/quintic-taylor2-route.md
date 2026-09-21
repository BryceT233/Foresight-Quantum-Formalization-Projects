# `bchQuinticTermTaylor2Decomp`：旧路线为何死、新路线为何活

本轮结论。已落地验证的代码在 `artifacts/examples/quintic-expansion-spike.lean`。

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

## 2. 新路线：按 snoc 归纳的顺序保持展开（已验证）

`artifacts/examples/quintic-expansion-spike.lean` 给出并证明（`[Semiring 𝔸]`，无 `omega`、
无 `sorry`，`#print axioms` = `[propext, Classical.choice, Quot.sound]`）：

```lean
/-- `a`-字母的绝对位置。 -/
def aPos (w : List (Fin 2)) : Finset ℕ :=
  (Finset.range w.length).filter fun j => w[j]? = some 0

/-- 把 `T` 中位置上的 `a` 换成 `c` 得到的三元词（`0=a, 1=c, 2=b`）。 -/
def substWord (w : List (Fin 2)) (T : Finset ℕ) : List (Fin 3) :=
  (List.range w.length).map fun j => if j ∈ T then 1 else if w[j]? = some 0 then 0 else 2

/-- 逐位置乘积：`a`-位置是 `a + c`，其余是 `b`。 -/
def posProd (w : List (Fin 2)) (a c b : 𝔸) : 𝔸 :=
  ((List.range w.length).map fun j => if w[j]? = some 0 then a + c else b).prod

/-- **顺序保持展开**。 -/
theorem expansion (w : List (Fin 2)) (a c b : 𝔸) :
    posProd w a c b
      = ∑ T ∈ (aPos w).powerset, ((substWord w T).map ![a, c, b]).prod
```

三条关键设计（踩点，别改）：

1. **归纳走 snoc**（`List.reverseRecOn`，`l ++ [k]`），不走 cons。`List.range l.length` 在
   追加一个字母后**就是**新 `range` 的前缀，位置下标不需要 `+1` 平移。走 cons 的话
   `Finset ℕ` 位置全体要平移，`T.erase` / `insert` 的簿记会翻倍。
2. **乘积用 `List.prod`，不用 `Finset.prod`。** `Finset.prod_range_succ` 要求 `CommMonoid`
   （它的证明结尾就是 `simp only [mul_comm, …]`，见
   `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:536`）；非交换要用
   `List.range_succ` + `List.map_append` + `List.prod_append`。
3. **和用 `Finset.sum`**：`Finset.sum_powerset_insert` 只管加法（`AddCommMonoid`），
   在非交换环上完全可用。这是把「集合簿记」和「非交换」拆开的关键。
4. **不要在证明里写 `have hf : … = …` 然后 `rw [hf]`。** 从 `substWord` 定义里展开出来的
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

### 3.1 第一步：把 `bchQuinticTerm` 接到 30 个核心词上（不动 `BCHTerms.lean`）

`BCHTerms.lean` 的四组是 `Fin 4 / 10 / 14 / 2` 的二元词表，系数 `-1 / +4 / -6 / +24`。
**把核心词表就取成四组的拼接**，于是不需要任何索引集合匹配：

```lean
def bchQuinticCoreWords : Fin 30 → List (Fin 2) :=   -- = append(四组词表)
def bchQuinticCoreCoeffs : Fin 30 → ℚ :=             -- = -1×4 ++ 4×10 ++ -6×14 ++ 24×2
```

`∑ i : Fin 30` 用三次 `Fin.sum_univ_add` 拆成 `4+10+14+2`，配合
`wordProdList letters l = (l.map letters).prod` 与
`(List.ofFn (wordEval v a b)).prod = wordProdList ![a,b] (List.ofFn v)` 两条桥，
得到

```lean
theorem bchQuinticTerm_eq_coreSum (a b : 𝔸) :
    bchQuinticTerm a b
      = ∑ i : Fin 30, (bchQuinticCoreCoeffs i / 720) • wordProdList ![a, b] (bchQuinticCoreWords i)
```

这是纯 `Finset.sum` 重组 + `wordEval`/`wordProdList` 桥接，**不动已被验收的 555 行**。

### 3.2 第二步：对每个核心词用 `expansion`

`a := x`、`c := V`、`w := 核心词`，`aPos` 恰好是这个词的 `x`-位置集合。`T = ∅` 那一项正是
`bchQuinticTerm x y`，两边相消；剩下 `∅ ≠ T ⊆ aPos i`，按 `T.card = 1,2,3,4` 分块，正是
linDiff / 2V / 3V / 4V。

### 3.3 第三步：定义四个片段为「按 `T.card` 过滤」的嵌套和

```lean
noncomputable def bchQuinticTermTaylor2Remainder2V (x V y : 𝔸) : 𝔸 :=
  ∑ i : Fin 30, (bchQuinticCoreCoeffs i / 720) •
    ∑ T ∈ (aPos (bchQuinticCoreWords i)).powersetCard 2,
      wordProdList ![x, V, y] (substWord (bchQuinticCoreWords i) T)
```

`Decomp` 于是 = 3.1 + `expansion` + `powerset.erase ∅ = ⋃_{k=1..4} powersetCard k`
（需要 `∀ i, (aPos i).card ≤ 4`，即没有全 `a` 的核心词；`powersetCard` 见
`Mathlib/Data/Finset/Powerset.lean:198`，`Finset.card_powersetCard` 在第 212 行）。
**全程不需要 `noncomm_ring`，也不需要 `maxHeartbeats` bump。**

### 3.4 代价：四条范数界要跟着重证（这是唯一实质工作量）

现在四条界用 `fin_cases i <;> norm_num [<75/70/30/5 条字面量表>]` 逐项算。换成
`(i, T)` 索引后，反而**更短**，因为词形是统一的：

* 词数：`∑ i, ((aPos i).powersetCard k).card = ∑ i, (aPos i).card.choose k`
  （`Finset.card_powersetCard`），需要算出 `75 / 70 / 30 / 5`；
* 最大系数：`|coreCoeffs i / 720| ≤ 24 / 720`，`Finset.sup'_le` + 30 个 `fin_cases`
  （现在是 70/30/5 个）；
* 每个词形统一：`substWord` 的词恰有 `k` 个字母 `1`、`5-k` 个字母属于 `{0,2}`，
  所以 `norm_wordProdList_le` + `profile_le` 给出 `M^(5-k)·Vn^k ≤ M³·Vn²`，
  **完全不需要 `fin_cases`**（现在每个片段要对 70/30/5 个字面量跑 `ring_nf`）。

即：`Decomp` 变简单，四条界也变简单，但**定义换了**。`QuinticTaylor2.lean`（428 行，目前
无消费者）整体重写；`BCHTerms.lean`、`QuinticRemainder.lean` **不动**。

### 3.5 开工前必须独立核对的一件事

`(i, T) ↦ 输出词` 是单射，且 30 个核心词 × 子集总共给出 180 个词
（`75 + 70 + 30 + 5 = Σ_i (2^{#a(i)} - 1)`）。**新的四个片段与源/旧表的 (词, 系数) 多重集
必须逐项一致**——旧表是逐词逐系数从源反推核对过的，重写后要再用同样的方式核对一次
（`scripts/` 下加一个独立的 CAS/枚举校验器，与本项目「生成器 + 独立校验器成对」的惯例一致）。
`linDiff` 的 75 个词应恰是每个核心词的每个 `x`-位置各取一次。

---

## 4. 与 `bch-port.md` §3.2 的关系

`bch-port.md` §3.2 把难点描述为「两套表示」的成因分析，并给出「统一表示」或「加桥接引理」
两个选项。本轮的修正是：

* 难点**不是**表示不统一，而是**非交换**：`Finset.prod_add` 一类工具在非交换环上不成立，
  所以任何「先按子集展开、再重排系数」的方案都会撞墙；
* 「统一表示」的方向仍然对，但**统一的目标形态是按 `(核心词, 子集)` 索引**，而不是按
  `Fin 5 → Bool` 或 `Fin 75/70/30/5` 的平坦表；
* 桥接引理（§3.2 的另一选项）与本方案**不冲突**：3.1 那条 `bchQuinticTerm_eq_coreSum`
  就是桥接引理，而且它只需要 `Finset.sum` 拆分，不需要展开。
