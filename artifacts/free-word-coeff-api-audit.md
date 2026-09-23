# 用自由词代数重构 BCH 项：API 实测勘察与下一步方案

勘察人：abstraction agent。本文只做**勘察与设计**，未改动 `FQFP/` 下任何正式文件。
所有结论都来自本轮 `lake env lean` 实跑（探针已删，结论保留）；本文也修正了
`artifacts/free-word-algebra-route.md` 里几处**已被实测推翻**的判断。

---

## 阶段 A 施工记录（第二轮：表层打通，六次恒等式已验证为数据恒等式）

**重大结论：六次纯恒等式确实是「表的恒等式」，不是「环的恒等式」。**
独立校验器 `scripts/check_sextic_free_identity.py` 从 `z` 与 `T_k = aⁿb^(k−n)/(n!(k−n)!)`
出发，按**正合成**枚举 `y^p` 的六次齐次部分，重建整条
`½W6 + ⅓y3₆ − ¼y4₆ + ⅕y5₆ − ⅙z⁶`，与 `BCHTerms.lean` 的
`bchSexticTermWords/Coeffs` 逐词比对：**28 个词全部一致**。

这就把 §6 阶段 A 的路彻底改了：**不需要**逐词 64 次 `norm_num`，也**不需要**在 Lean 里
展开多项式乘积。证明形态是
「两条表逐行相同 ⟹ 两侧求值相同」，而「逐行相同」在两侧用同一套字面量时就是 `rfl`。

（调试过程中修掉一个真实错误：`y_d6 = Σ_{i+j=6, i,j≥1} z^i T_j` 里 i=0 那一项就是
`T₆`，我第一版漏了，导致纯词 `aaaaaa` 的系数算出 `31/360` 而不是 `1/720`。
校验器里保留了这条断言 `T₆(aaaaaa) = 1/720` 作为自检。）

**已落地**（`FQFP/BCH/WordAlgebra.lean`，验收全绿）：

| 声明 | 内容 |
|---|---|
| `prod_mono_aux` | 单项式之积是单项式：词拼接、系数相乘 |
| `coeff_mono_sum` | 单项式之和的系数 = 各行系数按词筛选求和（纯数据，无环运算） |
| `evalTab t` | 表的求值：`(t.map (mono ·.1 ·.2)).sum` |
| `mulTab s t` | 表的行式乘法：笛卡尔积 + 词拼接 + 系数相乘 |
| `evalTab_mulTab` | **表积的求值 = 求值之积**（让多项式恒等式落到 `List`/`ℚ` 的那一条） |
| `evalTab_nil/cons/append`、`evalTab_mul_single` | 上一条的组装件 |

**新增实测结论**：

* `decide` 对 `ℚ` 不归约（`Rat.blt` / `Rat.num` 不做 kernel 归约），
  所以「两条表相等」不能用 `decide`；只能让两侧用**同一套字面量**从而 `rfl`。
  这条与 `bch-port.md` §5.3 原有记录一致。
* `List.flatMap` 的求值没有现成的 `List.sum_flatMap`，`evalTab_mulTab` 靠对 `s` 的结构归纳
  （`List.flatMap_cons` + `evalTab_append` + `evalTab_mul_single`）走通。

**剩余的工程件**（已定位，不含数学障碍）：

1. 生成器输出规范表（行序 = 校验器的计算序，系数用与 `bchSexticTermCoeffs`
   相同的字面量）。
2. 在 Lean 里写出**自由侧的 Dynkin 表**：`mulTab` 组合 `Z`、`T2`…`T5`，
   与生成器输出同序，于是「表相等」是 `rfl`。
3. 用 `evalTab_mulTab` 把自由侧的**环表达式**（`bchW6 (mono …) …` 那一串）
   转成表，即得恒等式；再用 §3.2 的正向传输回到 `𝔸`，替换 `SmallSDischarge.lean` 的 `sorry`。
4. 7/8 次项（`octic_pure_identity` / `nonic_pure_identity`）同一套流程：只要校验器扩到
   度 7/8 仍全绿，Lean 侧的形态完全不变。

---

## 阶段 A 施工记录（第三轮：基表落地的配方已定）

**已跑通一条完整的基表引理**（`T₂`，探针已删，配方保留）：度数 2 的基表
`T₂ = a²/2 + ab + b²/2` 满足

```lean
evalTab (tTab 2) = bchT2 (mono [0] 1) (mono [1] 1)
```

收尾的**固定配方**（五步，之后每个 `T_k` 都是一样的）：

```lean
rw [tTab, bchT_k, evalTab]                       -- 展开成单项式之和
simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
rw [mono_sq 0, mono_sq 1, mono_mul,              -- 幂与积 → 单项式
    show (2:ℚ)⁻¹ • mono [0,0] 1 = mono [0,0] ((2:ℚ)⁻¹ * 1) from by rw [mono, mono, smul_smul],
    ...]                                          -- 纯量搬进系数
norm_num [mono, List.nil_append, List.cons_append, List.singleton_append, List.append_nil,
  FreeMonoid.ofList_cons, FreeMonoid.ofList_singleton]   -- 词归一 + 系数算术
abel                                              -- 加法重排（两侧项序不同）
```

其中新增的小引理只有一条：

```lean
lemma mono_sq (k : Fin 2) : (mono [k] 1) ^ 2 = mono [k, k] 1 := by
  rw [mono_pow, List.replicate_succ, List.replicate_one]
```

**关键实测**：一旦 `mono` 用「幂 / 积」写成 `MonoidAlgebra.single (FreeMonoid.of 0 * …) …`，
`norm_num` 配 `FreeMonoid.ofList_*` 就能把词归一，最后只剩**加法项序**不同，
一条 `abel` 收掉。也就是说这条路的收尾成本是**常数级**的，不随度数增长。

**注意**：`mono_pow` 之后的 `List.replicate` 归一用 `List.replicate_succ` + `List.replicate_one`
即可，**不要**把 `List.append_cons` 放进 simp 集（会 `maximum recursion depth`）。

**下一步**：把 `tTab` 0..5 与上面五个配方（T₂…T₅ 各一条）写进正式文件，
接 `evalTab_mulTab` 组合出自由侧 Dynkin 表，再比对生成器输出的规范表。

---

## 阶段 A 施工记录（第一轮：合并与 API）

**已落地**：`FQFP/BCH/WordAlgebra.lean`（已注册进 `FQFP.lean`），
全部声明在 `namespace FQFP.BCH.WordAlgebra` 下。它由原来的 `WordAlgebraLift.lean`
（`wordAlgebraLift` / `wordAlgebraLift_injective`）与 `FreeWordCoeff.lean`（系数读取）
**合并**而成，两个旧文件已删除；`BinWordAlg` 这个 `abbrev` 无人使用，也已删除。
验收全绿：`lake build FQFP`、`lake exe runLinter FQFP.BCH.WordAlgebra`、`lake exe lint-style`。
零 `sorry`、零 `maxHeartbeats` bump。

已证声明：

| 声明 | 内容 |
|---|---|
| `wordAlgebraLift a b` | 自由词代数到任意 `ℚ`-代数 `𝔸` 的求值（`MonoidAlgebra.lift` ∘ `FreeMonoid.lift`） |
| `wordAlgebraLift_injective` | 在两个自由生成元处单射（系数比对可靠） |
| `freeGen` | 两个生成元，`MonoidAlgebra.of ∘ FreeMonoid.of` |
| `mono l q` | 单项式 `q • of (ofList l)` |
| `ofList_mul` | `ofList a * ofList b = ofList (a ++ b)`（推回规范形） |
| `of_pow_eq_ofList_replicate` | `(of k)^n = ofList (replicate n k)` |
| `mono_singleton` | `mono [k] 1 = freeGen k` |
| `mono_mul` | `mono l₁ r₁ * mono l₂ r₂ = mono (l₁ ++ l₂) (r₁ * r₂)` |
| `prod_eq_mono` | `(l.map freeGen).prod = mono l 1` |
| `wordEval_gen` | **桥**：`wordEval freeGen v = mono (List.ofFn v) 1` |
| `coeff_mono` | 单项式在具体词上的系数 |
| `coeff_smul_mono` | 缩放单项式的系数 |
| `coeff_mono_mul` | 两个单项式之积的系数 |
| `mono_pow` | `(mono [k] 1)^n = mono (replicate n k) 1` |

**新增实测结论（补充 §1.2）**：

* **`MonoidAlgebra` 与 `Finsupp` 的转换走 `MonoidAlgebra.coeff` / `ofCoeff` / `coeff_single`，
  不需要 `change`。** 可行路径（`coeff_mono` 就是这么写的）：

  ```lean
  rw [mono, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  ```

  关键是一路 `.coeff` **已经在目标里**，`coeff_single` 把 `MonoidAlgebra.single m r` 的
  `.coeff` 换成 `Finsupp.single m r`，于是 `Finsupp.single_apply` 能接上。
  之前的 `change` 是因为把 `mono_eq_single` 写在前面、绕了一圈；那条引理已删。
* **`decide` / `native_decide` 在这条路线上没有位置**，也不该被考虑：两者的 `DecidableEq`
  对 `MonoidAlgebra` 和 `Finsupp` 都经 `Quot` 不归约（`native_decide` 另有一层
  `Finsupp.single` 是 noncomputable，编不出代码）。`decide` 只作为 `rw` 的**输入**
  出现在「具体词相等/不等」这种 `List` 级命题上。
* `norm_num` 必须在 `Finsupp` 展开**之后**才能收尾：先 `norm_num` 会把 `ℚ` 系数算掉、
  却把 `Finsupp.single m q` 当成原子留着，随后的 `rw` 匹配不上（实测「simp made no progress」）。
  正确顺序是 `simp only [<展开词>] → simp only [Finsupp.single_apply] → norm_num`。

**未完成（阶段 A 的核心）**：把「任意乘积的系数」变成一条可复用的读法。
目前 `bchT4 (mono [0] 1) (mono [1] 1)` 的一个系数已经能一路化简到
五个 `Finsupp.single … ` 相加的具体目标，但**收尾那一步没有自动化**：需要一条

```lean
lemma prod_mono_aux (o : ℚ) (os : List (List (Fin 2) × ℚ)) :
    o • ((os.map fun p => mono p.1 p.2).prod)
      = mono (os.map Prod.fst).flatten (o * (os.map Prod.snd).prod)
```

即「单项式之积的词是各词拼接、系数是各系数之积」。骨架已对（`smul_mul_assoc` +
`smul_smul` + `ih` + `mono_mul`），只剩两处 `rw` 的匹配要调：`mono` 是 `abbrev`，
`MonoidAlgebra.of … (ofList l)` 与 `mono l 1` 之间 `rw` 不穿（需一条 `ofList_eq_mono`
或直接 `rw [mono]` 展开）；以及空表分支的 `[].prod` 不归约。
它一成立，`bchT4`/`bchY36` 这类「单项式之积的和」的系数就是机械代入，
接着才是 64 个词的比对。

---

## 0. 结论摘要（先看这段）

| 问题 | 结论 |
|---|---|
| 自由词代数路线数学上成立吗？ | 成立。`ℚ[FreeMonoid (Fin 2)]` 是双生成元自由结合代数，词是基，系数比对可靠。 |
| 已有的两个基建文件还用得上吗？ | `WordAlgebraLift.lean` 的 `wordAlgebraLift` / `wordAlgebraLift_injective` **保留**；`BinWordAlg` 这个 `abbrev` 建议删掉直接内联。 |
| `free-word-algebra-route.md` 的哪条结论是错的？ | **§5bis「缺一个 normalizer / 需要 §5.1 的三条原语串起来」是错的**。真正的分配律用的是**已有的** `MonoidAlgebra.coeff_mul`（`Finsupp` 卷积公式）。不需要 `sum_mul_sum`，不需要 `m_mul`，不需要 `single_add` 合并——**卷积公式一次给出所有项**。 |
| 那真正的卡点是什么？ | 只有两件工程件：（1）`MonoidAlgebra` 在 v4.34.0 里是**单字段 structure**，不是 `Finsupp` 的同义类型，所以 `Finsupp.single_eq_same` 之类**不能直接 `rw`**，必须先 `.coeff` / `change`；（2）`FreeMonoid.of` 的乘积是**右结合**的，与 `FreeMonoid.ofList` 的字面形状对不上，需要一条规范化引理。**都是机械问题，不是数学问题。** |
| 能不能用 mathlib 现成定义拼出来？ | 能。求值走 `MonoidAlgebra.lift` ∘ `FreeMonoid.lift`（已封装成 `wordAlgebraLift`）；分配律走 `MonoidAlgebra.coeff_mul`；词等于 `FreeMonoid.ofList`（`Equiv.refl`）；单项式乘积走 `MonoidAlgebra.single_mul_single`。**探针里唯一新增的引理是一条 `rfl` 级的词规范化。** |
| 下一步做什么？ | **先做垂直切片（只做 degree-6 一个恒等式）**，把上面两个工程件钉死；再按 §6 的顺序重构 `BCHTerms.lean` / `WordExpansion.lean`。 |

---

## 1. 本轮实测记录（哪些通过、哪些踩坑）

### 1.1 通过的关键事实

| 事实 | 写法 | 出处 |
|---|---|---|
| `List.prod_map_hom` 的准确签名 | `(List.map (⇑g ∘ f) L).prod = g (List.map f L).prod`，`g : G` 是 `MonoidHomClass` | `Mathlib/Algebra/Group/...`（`#check` 实测） |
| 词求值的桥 | `FreeMonoid.lift_ofList : lift f (ofList l) = (l.map f).prod` | `Mathlib.Algebra.FreeMonoid.Basic` |
| 两个同态相等 | `FreeMonoid.hom_eq`（逐生成元比对） | 同上；探针里用它把 `FreeMonoid.lift gen` 与 `MonoidAlgebra.of ℚ _` 对齐，**一行** |
| `wordEval` 即单项式 | `wordEval gen v = mono (List.ofFn v) 1`，`gen := MonoidAlgebra.of ℚ (FreeMonoid (Fin 2)) ∘ FreeMonoid.of`，`mono l q := MonoidAlgebra.single (FreeMonoid.ofList l) q` | 探针通过（`rw [wordEval, ← h, FreeMonoid.lift_ofList]`，`h` 由 `FreeMonoid.hom_eq` 给出） |
| 分配律 | `MonoidAlgebra.coeff_mul (x y : R[M]) (m : M) : (x * y).coeff m = x.coeff.sum fun m₁ r₁ ↦ y.coeff.sum fun m₂ r₂ ↦ if m₁ * m₂ = m then r₁ * r₂ else 0` | `Mathlib.Algebra.MonoidAlgebra.Defs`（**这就是需要的唯一分配律**） |
| 系数即 `Finsupp` | `MonoidAlgebra.coeff_inj : x.coeff = y.coeff ↔ x = y`；`coeff_add` / `coeff_smul` / `coeff_single` 全是 `rfl` | `Defs.lean:149,198,318,225` |
| 词的相等可判 | `example : FreeMonoid.ofList ([0,0] ++ [1]) ≠ FreeMonoid.ofList [1,0,0] := by decide` | 探针通过（`instDecidableEqFreeMonoid` + `List` 可判） |
| 单项式乘积 | `MonoidAlgebra.single_mul_single : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)` | `Basic.lean`（注意：**不是** `Finsupp.single_mul_single`，后者不存在） |

### 1.2 踩到的坑（给下一步省时间）

**坑 1：`MonoidAlgebra` 在 v4.34.0 是 structure，不是 `Finsupp` 的同义类型。**

```lean
structure MonoidAlgebra (R M : Type*) [Semiring R] where
  ofCoeff ::
  coeff : M →₀ R
```

后果（都实测过）：
* `example : MonoidAlgebra.single m (1:ℚ) = (Finsupp.single m 1 : M →₀ ℚ) := rfl` —— **类型不匹配，失败**；
* `(MonoidAlgebra.single m 1 : MonoidAlgebra ℚ M) x` —— **"Function expected"，失败**；
* `rw [Finsupp.single_eq_same]` 在 `(MonoidAlgebra.single m 1).coeff x` 上 —— **"Did not find an occurrence"，失败**；
* `change (Finsupp.single m 1) x = 1` —— 也失败。

**正确写法**：先用 `.coeff` 把目标降到 `Finsupp` 层，再 `rw`：

```lean
-- 通过（探针 RESULT A/B）
example : (mono [0,0] 1 * mono [1] 1).coeff (FreeMonoid.ofList [0,0,1]) = 1 := by
  unfold mono
  rw [MonoidAlgebra.single_mul_single, mul_one, ofList_append',
    show ([0,0] ++ [1] : List (Fin 2)) = [0,0,1] from rfl]
  simp
```

`ofList_append' := (FreeMonoid.ofList_append a b).symm`，即把 `ofList a * ofList b` 推回
`ofList (a ++ b)`。

**坑 2：`FreeMonoid.of` 的乘积是右结合的。**

`MonoidAlgebra.single_mul_single` 作用后词是 `of 0 * (of 0 * of 1)`，而规范形是
`ofList [0,0,1]`。`norm_num` / `simp` 都收不掉（`List.append_cons` 进 simp 集会
`maximum recursion depth`）。可行的两条：
* 要求词的形状**从左边拼**：`ofList_append'` 给出 `ofList (a ++ b)`，其中 `b` 是单元素列表，
  再 `show ([0,0] ++ [1]) = [0,0,1] from rfl` 把列表字面量归一；
* 或者为每种长度准备一条 `rfl` 级引理 `of a * (of b * of c) = ofList [a,b,c]`
  （`rw [ofList_cons, ofList_cons, ofList_singleton]` 后 `rfl`）。

**坑 3：`coeff_mul` 之后是嵌套 `Finsupp.sum`，`norm_num` 收不动。**

```lean
rw [MonoidAlgebra.coeff_mul]
-- ⊢ (single (of 0) 1 + single (of 1) 1).sum fun m₁ r₁ ↦
--     (single (of 0) 1 + single (of 1) 1).sum fun m₂ r₂ ↦ if m₁ * m₂ = m then r₁ * r₂ else 0 = 1
```

`norm_num`、`Finsupp.sum_add_index`、`Finsupp.sum_single_index` 都没关掉它。要么
`change` 到 `Finset.sum` 形态，要么**在数据层就把乘积做完**（见 §3 的 `coeffMul`）。

**坑 4：`List.append_cons` 不能进 simp 集**（`maximum recursion depth`）。
列表字面量的相等一律交给 `show … from rfl` 或 `decide`。

**坑 5：`decide` 判不了 `FreeMonoid` 词的不等**，除非先 `rw [FreeMonoid.ofList.injective.eq_iff]`
把两边降到 `List`；直接写 `by decide : FreeMonoid.ofList a ≠ FreeMonoid.ofList b` 在部分形状下会失败。
稳妥写法：

```lean
rw [Finsupp.single_eq_of_ne (by
  rw [FreeMonoid.ofList.injective.eq_iff]; decide : a ≠ b)]
```

（但注意坑 1：这一步只在 `.coeff` 降到 `Finsupp` 之后才可能触发。）

---

## 2. 对 `free-word-algebra-route.md` 的修正

| 原文 | 修正 |
|---|---|
| §5bis.0「缺一个『词单项式正规化 + 同类项合并』的过程」 | **不需要**。`MonoidAlgebra.coeff_mul` 就是那个过程：它对每个 `(m₁, m₂)` 对直接给出卷积项，同类项由 `Finsupp` 的加法自动合并。 |
| §5bis.2「`noncomm_ring` 分配了但把 `single` 当原子，既没把词乘起来也没合并同类项」 | 对 `noncomm_ring` 的判断正确，但结论方向错了：**根本不该用 `noncomm_ring`，也不该手工分配**，而该用 `coeff_mul`。 |
| §5bis.3 路线 (A) 手写 normalizer | 不需要。 |
| §5bis.3 路线 (B) 换载体 `Finsupp (List (Fin 2)) ℚ` 配自定义乘法 | **明确否决**：自定义 `Semiring` 是典型的「mathlib 已有定义能组合出来却另开一套」，且会与 `MonoidAlgebra` 的全部 API 脱钩。 |
| §5quater.3「需要 `Finset.sum_mul_sum`（分配）+ `m_mul`/`single_mul_single`（单项式相乘）+ `Finsupp.single_add`（合并同词项），缺的是把它们串起来」 | 三条里只需要第二条（且用 `MonoidAlgebra.single_mul_single`），分配律与合并都由 `coeff_mul` 一体给出。 |
| §5quinquies.3「`List.ofFn` 不归约 → 必须生成显式列表」 | **仍然成立且重要**。`reprTab` 在显式列表上归约、在 `List.ofFn` 上不归约，这条实测无误。 |
| §5sexies.3「让两侧字面上是同一张表 → 比较就是 `rfl`」 | 这正是**应该走的路**：把 Dynkin 侧也变成同一张表（数据层做乘法），就不要 64 个词逐个比对了。 |

---

## 3. 需要设计的三个数据结构（以及「不许新开定义」的边界）

用户约束：**能用 mathlib 现成定义简单组合出来的对象，不要新开一个定义。** 按这条逐项审：

| 想要的 | 是否新开 | 结论 |
|---|---|---|
| 自由词代数的类型 | 否 | 直接写 `MonoidAlgebra ℚ (FreeMonoid (Fin 2))`。`BinWordAlg` 只是缩写，建议删掉内联。 |
| 自由元素到 `𝔸` 的求值 | 已存在 | `wordAlgebraLift`（`MonoidAlgebra.lift` ∘ `FreeMonoid.lift`）。用点 ≥ 5 处，命名有价值，保留。 |
| 词 → 单项式 | 否 | 组合 `MonoidAlgebra.single` + `FreeMonoid.ofList`。 |
| 词 → `𝔸` 的词积 | 已存在 | `WordExpansion.wordEval`。 |
| 系数函数 | 否 | `Finsupp` 本身就是系数函数；`MonoidAlgebra.coeff` 就是取它。 |
| **「表乘法」** | **需要判断** | 见下。 |
| 两份并行数据（词表 + 系数表） | **应合并** | 用户提议的「系数 list」正解。见 §4。 |

### 3.1 关于「表乘法」

如果两侧都要变成同一张表，就需要一个「表 × 表 → 表」的运算。**但这可以是纯数据层的
`List` 运算，不需要触碰代数结构**：

```lean
/-- 一张表：词（字母表）与系数配对。刻意不做成新类型——
`List (List (Fin 2) × ℚ)` 已经够用，`List.map` / `List.sum` / `List.flatten` 都是现成的。 -/
-- 不定义新类型。

/-- 表的乘法：笛卡尔积 + 词拼接 + 系数相乘。纯 `List` 运算。 -/
def mulTab (s t : List (List (Fin 2) × ℚ)) : List (List (Fin 2) × ℚ) :=
  s.flatMap fun p => t.map fun r => (p.1 ++ r.1, p.2 * r.2)
```

`mulTab` 是不是「能简单组合出来」？它等于 `s.flatMap (fun p => t.map …)`。这个组合本身
就是定义体，没有现成 mathlib 定义能直接给出（`List` 层面没有「多项式乘法」）。
所以 `mulTab` 是**允许的新定义**，但它必须是**数据层**的、不进任何数学陈述。

配套只需要的引理（每条都是对 `List` 的归纳，不需要任何代数）：

| 引理 | 内容 |
|---|---|
| `evalTab_append` | `evalTab (s ++ t) = evalTab s + evalTab t` |
| `evalTab_mulTab` | `evalTab (mulTab s t) = evalTab s * evalTab t` |
| `coeff_evalTab` | `(evalTab t).coeff = reprTab t`（`reprTab` 是同词系数求和） |
| `evalTab_of_reprTab_eq` | `reprTab s = reprTab t → evalTab s = evalTab t` |

**这四条正是 `Norm.lean` 里已经写通的那套**（本轮之前的探针，161 行，全部编译通过）。
它们**不含 `noncomm_ring`**，也不含任何 `maxHeartbeats`。也就是说：**该拿的部分已经拿在手里了**，
缺的只是把它接到 `BCHTerms.lean` 的数据形状上。

### 3.2 从表回到 `𝔸`：不需要单射

一个容易绕远的点：`wordAlgebraLift_injective` 在**正向**传输里**用不上**。
证明结构是

```
在 ℚ[FreeMonoid (Fin 2)] 里证 P(gen 0) (gen 1) = 0   （系数比对）
  → 对 wordAlgebraLift a b 取像                            （map_sum / map_smul / lift_single）
  → P a b = 0                                              （map_zero）
```

正向只需要「同态保持运算」，这是 `map_*` 的自动结果。单射只在**反向**（从 `𝔸` 的恒等式
反推系数恒等式）才需要，而本路线不走反向。

**所以 `wordAlgebraLift_injective` 与 `FreeAlgebra.equivMonoidAlgebraFreeMonoid` 的桥接
（`private def freeGenerators` + `private theorem wordAlgebraLift_free_eq_symm`）在重构后
可能变成死代码。** 重构时先确认还有没有别的消费者，没有就删掉——这也符合「不要为了
已有定义再包一层」。

---

## 4. `BCHTerms.lean`：系数函数重定义为「系数 list」

### 4.1 现状的三处病

1. **两份并行表**：`bchSexticTermWords : Fin 28 → Fin 6 → Fin 2` 与
   `bchSexticTermCoeffs : Fin 28 → ℚ` 是同一个数学对象（自由代数的一个元素）的两个投影，
   靠下标隐式对齐。任何一处生成错误都不会被类型系统发现。
2. **无法做系数比对**：`List.ofFn` 编译成 `Fin.foldr`，`simp` 不归约（实测，`Fin 2` 和 `Fin 28`
   都一样），所以系数既不能 `rfl` 也不能 `decide`。
3. **四组并列**：五次项被拆成 `bchQuinticGroup{1,4,6,24}` + 四张词表，纯粹为了分组做范数界；
   对系数比对是噪声。

### 4.2 提议的形状

```lean
/-- 一张词表：`(字母串, 系数)` 的列表，按源里的规范词序给出。
生成器负责保证词序与系数互相对齐，`--check` 交叉核对。 -/
def bchSexticTermTable : List (List (Fin 2) × ℚ) :=
  [([0, 0, 0, 0, 1, 1], -1 / 1440), … ]   -- 28 项，由 scripts/gen_*.py 生成

/-- 表的求值：一行就是原定义。`wordEval` 是现成的，`wordAlgebraLift` 是现成的。 -/
noncomputable def bchSexticTerm (a b : 𝔸) : 𝔸 :=
  ∑ p ∈ bchSexticTermTable, p.2 • wordEval ![a, b] (List.ofFn p.1)   -- 或 List 版 wordEval
```

* **接口不变**：`bchSexticTerm : 𝔸 → 𝔸 → 𝔸`，下游一行不用改。
* **系数函数就是 `bchSexticTermTable`**，`Finsupp` 可由它构造，且**归约**（显式列表）。
* 范数界仍然一行：把表当索引，`norm_sum_smul_wordEval_le` 直接吃（见 §5.3）。
* 五次项同理：一张 30 行的表替掉四组 + 四张词表；范数界的 `176/720` 从表的绝对值和算出。

### 4.3 需要注意的接口后果

* `bchQuinticGroup{1,4,6,24}` 及其 `_smul`、`norm_*_le` 有下游消费者
  （`QuinticRemainder.lean`、`QuinticTaylor2.lean`、`SmallSDischarge.lean`）。
  合并成单表会**减少**这些消费者的数量，但需要同步改 `QuinticTaylor2` 的分片定义
  （它现在正是按「四组 × 子集」组织的，见 `bch-port.md` §3.2）。
* `bchCubicTerm` / `bchQuarticTerm` 是**紧凑的括号表达式**，不是词表和。它们不该被改成表
  （那会破坏「数学陈述的忠实性」：源就是把三次/四次写成交换子的）。系数比对只在
  `_LQ_decomp` 那种恒等式里需要它们，届时可以在自由代数侧临时展开。
* `norm_bchSepticTerm_le` / `norm_bchOcticTerm_le` 现在的 `set_option maxRecDepth 8000 in`
  是「平坦表 + 系数向量」逼出来的。**改成表之后系数是显式列表，`simp` 不需要穿
  `Fin.sum_univ_succ` 那 126 层**，这条 `maxRecDepth` 很可能可以去掉——这是重构的一个
  可验证收益，值得在切片里一并测。

---

## 5. `WordExpansion.lean`：需要重构，但幅度可以很小

用户提出「`WordExpansion.lean` 可能也需要被重构」，这个判断成立。分三部分看：

### 5.1 `wordEval`（保留，最多加一个 `List` 入口）

```lean
abbrev wordEval {n : ℕ} {κ 𝔸 : Type*} [Monoid 𝔸] (letters : κ → 𝔸) (v : Fin n → κ) : 𝔸 :=
  ((List.ofFn v).map letters).prod
```

这条**方向是对的**（arity-free、`abbrev` 保持透明、`List` 现成 API），不建议推翻。
但它把词固定成 `Fin n → κ`，而系数比对天然用 `List κ`。两条出路：

* **(a) 加一个 `List` 版**：`wordEvalList letters l := (l.map letters).prod`——但这**是新定义**，
  而且它就是 `(·.map letters).prod`，属于「能简单组合出来」。**更好的做法**：不新增定义，
  在需要处直接写 `(l.map letters).prod`，让 `List.prod` / `List.prod_append` 的现成 API 工作。
* **(b) 让表里的词存成 `Fin n → Fin 2`**：那又回到 `List.ofFn` 不归约的死路。

**结论：选 (a)，但不新增 `wordEvalList`，直接用 `(l.map letters).prod`。**
`wordEval` 保持不变，供既有的范数引理继续用。

### 5.2 范数层（保留，几乎不动）

`norm_prod_map_le`、`norm_binWord_le`、`norm_sum_smul_prod_map_le`、
`norm_sum_smul_wordEval_le`、`norm_sum_wordEval_le` 全部**与数据表示无关**
（`ι` 是任意 `Fintype`，`v : ι → Fin n → κ`），是把词表从 `Fin 28` 换成
`Fin table.length` 或直接换 `List` 索引即可。这部分是阶段 2/3 已经压下来的最大杠杆，**不动**。

### 5.3 唯一真正需要审的：子集展开那一段（`wordAPositions` / `wordSubstA` / `prod_map_add`）

`prod_map_add`（顺序保持的 `(a + c)` 展开，`[Semiring 𝔸]`，无 `noncomm_ring`）是为
**`bchQuinticTermTaylor2Decomp`** 写的，而 taylor2 已经完成、正在服役。所以：

* **不要动它**——它在服役，且证明无 bump。
* 但如果 §7 的自由代数路线推广到 `QuinticMixed` / `SexticMixed` / `SepticTaylor`
  的 taylor2 型分解，这些分解会**重新变成系数比对的形状**，届时 `prod_map_add` 这条
  子集展开路线可能整体被替换掉。**这是一个需要在切片之后重新评估的决策点**，
  不要现在就删。

### 5.4 建议顺手清理的死代码

* `probe2.lean`、`xxyyytest.lean`（工作树根）—— 探针残留，不在构建内，建议删。
* `FreeTables.lean`、`Norm.lean`（工作树根）—— 见 §6.1，收敛进正式文件。
* `WordNorm.lean` 在本轮改动里被删了 68 行（`git diff` 可见），确认是有意为之还是顺手删的。

---

## 6. 分阶段实施方案

### 阶段 A（切片，1 个文件，先做这个）

**目标**：只证 degree-6 的 `septic_pure_identity`，把 §1.2 的两个工程件钉死，拿到心跳读数。

1. 新建 `FQFP/BCH/FreeWordCoeff.lean`（名字待定，按数学内容命名）：
   * `wordEval` 与 `MonoidAlgebra.single`/`FreeMonoid.ofList` 的桥（§1.1 第 4 条）；
   * 词规范化引理（坑 2 的两种写法各来一条，取最省的那条）；
   * `evalTab` / `mulTab` / `reprTab` 四条引理（§3.1，从 `Norm.lean` 收敛过来）。
2. 把 `septic_pure_identity` 的**自由代数版**陈述出来并在其上完成证明：
   * 自由侧 `W6/T2…T5/Y36/Y46/Y56` 用 `mulTab` 在数据层算出四张表；
   * `bchSexticTerm` 侧的 28 项表由生成器给出；
   * 两表的 `reprTab` 逐词比对（64 个词；**先测逐词 `norm_num` 的心跳**，
     如果太慢再用「两侧同一张表 → `rfl`」的形态）。
3. 正向传输回 `𝔸`（§3.2），替换 `SmallSDischarge.lean` 里的 `sorry`。
4. 记录：心跳读数、`maxRecDepth` 是否可去、每条新引理的行数。
5. 验收：`lake build FQFP`、`lake exe runLinter`、`lake exe lint-style`，零 `sorry`。

**切片失败的判据**：如果 64 个词的比对仍然需要 `maxHeartbeats`，说明「按词逐项」
这条路的心跳与词数成正比且常数太大；那时改用「两侧同一张表」的形态（把 Dynkin 侧
完全数据化，`rfl` 收尾），或者放弃自由代数改用 §6.4 的降级方案。

### 阶段 B（`BCHTerms.lean` 数据形状重构）

前提：阶段 A 通过。

1. 生成器改为输出**单张表**（词 + 系数，按源词序），替掉「词表 + 系数表」两份数据；
   `--check` 交叉核对词数、词互异、公分母、系数和为零（Lie 元素）。
2. `bchSexticTerm` / `bchSepticTerm` / `bchOcticTerm` 改成表上的 `∑`；顺带删掉
   两处 `set_option maxRecDepth 8000 in`（可验证收益）。
3. 五次项：四组 + 四张词表 → 一张 30 行表；`norm_bchQuinticTerm_le` 的 `176/720`
   改由表的绝对值和给出。
4. 同步改 `QuinticTaylor2.lean` 的分片定义（它依赖四组的名字）。
5. 验收全绿，`SmallSDischarge` 的 degree-5/6 恒等式改走新的系数比对路径。

### 阶段 C（下游恒等式迁移）

按 `bch-port.md` §3.3 的表，从紧到松：
`QuinticMixed` → `SexticMixed` → `SepticTaylor` → `RemainderBounds` →
`SymmetricQuinticCore` → `SymmetricSeptic{PhaseBC,Pieces,Assembly}` → `BCHHigherOrder`。

每一步都是「纯恒等式层」的替换，范数界层不受影响。

### 阶段 D（清理）

* `WordExpansion.lean` 的子集展开段：视阶段 C 的结果决定是保留还是退役（§5.3）。
* `WordAlgebraLift.lean`：确认 `wordAlgebraLift_injective` 是否还有消费者，
  没有则连同 `freeGenerators` / `wordAlgebraLift_free_eq_symm` 一起删（§3.2）。
* 删掉工作树根的 `FreeTables.lean`、`Norm.lean`、`probe2.lean`、`xxyyytest.lean`。
* 更新 `artifacts/bch-port.md`（它现在还写着「阶段 3」但实际已到六/七/八次项，
  §3.3 的表与工作树状态已经不一致）和 `artifacts/free-word-algebra-route.md`
  （按 §2 修正）。

### 降级方案（如果自由代数路线整体不划算）

把 §6.1 的表机器**只**用于生成数据，恒等式仍在 `𝔸` 里用现有的
`unfold + simp only + noncomm_ring; module` 证，但把系数比对的部分换成
「两侧表的 `reprTab` 相等」的**独立校验器**（`scripts/` 里的 Python 工具，
像已删的 `check_pure_identity.py` 那样），只保证数据不错、不替代证明。
代价是 degree-6 及以上的恒等式仍然需要 `maxHeartbeats`——所以这只是保底。

---

## 7. 明确的决策点（需要你拍板）

1. **切片先做 degree-6 的 `septic_pure_identity`**（推荐）还是先做更小的 degree-4
   作为脚手架验证？后者更省时但对天花板没有说服力。
2. **系数比对的形态**：逐词 64 次 `norm_num`（通用、可推广到 7/8 次项）还是
   「两侧同一张表 → `rfl`」（更快但要求 Dynkin 侧完全数据化，且要额外证明
   「数据化的表 = 环表达式」）？建议**先试前者**，因为它对 7/8 次项是同一套代码。
3. **五次项的四组是否合并成单表**（阶段 B.3）？合并会简化系数比对，但会动
   `QuinticTaylor2.lean` 已经稳定的分片结构。
4. **`wordAlgebraLift` 是否保留命名**？按「能组合就不新开」它应该内联；
   但它在 ≥5 处出现且数学上是「自由代数的求值」这一有名字的概念，建议保留。
