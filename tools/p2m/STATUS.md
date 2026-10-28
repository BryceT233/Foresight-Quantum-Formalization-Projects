# TrotterError → Prove2Me 发布前的本地审计报告

> 生成时间：2026-09-28 ｜ 状态：**Phase 0 与 Phase 1 已完成，等待 API key**

本文件记录在拿到平台凭据之前，已经独立于平台完成的所有验证工作。

---

## 1. 源项目定位（已核实）

| 项 | 值 |
|---|---|
| **Lake 项目根** | `D:\project\CQM1`（不是 `FQFP\`，`FQFP\` 只是库源码目录） |
| Lake 包名 | `FQFP` |
| Lean toolchain | `leanprover/lean4:v4.34.0` |
| mathlib pin | `5ed2965256430c3649e86755f9576b54eca72435`（`rev = v4.34.0`） |
| git remote | `https://github.com/BryceT233/Categorical-Quantum-Mechanics.git` |
| HEAD commit | `0e354ce6dc12288391d9c1092cbb92b083b53d3d`（2026-09-28） |
| LICENSE | Apache 2.0（仅 15 行 boilerplate 头，非完整文本） |
| 规模 | 41 个 `.lean` / 18,565 行；TrotterError 子树 16 文件 / 10,177 行 |

`lake build FQFP` **全绿通过（8961 jobs, exit 0）**。

---

## 2. sorry / axiom 审计 — 内核级（不是文本扫描）

**结论：TrotterError 子树完全干净。**

- 全树 `sorry` 文本命中 2 处，均在 `FQFP/CQM/Category/MonoidalCategory.lean` 的
  块注释 `/- ... -/`（149–161 行）内，`CQM` 与 TrotterError 无关。
- `axiom` / `admit` / `unsafe` / `native_decide` / `@[implemented_by]`：**0 命中**。

**内核级验证**（`tools/p2m/check_axioms.lean`，用 `Lean.collectAxioms`）：

对 21 个 headline / engine 定理逐个检查公理依赖，结果：

```
checked 21 theorems — extra-axiom: 0, missing: 0
```

全部 21 个定理的公理集合都恰好是 `[propext, Classical.choice, Quot.sound]`，
即**没有任何额外公理、没有 sorryAx**。满足 playbook Phase 0 的硬性门槛。

已核验清单：`trotter_error_bound_comm_scaling`、`trotter_error_comm_scaling`、
`trotter_error_bound_comm_scaling_of_skewAdjoint`、`trotter_error_comm_scaling_of_skewAdjoint`、
`multiplicative_error_bound_comm_scaling`、`multiplicative_error_comm_scaling`、
`multiplicative_error_bound_comm_scaling_of_skewAdjoint`、`multiplicative_error_comm_scaling_of_skewAdjoint`、
`norm_additiveKernel_le`、`norm_additiveResidual_le`、
`trotter_error_bound_one_norm_scaling`、`trotter_error_one_norm_scaling`、
`trotter_error_bound_one_norm_scaling_of_skew_adjoint`、`trotter_error_one_norm_scaling_of_skew_adjoint`、
`trotter_number_one_norm_scaling`、`norm_commutatorRemainder_le`、
`norm_commutatorRemainder_le_of_skewAdjoint`、`errorOrderCond_iff`、
`commutatorExpansion_conj`、`secondOrder_bound`、`firstOrder_bound`。

---

## 3. Stage 1 声明图（已提取）

`tools/p2m/extract_decl_graph.lean`（平台官方脚本，为 Lean 4.34 做了 3 处必要修补）
→ `decl_graph.jsonl`，**1473 条声明**，603 KB。

| 模块前缀 | 声明数 |
|---|---|
| `FQFP.TrotterError` | 676 |
| `FQFP.BCH` | 434 |
| `FQFP.CQM` | 360 |

TrotterError 明细：676 条中 **461 条有真实源码 span**，215 条是编译器生成
（`*.eq_*`、`*.match_*`，`startLine == 0`，按 playbook 规则在可达性计算**之后**丢弃）。
私有声明 154 条，instance 0 条。

### 脚本修补记录（重要）

平台脚本是为 Lean 4.30 写的，在 **4.34.0 上有 3 处不兼容**，已修：

1. `let some m := getMod n | continue` → 改为 `if ... isNone then continue`。
   （`let some x := e | continue` 在 4.34 的 `run_meta`/`for` 里报
   `unexpected token 'continue'`。）
2. 同上的第二处（`collect` 内部 `let some um := getMod u | continue`）。
3. `match ci with` 的**多个 arm 写在同一行**会让 4.34 parser 在第二个 `=>` 处
   报 `expected '⟩'`；改为**每个 arm 独占一行**后通过。

另：仓库 `.gitattributes` 规定 `*.lean text eol=lf`。复制脚本到 Windows 后若为 CRLF，
也会触发 parser 报错——已统一转成 LF。**这是 4.34 parser 的 CRLF 敏感性问题，务必记住。**

---

## 4. Phase 2 可达性闭包（已计算）

从 11 个目标定理出发，沿 `typeDeps + valueDeps` 做 BFS：

```
reached (含编译器生成): 415
kept (有真实 span):     358
  ├─ theorem  305
  ├─ def       51
  ├─ inductive  1
  └─ ctor       1
```

**关键结果：闭包泄露到 TrotterError 之外 = 0 条。** 即 TrotterError 是一个自洽的
发布单元，不依赖 `BCH` 或 `CQM`。

按模块分布：

| 模块 | kept | 模块 | kept |
|---|---|---|---|
| CommutatorExpansion | 47 | OrderCondition | 21 |
| ErrorTypes | 46 | MainTheorem | 17 |
| Calculus | 44 | OrderingRemoval | 15 |
| Commutator | 43 | ListLemmas | 13 |
| ProductFormula | 39 | ExpSMulConj | 12 |
| TimeOrderedExp | 29 | CommutatorScaling | 6 |
| OneNormScaling | 21 | Integrals | 5 |

TrotterError 有 span 的 461 条中 358 条可达，**103 条是死代码**，不上传。

### ⚠️ 重要发现：`Suzuki.lean` 与 `Prefactor.lean` 不在闭包内

这两个文件（Suzuki 18 定理、Prefactor 16 定理）**不被任何 headline 目标引用**。
它们实现 Lie–Trotter / Suzuki 二阶特例与一阶/二阶 prefactor 界
（`firstOrder_bound`、`secondOrder_bound`、`lieTrotter_eq_eval`、`suzuki_eq_eval` 等），
是独立结果而非主定理的依赖。

**需要你决定**：是否把它们作为额外的顶层目标一并发布（论文计划 3.3 节把它们列为
要报告的结果）。若发布，应把它们加进 roots 重算闭包。

---

## 5. ✅ 环境不匹配已解决 — 降级只需 6 处单行修改

**已用真实构建验证。** 结论推翻了最初的悲观估计（原本以为要改 1 万行）。

### 5.1 平台真实环境（`GET /environments`，已鉴权确认）

```json
{"mathlib_rev":"0df444a360eaa60ab8c11dca51a86af692955474","toolchain":"leanprover/lean4:v4.33.1","is_default":true}
{"mathlib_rev":"777aaa61dcd2a1258d2b4962dbe983ede4d23b2e","toolchain":"leanprover/lean4:v4.29.0-rc3","is_default":false}
{"mathlib_rev":"c5ea00351c28e24afc9f0f84379aa41082b1188f","toolchain":"leanprover/lean4:v4.30.0","is_default":false}
```

平台确实**没有 v4.34 环境**。默认目标是 `v4.33.1` / mathlib `0df444a`。

### 5.2 关键惊喜：v4.33.1 **支持 module system**

我先前用裸 `lean Test.lean` 得到的 "v4.33.1 不认 `module` 关键字" 是**错误结论**
（裸 lean 的 `--root` 选择问题）。用 `lake build` 实测：**`module` / `public import` /
`@[expose] public section` 在 v4.33.1 下全部正常工作**，大部分模块一次编译通过。

→ 所以**不需要**回退 module system。降级成本从「全量重写」降到「修 API drift」。

### 5.3 实测降级结果

在隔离 worktree `D:\p2m-v4331`（pin `v4.33.1` + mathlib `0df444a`，
`lake update` 后 8689 个 mathlib 缓存文件直接命中，**无需从源码编译 mathlib**）：

**TrotterError 全部 16 个模块编译通过，0 error。**

总改动 = **6 处单行修改**，全部是 mathlib v4.33→v4.34 的重命名/签名变化：

| 文件 | v4.34 写法 | v4.33.1 写法 | 原因 |
|---|---|---|---|
| `Commutator.lean:446` | `prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => …)` | `Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => …)` | 改名；且 `prod_le_one'` 需要 v4.33.1 没有的 `MulLeftMono ℝ` 实例 |
| `Calculus.lean:158` | `ite_eq_right h` | `if_neg h` | `ite_eq_*` 已废弃，改用 `if_pos`/`if_neg` |
| `ProductFormula.lean:268` | `prod_le_prod₀ (fun i _ => norm_nonneg _) (…)` | `Finset.prod_le_prod (fun i _ => norm_nonneg _) (…)` | 改名 |
| `ProductFormula.lean:388` | `dite_eq_left h` | `dif_pos h` | `dite_eq_*` 已废弃，改用 `dif_pos`/`dif_neg` |
| `ProductFormula.lean:394` | `dite_eq_right h` | `dif_neg h` | 同上 |
| `OneNormScaling.lean:377` | `Finset.prod_le_prod₀ (…)` | `Finset.prod_le_prod (…)` | 改名 |

> ⚠️ **实测结论：这 6 处修改不能反向兼容 v4.34.0。** 我试过把同样 6 处改动应用到
> v4.34.0 主仓库，`Commutator.lean:446` 会失败——两个版本的 `Finset.prod_le_one`
> 签名不同：
>
> - v4.34.0：`prod_le_one [MulLeftMono N] (h : ∀ i ∈ s, f i ≤ 1)`（**1 个**参数）
> - v4.33.1：`prod_le_one (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1)`（**2 个**参数）
>
> v4.33.1 里没有 `MulLeftMono ℝ` 实例，所以 `prod_le_one'` 也用不了。
> 这一处是**真正的 API 分歧**，无法用单行同时满足两个版本。
> 其余 5 处（`if_neg`/`dif_pos`/`dif_neg`/`prod_le_prod`/`prod_le_one`）都是
> 向后兼容的，只有 `Commutator.lean:446` 需要按版本二选一。
>
> → 主仓库 `D:\project\CQM1` 已 `git checkout` **完全还原到 v4.34.0 原始状态**
> （`lake build FQFP` 重新验证 8961 jobs 全绿），v4.33.1 适配只存在于 worktree。

### 5.4 v4.33.1 下重新做内核公理审计

用同一份 `check_axioms.lean` 在 v4.33.1 / mathlib `0df444a` 下重跑：

```
checked 21 theorems — extra-axiom: 0, missing: 0
```

**21 个 headline 定理在目标环境下依然只依赖 `[propext, Classical.choice, Quot.sound]`。**
降级没有引入任何 sorry 或额外公理。这是「移植」而非「重证」的证明。

### 5.5 顺手发现的 BCH / CQM 漂移（**与我们无关**）

同一 worktree 里 `lake build FQFP` 全量构建还报 4 处错，**全部在 BCH 和 CQM**：

- `BCH/WordNorm.lean:75` — `prod_le_prod₀`（同上改名）
- `BCH/Logarithm.lean:179/180/189/191/337/350` — `dite_eq_right` / `dite_eq_left`（同上改名）
- `CQM/Category/DaggerCategory.lean:197` — `zero_comp` 的 `Type mismatch`（这个不是简单改名）

由于 `FQFP.lean` 根模块 `public import` 了全部 40 个文件，**BCH/CQM 的错误会阻止
`FQFP` 根模块的 olean 生成**。但 TrotterError 子树本身可以单独构建
（`lake build FQFP.TrotterError.MainTheorem` 等），不受影响。

→ **发布 TrotterError 不需要修 BCH/CQM。** 但如果希望整个仓库在 v4.33.1 下全绿，
需要额外修这 4 处（其中 DaggerCategory 那处需要真正读懂证明）。

### 5.6 修正后的路线

**推荐：本地降级到 v4.33.1 并匹配平台 pin。** 6 处单行修改已完成并验证，
零 sorry 引入，公理审计通过。`D:\p2m-v4331` worktree 已处于可上传状态。

---

<details>
<summary>原始风险评估（已被上面的实测推翻，保留备查）</summary>

## 5-旧. 环境不匹配 — 最大技术风险（待 API key 确认）

平台文档列出的环境（`GET /environments` 为权威，需鉴权）：

| mathlib_rev | toolchain | 默认 |
|---|---|---|
| `0df444a360eaa60ab8c11dca51a86af692950474` | `leanprover/lean4:v4.33.1` | ✅ |
| `c5ea00351c28e24afc9f0f84379aa41082b1188f` | `leanprover/lean4:v4.30.0` | |
| `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e` | `leanprover/lean4:v4.29.0-rc3` | |

**你的项目是 v4.34.0 / `5ed2965`，与三者都不匹配。** playbook 明确要求：

> pick the **source-project commit whose own Mathlib pin matches it** … A matching pin means zero drift repair.

git 历史里只有两个 toolchain 值：`v4.33.0`（`7d71dc5` Initial commit）和 `v4.34.0`（`a946626` bump），
**没有 v4.33.1**。所以没有现成 commit 可用。

雪上加霜：**全部 40 个文件都用了 Lean 4.34 的 module system**
（`module` 头 + `public import`），而我实测 v4.33.1 无法解析 `module` 关键字
（`Test.lean:1:0: error: expected token`）。

→ 降到 v4.33.1 不是改 pin 那么简单，而是要把 40 个文件的 module system 全量回退，
再加上 v4.33→v4.34 的 mathlib API drift。**这是本次发布最大的工作量与风险。**

候选路线（待确认平台是否新增了 v4.34 环境后再定）：
- **A（首选）**：平台若已有 v4.34 环境 → 直接匹配，零改动。
- **B**：请平台管理员加一个 v4.34.0 环境（mathlib `5ed2965`）。
- **C**：本地降级到 v4.33.1，修 module system + drift（工作量大，约 1 万行需重新编译验证）。

</details>

---

## 6. 试跑结果（pilot dry-run）— 端到端跑通，暴露一个关键约束

### 8.1 已跑通的链路

选择最小目标 `TrotterError.norm_commutatorRemainder_le` 做试跑（闭包最小：
7 个模块 / 217 条声明）。生成器 `tools/p2m/gen_pilot.py` 实现了 playbook 的
**skeleton subtraction**：

1. 从 `decl_graph.jsonl` 取声明图，从 `sketch/*.jsonl` 取每个声明的
   `declStart` / `valStart` / `docstring` 字节位置。
2. **模块级**导入闭包（不是声明级）——见 8.3 的教训。
3. 按模块依赖拓扑排序，整模块拼接，剥掉 `module` / `import FQFP.*` /
   `@[expose] public section`，保留 `namespace` / `section` / `end`。
4. 用 `declStart..valStart` 切出 `formal_statement`（剥 docstring，补 `:= by sorry`）。
5. 生成平台入口 `theorem solution`。

**结果：`Sol_norm_commutatorRemainder_le.lean`（4818 行）在 v4.33.1 下编译干净。**

### 8.2 试跑提交结果：`FAILED`，但错误极有价值

`POST /submit-problem` → `202` + job_id，轮询 `~4 分钟后` → `FAILED`：

```
formal statement does not compile:
  line 4: Unknown identifier `commutatorRemainder`
  line 4: Unknown identifier `αCommConj`
  line 7: Unknown constant `TrotterError.norm_commutatorRemainder_le`
Note: ... the `autoImplicit` option is set to `false`
```

**这个失败证明了平台的关键约束（playbook Phase 7 的「Definitions 必须先行」）：**

- 每个定理的 `preamble` 里**不能放自己的 `def`**（`contribute.md` 明说：
  "Never local `def`s: publish those via `POST /submit-definition` and import
  them with `import Definitions.Def_<definition_name>`"）。
- 我的 pilot 把 `commutatorRemainder`、`αCommConj` 这些定义留在了 solution 文件里，
  于是 `formal_statement` 单独编译时找不到它们。
- 平台确实**独立编译 formal_statement**，不能靠 solution 文件兜底。

→ **正确顺序必须是**：先把 `def` 层上传成 `Definitions.Def_*` 包，然后每个
`formal_statement` 的 `preamble` 写 `import Definitions.Def_<name>`，
最后才上传 `Thm_` 存根和 `Sol_` 证明。这正是 playbook Phase 7 的顺序。

### 8.3 试跑中发现的三个真实坑（都已定位并修复）

1. **Stage 1 的 `valueDeps` 会漏边。**
   声明级可达闭包**不完整**：`integral_mul_left`、`TrotterError.List.*`
   等明明是必需依赖，但不在闭包里（图上确实有这些边，但沿私有辅助
   （`*._abel_1_1`、`*._simp_1_4`）走时闭包会漏）。
   → **修复：改用模块级 `import` 闭包，整模块发射。** TrotterError 子树在
   导入上是封闭的，不会泄漏到 BCH/CQM。

2. **Stage 2 的 `offset` 是 UTF-8 字节偏移，不是字符下标。**
   Lean 打印的是 `String.Pos`。用 Python 字符串切片（字符）会切错位置，
   表现为切出来的「语句」其实是证明体。
   → **修复：`data = text.encode('utf-8')` 后再按 offset 切片。**

3. **平台脚本在 Lean 4.34 上有 3 处 parser 不兼容**（见第 3 节），
   且**对 CRLF 敏感**（仓库 `.gitattributes` 是 `eol=lf`）。

### 8.4 入口点的正确写法

平台要求**顶层** `theorem solution`，类型与目标 `formal_statement` 完全一致。
踩坑记录（都试过并失败）：

- `theorem solution := <target>` → Lean 语法错误（`theorem` 不能无类型）。
- 手工把 binder 重建成 `fun (…) => …` → 实例 binder / 隐式 binder 重建极易出错
  （`_` 不绑定名字，后续 `Fin s → 𝔸` 就变成未绑定变量）。

**可用写法**（`exact` 让 Lean 从目标类型推断所有 implicit 与 instance binder）：

```lean
namespace TrotterError
theorem solution : ∀ {s} {𝔸 : Type*} [NormedRing 𝔸] … (A : Fin s → 𝔸) … , <结论> := by
  exact TrotterError.<target>
end TrotterError
```

### 8.5 下一步（明确）

1. 用生成器产出 **Definitions/Def_<module>.lean** 定义包（每个源模块一个，
   只含 `def`/`structure`/`instance`），走 `POST /submit-definition` 上传。
2. 每个 `Thm_*` 的 `preamble` 改为 `import Mathlib` + 所需的
   `import Definitions.Def_*`，**不含任何自有 `def`**。
3. 重新试跑 pilot 的 `submit-problem` → 应能 `PUBLISHED`。
4. 再 `POST /verify`（multipart：`theorem_id` + `file=@Sol_*.lean`）验证证明。
5. pilot 全绿后，再按 Phase 2 做完整的节点切分（379 个声明）并铺开上传。

---

### 6.5b 本轮（第 2–3 轮）实测通过的关键里程碑

| 提交 | 结果 | 证据 |
|---|---|---|
| `submit-definition` (`definition_name="Def_TrotterError"`) | ✅ `PUBLISHED` | id `a21336ae-…`（但模块名错，见 6.6） |
| `submit-definition` (`definition_name="TrotterError"`) | ✅ `PUBLISHED` | id `aa4c62f0-09e1-499c-aaab-31fc5fbd3d77` |
| `submit-problem`（**带 `import Definitions.Def_TrotterError` 的 preamble**） | ✅ `PUBLISHED` | id `f7c88b3b-41df-498e-af3e-2d9fbb8a5dd8` |
| `submit-problem`（第一次，preamble 只有 `import Mathlib`） | ❌ `FAILED` | `Unknown identifier 'commutatorRemainder'` |

**`submit-problem` 这次成功是决定性的**：它证明
「def 层先上传 → 定理 preamble 用 `import Definitions.Def_*` 引入 →
`formal_statement` 就能在服务端独立编译」这条链路完全成立。
第一次失败与这次成功的唯一差别就是 preamble。

服务端编译排队较慢：一次 `submit-problem` / `submit-definition` 约需
**3–10 分钟**（`PENDING` → `COMPILING` → 终态），`/verify` 类似。
按 379 个节点估算，铺开上传需要数小时到十几小时，必须用幂等上传器 + 后台任务。



playbook 只说"用 `import Definitions.Def_<definition_name>`"，实测才发现
**`definition_name` 必须是裸名字，模块名是 `Definitions.Def_<definition_name>`**：

| 我提交的 `definition_name` | 生成的模块 | `import` 应当写 |
|---|---|---|
| `Def_TrotterError` ❌ | `Definitions.Def_Def_TrotterError` | — |
| `TrotterError` ✅ | `Definitions.Def_TrotterError` | `import Definitions.Def_TrotterError` |

我第一次提交用了 `Def_TrotterError`，于是 `import Definitions.Def_TrotterError`
在服务端报：

```
formal statement does not compile: unknown import: Definitions.Def_TrotterError.
No such definition exists in this Lean environment (mathlib 0df444a).
Call POST /api/v1/submit-definition for 'TrotterError' first.
```

**报错信息本身就是答案**：服务端要的是 `definition_name = "TrotterError"`。
改用裸名重新提交后模块名就对齐了。

（旁证：平台自带示例 `examples/upload_full_project/expected/platform/Definitions/Def_SumSquares_Defs.lean`
给出的 import 是 `Definitions.Def_SumSquares_Defs`，即 `definition_name` 为
`SumSquares_Defs` —— 同样印证"模块名 = `Def_` + 裸名"。）

### 6.6 平台 Definitions 层的真实语义（试跑实测，文档没写清）

### 6.7 Definitions bundle 生成要点（`tools/p2m/gen_defs.py`）

生成一个能独立编译的定义包，踩了 5 个坑，全部已修：

1. **必须带上源模块的 `open` / `open scoped` / `attribute [local instance]`。**
   定义体是逐字摘出来的，缺了 `open Finset LieAlgebra` 就报
   `Unknown identifier 'ad'`；缺了
   `attribute [local instance] LieRing.ofAssociativeRing` 就报
   `failed to synthesize instance of type class LieRing 𝔸`。
   → 所有 `open` 统一收集后**放在全部 import 之后**（否则 `unknown namespace`）。

2. **import 要取整个 TrotterError 子树的并集。**
   项目模块只直接 import 了 5 个 Mathlib 模块，其余全靠 FQFP 内部 import 传递；
   剥掉 FQFP import 后传递面就丢了，报 `unknown namespace 'MeasureTheory'` /
   `'ContDiff'`。→ 收集子树里所有 `Mathlib.*` import 求并集。

3. **不能把 `/-!` 或 `/--` 当成前言的终止信号一刀切。**
   文件头部的模块 docstring 是 `/-! ... -/`，若一律 break 会丢掉后面的 `open`。
   → 需要注释状态机：`/-!` 和 `/-` 作为上下文丢弃，`/--`（声明的 docstring）
   才是前言的终点。

4. **`open TrotterError.List` 必须剔除**（该 namespace 不在本包里）。

5. **字节偏移必须全程一致**：Lean 的 `String.Pos` 是 UTF-8 字节偏移，
   混入字符计数会切错。已改为按行预计算字节索引。

### 6.8 定理侧 payload（已验证可在服务端编译）

```
preamble          : "import Mathlib\nimport Definitions.Def_TrotterError"
formal_statement  : 从 declStart..valStart 切出、剥 docstring、补 := by sorry
```

本地用**完全等同服务端的目录结构**验证过：

```
Definitions/Def_TrotterError.lean   → lake build 通过
Theorems/Thm_<slug>.lean            → 单独编译通过（preamble + formal_statement）
Solutions/Sol_<slug>.lean           → 单独编译通过
```

三条 gating 规则同时满足：顶层 `theorem solution` ✅ / 不 import 自己的目标 ✅ / 无 `sorry` ✅

---

### 6.9 平台验证的 `SORRY` 陷阱 —— 不能与目标的 `by sorry` 存根同名

第一次 `POST /verify` 返回：

```json
{"status":"SORRY",
 "error_message":"Usage of `sorry`/`sorryAx` is not allowed:\n  - line 4034: declaration uses `sorry`"}
```

**但提交的文件里一个 `sorry` 都没有**（我用 Python 逐字节确认：`contains "sorry": False`，
`count: 0`），而且本地内核级检查显示：

```
TrotterError declarations: 327
depending on sorryAx     : 0
```

即整份提交里**没有任何声明依赖 `sorryAx`**。所以这个 `sorryAx` 来自**平台侧**。

**根因（高度确信）**：平台把目标定理 `TrotterError.norm_commutatorRemainder_le`
以 `:= by sorry` 存根的形式放进待检查的环境里。我的 solution 文件**又完整重新声明了
同名定理**（skeleton subtraction 会把目标本身也发射出来），两者冲突 / 该名字在环境里
已经带有 `sorryAx`，于是验证器扫描到这个声明就报 `declaration uses sorry`。

**修复**：把重发射出来的目标声明**改名**成 `TrotterError.solution_helper`，
平台入口再用它来证明 `solution`：

```lean
open TrotterError

theorem solution : ∀ {s} {𝔸 : Type*} [NormedRing 𝔸] … (A : Fin s → 𝔸) … , <结论> := by
  exact TrotterError.solution_helper
```

两个配套要点（都踩过）：

- **入口点必须是 `∀ …` 形式，不能用裸 binder**。写成
  `theorem solution {s} {𝔸 : Type*} [NormedRing 𝔸] … : <结论>:= by exact …`
  会报 `typeclass instance problem is stuck: NormOneClass ?m`——
  实例 binder 成了元变量无法消解。加 `∀` 后 Lean 从目标类型反推，就正常了。
- **`solution` 必须是顶层**（不能包在 `namespace` 里），所以用 `open TrotterError`
  把名字带进作用域，而不是把 `solution` 放进命名空间。

> 这条对**整个 379 节点的铺开**都适用：每个 `Sol_*.lean` 里重发射的目标声明都要改名，
> 否则每个节点都会撞上平台自己的 `by sorry` 存根。

### 6.10 对照组实验：平台流水线本身是通的，`SORRY` 出在我们的证明链里
改名修复**没有**解决 `SORRY`（第二次提交仍在同一行 4034 报同样的错），
所以 6.9 的「同名冲突」假设**被证伪**。于是做了一个简单对照：

| 提交 | 内容 | 结果 |
|---|---|---|
| 对照定理 | `theorem P2MControl.add_zero_control (n : Nat) : n + 0 = n := by sorry` | `PUBLISHED` |
| 对照证明 | `import Mathlib` + `theorem solution (n : ℕ) : n + 0 = n := by simp` | **`ACCEPTED`** ✅ |
| pilot 定理 | `TrotterError.norm_commutatorRemainder_le` + Def preamble | `PUBLISHED` ✅ |
| pilot 证明 | 4811 行 solution | `SORRY` ❌ line 4034 |

**结论**：认证、上传、服务端编译、`/verify` 判定这条链路**完全正常**
（控制组 `ACCEPTED` 就是证明）。`SORRY` 是 pilot 证明特有的。

已排除的可能：
- 文件里没有 `sorry`（逐字节确认，count = 0）。
- 本地内核检查：`TrotterError` 命名空间下 **327 个声明，0 个依赖 `sorryAx`**。
- 目标声明已改名为 `solution_helper`，仍报同一行 —— 不是同名冲突。

**因此 `sorryAx` 只可能来自平台环境**：solution 里某个声明在服务端解析到了
一个带 `sorry` 的依赖。line 4034 = `lemma norm_commutatorRemainderTerm_le`，
它在本地是干净的。

**最可能的原因**：我用的「单文件内联」策略把**整条证明链**都塞进了一个
`Sol_*.lean`，而平台为每个定理保存的是 `by sorry` 存根。当内联文件里
重发射了平台已存在的同名定理/定义时，服务端环境里就出现了带 `sorryAx` 的
同名声明。改名只处理了**目标**这一个名字，链上其它与平台重名的声明没有处理。

### 6.11 结论：必须改用 playbook 的 **379 节点切分**，不能单文件内联

| 策略 | 本地能否编译 | 服务端能否通过 |
|---|---|---|
| 单文件内联整条链 | ✅ 能 | ❌ `SORRY` |
| playbook 的节点切分（`Sol_X` 只引用平台子节点） | ✅ 能 | 预期 ✅ |

单文件内联在**本地**看起来更省事，但它绕过了平台的节点模型，所以被 `sorry` 检查挡住。
**pilot 的价值正在于提前暴露了这一点** —— 否则会在铺开 379 个节点之后才踩到。

### 6.12 决定性实验：平台确实在读我们的文件，`sorryAx` 来自服务端环境

`SORRY` 报告的行号一直稳定在 4034，这很可疑（可能意味着平台读的是别的文件）。
于是做了**行位移对照实验**：在同一份 solution 前面加 2 行注释，使目标声明
从 4034 行移到 **4036** 行，重新提交：

| 提交 | 目标声明所在行 | 平台报告的行号 |
|---|---|---|
| 原文件（265751 B） | 4034 | `line 4034: declaration uses sorry` |
| 行位移后（+2 行） | 4036 | **`line 4036: declaration uses sorry`** ✅ |

**行号跟着走了** → 平台确实在编译我们提交的那一份文件，没有缓存也没有读错文件。

同时，本地对同一份文件做了穷尽的内核级检查（包含私有声明）：

```
declarations owned by this module : 336
depending on sorryAx              : 0
```

即**本地一个依赖 `sorryAx` 的声明都没有**。

**结论**：文件在本地干净、在服务端被判定使用了 `sorry`。差异只能来自**环境**——
服务端编译 solution 时，环境里存在本地没有的东西：平台自己保存的
`Theorems.Thm_<target>`（`:= by sorry` 存根）以及 `Definitions.Def_*` 节点。
solution 里**重新声明**了与这些平台节点同名的声明
（`commutatorRemainderTerm`、`commutatorRemainder`、`αCommConj`、
`adPow`、`adSequence`、`expSMulConj`、`layerSum` 都在 `Def_TrotterError` 里），
于是服务端环境中的名字解析到了带 `sorry` 的那一份。

**这就把「单文件内联」判了死刑**，并直接印证 playbook 为什么坚持：
`Sol_X` 只证明 `X`，其余一律 `import` 平台节点（`Theorems.Thm_*` / `Definitions.Def_*`），
**绝不重新声明平台上已有的东西**。

### 6.14 第一个真正的 split-node 节点（验证架构）

按 §6.13 的做法做了最小 split-node：

| 项 | 内容 |
|---|---|
| 目标 | `TrotterError.exp_neg_mul_self`（`Calculus.lean:723-726`，4 行，**无定理依赖**） |
| `formal_statement` | `open NormedSpace` + `theorem TrotterError.exp_neg_mul_self … := by sorry` |
| preamble | `import Mathlib` |
| solution | **只含 `theorem solution`**，无任何重发射声明 |
| 证明 | `intro 𝔸 _ _ _ x; simpa using (exp_add_of_commute (Commute.refl x).neg_left).symm` |

关键发现：**`exp` 在这个项目里是 `NormedSpace.exp`，不是 `Real.exp`**，
靠模块里的 `open NormedSpace` 进入作用域。语句和证明都必须带这行 `open`，
否则报 `Unknown identifier 'exp'`。这一点对全部 379 个节点的 payload 都适用——
`preamble` 必须包含源模块对应的 `open`（以及 `open scoped`）。

本地服务端等价布局两个都编译通过：

```
Theorems/Thm_exp_neg_mul_self.lean   → OK（preamble + formal_statement）
Solutions/Sol_exp_neg_mul_self.lean  → OK（仅 theorem solution）
```

平台侧：`theorem_id = ac8829e4-2dcc-4f19-80a7-2397990e6641`（已 `PUBLISHED`），
证明提交 `submission_id = daa69aec-…` → **`ACCEPTED`** ✅

**这是整个发布的决定性验证**：split-node 形态（`Sol_*` 只含 `theorem solution`、
不重发射任何声明、不 import 自己的目标）**能通过平台的 `sorry` 检查并验收**。
配合 §6.11（单文件内联 → `SORRY`）与 §6.10（对照组 → `ACCEPTED`），
架构问题彻底定性。

**平台现状（3 个节点）**

| 节点 | 类型 | id | 状态 |
|---|---|---|---|
| `TrotterError`（定义层） | Definition | `aa4c62f0-…` | PUBLISHED |
| `TrotterError.norm_commutatorRemainder_le` | Theorem | `f7c88b3b-…` | PUBLISHED / Open |
| `TrotterError.exp_neg_mul_self` | Theorem | `ac8829e4-…` | **Proved**（ACCEPTED） |

### 6.13 下一步（唯一正确路径）

1. 目标定理 `TrotterError.norm_commutatorRemainder_le` 已发布（`f7c88b3b-…`），
   `Definitions.Def_TrotterError` 已发布（`aa4c62f0-…`）——**基础设施已就绪**。
2. 写一个新的 `Sol_*.lean`：**只保留 `theorem solution` 本身**，
   其证明直接引用 `import Definitions.Def_TrotterError` 里的定义，
   **不重新声明任何东西**。这就是「split-node」形态。
3. 若该形态通过 `ACCEPTED`，则按 Phase 2 铺开 379 个节点：
   每个 `Thm_X` 先发布，每个 `Sol_X` 只引用子节点。
4. 注意 `Sol_X` 的证明体需要子引理，而这些子引理必须**先作为平台节点发布**
   才能被 `import Theorems.Thm_<child>` 引用——这正是 playbook 说的
   「叶到根」顺序，也是为什么 379 个节点必须拆开而不是内联。

---

## 9. 方向修正：以 **mission** 为发布单元，milestone 对照论文原文

### 9.0 两份 mission 产物已完成

见 **[PAPER_MAP.md](PAPER_MAP.md)**（275 行）与
**[mission_description.md](mission_description.md)**（约 1590 词）。

PAPER_MAP.md 的结构：

| 节 | 内容 |
|---|---|
| §A | 论文全部 30 条编号结果清单（按文件） |
| §B | **65 处** docstring 引用构成的权威映射表（论文 label → Lean 声明 → 状态） |
| §C | 论文中**尚未形式化**的结果（mission 的开发空间） |
| §D | 形式化相对论文的 **8 项约定/差异** |
| §E | mission 结构与 10 条 milestone（含推导出的论文编号） |
| §F | **milestone_description 的论文逐字原文**（可直接用于提交） |

`mission_description.md` 按平台七段式规范撰写，已含规范强制要求的
「反平凡化」句子（trivialization guard）。

### 9.0b 论文编号（已推导）

正文 `Theorem/Lemma/Proposition/Corollary` **共用计数器**
（`\newtheorem{lemma}[theorem]{Lemma}` 等），正文序列：

```
Lemma 1   Duhamel 公式          Lemma 6   一范数标度界
Lemma 2   相互作用绘景          Cor 7     一范数 Trotter number
Lemma 3   时间序演化基本定理    Thm 8     三种误差类型
Lemma 4   时间序指数范数界      Thm 9     阶条件
Cor 5     时间序距离界          Thm 10    共轭的交换子展开
                                Thm 11  ★ commutator scaling 主定理（goal）
                                Cor 12    commutator 版 Trotter number（未形式化）
                                Prop 13/14  Lie–Trotter / Suzuki 前因子
```

> ⚠️ **提交前必须对照已发表 PDF 核对编号**。`milestone_title` 的硬性规则是
> 「以原文编号开头」，编号错了会被 moderator 退回。

### 9.0c 独立交叉核验（第二份报告）

一个独立子代理从头读完 16 个文件全部 **9,021 行**，产出了
**[PAPER_MAPPING_full.md](PAPER_MAPPING_full.md)**（1902 行），
并**纠正/补充**了我的初版对照表：

**⚠️ 最重要：4 个 docstring 标签在论文源码里根本不存在**（已 grep 全部 `*.tex` 核实）：

| docstring 引用 | 位置 | 真相 |
|---|---|---|
| `thm:trotter_error_order_cond` | MainTheorem.lean:45,93；CommutatorScaling.lean:127 | 真实标签是 `thm:trotter_error_comm_scaling`；`thm:error_order_cond` 是**另一条**真实定理 |
| `prop:pf1_bound` | Prefactor.lean:224 | prefactor.tex l.45–50 的 proposition **无 `\label`** |
| `prop:pf2_bound` | Prefactor.lean:620 | prefactor.tex l.105–114 的 proposition **无 `\label`** |
| `eq:trotter_error_comm_scaling_bound` | MainTheorem.lean:540 | theory.tex l.273–276 的 display **无 `\label`** |

→ milestone_title 必须用**论文真实编号或明确位置**，不能照抄这些自造标签。

**⚠️ prefactor 的厄米约定是反的**（作者自述，Prefactor.lean:14-33）：
论文用**厄米** $H$ 与 $e^{-itH}$；形式化用**反厄米** $K_\gamma$ 与 $\exp(t\cdot K_\gamma)$，
对应 $K_\gamma=-iH_\gamma$，常数 $t^2/2,t^3/12,t^3/24$ 不变。

**⚠️ 指数前因子是 2 不是 4**：`rep.tex` l.36–44 展示的是改进前的 4，
l.44–50 宣布改进；Lean 对应改进后的 2（我核对了 theory.tex:272 的主定理陈述）。

其余补充差异（`[NormOneClass]` 显式化、有向区间积分、$\OO{}$→`𝓝 0` / $\cO{}$→`atTop`、
`cor:trotter_number_one_norm_scaling` 被改写成 $O(r^{-p})$ 而非 $\epsilon$-精度形式、
`suzuki 0` 是 junk identity 等）已并入 PAPER_MAP.md §D（现共 16 条）。

**`pf2k.tex` 在 Lean 树中从未被任何声明引用** —— 整个 §5.2（四阶前因子）未形式化。

> 注：该子代理把报告写进了 `FQFP\TrotterError\PAPER_MAPPING.md`（污染了可发布源码树），
> 已移到 `tools/p2m/PAPER_MAPPING_full.md`；源码树已确认只剩 `.lean` 文件。

### 9.1 为什么改方向

前几轮把精力放在「怎么把 379 个声明灌到平台上」。用户指出更正确的路线：
**本项目是形式化一篇论文，应该开一个 mission，并按论文原文的编号引理来设里程碑。**
这完全符合 playbook 对 captain 的定义：

> **Already have the Lean code?** … By default you upload the project first
> (definitions, theorems, and solutions, in dependency order) and then **set up the
> mission on top of the published nodes**.

以及 milestone 的唯一原则：

> The ONLY principle is copying the exact lemmas/theorems/propositions used by the
> authors in the source. … Your curation of milestones must stay faithful to the
> original source — read the source carefully instead of guessing.

**所以正确顺序是**：
`上传定义层 → 上传定理/证明节点 → 在已发布节点上建 mission（goal = 主定理，
milestones = 论文的核心引理）→ 人工审计 → 发布`。

这也让「单文件内联 vs 节点切分」的争论有了答案：mission 的 milestone 必须能
**链到具体的平台定理节点**，所以节点切分不是可选项，而是 mission 的前置条件
（playbook: "Linking is attestation"，milestone 要挂 `theorem_id`）。

### 9.2 论文源码已定位

```
C:\Users\Windows11\Downloads\papers\TrotterError\
├── TrotterErrorTheory.tex   主文件
├── theory.tex      29.8 KB  核心理论（commutator scaling）
├── order.tex       11.5 KB  阶条件
├── rep.tex         13.7 KB  误差表示
├── prefactor.tex   38.3 KB  前因子 / Lie–Trotter / Suzuki
├── pf2k.tex        17.3 KB  高阶 product formula
├── prelim.tex      24.9 KB  预备
└── app.tex         47.7 KB  附录
```

**这解释了形式化 docstring 里的 `theory.tex:238-241`、`rep.tex:50–113` 等引用**——
它们指向的就是这份源码。现在可以逐条把论文的编号引理与 Lean 声明对应起来，
从而写出**忠实于原文**的 milestone 列表。

### 9.3 mission 要素（按 mission_description.md 的七段结构）

- `mission_type`: **`ResearchPaper`**（"a result from a specific paper"）
- `main_item_id`: 主定理节点（`TrotterError.trotter_error_comm_scaling` 或
  `..._bound_comm_scaling`）
- milestone: 论文的核心 lemma/theorem/equation，标题必须以原文编号开头
  （如 `Lemma 3.2`），描述为论文原文陈述
- `description`: 七段式介绍（Motivation / Setting / Targets / Significance /
  Difficulty / Formalization scope / Selected references），800–1500 词，
  **要诚实区分「已证明」与「已形式化」**——本项目已经形式化完成，
  这一点必须在 Significance 里说明，不能假装是 open problem。

---

## 9.4 方案 A 执行记录与本轮发现（第 5 轮）

### 9.4a proposal 已创建

```
id      : aef100c6-15dc-4d9c-934b-4dae02a04c3e
name    : Trotter Error with Commutator Scaling
status  : Draft
type    : ResearchPaper
fields  : functional-analysis, mathematical-physics, quantum-information
items   : 0
```

已写入 `mission_description.md` 全文；`visibility = private`。
用户已确认 **Theorem 11 = Trotter error with commutator scaling**，编号无误。

### 9.4b 10 条 milestone 的 payload 已生成并**本地编译全部通过**

`gen_payloads.py` 从 v4.33.1 源码逐字切出 `preamble + formal_statement`，
输出到 `nodes/payload/*.json`。全部 10 条的 `formal_statement` 都是
「`import Mathlib` + 本模块的 `open`/`variable` + 语句 + `:= by sorry`」。

### 9.4c ⚠️ 关键发现：平台的 **Definitions 会被修剪（pruning）**

`Definitions.Def_TrotterError` 在平台上是通过 `submit-definition` 发布的，
但我**先后发布过两个不同内容的同名定义包**（先 7 个 def 的 pilot 版，
后 66/37 个 def 的完整版），而平台上只保留了一个。

本地验证：我自己生成的 37-def 包 **编译通过**（`*** DEF BUNDLE COMPILES ***`），
且其中**确实包含** `timeOrderedExp`、`lieTrotter`、`suzuki2`、`evalIndexList`、
`commutatorRemainder`、`IsOrderOf` 等全部所需名字。
但 10 条 milestone 语句**全部编译失败**，错误形态高度一致：

```
error: unknown namespace `TrotterError.List`
error: unknown namespace `ProductFormulaData`
error: Function expected at
  timeOrderedExp          ← 名字不在作用域，被当成 autoImplicit 变量
```

「Function expected at X」正是 `X` 未被解析时的典型症状。

→ 说明平台上那份 `Definitions.Def_TrotterError` **不包含**这些定义，
即平台的 definition 节点在其依赖者出现之前会**丢弃未被引用的声明**
（这也解释了为什么 pilot 那次只要 7 个 def 就够：刚好够它自己用）。

### 9.4d 由此得到的正确做法（重要架构决定）

**不要把定义拆成独立的 `submit-definition` 包再 import。**
每个定理的 `preamble` 里**内联它自己需要的定义与私有辅助引理**，
让每个 `Thm_*` / `Sol_*` **自包含**。理由：

1. 绕开 pruning —— preamble 是定理的一部分，不会被单独修剪；
2. 绕开「`Sol_*` 不能重声明平台已有名字」的问题 —— 定义写在 preamble 里，
   不在 solution 文件里；
3. 与平台实测行为一致：§6.14 那个 **ACCEPTED** 的 split-node 就是
   `import Mathlib` + 一个自包含的 `theorem solution`，**没有**依赖外部 definition 包。

代价：379 个节点会有重复的 preamble，体积偏大；但**正确性优先**。

### 9.4e 判定提交结果（已跑）

以 `definition_name = "TrotterErrorMilestones"` **重新发布**完整定义包
（18.6 KB，35 个定义；`theorem_id = e61248db-b24a-47cb-9ab6-10a1e8ce0ca3`，PUBLISHED），
再把 payoff 的 import 改成 `Definitions.Def_TrotterErrorMilestones`，
用 `TrotterError.timeOrderedExp_duhamel` 做判定提交（job `7f1cfd18-…`）：

```json
{"status":"FAILED",
 "error_message":"formal statement does not compile:
   line 5: expected token; line 6: expected token;
   line 10: Unknown constant `TrotterError.timeOrderedExp_duhamel`"}
```

**对比之前（旧包）的错误**：

| | 旧包 `Def_TrotterError` | 新包 `Def_TrotterErrorMilestones` |
|---|---|---|
| `timeOrderedExp` | `Function expected at / Unknown identifier` | **已解析**（不再报这个错） |
| 错误性质 | 定义缺失 | 变成 **parse error** |

**→ §9.4d 的 pruning 假设被证伪；真正的问题是「同名定义包重复发布导致旧版被保留」。**
换新包名后定义层就能被解析了，这是本轮最重要的结论。

**新的、更浅的失败**：`expected token` 出现在 preamble 的第 5/6 行
（即 `open scoped Topology BigOperators Interval` 与 `variable …` 之后），
而 `TrotterError.timeOrderedExp_duhamel` 因此未被声明。
这说明 **payload 的 `preamble` + `formal_statement` 拼接上有语法问题**，
与定义层无关。下一轮只需在本地把这一条 `preamble + formal_statement`
当作一个文件编译一次即可定位（服务端 `autoImplicit false`，
`variable` 与 `theorem` 的衔接需要显式化）。

**架构结论（不变）**：
- 定义层要用**唯一的新包名**发布一次，不要同名重发；
- 每个 `Thm_*` 的 `preamble` 用 `import Mathlib` + `import Definitions.Def_TrotterErrorMilestones`
  + 该源模块的 `open`/`variable`；
- `Sol_*` 仍是自包含、不重声明平台名字（§6.14 已验证 `ACCEPTED`）。

---

## 10. 阻塞项 — 已全部解除

~~唯一阻塞：Prove2Me API key。~~ → **API key 已收到并验证。**

状态更新：

| 原计划步骤 | 状态 |
|---|---|
| 1. `GET /environments` 确认环境 | ✅ 已做：只有 v4.33.1 / v4.30.0 / v4.29.0-rc3 |
| 2. 检查顶层名撞名 | ✅ 已做：`TrotterError` 命名空间下 7 组探测**全部 0 命中**，无冲突 |
| 3. Stage 2 提取语句/证明分界 | ✅ 已做：16 文件全部完成，451 decl facts + 4096 ref facts |
| 4. 生成三棵树 | ⏳ 下一步 |
| 5. 私有 mission 试跑 | ⏳ 待环境决策后 |

### 账号信息（已鉴权确认）

- username: `Bingyu Xia`，email: `xiabingyu@gmail.com`
- `num_solved_prob: 0`、`num_submitted_prob: 0`、`trust: 0`（全新账号）
- `licensing.status: "not_required"` → **无需处理 Apache 2.0 授权确认**
- 平台版本 `0.11.4`，与本地缓存的 skill 版本**一致**，无需重新拉取文档

### 命名冲突探测结果（全部 0 命中）

`TrotterError`、`TrotterError.additiveKernel`、`TrotterError.ProductFormulaData`、
`TrotterError.List`、`trotter_error_bound_comm_scaling`、`timeOrderedExp`、`commutatorRemainder`

→ 全部 455 个声明都在 `TrotterError` 命名空间内（子命名空间
`TrotterError.ProductFormulaData` 33 条、`TrotterError.List` 18 条），
命名空间**完全干净**，不需要加额外上传前缀。已存在的 mission
「Spencer–Szemerédi–Trotter Unit Distance 4/3 Upper Bound」与本题无关。

### 剩余决策

`D:\p2m-v4331` 已可直接上传，但那 6 处修复只存在于 worktree，**未提交到 git 仓库**。
需要一个 commit SHA 来填每个上传项的 `source` 字段
（格式 `blob/<sha>/<file>#L<start>-<end>`）。需要决定提交方式。

---

## 8. 本地工具

```
D:\project\CQM1\tools\p2m\          # 原始仓库（v4.34.0，保持不动）
├── extract_decl_graph.lean   平台 Stage 1 脚本（已修补 4.34 兼容性 3 处）
├── extract_sketch_info.lean  平台 Stage 2 脚本（原样可用）
├── check_axioms.lean         内核级公理审计（21 定理全过）
├── reach.ps1                 可达性闭包脚本（执行策略受限，逻辑已内联跑通）
├── STATUS.md                 本文件
├── decl_graph.jsonl          Stage 1 输出（1473 条声明，603 KB）
└── sketch/                   Stage 2 输出（16 个 jsonl）

D:\p2m-v4331\                       # 降级验证 worktree（v4.33.1，可上传状态）
└── 6 处 drift 修复已应用，TrotterError 全 16 模块编译通过
    （worktree 的 tools/p2m 未纳入版本控制，属临时验证设施）
```

> ⚠️ Windows 上的三个坑：
> **（1）** PowerShell 默认按 CP1252 解码 UTF-8，Lean 源码里的 `γ`、`‖`、`≤` 会被
> 破坏成含引号的乱码并打破 JSON——读写一律用
> `[System.IO.File]::ReadAllText/WriteAllText` + 显式 UTF8。
> **（2）** `Set-Location`/`cd` 不影响 .NET API 的相对路径，.NET 调用必须用绝对路径。
> **（3）** 本机 `pwsh` 不在 PATH（只有 Windows PowerShell 5.1），且执行策略禁止运行
> `.ps1` 文件；需要 `??`、三元等 PS7 语法会失败，脚本逻辑要内联或用 PS5 兼容写法。
