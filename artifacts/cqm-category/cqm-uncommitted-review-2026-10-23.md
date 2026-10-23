# CQM 未提交修改审核（2026-10-23）

## 修复状态（2026-10-23）

本记录下文保留修复前的审核发现、行号与验证证据。按后续修复请求，两个 P2 及文档、
风格问题现已修复，当前实现与验收见 `artifacts/m3/m3-teleportation-2026-10-20.md`。

- 已新增 `QuditCat.isUnitary_corrections`，族索引的归一化与概率定理可直接调用，
  不需要调用方再次分类或补局部实例。
- 实施笔记及两份探针已同步到 `correctedTeleportation L R U` 和配对实例接口；
  旧 M3 探针已重新编译通过，review 探针也改为验证实例搜索成功。
- 已修正不存在的 Qubit 家族引用、效果归一化的 unitary 条件、配对参数描述和结果命名空间，
  并将滑移证明的三处分号拼接拆行。
- `lake build FQFP`（9131 jobs）、`lake exe runLinter`、`lake exe lint-style` 已依次 exit 0；
  style 保留原有脚本缺 `module` 的警告，两份探针均 exit 0 且无警告。

修复后日志为 `scratch/logs/cqm-review-fix-*-2026-10-23.log`，确切路径列在实施笔记的
当前验收表中。M2/M3 的数学覆盖没有扩展，第 6 节列出的既有覆盖缺口仍然存在。
审核与修复阶段未提交代码。

## 范围与结论

审核当前工作树相对 HEAD 的 CQM 修改，包含未跟踪的新文件：

- `FQFP/CQM/Category/Teleportation.lean`；
- `FQFP/CQM/QuditCat/Rigid.lean`、`QuditCat/Teleportation.lean`；
- `FQFP/CQM/RelCat/Rigid.lean`、`RelCat/Teleportation.lean`；
- `FQFP/CQM/RelCat/Monoidal.lean` 新增的结构关系 membership API；
- `FQFP.lean` 中对应的五条 import。

其他目录的未提交修改不属于本次审核范围。没有修改待审 Lean 源码或提交代码。

规范依据为当前 `AGENTS.md`、`.claude/commands/mathlib-review.md`、
`.claude/skills/improve/SKILL.md`、`artifacts/abstraction-agent-prompt-v3.md` 和
`artifacts/have_lessons.md`；验收依据为
`artifacts/cqm-category/cqm-next-steps-2026-10-16.md` 的 M2/M3。
按仓库 review 指引分别检查了架构、数学保真、风格与证明质量。

**没有发现错误数学定理、定义弱化或 P0/P1 级代码缺陷。** 抽象分支公式、Rel 模型以及
Qubit 的双归一化计算正确。发现一个可复现的修正族实例缺口、一个已失效的验收探针，
以及文档、局部格式问题。当前成果可以作为阶段性实现；整个 M2/M3 的教材覆盖仍未闭环。

## 1. [P2] 四修正族缺少统一的 unitary 实例

位置：`QuditCat/Teleportation.lean:98`，以及消费者 `normalizedBranch_apply:183`、
`normalizedBranch_eq_smul:194`、`branch_probability:201`。

现有声明：

```lean
def corrections : Fin 4 → (Qubit ⟶ Qubit) :=
  ![𝟙 Qubit, Qubit.pauliZ.asHom, Qubit.pauliX.asHom, jGate.asHom]

theorem branch_probability (U : Qubit ⟶ Qubit) [IsUnitary U] (ψ : Qubit.state)
    (hψ : ‖ψ‖ = 1) :
    ‖(teleportationBranch bellState (bellEffect U) U) ψ‖ ^ 2 = 1 / 4
```

各具体 gate 已有实例，但对变量 `i : Fin 4`，实例搜索无法得到
`IsUnitary (corrections i)`。因此下游直接调用
`branch_probability (corrections i) ψ hψ` 或
`normalizedBranch_apply (corrections i) ψ` 会失败，必须再次逐项分类。
未归一化的 `correctedTeleportation_corrections` 不受影响，因为它自己做了分类。

建议补一个族实例，保留现有定理的一般性：

```lean
/-- Every correction in the qubit teleportation family is unitary. -/
instance isUnitary_corrections (i : Fin 4) : IsUnitary (corrections i) := by
  fin_cases i <;> dsimp [corrections] <;> infer_instance
```

证据：本次探针先用 `fail_if_success` 确认原有搜索失败，再在局部用以上分类证明得到实例，
随后成功调用 `branch_probability (corrections i) ψ hψ`。这是 API 接入缺口，
不是现有分支等式的反例。按 AGENTS，应补上游实例，而不让每个调用者重复分类。

## 2. [P2] 实施笔记的配对签名失真，所引用的验收探针现已编译失败

源码 `Category/Teleportation.lean:138–145` 实际声明：

```lean
def correctedTeleportation (L R : C) [DaggerCategory C] [ExactPairing R L]
    (U : L ⟶ L) : L ⟶ L

theorem correctedTeleportation_eq_id {L R : C} [ExactPairing R L] [DaggerCategory C]
    (U : L ⟶ L) [IsUnitary U] : correctedTeleportation L R U = 𝟙 L
```

但是 `artifacts/m3/m3-teleportation-2026-10-20.md:29–31,43–47` 及其第 7 节仍声称
主接口直接接收 `(p : ExactPairing R L)`，模型直接传入该见证且不需要局部实例。
该笔记第 5 节引用的 `scratch/m3-teleportation-probe-2026-10-20.lean` 也仍使用旧调用：

```lean
example : correctedTeleportation (RelCat.exactPairingSelf RelCat.bit) (𝟙 RelCat.bit)
    = 𝟙 RelCat.bit := RelCat.correctedTeleportation_id
```

本次原样重跑这个历史探针，退出码为 1，第一处错误就在第 20 行的参数类型不匹配。
所以旧笔记里的“探针通过”不能作为当前签名的可重跑验收证据。

建议将笔记和探针同步至当前接口，例如：

```lean
example : correctedTeleportation RelCat.bit RelCat.bit (𝟙 RelCat.bit)
    = 𝟙 RelCat.bit := RelCat.correctedTeleportation_id
```

建议说明文字：

> 主定理适用于任意 `[ExactPairing R L]`，不再要求 `L` 是选定右 dual 的投影。
> 当前模型调用使用已注册的标准配对；指定其他见证时，可在局部引入该实例。

**这不是一般性不足。** 本次新探针已验证，在任意显式 `p : ExactPairing R L`
的局部实例下可以直接使用主定理。无需为了迁就旧笔记而改回显式参数，
也不应沿用旧审核对 `[HasRightDual]` 接口收窄的指控。

## 3. [P3] 两处模块/声明文档不符合实际覆盖与假设

### 3.1 尚不存在的 Qubit Bell 家族

`Category/Teleportation.lean:36–39` 写道：

> “…is a separate statement (`QuditCat.qubitBellEffects`, `RelCat.bitBellEffects`).”

当前不存在 `QuditCat.qubitBellEffects`；Qubit 文件第 33–43 行也明确承认测量性尚未形式化。
建议替换为：

> Completeness and disjointness of the branch effects are separate requirements.
> They are proved for `RelCat.bitBellEffects`; the corresponding qubit Bell measurement
> remains to be formalized.

### 3.2 任意 U 的效果不能无条件称为 normalized

`QuditCat/Teleportation.lean:81–83`：

```lean
/-- The normalized Bell effect of the branch whose correction is `U`. -/
def bellEffect (U : Qubit ⟶ Qubit) : Qubit ⊗ Qubit ⟶ 𝟙_ QuditCat :=
  ofHom (bellFactor • ((U† ▷ Qubit) ≫ basisEvaluation (ZBasis 2)).hom)
```

当 `U = 0` 时，这个效果为零，并不归一化。定义保持接受任意 `U` 是合理的一般性；
应修正文案，而不是为方便文档添加不必要的定义参数：

> The scaled Bell effect associated with `U`; it is normalized when `U` is unitary.

## 4. [P3] 三处分号拼接违反本仓库的明确风格规则

`Category/Teleportation.lean:103,105,107` 的
`tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing` 使用：

```lean
dsimp [tensorRightHomEquiv]; monoidal
rw [whisker_exchange]; monoidal
rw [ExactPairing.coevaluation_evaluation'']; monoidal
```

`.claude/skills/improve/SKILL.md` 的 “What doesn't work” 明确列出
“Semicolon joins in multiline proofs — banned antipattern.”
每处原样拆为两行即可，不需要更换 tactic、剖析性能或改变证明策略。
Mathlib 相邻原证明也使用这种写法，因此这是本仓库规范项，不是数学或内核正确性问题。

## 5. 数学与架构核对：已通过的部分

核对本地教材 `D:/prove2me/1/CQM/textbook/mineru/CQM.md`，并查看原 PDF 已保存的页图
`artifacts/sources/cqm-next-plan-pages-2026-10-16/source-099.png`、`source-100.png`。

- `ExactPairing R L` 的 cup 类型为 `I → R ⊗ L`、cap 为 `L ⊗ R → I`，与教材
  `L ⊣ R` 的方向一致。
- `teleportationBranch_evaluation` 只假设 monoidal category 和给定 exact pairing；
  `correctedTeleportation_eq_id` 再使用 dagger 和 unitary correction。
  没有暗加整个范畴 rigid、symmetric 或 `MonoidalPreadditive` 等假设。
- 新滑移引理把 Mathlib `Monoidal/Rigid/Basic.lean` 的相邻 API 放宽至任意给定配对，
  是真实的接口补充。没有必要重新建立 Dual/Transpose 类。
- Rel 的 diagonal/codiagonal、两条 snake、transpose 等于 converse，以及两支效果的
  complete/disjoint 与 Example 3.2、Definition 3.9、Example 3.18 相符。
- Qudit 的 `basisForm` 是双线性坐标形式，不是复内积。`exactPairingOfOrthonormalBasis b`
  显式依赖基，`dagger_basisCoevaluation` 正确；源码没有把这种 self-dual 选择误称为
  任意 Hilbert 空间的 canonical dual。
- Example 3.17 的效果表顺序对应 `I,Z,X,J`，第四个 `J=[[0,1],[-1,0]]`。
  当前效果为 `ε(U†a,b)=aᵀ·conj(U)·b`，四个行向量确为
  `1001`、`100−1`、`0110`、`01−10`；第四支符号和 `J=iY` 的解释正确。
  此处为源码/PDF 数学核对，项目尚未提供四个行向量的正式 Lean 等式。
- 两个归一化因子各为 `1/√2`，归一化单分支为 `(1/2)·id`，单位输入的输出范数平方
  为 `1/4`。没有把 normalized cup/cap 错用成满足原 snake 的 exact pairing。
- Rel 与 Qudit 标准对象的直接 pairing、`HasRightDual.exact` 路径在探针中以 `rfl`
  验证一致。Mathlib 允许同一对象间有不同合法 pairing，不能仅凭实例重叠报 coherence 错误。
- 零维标准对象 `std 0` 的抽象分支也通过编译检查。新增文件未见 `sorry`、
  自定义 `axiom`、`omega`、`maxHeartbeats` bump、`nolint` 或具名实例的显式 `@` 传参。

## 6. 计划验收边界：已承认的缺口，不能当成新增错误定理

| 计划目标 | 当前状态 |
| --- | --- |
| M2 Rel 具体 dual | 已实现 diagonal self-pairing 和左右 dual |
| M2 Qudit 标准对象及给定 ONB 的 self-dual | 已实现，足够支持本轮 qubit 分支 |
| M2 任意 Qudit 的 canonical `H*` 配对及基无关性 | 尚未实现，源码已明确说明 |
| M3 任意 exact pairing 的单分支恒等式 | 已实现 |
| M3 Rel 两支正确性及 Bell 效果测量性 | 已实现 |
| M3 Qubit 四支正确性与双归一化计算 | 已实现；族实例接入问题见第 1 节 |
| Qubit Bell 家族的 Complete/Disjoint 与 Born API 接入 | 尚未实现，源码已明确说明 |
| 教材四个行效果与实现逐项相等的 Lean 定理 | 尚未实现 |
| L 侧 dagger 效果与教材 R 侧 transpose/conjugate 图式的等式 | 尚未实现 |
| Shannon 意义的保密性 | 不在本轮关系语义范围，没有被冒称已证明 |

因此不建议把整个 M2/M3 或 Example 3.17 的完整测量协议标成完成。
这些缺口已有明确记录，不再重复作为新的 P1 代码错误。

建议后续测量接口仍使用已有 `Effect.Complete`、`Effect.Disjoint` 和 M1 的 ONB 定理：

```lean
def qubitBellEffects : Fin 4 → Effect (Qubit ⊗ Qubit) :=
  fun i ↦ bellEffect (corrections i)

theorem qubitBellEffects_complete : Effect.Complete qubitBellEffects
theorem qubitBellEffects_disjoint : Effect.Disjoint qubitBellEffects
```

## 7. 非阻塞的 API 改进建议

`QuditCat/Teleportation.lean:151–180` 的 `branch_no_correction` 重新展开纯张量与基求和，
与 `QuditCat/Rigid.lean` 的 snake 计算有重复。按“重复意味着缺 API”的原则，
下一次整理宜补一个 Qudit 模型的双标量缩放引理，再调用已有
`teleportationBranch_evaluation` 和 `bellFactor_mul_self`，而不是机械删除 `have`。
下面是建议签名草图，未在本次实现或验证：

```lean
lemma teleportationBranch_smul {L R : QuditCat}
    (a b : ℂ) (η : 𝟙_ QuditCat ⟶ R ⊗ L)
    (x : L ⊗ R ⟶ 𝟙_ QuditCat) (U : L ⟶ L) :
    (teleportationBranch
      (ofHom (a • η.hom)) (ofHom (b • x.hom)) U).hom =
    (a * b) • (teleportationBranch η x U).hom
```

范围为一个模型引理及其使用点；当前证明正确，无需因此提前建立完整线性范畴实例体系。

## 8. 本次验证与证据

Mathlib 4.35 缓存已在本地，跳过 `cache get`；没有运行 `lake update`。
严格按顺序执行项目 build、声明 lint、style lint，没有运行裸 `lake build`。
当前工具环境缺少 `ELAN_HOME`，首次构建命令在启动阶段失败；
随后仅在命令进程设置 `ELAN_HOME=C:/Users/Windows11/.elan`，正常运行以下检查，未改配置。

| 检查 | 当前结果 | 证据 |
| --- | --- | --- |
| `lake build FQFP` | exit 0，9131 jobs，无源码警告 | `scratch/logs/cqm-review-build-2026-10-23.log` |
| `lake exe runLinter` | exit 0，Linting passed for FQFP | `scratch/logs/cqm-review-declaration-lint-2026-10-23.log` |
| `lake exe lint-style` | exit 0，无风格违规；有原有脚本警告，见下 | `scratch/logs/cqm-review-style-lint-2026-10-23.log` |
| 新探针 `lake env lean scratch/cqm-review-probe-2026-10-23.lean` | exit 0，最终版本无警告 | `scratch/logs/cqm-review-probe-2026-10-23.log` |
| 原样重跑 10-20 探针 | exit 1，旧配对调用已失效 | `scratch/logs/cqm-review-historical-probe-2026-10-23.log` |
| `git diff --check -- FQFP/CQM FQFP.lean` | exit 0；只覆盖 tracked diff | 未把它代替对五个 untracked 文件的审核 |

Style 命令仍重放 `scripts/lint-style.lean` 缺少 `module` 的工具构建警告。
该脚本没有本轮修改，10-20 的 style 日志也包含同一警告。不能称“全部零警告”，
也不应把该既有警告归因于本轮 CQM 修改。

新探针检查任意配对的适用性、两个模型的配对实例路径、`std 0`、修正族缺失实例及其
局部补法、Rel 测量定理；对 11 条关键声明执行 `#print axioms`，依赖均仅为
`propext`、`Classical.choice`、`Quot.sound`。
探针与日志留在 `scratch/`，结论保存在本笔记。
