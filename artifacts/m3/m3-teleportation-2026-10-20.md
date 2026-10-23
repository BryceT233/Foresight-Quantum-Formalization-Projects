# M3 实施与验收记录：teleportation 的抽象单分支恒等式与 Rel/Qubit 接入

初稿：2026-10-20；修订：2026-10-23，回应
`artifacts/cqm-category/cqm-uncommitted-review-2026-10-23.md`。
本次修订只修复实例、文档、风格及验收探针，不扩展 M2/M3 覆盖。实施范围：推进
`cqm-next-steps-2026-10-16.md` 的 M3。新增

- `FQFP/CQM/Category/Teleportation.lean`（抽象层，任意 `[ExactPairing R L]`）；
- `FQFP/CQM/RelCat/Teleportation.lean`（Rel 接入 + 两支 Bell 效果的测量性）；
- `FQFP/CQM/QuditCat/Teleportation.lean`（Qubit 接入、教材修正族、归一化）；

并在 `FQFP.lean` 注册三个模块。

## 1. 抽象层：单分支恒等式（任意配对实例）

实际声明（`CategoryTheory`，`[Category C] [MonoidalCategory C]`）：

```lean
def teleportationBranch {L R : C} (η : 𝟙_ C ⟶ R ⊗ L) (x : L ⊗ R ⟶ 𝟙_ C) (U : L ⟶ L) : L ⟶ L
lemma teleportationBranch_comp (η) (x) (U V) :
    teleportationBranch η x U ≫ V = teleportationBranch η x (U ≫ V)

-- 在 section `variable {L R : C} [ExactPairing R L]` 中：
theorem tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing (V : L ⟶ L) :
    (tensorRightHomEquiv L R L (𝟙_ C)) ((V ▷ R) ≫ ε_ R L) = V ≫ (λ_ L).inv
theorem teleportationBranch_evaluation (V : L ⟶ L) :
    teleportationBranch (η_ R L) ((V ▷ R) ≫ ε_ R L) (𝟙 L) = V
theorem teleportationBranch_correction [DaggerCategory C] (U : L ⟶ L) [IsUnitary U] :
    teleportationBranch (η_ R L) ((U† ▷ R) ≫ ε_ R L) U = 𝟙 L

def correctedTeleportation (L R : C) [DaggerCategory C] [ExactPairing R L]
    (U : L ⟶ L) : L ⟶ L
theorem correctedTeleportation_eq_id {L R : C} [ExactPairing R L] [DaggerCategory C]
    (U : L ⟶ L) [IsUnitary U] : correctedTeleportation L R U = 𝟙 L
```

`teleportationBranch` 就是教材 §3.2.1 的单分支：

`L --ρ⁻¹--> L ⊗ 𝟙 --L◁η--> L ⊗ (R ⊗ L) --α⁻¹--> (L ⊗ R) ⊗ L --x▷L--> 𝟙 ⊗ L --λ--> L --U--> L`。

证明不展开 snake，而是用转置双射 `tensorRightHomEquiv` 加滑移恒等式（本文件里的
`tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing`，将 Mathlib 相邻引理推广到任意
`[ExactPairing R L]`），于是分支（未加修正）等于 `V`，`U† ≫ U = 𝟙` 由
`IsUnitary` 给出。

主定理适用于任意 `[ExactPairing R L]`，`L` 是独立对象，不要求它是选定右对偶的投影
`Rᘁ`。模型调用使用全局标准配对实例：Rel 选择 `exactPairingSelf bit`，Qubit 选择
`exactPairingOfOrthonormalBasis (ZBasis 2)`。接口的显式参数为对象 `L R` 和修正 `U`，
不直接接收配对见证。指定其他 `p : ExactPairing R L` 时，可在局部引入该实例；
两份验收探针均包含任意 `p` 的调用检查。

未做：教材图里 R 侧的 transpose/conjugate 形式（需要 `rightAdjointMate` 对配对的滑移引理）。

## 2. Rel 接入：one-time pad 的输入输出正确性与测量性

```lean
def bit : RelCat.{0}                                    -- 二元集
def bellEffect (U : X ⟶ X) : Effect (X ⊗ X)             -- U† ▷ X ≫ ε
lemma mem_bellEffect (U) (a b) :
    ((a, b), ()) ∈ (bellEffect U).rel ↔ (b, a) ∈ U.rel
lemma effectSet_bellEffect (U) (a b) :
    effectSet (bellEffect U) (a, b) ↔ (b, a) ∈ U.rel
def boolNot : bit ⟶ bit                                 -- 布尔取反（unitary）
lemma mem_boolNot_rel (a b) : (a, b) ∈ boolNot.rel ↔ (!a) = b
def bitBellEffects : Fin 2 → Effect (bit ⊗ bit)          -- 两支的 Bell effect
theorem bitBellEffects_complete : Effect.Complete bitBellEffects
theorem bitBellEffects_disjoint : Effect.Disjoint bitBellEffects
theorem correctedTeleportation_id : correctedTeleportation bit bit (𝟙 bit) = 𝟙 bit
theorem correctedTeleportation_not : correctedTeleportation bit bit boolNot = 𝟙 bit
```

两条分支定理是 one-time pad 的输入输出正确性：无论测量结果是哪一支，修正后都是恒等关系。
`bitBellEffects_complete` / `bitBellEffects_disjoint` 说明两支效果覆盖 `bit ⊗ bit` 且互不相交，
即它们构成 Definition 2.51 意义下的测量（用 `complete_iff_cover` 与
`disjoint_iff_nonempty_pairwise`，把集合条件化归为 `Bool` 的有限检查）。因此“必有一支发生”
在 Rel 里已经形式化，而不只是文字。

**语义边界**：关系语义只表达可能性，`RelCat` 没有概率分布，所以这里没有、也不宣称 Shannon
意义的完美保密。

## 3. Qubit 接入：教材修正族与归一化

```lean
def bellFactor : ℂ                                    -- 1/√2
lemma bellFactor_mul_self : bellFactor * bellFactor = 1 / 2
def bellState : 𝟙_ QuditCat ⟶ Qubit ⊗ Qubit          -- (1/√2)(|00⟩ + |11⟩)
def bellEffect (U : Qubit ⟶ Qubit) : Qubit ⊗ Qubit ⟶ 𝟙_ QuditCat
def jGate : End Qubit                                 -- 教材的 J = [[0,1],[-1,0]]
def corrections : Fin 4 → (Qubit ⟶ Qubit)             -- I, Z, X, J（Example 3.17 的顺序）
instance isUnitary_corrections (i : Fin 4) : IsUnitary (corrections i)
theorem correctedTeleportation_id / _pauliZ / _pauliX / _jGate
theorem correctedTeleportation_corrections (i : Fin 4) : …
```

四个（未归一化）分支都等于恒等，直接由抽象定理在 `exactPairingOfOrthonormalBasis (ZBasis 2)`
的全局标准实例下得到。`isUnitary_corrections` 使变量 `i : Fin 4` 的调用也能自动推断
unitarity，`correctedTeleportation_corrections` 直接调用一般定理，不再重复分类。
修正族按 Example 3.17 的效果表取 `I, Z, X, J`：该表的前四个效果是
`(1 0 0 1)`、`(1 0 0 -1)`、`(0 1 1 0)`、`(0 1 -1 0)`，与这四个修正的 Bell 效果一致（差公共的
`1/√2`）；`J = i • pauliY`，所以第四项与 Pauli `Y` 只差相位 `i`。

归一化部分：教材的 cup 与四个 Bell effect 都不带 `1/√2`（M2 已记录这个边界）；把资源态与
effect 各乘 `1/√2` 后

```lean
lemma branch_no_correction (U) (x) :
    (teleportationBranch bellState (bellEffect U) (𝟙 Qubit)) x = (1 / 2 : ℂ) • (U† x)
theorem normalizedBranch_apply (U) [IsUnitary U] (x) :
    (teleportationBranch bellState (bellEffect U) U) x = (1 / 2 : ℂ) • x
theorem normalizedBranch_eq_smul (U) [IsUnitary U] :
    (teleportationBranch bellState (bellEffect U) U).hom = (1 / 2 : ℂ) • LinearMap.id
theorem branch_probability (U) [IsUnitary U] (ψ) (hψ : ‖ψ‖ = 1) :
    ‖(teleportationBranch bellState (bellEffect U) U) ψ‖ ^ 2 = 1 / 4
```

`bellEffect` 的定义允许任意 `U`，只有在 unitary 假设下才称为归一化效果。
对任意索引 `i : Fin 4`，以上三个归一化定理现在都能直接用于 `corrections i`，
调用方不需要局部实例或再次分类。资源态与效果各带一个 `1/√2`，故修正后的分支为
`(1/2) • 𝟙`；只缩放 cup 或 cap 不会保留原 exact-pairing 的 snake 恒等式。

## 4. 教材覆盖（M3 范围）

| 教材内容 | 本项目状态 |
| --- | --- |
| Example 3.17 单分支正确性（未归一化 Bell 数据） | **已完成**：抽象（任意配对实例）+ Rel（两支）+ Qubit（I, Z, X, J 四项） |
| Example 3.17 的归一化 Bell 数据 | **已完成**（Qubit）：分支 `(1/2) • 𝟙`，单位输入分支概率 `1/4` |
| Definition 2.51 的测量性（complete + disjoint） | **Rel 已完成**（`bitBellEffects_*`）；**Qubit 未完成**（见第 6 节） |
| 教材图里 R 侧的 transpose/conjugate 修正形式 | 未做 |
| one-time pad 的 Shannon 保密性 | 未做且不在范围：Rel 无概率 |
| name/coname、pivotal / dagger-compact | 未做（§3.4 支线，规划列在 M4） |

## 5. 当前验收（2026-10-23）

Mathlib cache 已在本地，未运行 `lake update`，按 AGENTS 跳过 `cache get`。

| 检查 | 结果 | 日志 |
| --- | --- | --- |
| `lake build FQFP` | exit 0，9131 jobs，无源码警告 | `scratch/logs/cqm-review-fix-build-2026-10-23.log` |
| `lake exe runLinter` | exit 0，Linting passed for FQFP | `scratch/logs/cqm-review-fix-declaration-lint-2026-10-23.log` |
| `lake exe lint-style` | exit 0，无风格违规；保留既有脚本警告，见下 | `scratch/logs/cqm-review-fix-style-lint-2026-10-23.log` |
| `lake env lean scratch/m3-teleportation-probe-2026-10-20.lean` | exit 0，无警告 | `scratch/logs/cqm-review-fix-m3-probe-2026-10-23.log` |
| `lake env lean scratch/cqm-review-probe-2026-10-23.lean` | exit 0，无警告 | `scratch/logs/cqm-review-fix-review-probe-2026-10-23.log` |

两份探针已同步到对象参数和配对实例接口，移除旧的显式配对调用；review 探针也已移除
“实例应搜索失败”的历史断言和局部补法。它们直接检查变量索引下的 `inferInstance`、
`normalizedBranch_apply`、`normalizedBranch_eq_smul`、`branch_probability`，
调用点均不再分类或提供局部 unitary 实例。

M3 探针另检查任意配对实例、Rel 两支及效果关系图、Bell 效果 complete/disjoint、
Qubit 四项和 `hadamardZero` 的 `1/4`。Review 探针保留配对实例路径及 `std 0` 检查。
两份探针分别打印 10 条与 12 条声明的 axioms，包含新族实例，依赖均仅为
`propext`、`Classical.choice`、`Quot.sound`。

构建、声明 lint、style lint 已按 AGENTS 顺序执行；未运行裸 `lake build`。
Style 命令仍重放 `scripts/lint-style.lean` 缺少 `module` 的既有工具构建警告，
与修复前及 10-20 日志相同，不能称全部零警告。该脚本不属于本次修复范围。

10-20 的日志保留为历史证据，不再用作当前接口的验收结果。10-23 审核时旧 M3 探针确曾失败，
其失败日志保存在 `scratch/logs/cqm-review-historical-probe-2026-10-23.log`；
修复后结果使用上表中的新日志。

## 6. 未做与下一步

- **Qubit 的 Bell 测量性**（已知覆盖缺口，本次不扩展）：需要把四个归一化 Bell effect
  认成某个正交 Bell 基的 bra，再用 `complete_braArrow_orthonormalBasis` /
  `disjoint_braArrow_orthonormalBasis`（M1 已有，输入是 `OrthonormalBasis`）。缺口在于
  `Qubit.state ⊗ Qubit.state` 上的 Bell 基还没有作为 `OrthonormalBasis` 构造出来；有了它，
  `Complete` / `Disjoint` 以及 `sum_probability_orthonormalBasis` 的“四支概率和为 1”都是直接
  推论。Rel 侧已完成，可作为模板。
- **四个 Bell effect 的行向量验证**（P3 的剩余部分）：先证
  `matrixToEnd_apply_basis : (matrixToEnd M).asHom (ZBasis n j) = ∑ i, M i j • ZBasis n i`，
  再由 `bellEffect_apply` 与 `basisForm_apply_basis` 逐项算出 `(1 0 0 1)`、`(1 0 0 -1)`、
  `(0 1 1 0)`、`(0 1 -1 0)`（各乘 `1/√2`）。
- **R 侧 transpose 形式**：需要 `rightAdjointMate` 对配对的滑移引理；Qudit 侧还与共轭有关。
- Qubit 的转置/共轭计算（M2 记录的缺口）。
- M4（name/coname、pivotal、Frobenius）按规划推进，本轮不动。

## 7. 本次审核修复

- **P2：修正族实例缺失**。新增 `isUnitary_corrections`，仅在实例定义中做有限分类；
  下游直接使用已有定理。未增加新测量公理或改变效果定义。
- **P2：笔记与验收探针失效**。本笔记所有主接口和模型调用已按实际的
  `correctedTeleportation L R U` 更新。两份探针覆盖任意配对与族索引直接调用，
  原失败探针已修复；新日志与旧证据区分保存。
- **文档**。抽象模块明确只有 Rel 测量性已证明，不再引用不存在的 Qubit Bell 家族；
  `bellEffect` 的文档将归一化限制在 unitary 情况；主定义描述配对实例而非不存在的显式
  `p` 参数；单分支范数说明与完整测量的覆盖边界保持一致。
- **风格**。滑移引理中的三处分号拼接均拆成独立 tactic 行，未更换证明策略。
- **范围**。保留原有 `I,Z,X,J` 修正族、双归一化和 Rel 结果；没有推进 canonical dual、
  Qubit Bell 测量性、行向量逐项等式、R 侧 transpose/conjugate 或新的缩放 API。
