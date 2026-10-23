# BCH 对数与 Mathlib 的去重建议

日期：2026-10-23。范围：当前工作区 `FQFP/BCH/Logarithm.lean` 与项目锁定的
Mathlib v4.35.0，commit `56a005855ea17e0b0958f73ec801ae140b0a1679`。
本文不对 Mathlib 最新分支作结论。以下对照记录去重前的状态；本次实施及验收见文末。

## 结论

采用 Mathlib 的 `NormedSpace.log`、`NormedSpace.logSeries` 作为唯一基础对象，
删除项目中同内容的基础声明；保留本项目补充的收敛、分析、余项和逆函数结果。
第一步保持当前文件路径和新增定理的 `FQFP` 命名空间，避免把去重、改名、拆文件绑在一起。

目前迁移只完成了一部分：

```lean
noncomputable abbrev FQFP.log (x : 𝔸) : 𝔸 := NormedSpace.log x
```

但 `FQFP.logSeries` 仍是另一条 `def`，基础引理中既有重复证明，也有单行转发。
两套 series 实际上定义相等，不需要新增“数学上相等”的转换层。

## 完全重合的公开声明

以下 15 个本地声明都能由 `NormedSpace` 下同名对象替代：

| 本地声明（均以 `FQFP.` 为前缀） | 处理 |
| --- | --- |
| `logSeries` | 删除独立定义，使用 `NormedSpace.logSeries` |
| `logSeries_eq_ofScalars` | 使用 Mathlib 同名定理 |
| `logSeries_apply_eq` | 使用 Mathlib 同名定理 |
| `logSeries_apply_zero` | 使用 Mathlib 同名定理 |
| `logSeries_sum_eq` | 使用 Mathlib 同名定理 |
| `logSeries_sum_eq_rat` | 使用 Mathlib 同名定理 |
| `logSeries_eq_logSeries_rat` | 使用 Mathlib 同名定理 |
| `log` | 删除兼容缩写后直接使用 `NormedSpace.log` |
| `log_of_isEmpty_algebra_rat` | 使用 Mathlib 同名定理 |
| `log_eq_logSeries_sum` | 使用 Mathlib 同名定理 |
| `log_eq_tsum` | 使用 Mathlib 同名定理 |
| `log_one` | 使用 Mathlib 同名定理及其已有 simp 属性 |
| `log_op` | 使用 Mathlib 同名定理 |
| `star_log` | 使用 Mathlib 同名定理 |
| `log_mem` | 使用 Mathlib 同名定理 |

例如原来的实际声明是：

```lean
def FQFP.logSeries (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸]
    [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  FormalMultilinearSeries.ofScalars 𝔸 fun n => ((-1 : 𝕂) ^ (n + 1) / n)
```

在相同假设下，以下两条均已由 Lean 验证：

```lean
example : FQFP.logSeries 𝕂 𝔸 = NormedSpace.logSeries 𝕂 𝔸 := rfl
example : (FQFP.log : 𝔸 → 𝔸) = NormedSpace.log := rfl
```

`Commute.log_right`、`Commute.log_left`、`Commute.log` 已经直接来自 Mathlib，维持现状。

## 应保留的新增内容

当前依赖的 Mathlib 文件明确只包含定义及直接代数性质；全库搜索也未发现本项目这组
分析定理的同名实现。以下不是上述基础 API 的重复：

- `logSeries_apply_eq'`、`logSeries_apply_one`、`logSeries_apply_two` 等局部补充。
- 系数范数与收敛半径，包括 `logSeries_radius_eq_one` 及实数版本。
- 球内可求和、`HasSum`、幂级数表示、连续性与解析性。
- 在 `1` 处的导数。
- `logCoeff`、`logPartialSum`、一般阶余项及低阶展开界。
- `exp_log_one_add`、`exp_log`，以及 `BCHElement.lean` 中的 `log_exp_sub_one`。

代表性实际声明如下；这里的 `log`、`logSeries` 都可以直接解析为 Mathlib 的名字：

```lean
-- [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸]
theorem logSeries_radius_eq_one : (logSeries ℚ 𝔸).radius = 1

-- 再加 [CompleteSpace 𝔸]
theorem log_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall log (logSeries ℚ 𝔸) 1 1

theorem exp_log {y : 𝔸} (hy : ‖y - 1‖ < 1) : exp (log y) = y

-- 下述余项界只需 [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]，
-- 不要求 [NormOneClass 𝔸]。
theorem norm_log_one_add_sub_logPartialSum_le (x : 𝔸) (n : ℕ) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - logPartialSum 𝔸 n x‖ ≤ ‖x‖ ^ n * (1 - ‖x‖)⁻¹
```

这些声明在整理时应保持现有假设。尤其不要因为收敛半径 API 用到了 `NormOneClass`，
就把这个要求扩散到原本通过几何级数控制的余项界；也不要把公开的有理数代数接口改成
必须显式提供实数代数接口。现有 ODE 证明通过 `RealScalar` 在内部取得实数结构。

## 一个不能归入“完全重复”的引理

在 `[Field 𝕂] [Field 𝕂'] [Ring 𝔸] [Algebra 𝕂 𝔸] [Algebra 𝕂' 𝔸]`
及相应拓扑假设下，本地还有：

```lean
theorem logSeries_eq_logSeries (n : ℕ) (x : 𝔸) :
    (logSeries 𝕂 𝔸 n fun _ => x) = logSeries 𝕂' 𝔸 n fun _ => x
```

它没有要求 `Algebra ℚ 𝔸`，而 Mathlib 的 `logSeries_eq_logSeries_rat` 要求该结构。
不能为了套用后者，给前者增加这个假设。

目前 `FQFP/` 内搜索只有该定理的定义，没有调用。建议第一步保留它及其两个私有
系数比较辅助引理，让迁移保持数学接口不变；这也是去重探针采用的做法。若之后决定
清理未使用的公开接口，可将这组三条声明一起删除。若保留此一般性，则两个私有
辅助证明暂时与 Mathlib 重复是有具体原因的，可另外考虑上游补充一般比较 API。

`logSeries_apply_one_const` 也只找到定义，且数学内容已由 `logSeries_apply_one` 覆盖；
可在单独的未使用 API 清理中处理。

## 推荐实施顺序

1. 在当前文件直接使用 Mathlib 的两条定义，删除表中的重复基础定理。
   当前文件已经 `open NormedSpace`；使用 `log` 的主要下游文件也已经打开该命名空间。
   实施时仍应编译全部下游，核查名称解析和公开导出。
2. 保持新增定理名称及证明主体不变。若确有仓库外调用者依赖 `FQFP.log` 等名字，
   可短期集中保留兼容缩写或废弃别名；不要为尚未确认的外部兼容需求永久维护整套转发 API。
3. 更新模块说明，将文件定位为 Mathlib 对数的分析扩展。
4. 按项目要求依次执行缓存检查、`lake build FQFP`、`lake exe runLinter`、
   `lake exe lint-style`。已有缓存可跳过获取；不执行裸 `lake build`。
5. 若后续有复用或上游贡献需求，再拆出通用的收敛/解析、余项估计、`exp`/`log` 互逆三层。
   路径整理与公开命名空间迁移另开一步；不要修改 `.lake/packages/mathlib` 来保存项目成果。

建议的模块说明核心文字：

> This file extends Mathlib's `NormedSpace.log` and `NormedSpace.logSeries` with convergence,
> analyticity, remainder bounds, and the identity `exp (log x) = x` on the open unit ball
> around `1`. The definitions and elementary algebraic properties come from Mathlib.

长期可优先把半径、可求和与解析性做成上游贡献，再处理余项和互逆结果。
提交上游前应重新核对当时的 Mathlib；本次仅针对项目已锁定版本作判断。

## 初次分析时的验证与边界

- `scratch/bch-log-mathlib-migration-2026-10-23.lean`：复制当前整份文件，在独立
  `LogarithmMigrationProbe` 命名空间删除上述 15 个重复公开声明，保留其他证明。
  `lake env lean` 编译通过，未提高 heartbeat 限额。它验证剩余文件可以直接依赖 Mathlib
  对象，不等于已验证生产模块改动后的所有下游。
- `scratch/bch-log-defeq-2026-10-23.lean`：验证两套定义均为 `rfl` 相等，并验证已有
  半径、幂级数、`exp_log` 结果可直接用于显式写成 `NormedSpace` 对象的目标。
- 初次分析阶段未修改生产 Lean 文件，未运行全项目构建和 linter，也未提交。
  上述定义相等探针针对去重前的接口；其中旧的 `FQFP.log`、`FQFP.logSeries` 名字现已删除。

顺带发现原文件有一句说明需要更正：

> “the series diverges at `x = 2`”

半径等于 `1` 不决定边界点是否收敛；在实数代数中，`x = 2` 对应交错调和级数，实际上收敛。
本次已改为：

> Unlike `exp`, the logarithm power series has radius `1`; the results here are stated
> on its open ball of convergence.

## 第一步实施及验收

已按用户授权完成，未拆文件、未提交：

- `FQFP/BCH/Logarithm.lean` 删除表中全部 15 个重复公开声明，直接使用 Mathlib 的
  `NormedSpace.log`、`NormedSpace.logSeries` 和基础引理，没有新增兼容转发层。
- 新增分析结果、跨任意标量域的 `logSeries_eq_logSeries` 及其两个私有辅助引理全部保留；
  保留声明的假设和证明主体未改写。
- 模块说明更新为 Mathlib 对数的分析扩展，修正了 `x = 2` 处发散的错误说明。
- `FQFP/BCH/BCHElement.lean` 的文档将已移除的 `FQFP.log` 引用改为 `NormedSpace.log`。

Mathlib 所需缓存已存在，未更新依赖，跳过 `lake exe cache get`。最终检查按以下顺序完成：

| 检查 | 结果 | 证据 |
| --- | --- | --- |
| `lake build FQFP` | 通过，9133 jobs；最终构建无警告 | `scratch/logs/bch-log-dedup-build-2026-10-23.log` |
| `lake exe runLinter` | 通过，`Linting passed for FQFP` | `scratch/logs/bch-log-dedup-declaration-lint-2026-10-23.log` |
| `lake exe lint-style` | 退出码 0；无样式错误 | `scratch/logs/bch-log-dedup-style-lint-2026-10-23.log` |

样式检查重放了现有 `scripts/lint-style.lean` 导入模块系统文件的提示；本次未改该检查器。
最终 `git diff --check` 通过；其余已有工作区改动保持原样。
