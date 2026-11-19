---
name: fqfp-upstream-attribution
description: 将第三方 Lean 定义、定理、证明或 API 移植到 FQFP，或核查已有移植的署名时，按实际使用的上游版本保留版权、作者及修改说明。
---

# FQFP 上游署名

首次移植时就写入署名。核查旧文件时，逐个把本地声明与迁移记录、上游源码对应起来。改名、拆分模块或改用 FQFP 的算子表示后，仍要保留所吸收内容的来源。只有主题相似、引用同一篇论文或导入已署名的本地模块时，保留本地署名。证据不足的对应关系在核查结果中说明。

## 文件头

- 核对实际使用的上游提交。在 Lean 文件开头、`module` 或首条 `import` 之前，用注释记录上游仓库、完整提交 SHA、源文件路径，以及本地采用的定义、定理或证明思路。
- 上游有文件级署名时，逐字保留其版权行、许可证说明和完整 `Authors:` 行，包括年份、姓名拼写、标点和顺序。保留已有本地贡献者的署名，将其与上游原文分开。
- 上游只在仓库层面署名时，从该提交的 README、LICENSE 或 NOTICE 核实并引用原文。沿用已声明的集体名称；个人姓名和版权年份均须有来源。
- 一个本地模块吸收多个上游文件时，将各源路径与各自的声明配对。版权和作者声明完全相同的来源可以共用一组署名。上游文件拆到多个本地模块时，每个含移植内容的模块都保留适用的声明。
- 对 Foresight Quantum 在 2026 年修改的文件，在上述来源说明中单列以下原文，整份文件只写一次。

```text
Modified by Foresight Quantum in 2026
```

## 仓库中的实例

- **Physlib / QuantumInfo** 使用逐文件署名。`FQFP/CQM/Qudit/State/Pure.lean` 分别记录 `MState.lean` 和 `Ensemble.lean` 的版权人与作者名单。
- **Qedia / Qhl** 的迁移版本在 README 中统一声明 `Copyright 2026 Qedia contributors.`。`FQFP/QuantumProgram` 中从该版本移植的文件统一使用以下文件头。随后在独立的来源注释中保留上游版权原文、源文件路径及适用的 `Modified by Foresight Quantum in 2026` 修改说明。可参见 `FQFP/QuantumProgram/Measurement.lean`。后续迁移从对应版本重新核对。

```lean
/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/
```

## 验证

核对上游许可证及适用于所移植内容的 NOTICE。对于 Apache 2.0，确保分发内容含有完整许可证正文及适用的 NOTICE 声明；FQFP 的根目录 `LICENSE` 已收录完整的 Apache 2.0 文本。

只补署名时，以修改前的工作区文件为基准，逐字节比对文件头之后的 Lean 正文，覆盖未提交和未跟踪文件。逐项复核上游路径、原始署名和修改说明，并运行 `lake exe lint-style`。需要提交时按仓库 `AGENTS.md` 执行完整检查。
