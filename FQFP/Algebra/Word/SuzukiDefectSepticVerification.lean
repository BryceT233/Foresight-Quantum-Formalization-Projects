/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Word.SuzukiDefectSepticStage6

/-!
# The complete degree-seven binary defect certificate

The six certified stages compute the actual half-defect coefficient. Its
difference from the reduced 128-position target is an explicit multiple of
the parameter's cubic relation.

## Main results

* `defectSepticResidual_eq_nil`: the actual grouped recurrence has the target coefficients.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

/-- The complete integer recurrence agrees modulo the cubic with the 128-position target. -/
theorem defectSepticResidual_eq_nil : defectSepticResidual = [] := by
  unfold defectSepticResidual
  rw [← prefixTables_six, stage6Degree6_eq]
  decide +kernel

end FQFP.SuzukiSepticCertificate
