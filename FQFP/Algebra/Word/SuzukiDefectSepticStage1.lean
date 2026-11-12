/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.SuzukiDefectSepticTable

/-!
# Certified Suzuki half-defect coefficients after stage 1

Each finite coefficient is computed from the preceding stage's certified
coefficients. Stored integer tables avoid recomputing earlier stages during
kernel reduction of the next stage.

## Main results

* `stage1Degree6_eq`: the exact degree-six coefficient after stage 1.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

/-- The complete integer degree-0 coefficient after half-stage 1. -/
def stage1Degree0 : ParamTable :=
  [
    (snapshotWord 1 1 0, 1),
    (snapshotWord 1 0 0, -1),
    (snapshotWord 1 0 1, -1)
  ]

/-- The stage-1 degree-0 table is the actual integer recurrence coefficient. -/
theorem stage1Degree0_eq :
    defectCoeffTable (prefixTables 1) 0 = stage1Degree0 := by
  decide +kernel

/-- The complete integer degree-1 coefficient after half-stage 1. -/
def stage1Degree1 : ParamTable :=
  [
    (snapshotWord 2 1 1, 420),
    (snapshotWord 2 1 2, -420)
  ]

/-- The stage-1 degree-1 table is the actual integer recurrence coefficient. -/
theorem stage1Degree1_eq :
    defectCoeffTable (prefixTables 1) 1 = stage1Degree1 := by
  decide +kernel

/-- The complete integer degree-2 coefficient after half-stage 1. -/
def stage1Degree2 : ParamTable :=
  [
    (snapshotWord 3 2 1, -88200),
    (snapshotWord 3 2 2, 176400),
    (snapshotWord 3 2 4, -88200)
  ]

/-- The stage-1 degree-2 table is the actual integer recurrence coefficient. -/
theorem stage1Degree2_eq :
    defectCoeffTable (prefixTables 1) 2 = stage1Degree2 := by
  decide +kernel

/-- The complete integer degree-3 coefficient after half-stage 1. -/
def stage1Degree3 : ParamTable :=
  [
    (snapshotWord 4 3 1, 12348000),
    (snapshotWord 4 3 2, -37044000),
    (snapshotWord 4 3 4, 37044000),
    (snapshotWord 4 3 8, -12348000)
  ]

/-- The stage-1 degree-3 table is the actual integer recurrence coefficient. -/
theorem stage1Degree3_eq :
    defectCoeffTable (prefixTables 1) 3 = stage1Degree3 := by
  decide +kernel

/-- The complete integer degree-4 coefficient after half-stage 1. -/
def stage1Degree4 : ParamTable :=
  [
    (snapshotWord 5 4 1, -1296540000),
    (snapshotWord 5 4 2, 5186160000),
    (snapshotWord 5 4 4, -7779240000),
    (snapshotWord 5 4 8, 5186160000),
    (snapshotWord 5 4 16, -1296540000)
  ]

/-- The stage-1 degree-4 table is the actual integer recurrence coefficient. -/
theorem stage1Degree4_eq :
    defectCoeffTable (prefixTables 1) 4 = stage1Degree4 := by
  decide +kernel

/-- The complete integer degree-5 coefficient after half-stage 1. -/
def stage1Degree5 : ParamTable :=
  [
    (snapshotWord 6 5 1, 108909360000),
    (snapshotWord 6 5 2, -544546800000),
    (snapshotWord 6 5 4, 1089093600000),
    (snapshotWord 6 5 8, -1089093600000),
    (snapshotWord 6 5 16, 544546800000),
    (snapshotWord 6 5 32, -108909360000)
  ]

/-- The stage-1 degree-5 table is the actual integer recurrence coefficient. -/
theorem stage1Degree5_eq :
    defectCoeffTable (prefixTables 1) 5 = stage1Degree5 := by
  decide +kernel

/-- The complete integer degree-6 coefficient after half-stage 1. -/
def stage1Degree6 : ParamTable :=
  [
    (snapshotWord 7 6 1, -7623655200000),
    (snapshotWord 7 6 2, 45741931200000),
    (snapshotWord 7 6 4, -114354828000000),
    (snapshotWord 7 6 8, 152473104000000),
    (snapshotWord 7 6 16, -114354828000000),
    (snapshotWord 7 6 32, 45741931200000),
    (snapshotWord 7 6 64, -7623655200000)
  ]

/-- The stage-1 degree-6 table is the actual integer recurrence coefficient. -/
theorem stage1Degree6_eq :
    defectCoeffTable (prefixTables 1) 6 = stage1Degree6 := by
  decide +kernel

end FQFP.SuzukiSepticCertificate
