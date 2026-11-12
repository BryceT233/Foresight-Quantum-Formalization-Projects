/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.SuzukiDefectSepticStage1

/-!
# Certified Suzuki half-defect coefficients after stage 2

Each finite coefficient is computed from the preceding stage's certified
coefficients. Stored integer tables avoid recomputing earlier stages during
kernel reduction of the next stage.

## Main results

* `stage2Degree6_eq`: the exact degree-six coefficient after stage 2.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

/-- The complete integer degree-0 coefficient after half-stage 2. -/
def stage2Degree0 : ParamTable :=
  [
    (snapshotWord 1 1 0, 1),
    (snapshotWord 1 1 1, 2),
    (snapshotWord 1 0 0, -1),
    (snapshotWord 1 0 1, -1)
  ]

/-- The stage-2 degree-0 table is the actual integer recurrence coefficient. -/
theorem stage2Degree0_eq :
    defectCoeffTable (prefixTables 2) 0 = stage2Degree0 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage1Degree0_eq]
  decide +kernel

/-- The complete integer degree-1 coefficient after half-stage 2. -/
def stage2Degree1 : ParamTable :=
  [
    (snapshotWord 2 2 1, 840),
    (snapshotWord 2 2 2, -840),
    (snapshotWord 2 1 1, -420),
    (snapshotWord 2 1 2, 420)
  ]

/-- The stage-2 degree-1 table is the actual integer recurrence coefficient. -/
theorem stage2Degree1_eq :
    defectCoeffTable (prefixTables 2) 1 = stage2Degree1 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage1Degree0_eq, stage1Degree1_eq]
  decide +kernel

/-- The complete integer degree-2 coefficient after half-stage 2. -/
def stage2Degree2 : ParamTable :=
  [
    (snapshotWord 3 3 3, 352800),
    (snapshotWord 3 3 5, -705600),
    (snapshotWord 3 3 6, 352800),
    (snapshotWord 3 2 1, -88200),
    (snapshotWord 3 2 2, 176400),
    (snapshotWord 3 2 4, -88200)
  ]

/-- The stage-2 degree-2 table is the actual integer recurrence coefficient. -/
theorem stage2Degree2_eq :
    defectCoeffTable (prefixTables 2) 2 = stage2Degree2 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage1Degree0_eq, stage1Degree1_eq, stage1Degree2_eq]
  decide +kernel

/-- The complete integer degree-3 coefficient after half-stage 2. -/
def stage2Degree3 : ParamTable :=
  [
    (snapshotWord 4 4 7, 98784000),
    (snapshotWord 4 4 11, -296352000),
    (snapshotWord 4 4 13, 296352000),
    (snapshotWord 4 4 14, -98784000),
    (snapshotWord 4 3 1, 12348000),
    (snapshotWord 4 3 2, -37044000),
    (snapshotWord 4 3 3, -74088000),
    (snapshotWord 4 3 4, 37044000),
    (snapshotWord 4 3 5, 148176000),
    (snapshotWord 4 3 7, 49392000),
    (snapshotWord 4 3 8, -12348000),
    (snapshotWord 4 3 10, -148176000),
    (snapshotWord 4 3 11, -148176000),
    (snapshotWord 4 3 12, 74088000),
    (snapshotWord 4 3 13, 148176000),
    (snapshotWord 4 3 14, -49392000)
  ]

/-- The stage-2 degree-3 table is the actual integer recurrence coefficient. -/
theorem stage2Degree3_eq :
    defectCoeffTable (prefixTables 2) 3 = stage2Degree3 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage1Degree0_eq, stage1Degree1_eq, stage1Degree2_eq,
    stage1Degree3_eq]
  decide +kernel

/-- The complete integer degree-4 coefficient after half-stage 2. -/
def stage2Degree4 : ParamTable :=
  [
    (snapshotWord 5 5 15, 20744640000),
    (snapshotWord 5 5 23, -82978560000),
    (snapshotWord 5 5 27, 124467840000),
    (snapshotWord 5 5 29, -82978560000),
    (snapshotWord 5 5 30, 20744640000),
    (snapshotWord 5 4 1, -1296540000),
    (snapshotWord 5 4 2, 5186160000),
    (snapshotWord 5 4 3, 10372320000),
    (snapshotWord 5 4 4, -7779240000),
    (snapshotWord 5 4 5, -31116960000),
    (snapshotWord 5 4 7, -31116960000),
    (snapshotWord 5 4 8, 5186160000),
    (snapshotWord 5 4 9, 31116960000),
    (snapshotWord 5 4 11, 62233920000),
    (snapshotWord 5 4 15, 20744640000),
    (snapshotWord 5 4 16, -1296540000),
    (snapshotWord 5 4 17, -20744640000),
    (snapshotWord 5 4 18, 31116960000),
    (snapshotWord 5 4 19, 31116960000),
    (snapshotWord 5 4 20, -31116960000),
    (snapshotWord 5 4 21, -124467840000),
    (snapshotWord 5 4 23, -82978560000),
    (snapshotWord 5 4 24, 10372320000),
    (snapshotWord 5 4 25, 31116960000),
    (snapshotWord 5 4 26, 62233920000),
    (snapshotWord 5 4 27, 124467840000),
    (snapshotWord 5 4 28, -31116960000),
    (snapshotWord 5 4 29, -82978560000),
    (snapshotWord 5 4 30, 20744640000)
  ]

/-- The stage-2 degree-4 table is the actual integer recurrence coefficient. -/
theorem stage2Degree4_eq :
    defectCoeffTable (prefixTables 2) 4 = stage2Degree4 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage1Degree0_eq, stage1Degree1_eq, stage1Degree2_eq,
    stage1Degree3_eq, stage1Degree4_eq]
  decide +kernel

/-- The complete integer degree-5 coefficient after half-stage 2. -/
def stage2Degree5 : ParamTable :=
  [
    (snapshotWord 6 6 31, 3485099520000),
    (snapshotWord 6 6 47, -17425497600000),
    (snapshotWord 6 6 55, 34850995200000),
    (snapshotWord 6 6 59, -34850995200000),
    (snapshotWord 6 6 61, 17425497600000),
    (snapshotWord 6 6 62, -3485099520000),
    (snapshotWord 6 5 1, 108909360000),
    (snapshotWord 6 5 2, -544546800000),
    (snapshotWord 6 5 3, -1089093600000),
    (snapshotWord 6 5 4, 1089093600000),
    (snapshotWord 6 5 5, 4356374400000),
    (snapshotWord 6 5 7, 4356374400000),
    (snapshotWord 6 5 8, -1089093600000),
    (snapshotWord 6 5 9, -6534561600000),
    (snapshotWord 6 5 11, -13069123200000),
    (snapshotWord 6 5 15, -8712748800000),
    (snapshotWord 6 5 16, 544546800000),
    (snapshotWord 6 5 17, 4356374400000),
    (snapshotWord 6 5 19, 13069123200000),
    (snapshotWord 6 5 23, 17425497600000),
    (snapshotWord 6 5 31, 5227649280000),
    (snapshotWord 6 5 32, -108909360000),
    (snapshotWord 6 5 34, -4356374400000),
    (snapshotWord 6 5 35, -13069123200000),
    (snapshotWord 6 5 36, 6534561600000),
    (snapshotWord 6 5 37, 26138246400000),
    (snapshotWord 6 5 39, 17425497600000),
    (snapshotWord 6 5 40, -4356374400000),
    (snapshotWord 6 5 41, -26138246400000),
    (snapshotWord 6 5 43, -52276492800000),
    (snapshotWord 6 5 47, -26138246400000),
    (snapshotWord 6 5 48, 1089093600000),
    (snapshotWord 6 5 49, 13069123200000),
    (snapshotWord 6 5 50, -13069123200000),
    (snapshotWord 6 5 52, 13069123200000),
    (snapshotWord 6 5 53, 52276492800000),
    (snapshotWord 6 5 55, 52276492800000),
    (snapshotWord 6 5 56, -4356374400000),
    (snapshotWord 6 5 57, -17425497600000),
    (snapshotWord 6 5 58, -17425497600000),
    (snapshotWord 6 5 59, -52276492800000),
    (snapshotWord 6 5 60, 8712748800000),
    (snapshotWord 6 5 61, 26138246400000),
    (snapshotWord 6 5 62, -5227649280000)
  ]

/-- The stage-2 degree-5 table is the actual integer recurrence coefficient. -/
theorem stage2Degree5_eq :
    defectCoeffTable (prefixTables 2) 5 = stage2Degree5 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage1Degree0_eq, stage1Degree1_eq, stage1Degree2_eq,
    stage1Degree3_eq, stage1Degree4_eq, stage1Degree5_eq]
  decide +kernel

/-- The complete integer degree-6 coefficient after half-stage 2. -/
def stage2Degree6 : ParamTable :=
  [
    (snapshotWord 7 7 63, 487913932800000),
    (snapshotWord 7 7 95, -2927483596800000),
    (snapshotWord 7 7 111, 7318708992000000),
    (snapshotWord 7 7 119, -9758278656000000),
    (snapshotWord 7 7 123, 7318708992000000),
    (snapshotWord 7 7 125, -2927483596800000),
    (snapshotWord 7 7 126, 487913932800000),
    (snapshotWord 7 6 1, -7623655200000),
    (snapshotWord 7 6 2, 45741931200000),
    (snapshotWord 7 6 3, 91483862400000),
    (snapshotWord 7 6 4, -114354828000000),
    (snapshotWord 7 6 5, -457419312000000),
    (snapshotWord 7 6 7, -457419312000000),
    (snapshotWord 7 6 8, 152473104000000),
    (snapshotWord 7 6 9, 914838624000000),
    (snapshotWord 7 6 11, 1829677248000000),
    (snapshotWord 7 6 15, 1219784832000000),
    (snapshotWord 7 6 16, -114354828000000),
    (snapshotWord 7 6 17, -914838624000000),
    (snapshotWord 7 6 19, -2744515872000000),
    (snapshotWord 7 6 23, -3659354496000000),
    (snapshotWord 7 6 31, -1829677248000000),
    (snapshotWord 7 6 32, 45741931200000),
    (snapshotWord 7 6 33, 457419312000000),
    (snapshotWord 7 6 35, 1829677248000000),
    (snapshotWord 7 6 39, 3659354496000000),
    (snapshotWord 7 6 47, 3659354496000000),
    (snapshotWord 7 6 63, 975827865600000),
    (snapshotWord 7 6 64, -7623655200000),
    (snapshotWord 7 6 65, -182967724800000),
    (snapshotWord 7 6 66, 457419312000000),
    (snapshotWord 7 6 67, 457419312000000),
    (snapshotWord 7 6 68, -914838624000000),
    (snapshotWord 7 6 69, -3659354496000000),
    (snapshotWord 7 6 71, -4879139328000000),
    (snapshotWord 7 6 72, 914838624000000),
    (snapshotWord 7 6 73, 5489031744000000),
    (snapshotWord 7 6 75, 10978063488000000),
    (snapshotWord 7 6 79, 5489031744000000),
    (snapshotWord 7 6 80, -457419312000000),
    (snapshotWord 7 6 81, -3659354496000000),
    (snapshotWord 7 6 83, -10978063488000000),
    (snapshotWord 7 6 87, -14637417984000000),
    (snapshotWord 7 6 95, -5854967193600000),
    (snapshotWord 7 6 96, 91483862400000),
    (snapshotWord 7 6 97, 457419312000000),
    (snapshotWord 7 6 98, 1829677248000000),
    (snapshotWord 7 6 99, 7318708992000000),
    (snapshotWord 7 6 100, -2744515872000000),
    (snapshotWord 7 6 101, -10978063488000000),
    (snapshotWord 7 6 103, -3659354496000000),
    (snapshotWord 7 6 104, 1829677248000000),
    (snapshotWord 7 6 105, 10978063488000000),
    (snapshotWord 7 6 107, 21956126976000000),
    (snapshotWord 7 6 111, 14637417984000000),
    (snapshotWord 7 6 112, -457419312000000),
    (snapshotWord 7 6 113, -4879139328000000),
    (snapshotWord 7 6 114, 3659354496000000),
    (snapshotWord 7 6 115, -3659354496000000),
    (snapshotWord 7 6 116, -3659354496000000),
    (snapshotWord 7 6 117, -14637417984000000),
    (snapshotWord 7 6 119, -19516557312000000),
    (snapshotWord 7 6 120, 1219784832000000),
    (snapshotWord 7 6 121, 5489031744000000),
    (snapshotWord 7 6 122, 3659354496000000),
    (snapshotWord 7 6 123, 14637417984000000),
    (snapshotWord 7 6 124, -1829677248000000),
    (snapshotWord 7 6 125, -5854967193600000),
    (snapshotWord 7 6 126, 975827865600000)
  ]

/-- The stage-2 degree-6 table is the actual integer recurrence coefficient. -/
theorem stage2Degree6_eq :
    defectCoeffTable (prefixTables 2) 6 = stage2Degree6 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage1Degree0_eq, stage1Degree1_eq, stage1Degree2_eq,
    stage1Degree3_eq, stage1Degree4_eq, stage1Degree5_eq,
    stage1Degree6_eq]
  decide +kernel

end FQFP.SuzukiSepticCertificate
