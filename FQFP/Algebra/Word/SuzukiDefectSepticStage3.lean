/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.SuzukiDefectSepticStage2

/-!
# Certified Suzuki half-defect coefficients after stage 3

Each finite coefficient is computed from the preceding stage's certified
coefficients. Stored integer tables avoid recomputing earlier stages during
kernel reduction of the next stage.

## Main results

* `stage3Degree6_eq`: the exact degree-six coefficient after stage 3.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

/-- The complete integer degree-0 coefficient after half-stage 3. -/
def stage3Degree0 : ParamTable :=
  [
    (snapshotWord 1 1 0, 3),
    (snapshotWord 1 1 1, 2),
    (snapshotWord 1 0 0, -1),
    (snapshotWord 1 0 1, -1)
  ]

/-- The stage-3 degree-0 table is the actual integer recurrence coefficient. -/
theorem stage3Degree0_eq :
    defectCoeffTable (prefixTables 3) 0 = stage3Degree0 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage2Degree0_eq]
  decide +kernel

/-- The complete integer degree-1 coefficient after half-stage 3. -/
def stage3Degree1 : ParamTable :=
  [
    (snapshotWord 2 2 1, -840),
    (snapshotWord 2 2 2, 840),
    (snapshotWord 2 1 1, 420),
    (snapshotWord 2 1 2, -420)
  ]

/-- The stage-3 degree-1 table is the actual integer recurrence coefficient. -/
theorem stage3Degree1_eq :
    defectCoeffTable (prefixTables 3) 1 = stage3Degree1 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage2Degree0_eq, stage2Degree1_eq]
  decide +kernel

/-- The complete integer degree-2 coefficient after half-stage 3. -/
def stage3Degree2 : ParamTable :=
  [
    (snapshotWord 3 3 3, 352800),
    (snapshotWord 3 3 5, -705600),
    (snapshotWord 3 3 6, 352800),
    (snapshotWord 3 2 1, -88200),
    (snapshotWord 3 2 2, 176400),
    (snapshotWord 3 2 4, -88200)
  ]

/-- The stage-3 degree-2 table is the actual integer recurrence coefficient. -/
theorem stage3Degree2_eq :
    defectCoeffTable (prefixTables 3) 2 = stage3Degree2 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage2Degree0_eq, stage2Degree1_eq, stage2Degree2_eq]
  decide +kernel

/-- The complete integer degree-3 coefficient after half-stage 3. -/
def stage3Degree3 : ParamTable :=
  [
    (snapshotWord 4 4 1, 98784000),
    (snapshotWord 4 4 2, -296352000),
    (snapshotWord 4 4 3, -296352000),
    (snapshotWord 4 4 4, 296352000),
    (snapshotWord 4 4 5, 592704000),
    (snapshotWord 4 4 7, 98784000),
    (snapshotWord 4 4 8, -98784000),
    (snapshotWord 4 4 10, -592704000),
    (snapshotWord 4 4 11, -296352000),
    (snapshotWord 4 4 12, 296352000),
    (snapshotWord 4 4 13, 296352000),
    (snapshotWord 4 4 14, -98784000),
    (snapshotWord 4 3 1, 37044000),
    (snapshotWord 4 3 2, -111132000),
    (snapshotWord 4 3 3, -74088000),
    (snapshotWord 4 3 4, 111132000),
    (snapshotWord 4 3 5, 148176000),
    (snapshotWord 4 3 7, 49392000),
    (snapshotWord 4 3 8, -37044000),
    (snapshotWord 4 3 10, -148176000),
    (snapshotWord 4 3 11, -148176000),
    (snapshotWord 4 3 12, 74088000),
    (snapshotWord 4 3 13, 148176000),
    (snapshotWord 4 3 14, -49392000)
  ]

/-- The stage-3 degree-3 table is the actual integer recurrence coefficient. -/
theorem stage3Degree3_eq :
    defectCoeffTable (prefixTables 3) 3 = stage3Degree3 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage2Degree0_eq, stage2Degree1_eq, stage2Degree2_eq,
    stage2Degree3_eq]
  decide +kernel

/-- The complete integer degree-4 coefficient after half-stage 3. -/
def stage3Degree4 : ParamTable :=
  [
    (snapshotWord 5 5 1, -41489280000),
    (snapshotWord 5 5 2, 165957120000),
    (snapshotWord 5 5 3, 124467840000),
    (snapshotWord 5 5 4, -248935680000),
    (snapshotWord 5 5 5, -248935680000),
    (snapshotWord 5 5 6, -124467840000),
    (snapshotWord 5 5 7, -82978560000),
    (snapshotWord 5 5 8, 165957120000),
    (snapshotWord 5 5 10, 497871360000),
    (snapshotWord 5 5 11, 248935680000),
    (snapshotWord 5 5 12, -124467840000),
    (snapshotWord 5 5 13, -248935680000),
    (snapshotWord 5 5 14, 165957120000),
    (snapshotWord 5 5 15, 20744640000),
    (snapshotWord 5 5 16, -41489280000),
    (snapshotWord 5 5 20, -248935680000),
    (snapshotWord 5 5 22, -248935680000),
    (snapshotWord 5 5 23, -82978560000),
    (snapshotWord 5 5 24, 124467840000),
    (snapshotWord 5 5 26, 248935680000),
    (snapshotWord 5 5 27, 124467840000),
    (snapshotWord 5 5 28, -82978560000),
    (snapshotWord 5 5 29, -82978560000),
    (snapshotWord 5 5 30, 20744640000),
    (snapshotWord 5 4 1, -22041180000),
    (snapshotWord 5 4 2, 88164720000),
    (snapshotWord 5 4 3, 72606240000),
    (snapshotWord 5 4 4, -132247080000),
    (snapshotWord 5 4 5, -155584800000),
    (snapshotWord 5 4 6, -62233920000),
    (snapshotWord 5 4 7, -72606240000),
    (snapshotWord 5 4 8, 88164720000),
    (snapshotWord 5 4 9, 31116960000),
    (snapshotWord 5 4 10, 248935680000),
    (snapshotWord 5 4 11, 186701760000),
    (snapshotWord 5 4 12, -62233920000),
    (snapshotWord 5 4 13, -124467840000),
    (snapshotWord 5 4 14, 82978560000),
    (snapshotWord 5 4 15, 20744640000),
    (snapshotWord 5 4 16, -22041180000),
    (snapshotWord 5 4 17, -20744640000),
    (snapshotWord 5 4 18, 31116960000),
    (snapshotWord 5 4 19, 31116960000),
    (snapshotWord 5 4 20, -155584800000),
    (snapshotWord 5 4 21, -124467840000),
    (snapshotWord 5 4 22, -124467840000),
    (snapshotWord 5 4 23, -82978560000),
    (snapshotWord 5 4 24, 72606240000),
    (snapshotWord 5 4 25, 31116960000),
    (snapshotWord 5 4 26, 186701760000),
    (snapshotWord 5 4 27, 124467840000),
    (snapshotWord 5 4 28, -72606240000),
    (snapshotWord 5 4 29, -82978560000),
    (snapshotWord 5 4 30, 20744640000)
  ]

/-- The stage-3 degree-4 table is the actual integer recurrence coefficient. -/
theorem stage3Degree4_eq :
    defectCoeffTable (prefixTables 3) 4 = stage3Degree4 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage2Degree0_eq, stage2Degree1_eq, stage2Degree2_eq,
    stage2Degree3_eq, stage2Degree4_eq]
  decide +kernel

/-- The complete integer degree-5 coefficient after half-stage 3. -/
def stage3Degree5 : ParamTable :=
  [
    (snapshotWord 6 6 1, 10455298560000),
    (snapshotWord 6 6 2, -52276492800000),
    (snapshotWord 6 6 3, -34850995200000),
    (snapshotWord 6 6 4, 104552985600000),
    (snapshotWord 6 6 5, 69701990400000),
    (snapshotWord 6 6 6, 69701990400000),
    (snapshotWord 6 6 7, 34850995200000),
    (snapshotWord 6 6 8, -104552985600000),
    (snapshotWord 6 6 10, -209105971200000),
    (snapshotWord 6 6 11, -104552985600000),
    (snapshotWord 6 6 13, 104552985600000),
    (snapshotWord 6 6 14, -104552985600000),
    (snapshotWord 6 6 15, -17425497600000),
    (snapshotWord 6 6 16, 52276492800000),
    (snapshotWord 6 6 20, 209105971200000),
    (snapshotWord 6 6 22, 209105971200000),
    (snapshotWord 6 6 23, 69701990400000),
    (snapshotWord 6 6 24, -69701990400000),
    (snapshotWord 6 6 26, -209105971200000),
    (snapshotWord 6 6 27, -104552985600000),
    (snapshotWord 6 6 28, 104552985600000),
    (snapshotWord 6 6 29, 69701990400000),
    (snapshotWord 6 6 31, 3485099520000),
    (snapshotWord 6 6 32, -10455298560000),
    (snapshotWord 6 6 40, -69701990400000),
    (snapshotWord 6 6 44, -104552985600000),
    (snapshotWord 6 6 46, -69701990400000),
    (snapshotWord 6 6 47, -17425497600000),
    (snapshotWord 6 6 48, 34850995200000),
    (snapshotWord 6 6 52, 104552985600000),
    (snapshotWord 6 6 54, 104552985600000),
    (snapshotWord 6 6 55, 34850995200000),
    (snapshotWord 6 6 56, -34850995200000),
    (snapshotWord 6 6 58, -69701990400000),
    (snapshotWord 6 6 59, -34850995200000),
    (snapshotWord 6 6 60, 17425497600000),
    (snapshotWord 6 6 61, 17425497600000),
    (snapshotWord 6 6 62, -3485099520000),
    (snapshotWord 6 5 1, 9039476880000),
    (snapshotWord 6 5 2, -45197384400000),
    (snapshotWord 6 5 3, -35940088800000),
    (snapshotWord 6 5 4, 90394768800000),
    (snapshotWord 6 5 5, 82771113600000),
    (snapshotWord 6 5 6, 60989241600000),
    (snapshotWord 6 5 7, 47920118400000),
    (snapshotWord 6 5 8, -90394768800000),
    (snapshotWord 6 5 9, -32672808000000),
    (snapshotWord 6 5 10, -182967724800000),
    (snapshotWord 6 5 11, -117622108800000),
    (snapshotWord 6 5 13, 52276492800000),
    (snapshotWord 6 5 14, -78414739200000),
    (snapshotWord 6 5 15, -26138246400000),
    (snapshotWord 6 5 16, 45197384400000),
    (snapshotWord 6 5 17, 21781872000000),
    (snapshotWord 6 5 19, -13069123200000),
    (snapshotWord 6 5 20, 182967724800000),
    (snapshotWord 6 5 21, 104552985600000),
    (snapshotWord 6 5 22, 156829478400000),
    (snapshotWord 6 5 23, 87127488000000),
    (snapshotWord 6 5 24, -60989241600000),
    (snapshotWord 6 5 25, -26138246400000),
    (snapshotWord 6 5 26, -156829478400000),
    (snapshotWord 6 5 27, -104552985600000),
    (snapshotWord 6 5 28, 78414739200000),
    (snapshotWord 6 5 29, 69701990400000),
    (snapshotWord 6 5 31, 5227649280000),
    (snapshotWord 6 5 32, -9039476880000),
    (snapshotWord 6 5 34, -21781872000000),
    (snapshotWord 6 5 35, -13069123200000),
    (snapshotWord 6 5 36, 32672808000000),
    (snapshotWord 6 5 37, 26138246400000),
    (snapshotWord 6 5 38, 26138246400000),
    (snapshotWord 6 5 39, 17425497600000),
    (snapshotWord 6 5 40, -82771113600000),
    (snapshotWord 6 5 41, -26138246400000),
    (snapshotWord 6 5 42, -104552985600000),
    (snapshotWord 6 5 43, -52276492800000),
    (snapshotWord 6 5 44, -52276492800000),
    (snapshotWord 6 5 46, -69701990400000),
    (snapshotWord 6 5 47, -26138246400000),
    (snapshotWord 6 5 48, 35940088800000),
    (snapshotWord 6 5 49, 13069123200000),
    (snapshotWord 6 5 50, 13069123200000),
    (snapshotWord 6 5 52, 117622108800000),
    (snapshotWord 6 5 53, 52276492800000),
    (snapshotWord 6 5 54, 104552985600000),
    (snapshotWord 6 5 55, 52276492800000),
    (snapshotWord 6 5 56, -47920118400000),
    (snapshotWord 6 5 57, -17425497600000),
    (snapshotWord 6 5 58, -87127488000000),
    (snapshotWord 6 5 59, -52276492800000),
    (snapshotWord 6 5 60, 26138246400000),
    (snapshotWord 6 5 61, 26138246400000),
    (snapshotWord 6 5 62, -5227649280000)
  ]

/-- The stage-3 degree-5 table is the actual integer recurrence coefficient. -/
theorem stage3Degree5_eq :
    defectCoeffTable (prefixTables 3) 5 = stage3Degree5 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage2Degree0_eq, stage2Degree1_eq, stage2Degree2_eq,
    stage2Degree3_eq, stage2Degree4_eq, stage2Degree5_eq]
  decide +kernel

/-- The parameter-degree-7 slice of half-stage 3, degree 6. -/
def stage3Degree6Parameter7 : ParamTable :=
  [
    (snapshotWord 7 7 1, -1951655731200000),
    (snapshotWord 7 7 2, 11709934387200000),
    (snapshotWord 7 7 3, 7318708992000000),
    (snapshotWord 7 7 4, -29274835968000000),
    (snapshotWord 7 7 5, -14637417984000000),
    (snapshotWord 7 7 6, -21956126976000000),
    (snapshotWord 7 7 7, -9758278656000000),
    (snapshotWord 7 7 8, 39033114624000000),
    (snapshotWord 7 7 10, 58549671936000000),
    (snapshotWord 7 7 11, 29274835968000000),
    (snapshotWord 7 7 12, 14637417984000000),
    (snapshotWord 7 7 13, -29274835968000000),
    (snapshotWord 7 7 14, 39033114624000000),
    (snapshotWord 7 7 15, 7318708992000000),
    (snapshotWord 7 7 16, -29274835968000000),
    (snapshotWord 7 7 20, -87824507904000000),
    (snapshotWord 7 7 22, -87824507904000000),
    (snapshotWord 7 7 23, -29274835968000000),
    (snapshotWord 7 7 24, 14637417984000000),
    (snapshotWord 7 7 26, 87824507904000000),
    (snapshotWord 7 7 27, 43912253952000000),
    (snapshotWord 7 7 28, -58549671936000000),
    (snapshotWord 7 7 29, -29274835968000000),
    (snapshotWord 7 7 30, -7318708992000000),
    (snapshotWord 7 7 31, -2927483596800000),
    (snapshotWord 7 7 32, 11709934387200000),
    (snapshotWord 7 7 40, 58549671936000000),
    (snapshotWord 7 7 44, 87824507904000000),
    (snapshotWord 7 7 46, 58549671936000000),
    (snapshotWord 7 7 47, 14637417984000000),
    (snapshotWord 7 7 48, -21956126976000000),
    (snapshotWord 7 7 52, -87824507904000000),
    (snapshotWord 7 7 54, -87824507904000000),
    (snapshotWord 7 7 55, -29274835968000000),
    (snapshotWord 7 7 56, 39033114624000000),
    (snapshotWord 7 7 58, 58549671936000000),
    (snapshotWord 7 7 59, 29274835968000000),
    (snapshotWord 7 7 60, -7318708992000000),
    (snapshotWord 7 7 61, -14637417984000000),
    (snapshotWord 7 7 62, 5854967193600000),
    (snapshotWord 7 7 63, 487913932800000),
    (snapshotWord 7 7 64, -1951655731200000),
    (snapshotWord 7 7 80, -14637417984000000),
    (snapshotWord 7 7 88, -29274835968000000),
    (snapshotWord 7 7 92, -29274835968000000),
    (snapshotWord 7 7 94, -14637417984000000),
    (snapshotWord 7 7 95, -2927483596800000),
    (snapshotWord 7 7 96, 7318708992000000),
    (snapshotWord 7 7 104, 29274835968000000),
    (snapshotWord 7 7 108, 43912253952000000),
    (snapshotWord 7 7 110, 29274835968000000),
    (snapshotWord 7 7 111, 7318708992000000),
    (snapshotWord 7 7 112, -9758278656000000),
    (snapshotWord 7 7 116, -29274835968000000),
    (snapshotWord 7 7 118, -29274835968000000),
    (snapshotWord 7 7 119, -9758278656000000),
    (snapshotWord 7 7 120, 7318708992000000),
    (snapshotWord 7 7 122, 14637417984000000),
    (snapshotWord 7 7 123, 7318708992000000),
    (snapshotWord 7 7 124, -2927483596800000),
    (snapshotWord 7 7 125, -2927483596800000),
    (snapshotWord 7 7 126, 487913932800000)
  ]

/-- The parameter-degree-6 slice of half-stage 3, degree 6. -/
def stage3Degree6Parameter6 : ParamTable :=
  [
    (snapshotWord 7 6 1, -2630161044000000),
    (snapshotWord 7 6 2, 15780966264000000),
    (snapshotWord 7 6 3, 11984385974400000),
    (snapshotWord 7 6 4, -39452415660000000),
    (snapshotWord 7 6 5, -29732255280000000),
    (snapshotWord 7 6 6, -30189674592000000),
    (snapshotWord 7 6 7, -19973976624000000),
    (snapshotWord 7 6 8, 52603220880000000),
    (snapshotWord 7 6 9, 17381933856000000),
    (snapshotWord 7 6 10, 84165153408000000),
    (snapshotWord 7 6 11, 49401285696000000),
    (snapshotWord 7 6 12, 18296772480000000),
    (snapshotWord 7 6 13, -14637417984000000),
    (snapshotWord 7 6 14, 45132038784000000),
    (snapshotWord 7 6 15, 15857202816000000),
    (snapshotWord 7 6 16, -39452415660000000),
    (snapshotWord 7 6 17, -11892902112000000),
    (snapshotWord 7 6 18, -16467095232000000),
    (snapshotWord 7 6 19, -2744515872000000),
    (snapshotWord 7 6 20, -109780634880000000),
    (snapshotWord 7 6 21, -43912253952000000),
    (snapshotWord 7 6 22, -98802571392000000),
    (snapshotWord 7 6 23, -47571608448000000),
    (snapshotWord 7 6 24, 18296772480000000),
    (snapshotWord 7 6 25, 10978063488000000),
    (snapshotWord 7 6 26, 65868380928000000),
    (snapshotWord 7 6 27, 43912253952000000),
    (snapshotWord 7 6 28, -51230962944000000),
    (snapshotWord 7 6 29, -29274835968000000),
    (snapshotWord 7 6 30, -14637417984000000),
    (snapshotWord 7 6 31, -6220902643200000),
    (snapshotWord 7 6 32, 15780966264000000),
    (snapshotWord 7 6 33, 457419312000000),
    (snapshotWord 7 6 34, 21956126976000000),
    (snapshotWord 7 6 35, 12807740736000000),
    (snapshotWord 7 6 36, -16467095232000000),
    (snapshotWord 7 6 37, -21956126976000000),
    (snapshotWord 7 6 38, -10978063488000000),
    (snapshotWord 7 6 39, -10978063488000000),
    (snapshotWord 7 6 40, 84165153408000000),
    (snapshotWord 7 6 41, 21956126976000000),
    (snapshotWord 7 6 42, 87824507904000000),
    (snapshotWord 7 6 43, 43912253952000000),
    (snapshotWord 7 6 44, 65868380928000000),
    (snapshotWord 7 6 46, 73187089920000000),
    (snapshotWord 7 6 47, 25615481472000000),
    (snapshotWord 7 6 48, -30189674592000000),
    (snapshotWord 7 6 49, -10978063488000000),
    (snapshotWord 7 6 50, -10978063488000000),
    (snapshotWord 7 6 52, -98802571392000000),
    (snapshotWord 7 6 53, -43912253952000000),
    (snapshotWord 7 6 54, -87824507904000000),
    (snapshotWord 7 6 55, -43912253952000000),
    (snapshotWord 7 6 56, 45132038784000000),
    (snapshotWord 7 6 57, 14637417984000000),
    (snapshotWord 7 6 58, 73187089920000000),
    (snapshotWord 7 6 59, 43912253952000000),
    (snapshotWord 7 6 60, -14637417984000000),
    (snapshotWord 7 6 61, -21956126976000000),
    (snapshotWord 7 6 62, 8782450790400000),
    (snapshotWord 7 6 63, 975827865600000),
    (snapshotWord 7 6 64, -2630161044000000),
    (snapshotWord 7 6 65, -182967724800000),
    (snapshotWord 7 6 66, 457419312000000),
    (snapshotWord 7 6 67, 457419312000000),
    (snapshotWord 7 6 68, -11892902112000000),
    (snapshotWord 7 6 69, -3659354496000000),
    (snapshotWord 7 6 70, -10978063488000000),
    (snapshotWord 7 6 71, -4879139328000000),
    (snapshotWord 7 6 72, 17381933856000000),
    (snapshotWord 7 6 73, 5489031744000000),
    (snapshotWord 7 6 74, 21956126976000000),
    (snapshotWord 7 6 75, 10978063488000000),
    (snapshotWord 7 6 76, 10978063488000000),
    (snapshotWord 7 6 78, 14637417984000000),
    (snapshotWord 7 6 79, 5489031744000000),
    (snapshotWord 7 6 80, -29732255280000000),
    (snapshotWord 7 6 81, -3659354496000000),
    (snapshotWord 7 6 82, -21956126976000000),
    (snapshotWord 7 6 83, -10978063488000000),
    (snapshotWord 7 6 84, -43912253952000000),
    (snapshotWord 7 6 86, -43912253952000000),
    (snapshotWord 7 6 87, -14637417984000000),
    (snapshotWord 7 6 88, -14637417984000000),
    (snapshotWord 7 6 92, -29274835968000000),
    (snapshotWord 7 6 94, -21956126976000000),
    (snapshotWord 7 6 95, -5854967193600000),
    (snapshotWord 7 6 96, 11984385974400000),
    (snapshotWord 7 6 97, 457419312000000),
    (snapshotWord 7 6 98, 12807740736000000),
    (snapshotWord 7 6 99, 7318708992000000),
    (snapshotWord 7 6 100, -2744515872000000),
    (snapshotWord 7 6 101, -10978063488000000),
    (snapshotWord 7 6 103, -3659354496000000),
    (snapshotWord 7 6 104, 49401285696000000),
    (snapshotWord 7 6 105, 10978063488000000),
    (snapshotWord 7 6 106, 43912253952000000),
    (snapshotWord 7 6 107, 21956126976000000),
    (snapshotWord 7 6 108, 43912253952000000),
    (snapshotWord 7 6 110, 43912253952000000),
    (snapshotWord 7 6 111, 14637417984000000),
    (snapshotWord 7 6 112, -19973976624000000),
    (snapshotWord 7 6 113, -4879139328000000),
    (snapshotWord 7 6 114, -10978063488000000),
    (snapshotWord 7 6 115, -3659354496000000),
    (snapshotWord 7 6 116, -47571608448000000),
    (snapshotWord 7 6 117, -14637417984000000),
    (snapshotWord 7 6 118, -43912253952000000),
    (snapshotWord 7 6 119, -19516557312000000),
    (snapshotWord 7 6 120, 15857202816000000),
    (snapshotWord 7 6 121, 5489031744000000),
    (snapshotWord 7 6 122, 25615481472000000),
    (snapshotWord 7 6 123, 14637417984000000),
    (snapshotWord 7 6 124, -6220902643200000),
    (snapshotWord 7 6 125, -5854967193600000),
    (snapshotWord 7 6 126, 975827865600000)
  ]

/-- The complete integer degree-6 coefficient after half-stage 3. -/
def stage3Degree6 : ParamTable :=
  stage3Degree6Parameter7 ++ stage3Degree6Parameter6

/-- The stage-3 degree-6 table is the actual integer recurrence coefficient. -/
theorem stage3Degree6_eq :
    defectCoeffTable (prefixTables 3) 6 = stage3Degree6 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage2Degree0_eq, stage2Degree1_eq, stage2Degree2_eq,
    stage2Degree3_eq, stage2Degree4_eq, stage2Degree5_eq,
    stage2Degree6_eq]
  decide +kernel

end FQFP.SuzukiSepticCertificate
