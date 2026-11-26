/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Word.SuzukiDefectSepticStage3

/-!
# Certified Suzuki half-defect coefficients after stage 4

Each finite coefficient is computed from the preceding stage's certified
coefficients. Stored integer tables avoid recomputing earlier stages during
kernel reduction of the next stage.

## Main results

* `stage4Degree6_eq`: the exact degree-six coefficient after stage 4.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

/-- The complete integer degree-0 coefficient after half-stage 4. -/
def stage4Degree0 : ParamTable :=
  [
    (snapshotWord 1 1 0, 3),
    (snapshotWord 1 1 1, 4),
    (snapshotWord 1 0 0, -1),
    (snapshotWord 1 0 1, -1)
  ]

/-- The stage-4 degree-0 table is the actual integer recurrence coefficient. -/
theorem stage4Degree0_eq :
    defectCoeffTable (prefixTables 4) 0 = stage4Degree0 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage3Degree0_eq]
  decide +kernel

/-- The complete integer degree-1 coefficient after half-stage 4. -/
def stage4Degree1 : ParamTable :=
  [
    (snapshotWord 2 2 1, 1680),
    (snapshotWord 2 2 2, -1680),
    (snapshotWord 2 1 1, -420),
    (snapshotWord 2 1 2, 420)
  ]

/-- The stage-4 degree-1 table is the actual integer recurrence coefficient. -/
theorem stage4Degree1_eq :
    defectCoeffTable (prefixTables 4) 1 = stage4Degree1 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage3Degree0_eq, stage3Degree1_eq]
  decide +kernel

/-- The complete integer degree-2 coefficient after half-stage 4. -/
def stage4Degree2 : ParamTable :=
  [
    (snapshotWord 3 3 3, 705600),
    (snapshotWord 3 3 5, -1411200),
    (snapshotWord 3 3 6, 705600),
    (snapshotWord 3 2 1, -88200),
    (snapshotWord 3 2 2, 176400),
    (snapshotWord 3 2 4, -88200)
  ]

/-- The stage-4 degree-2 table is the actual integer recurrence coefficient. -/
theorem stage4Degree2_eq :
    defectCoeffTable (prefixTables 4) 2 = stage4Degree2 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage3Degree0_eq, stage3Degree1_eq, stage3Degree2_eq]
  decide +kernel

/-- The complete integer degree-3 coefficient after half-stage 4. -/
def stage4Degree3 : ParamTable :=
  [
    (snapshotWord 4 4 1, 98784000),
    (snapshotWord 4 4 2, -296352000),
    (snapshotWord 4 4 3, -296352000),
    (snapshotWord 4 4 4, 296352000),
    (snapshotWord 4 4 5, 592704000),
    (snapshotWord 4 4 7, 395136000),
    (snapshotWord 4 4 8, -98784000),
    (snapshotWord 4 4 10, -592704000),
    (snapshotWord 4 4 11, -1185408000),
    (snapshotWord 4 4 12, 296352000),
    (snapshotWord 4 4 13, 1185408000),
    (snapshotWord 4 4 14, -395136000),
    (snapshotWord 4 3 1, 37044000),
    (snapshotWord 4 3 2, -111132000),
    (snapshotWord 4 3 3, -148176000),
    (snapshotWord 4 3 4, 111132000),
    (snapshotWord 4 3 5, 296352000),
    (snapshotWord 4 3 7, 98784000),
    (snapshotWord 4 3 8, -37044000),
    (snapshotWord 4 3 10, -296352000),
    (snapshotWord 4 3 11, -296352000),
    (snapshotWord 4 3 12, 148176000),
    (snapshotWord 4 3 13, 296352000),
    (snapshotWord 4 3 14, -98784000)
  ]

/-- The stage-4 degree-3 table is the actual integer recurrence coefficient. -/
theorem stage4Degree3_eq :
    defectCoeffTable (prefixTables 4) 3 = stage4Degree3 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage3Degree0_eq, stage3Degree1_eq, stage3Degree2_eq,
    stage3Degree3_eq]
  decide +kernel

/-- The complete integer degree-4 coefficient after half-stage 4. -/
def stage4Degree4 : ParamTable :=
  [
    (snapshotWord 5 5 1, -41489280000),
    (snapshotWord 5 5 2, 165957120000),
    (snapshotWord 5 5 3, 207446400000),
    (snapshotWord 5 5 4, -248935680000),
    (snapshotWord 5 5 5, -497871360000),
    (snapshotWord 5 5 6, -124467840000),
    (snapshotWord 5 5 7, -331914240000),
    (snapshotWord 5 5 8, 165957120000),
    (snapshotWord 5 5 9, 248935680000),
    (snapshotWord 5 5 10, 497871360000),
    (snapshotWord 5 5 11, 746807040000),
    (snapshotWord 5 5 12, -124467840000),
    (snapshotWord 5 5 13, -248935680000),
    (snapshotWord 5 5 14, 165957120000),
    (snapshotWord 5 5 15, 207446400000),
    (snapshotWord 5 5 16, -41489280000),
    (snapshotWord 5 5 17, -165957120000),
    (snapshotWord 5 5 18, 248935680000),
    (snapshotWord 5 5 19, 248935680000),
    (snapshotWord 5 5 20, -497871360000),
    (snapshotWord 5 5 21, -995742720000),
    (snapshotWord 5 5 22, -248935680000),
    (snapshotWord 5 5 23, -829785600000),
    (snapshotWord 5 5 24, 207446400000),
    (snapshotWord 5 5 25, 248935680000),
    (snapshotWord 5 5 26, 746807040000),
    (snapshotWord 5 5 27, 1244678400000),
    (snapshotWord 5 5 28, -331914240000),
    (snapshotWord 5 5 29, -829785600000),
    (snapshotWord 5 5 30, 207446400000),
    (snapshotWord 5 4 1, -22041180000),
    (snapshotWord 5 4 2, 88164720000),
    (snapshotWord 5 4 3, 103723200000),
    (snapshotWord 5 4 4, -132247080000),
    (snapshotWord 5 4 5, -248935680000),
    (snapshotWord 5 4 6, -62233920000),
    (snapshotWord 5 4 7, -165957120000),
    (snapshotWord 5 4 8, 88164720000),
    (snapshotWord 5 4 9, 124467840000),
    (snapshotWord 5 4 10, 248935680000),
    (snapshotWord 5 4 11, 373403520000),
    (snapshotWord 5 4 12, -62233920000),
    (snapshotWord 5 4 13, -124467840000),
    (snapshotWord 5 4 14, 82978560000),
    (snapshotWord 5 4 15, 82978560000),
    (snapshotWord 5 4 16, -22041180000),
    (snapshotWord 5 4 17, -82978560000),
    (snapshotWord 5 4 18, 124467840000),
    (snapshotWord 5 4 19, 124467840000),
    (snapshotWord 5 4 20, -248935680000),
    (snapshotWord 5 4 21, -497871360000),
    (snapshotWord 5 4 22, -124467840000),
    (snapshotWord 5 4 23, -331914240000),
    (snapshotWord 5 4 24, 103723200000),
    (snapshotWord 5 4 25, 124467840000),
    (snapshotWord 5 4 26, 373403520000),
    (snapshotWord 5 4 27, 497871360000),
    (snapshotWord 5 4 28, -165957120000),
    (snapshotWord 5 4 29, -331914240000),
    (snapshotWord 5 4 30, 82978560000)
  ]

/-- The stage-4 degree-4 table is the actual integer recurrence coefficient. -/
theorem stage4Degree4_eq :
    defectCoeffTable (prefixTables 4) 4 = stage4Degree4 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage3Degree0_eq, stage3Degree1_eq, stage3Degree2_eq,
    stage3Degree3_eq, stage3Degree4_eq]
  decide +kernel

/-- The complete integer degree-5 coefficient after half-stage 4. -/
def stage4Degree5 : ParamTable :=
  [
    (snapshotWord 6 6 1, 10455298560000),
    (snapshotWord 6 6 2, -52276492800000),
    (snapshotWord 6 6 3, -69701990400000),
    (snapshotWord 6 6 4, 104552985600000),
    (snapshotWord 6 6 5, 209105971200000),
    (snapshotWord 6 6 6, 69701990400000),
    (snapshotWord 6 6 7, 174254976000000),
    (snapshotWord 6 6 8, -104552985600000),
    (snapshotWord 6 6 9, -209105971200000),
    (snapshotWord 6 6 10, -209105971200000),
    (snapshotWord 6 6 11, -418211942400000),
    (snapshotWord 6 6 14, -104552985600000),
    (snapshotWord 6 6 15, -191680473600000),
    (snapshotWord 6 6 16, 52276492800000),
    (snapshotWord 6 6 17, 139403980800000),
    (snapshotWord 6 6 19, 104552985600000),
    (snapshotWord 6 6 20, 209105971200000),
    (snapshotWord 6 6 21, 418211942400000),
    (snapshotWord 6 6 22, 209105971200000),
    (snapshotWord 6 6 23, 487913932800000),
    (snapshotWord 6 6 24, -69701990400000),
    (snapshotWord 6 6 25, -104552985600000),
    (snapshotWord 6 6 26, -209105971200000),
    (snapshotWord 6 6 27, -313658956800000),
    (snapshotWord 6 6 28, 104552985600000),
    (snapshotWord 6 6 29, 209105971200000),
    (snapshotWord 6 6 31, 83642388480000),
    (snapshotWord 6 6 32, -10455298560000),
    (snapshotWord 6 6 34, -139403980800000),
    (snapshotWord 6 6 35, -209105971200000),
    (snapshotWord 6 6 36, 209105971200000),
    (snapshotWord 6 6 37, 418211942400000),
    (snapshotWord 6 6 38, 104552985600000),
    (snapshotWord 6 6 39, 278807961600000),
    (snapshotWord 6 6 40, -209105971200000),
    (snapshotWord 6 6 41, -418211942400000),
    (snapshotWord 6 6 42, -418211942400000),
    (snapshotWord 6 6 43, -836423884800000),
    (snapshotWord 6 6 46, -209105971200000),
    (snapshotWord 6 6 47, -418211942400000),
    (snapshotWord 6 6 48, 69701990400000),
    (snapshotWord 6 6 49, 209105971200000),
    (snapshotWord 6 6 50, -104552985600000),
    (snapshotWord 6 6 52, 418211942400000),
    (snapshotWord 6 6 53, 836423884800000),
    (snapshotWord 6 6 54, 313658956800000),
    (snapshotWord 6 6 55, 836423884800000),
    (snapshotWord 6 6 56, -174254976000000),
    (snapshotWord 6 6 57, -278807961600000),
    (snapshotWord 6 6 58, -487913932800000),
    (snapshotWord 6 6 59, -836423884800000),
    (snapshotWord 6 6 60, 191680473600000),
    (snapshotWord 6 6 61, 418211942400000),
    (snapshotWord 6 6 62, -83642388480000),
    (snapshotWord 6 5 1, 9039476880000),
    (snapshotWord 6 5 2, -45197384400000),
    (snapshotWord 6 5 3, -54454680000000),
    (snapshotWord 6 5 4, 90394768800000),
    (snapshotWord 6 5 5, 156829478400000),
    (snapshotWord 6 5 6, 60989241600000),
    (snapshotWord 6 5 7, 121978483200000),
    (snapshotWord 6 5 8, -90394768800000),
    (snapshotWord 6 5 9, -143760355200000),
    (snapshotWord 6 5 10, -182967724800000),
    (snapshotWord 6 5 11, -287520710400000),
    (snapshotWord 6 5 14, -78414739200000),
    (snapshotWord 6 5 15, -121978483200000),
    (snapshotWord 6 5 16, 45197384400000),
    (snapshotWord 6 5 17, 95840236800000),
    (snapshotWord 6 5 19, 52276492800000),
    (snapshotWord 6 5 20, 182967724800000),
    (snapshotWord 6 5 21, 313658956800000),
    (snapshotWord 6 5 22, 156829478400000),
    (snapshotWord 6 5 23, 313658956800000),
    (snapshotWord 6 5 24, -60989241600000),
    (snapshotWord 6 5 25, -78414739200000),
    (snapshotWord 6 5 26, -156829478400000),
    (snapshotWord 6 5 27, -209105971200000),
    (snapshotWord 6 5 28, 78414739200000),
    (snapshotWord 6 5 29, 139403980800000),
    (snapshotWord 6 5 31, 45306293760000),
    (snapshotWord 6 5 32, -9039476880000),
    (snapshotWord 6 5 34, -95840236800000),
    (snapshotWord 6 5 35, -130691232000000),
    (snapshotWord 6 5 36, 143760355200000),
    (snapshotWord 6 5 37, 261382464000000),
    (snapshotWord 6 5 38, 78414739200000),
    (snapshotWord 6 5 39, 174254976000000),
    (snapshotWord 6 5 40, -156829478400000),
    (snapshotWord 6 5 41, -261382464000000),
    (snapshotWord 6 5 42, -313658956800000),
    (snapshotWord 6 5 43, -522764928000000),
    (snapshotWord 6 5 46, -139403980800000),
    (snapshotWord 6 5 47, -226531468800000),
    (snapshotWord 6 5 48, 54454680000000),
    (snapshotWord 6 5 49, 130691232000000),
    (snapshotWord 6 5 50, -52276492800000),
    (snapshotWord 6 5 52, 287520710400000),
    (snapshotWord 6 5 53, 522764928000000),
    (snapshotWord 6 5 54, 209105971200000),
    (snapshotWord 6 5 55, 453062937600000),
    (snapshotWord 6 5 56, -121978483200000),
    (snapshotWord 6 5 57, -174254976000000),
    (snapshotWord 6 5 58, -313658956800000),
    (snapshotWord 6 5 59, -453062937600000),
    (snapshotWord 6 5 60, 121978483200000),
    (snapshotWord 6 5 61, 226531468800000),
    (snapshotWord 6 5 62, -45306293760000)
  ]

/-- The stage-4 degree-5 table is the actual integer recurrence coefficient. -/
theorem stage4Degree5_eq :
    defectCoeffTable (prefixTables 4) 5 = stage4Degree5 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage3Degree0_eq, stage3Degree1_eq, stage3Degree2_eq,
    stage3Degree3_eq, stage3Degree4_eq, stage3Degree5_eq]
  decide +kernel

/-- The parameter-degree-7 slice of half-stage 4, degree 6. -/
def stage4Degree6Parameter7 : ParamTable :=
  [
    (snapshotWord 7 7 1, -1951655731200000),
    (snapshotWord 7 7 2, 11709934387200000),
    (snapshotWord 7 7 3, 16101159782400000),
    (snapshotWord 7 7 4, -29274835968000000),
    (snapshotWord 7 7 5, -58549671936000000),
    (snapshotWord 7 7 6, -21956126976000000),
    (snapshotWord 7 7 7, -53670532608000000),
    (snapshotWord 7 7 8, 39033114624000000),
    (snapshotWord 7 7 9, 87824507904000000),
    (snapshotWord 7 7 10, 58549671936000000),
    (snapshotWord 7 7 11, 146374179840000000),
    (snapshotWord 7 7 12, 14637417984000000),
    (snapshotWord 7 7 13, 29274835968000000),
    (snapshotWord 7 7 14, 39033114624000000),
    (snapshotWord 7 7 15, 90264077568000000),
    (snapshotWord 7 7 16, -29274835968000000),
    (snapshotWord 7 7 17, -87824507904000000),
    (snapshotWord 7 7 19, -87824507904000000),
    (snapshotWord 7 7 20, -87824507904000000),
    (snapshotWord 7 7 21, -175649015808000000),
    (snapshotWord 7 7 22, -87824507904000000),
    (snapshotWord 7 7 23, -234198687744000000),
    (snapshotWord 7 7 24, 14637417984000000),
    (snapshotWord 7 7 26, 87824507904000000),
    (snapshotWord 7 7 27, 87824507904000000),
    (snapshotWord 7 7 28, -58549671936000000),
    (snapshotWord 7 7 29, -117099343872000000),
    (snapshotWord 7 7 30, -7318708992000000),
    (snapshotWord 7 7 31, -76114573516800000),
    (snapshotWord 7 7 32, 11709934387200000),
    (snapshotWord 7 7 33, 43912253952000000),
    (snapshotWord 7 7 35, 58549671936000000),
    (snapshotWord 7 7 39, 29274835968000000),
    (snapshotWord 7 7 40, 58549671936000000),
    (snapshotWord 7 7 41, 175649015808000000),
    (snapshotWord 7 7 43, 175649015808000000),
    (snapshotWord 7 7 44, 87824507904000000),
    (snapshotWord 7 7 45, 175649015808000000),
    (snapshotWord 7 7 46, 58549671936000000),
    (snapshotWord 7 7 47, 219561269760000000),
    (snapshotWord 7 7 48, -21956126976000000),
    (snapshotWord 7 7 49, -58549671936000000),
    (snapshotWord 7 7 51, -43912253952000000),
    (snapshotWord 7 7 52, -87824507904000000),
    (snapshotWord 7 7 53, -175649015808000000),
    (snapshotWord 7 7 54, -87824507904000000),
    (snapshotWord 7 7 55, -204923851776000000),
    (snapshotWord 7 7 56, 39033114624000000),
    (snapshotWord 7 7 57, 87824507904000000),
    (snapshotWord 7 7 58, 58549671936000000),
    (snapshotWord 7 7 59, 146374179840000000),
    (snapshotWord 7 7 60, -7318708992000000),
    (snapshotWord 7 7 61, -14637417984000000),
    (snapshotWord 7 7 62, 5854967193600000),
    (snapshotWord 7 7 63, 26347352371200000),
    (snapshotWord 7 7 64, -1951655731200000),
    (snapshotWord 7 7 65, -17564901580800000),
    (snapshotWord 7 7 66, 43912253952000000),
    (snapshotWord 7 7 67, 43912253952000000),
    (snapshotWord 7 7 68, -87824507904000000),
    (snapshotWord 7 7 69, -175649015808000000),
    (snapshotWord 7 7 70, -58549671936000000),
    (snapshotWord 7 7 71, -156132458496000000),
    (snapshotWord 7 7 72, 87824507904000000),
    (snapshotWord 7 7 73, 175649015808000000),
    (snapshotWord 7 7 74, 175649015808000000),
    (snapshotWord 7 7 75, 351298031616000000),
    (snapshotWord 7 7 78, 87824507904000000),
    (snapshotWord 7 7 79, 161011597824000000),
    (snapshotWord 7 7 80, -58549671936000000),
    (snapshotWord 7 7 81, -175649015808000000),
    (snapshotWord 7 7 83, -175649015808000000),
    (snapshotWord 7 7 84, -175649015808000000),
    (snapshotWord 7 7 85, -351298031616000000),
    (snapshotWord 7 7 86, -175649015808000000),
    (snapshotWord 7 7 87, -468397375488000000),
    (snapshotWord 7 7 88, 29274835968000000),
    (snapshotWord 7 7 90, 175649015808000000),
    (snapshotWord 7 7 91, 175649015808000000),
    (snapshotWord 7 7 92, -117099343872000000),
    (snapshotWord 7 7 93, -234198687744000000),
    (snapshotWord 7 7 94, -14637417984000000),
    (snapshotWord 7 7 95, -158084114227200000),
    (snapshotWord 7 7 96, 16101159782400000),
    (snapshotWord 7 7 97, 43912253952000000),
    (snapshotWord 7 7 98, 58549671936000000),
    (snapshotWord 7 7 99, 146374179840000000),
    (snapshotWord 7 7 100, -87824507904000000),
    (snapshotWord 7 7 101, -175649015808000000),
    (snapshotWord 7 7 102, -43912253952000000),
    (snapshotWord 7 7 103, -87824507904000000),
    (snapshotWord 7 7 104, 146374179840000000),
    (snapshotWord 7 7 105, 351298031616000000),
    (snapshotWord 7 7 106, 175649015808000000),
    (snapshotWord 7 7 107, 526947047424000000),
    (snapshotWord 7 7 108, 87824507904000000),
    (snapshotWord 7 7 109, 175649015808000000),
    (snapshotWord 7 7 110, 146374179840000000),
    (snapshotWord 7 7 111, 395210285568000000),
    (snapshotWord 7 7 112, -53670532608000000),
    (snapshotWord 7 7 113, -156132458496000000),
    (snapshotWord 7 7 114, 29274835968000000),
    (snapshotWord 7 7 115, -87824507904000000),
    (snapshotWord 7 7 116, -234198687744000000),
    (snapshotWord 7 7 117, -468397375488000000),
    (snapshotWord 7 7 118, -204923851776000000),
    (snapshotWord 7 7 119, -526947047424000000),
    (snapshotWord 7 7 120, 90264077568000000),
    (snapshotWord 7 7 121, 161011597824000000),
    (snapshotWord 7 7 122, 219561269760000000),
    (snapshotWord 7 7 123, 395210285568000000),
    (snapshotWord 7 7 124, -76114573516800000),
    (snapshotWord 7 7 125, -158084114227200000),
    (snapshotWord 7 7 126, 26347352371200000)
  ]

/-- The parameter-degree-6 slice of half-stage 4, degree 6. -/
def stage4Degree6Parameter6 : ParamTable :=
  [
    (snapshotWord 7 6 1, -2630161044000000),
    (snapshotWord 7 6 2, 15780966264000000),
    (snapshotWord 7 6 3, 19577546553600000),
    (snapshotWord 7 6 4, -39452415660000000),
    (snapshotWord 7 6 5, -67698058176000000),
    (snapshotWord 7 6 6, -30189674592000000),
    (snapshotWord 7 6 7, -57939779520000000),
    (snapshotWord 7 6 8, 52603220880000000),
    (snapshotWord 7 6 9, 93313539648000000),
    (snapshotWord 7 6 10, 84165153408000000),
    (snapshotWord 7 6 11, 150033534336000000),
    (snapshotWord 7 6 12, 18296772480000000),
    (snapshotWord 7 6 13, 36593544960000000),
    (snapshotWord 7 6 14, 45132038784000000),
    (snapshotWord 7 6 15, 85384938240000000),
    (snapshotWord 7 6 16, -39452415660000000),
    (snapshotWord 7 6 17, -87824507904000000),
    (snapshotWord 7 6 18, -16467095232000000),
    (snapshotWord 7 6 19, -76846444416000000),
    (snapshotWord 7 6 20, -109780634880000000),
    (snapshotWord 7 6 21, -197605142784000000),
    (snapshotWord 7 6 22, -98802571392000000),
    (snapshotWord 7 6 23, -212242560768000000),
    (snapshotWord 7 6 24, 18296772480000000),
    (snapshotWord 7 6 25, 10978063488000000),
    (snapshotWord 7 6 26, 65868380928000000),
    (snapshotWord 7 6 27, 65868380928000000),
    (snapshotWord 7 6 28, -51230962944000000),
    (snapshotWord 7 6 29, -95143216896000000),
    (snapshotWord 7 6 30, -14637417984000000),
    (snapshotWord 7 6 31, -62940897331200000),
    (snapshotWord 7 6 32, 15780966264000000),
    (snapshotWord 7 6 33, 38423222208000000),
    (snapshotWord 7 6 34, 21956126976000000),
    (snapshotWord 7 6 35, 62209026432000000),
    (snapshotWord 7 6 36, -16467095232000000),
    (snapshotWord 7 6 37, -21956126976000000),
    (snapshotWord 7 6 38, -10978063488000000),
    (snapshotWord 7 6 40, 84165153408000000),
    (snapshotWord 7 6 41, 175649015808000000),
    (snapshotWord 7 6 42, 87824507904000000),
    (snapshotWord 7 6 43, 219561269760000000),
    (snapshotWord 7 6 44, 65868380928000000),
    (snapshotWord 7 6 45, 131736761856000000),
    (snapshotWord 7 6 46, 73187089920000000),
    (snapshotWord 7 6 47, 182967724800000000),
    (snapshotWord 7 6 48, -30189674592000000),
    (snapshotWord 7 6 49, -62209026432000000),
    (snapshotWord 7 6 50, -10978063488000000),
    (snapshotWord 7 6 51, -43912253952000000),
    (snapshotWord 7 6 52, -98802571392000000),
    (snapshotWord 7 6 53, -175649015808000000),
    (snapshotWord 7 6 54, -87824507904000000),
    (snapshotWord 7 6 55, -175649015808000000),
    (snapshotWord 7 6 56, 45132038784000000),
    (snapshotWord 7 6 57, 80505798912000000),
    (snapshotWord 7 6 58, 73187089920000000),
    (snapshotWord 7 6 59, 131736761856000000),
    (snapshotWord 7 6 60, -14637417984000000),
    (snapshotWord 7 6 61, -21956126976000000),
    (snapshotWord 7 6 62, 8782450790400000),
    (snapshotWord 7 6 63, 18540729446400000),
    (snapshotWord 7 6 64, -2630161044000000),
    (snapshotWord 7 6 65, -15369288883200000),
    (snapshotWord 7 6 66, 38423222208000000),
    (snapshotWord 7 6 67, 38423222208000000),
    (snapshotWord 7 6 68, -87824507904000000),
    (snapshotWord 7 6 69, -153692888832000000),
    (snapshotWord 7 6 70, -62209026432000000),
    (snapshotWord 7 6 71, -129297192192000000),
    (snapshotWord 7 6 72, 93313539648000000),
    (snapshotWord 7 6 73, 153692888832000000),
    (snapshotWord 7 6 74, 175649015808000000),
    (snapshotWord 7 6 75, 285429650688000000),
    (snapshotWord 7 6 76, 10978063488000000),
    (snapshotWord 7 6 77, 21956126976000000),
    (snapshotWord 7 6 78, 80505798912000000),
    (snapshotWord 7 6 79, 131736761856000000),
    (snapshotWord 7 6 80, -67698058176000000),
    (snapshotWord 7 6 81, -153692888832000000),
    (snapshotWord 7 6 82, -21956126976000000),
    (snapshotWord 7 6 83, -131736761856000000),
    (snapshotWord 7 6 84, -197605142784000000),
    (snapshotWord 7 6 85, -351298031616000000),
    (snapshotWord 7 6 86, -175649015808000000),
    (snapshotWord 7 6 87, -380572867584000000),
    (snapshotWord 7 6 88, 36593544960000000),
    (snapshotWord 7 6 89, 21956126976000000),
    (snapshotWord 7 6 90, 131736761856000000),
    (snapshotWord 7 6 91, 131736761856000000),
    (snapshotWord 7 6 92, -95143216896000000),
    (snapshotWord 7 6 93, -175649015808000000),
    (snapshotWord 7 6 94, -21956126976000000),
    (snapshotWord 7 6 95, -111244376678400000),
    (snapshotWord 7 6 96, 19577546553600000),
    (snapshotWord 7 6 97, 38423222208000000),
    (snapshotWord 7 6 98, 62209026432000000),
    (snapshotWord 7 6 99, 117099343872000000),
    (snapshotWord 7 6 100, -76846444416000000),
    (snapshotWord 7 6 101, -131736761856000000),
    (snapshotWord 7 6 102, -43912253952000000),
    (snapshotWord 7 6 103, -73187089920000000),
    (snapshotWord 7 6 104, 150033534336000000),
    (snapshotWord 7 6 105, 285429650688000000),
    (snapshotWord 7 6 106, 219561269760000000),
    (snapshotWord 7 6 107, 439122539520000000),
    (snapshotWord 7 6 108, 65868380928000000),
    (snapshotWord 7 6 109, 131736761856000000),
    (snapshotWord 7 6 110, 131736761856000000),
    (snapshotWord 7 6 111, 278110941696000000),
    (snapshotWord 7 6 112, -57939779520000000),
    (snapshotWord 7 6 113, -129297192192000000),
    (snapshotWord 7 6 115, -73187089920000000),
    (snapshotWord 7 6 116, -212242560768000000),
    (snapshotWord 7 6 117, -380572867584000000),
    (snapshotWord 7 6 118, -175649015808000000),
    (snapshotWord 7 6 119, -370814588928000000),
    (snapshotWord 7 6 120, 85384938240000000),
    (snapshotWord 7 6 121, 131736761856000000),
    (snapshotWord 7 6 122, 182967724800000000),
    (snapshotWord 7 6 123, 278110941696000000),
    (snapshotWord 7 6 124, -62940897331200000),
    (snapshotWord 7 6 125, -111244376678400000),
    (snapshotWord 7 6 126, 18540729446400000)
  ]

/-- The complete integer degree-6 coefficient after half-stage 4. -/
def stage4Degree6 : ParamTable :=
  stage4Degree6Parameter7 ++ stage4Degree6Parameter6

/-- The stage-4 degree-6 table is the actual integer recurrence coefficient. -/
theorem stage4Degree6_eq :
    defectCoeffTable (prefixTables 4) 6 = stage4Degree6 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage3Degree0_eq, stage3Degree1_eq, stage3Degree2_eq,
    stage3Degree3_eq, stage3Degree4_eq, stage3Degree5_eq,
    stage3Degree6_eq]
  decide +kernel

end FQFP.SuzukiSepticCertificate
