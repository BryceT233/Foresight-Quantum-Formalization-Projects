/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Word.SuzukiDefectSepticStage4

/-!
# Certified Suzuki half-defect coefficients after stage 5

Each finite coefficient is computed from the preceding stage's certified
coefficients. Stored integer tables avoid recomputing earlier stages during
kernel reduction of the next stage.

## Main results

* `stage5Degree6_eq`: the exact degree-six coefficient after stage 5.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

/-- The complete integer degree-0 coefficient after half-stage 5. -/
def stage5Degree0 : ParamTable :=
  [
    (snapshotWord 1 1 1, 4),
    (snapshotWord 1 0 1, -1)
  ]

/-- The stage-5 degree-0 table is the actual integer recurrence coefficient. -/
theorem stage5Degree0_eq :
    defectCoeffTable (prefixTables 5) 0 = stage5Degree0 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage4Degree0_eq]
  decide +kernel

/-- The complete integer degree-1 coefficient after half-stage 5. -/
def stage5Degree1 : ParamTable :=
  [
    (snapshotWord 2 2 1, 6720),
    (snapshotWord 2 2 2, -6720),
    (snapshotWord 2 1 1, -3360),
    (snapshotWord 2 1 2, 3360),
    (snapshotWord 2 0 1, 420),
    (snapshotWord 2 0 2, -420)
  ]

/-- The stage-5 degree-1 table is the actual integer recurrence coefficient. -/
theorem stage5Degree1_eq :
    defectCoeffTable (prefixTables 5) 1 = stage5Degree1 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage4Degree0_eq, stage4Degree1_eq]
  decide +kernel

/-- The complete integer degree-2 coefficient after half-stage 5. -/
def stage5Degree2 : ParamTable :=
  [
    (snapshotWord 3 3 1, 5292000),
    (snapshotWord 3 3 2, -10584000),
    (snapshotWord 3 3 3, 705600),
    (snapshotWord 3 3 4, 5292000),
    (snapshotWord 3 3 5, -1411200),
    (snapshotWord 3 3 6, 705600),
    (snapshotWord 3 2 1, -4233600),
    (snapshotWord 3 2 2, 8467200),
    (snapshotWord 3 2 4, -4233600),
    (snapshotWord 3 1 1, 1058400),
    (snapshotWord 3 1 2, -2116800),
    (snapshotWord 3 1 4, 1058400),
    (snapshotWord 3 0 1, -88200),
    (snapshotWord 3 0 2, 176400),
    (snapshotWord 3 0 4, -88200)
  ]

/-- The stage-5 degree-2 table is the actual integer recurrence coefficient. -/
theorem stage5Degree2_eq :
    defectCoeffTable (prefixTables 5) 2 = stage5Degree2 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage4Degree0_eq, stage4Degree1_eq, stage4Degree2_eq]
  decide +kernel

/-- The complete integer degree-3 coefficient after half-stage 5. -/
def stage5Degree3 : ParamTable :=
  [
    (snapshotWord 4 4 1, 2765952000),
    (snapshotWord 4 4 2, -8297856000),
    (snapshotWord 4 4 3, 592704000),
    (snapshotWord 4 4 4, 8297856000),
    (snapshotWord 4 4 5, -1185408000),
    (snapshotWord 4 4 7, 395136000),
    (snapshotWord 4 4 8, -2765952000),
    (snapshotWord 4 4 10, 1185408000),
    (snapshotWord 4 4 11, -1185408000),
    (snapshotWord 4 4 12, -592704000),
    (snapshotWord 4 4 13, 1185408000),
    (snapshotWord 4 4 14, -395136000),
    (snapshotWord 4 3 1, -2963520000),
    (snapshotWord 4 3 2, 8890560000),
    (snapshotWord 4 3 3, -444528000),
    (snapshotWord 4 3 4, -8890560000),
    (snapshotWord 4 3 5, 889056000),
    (snapshotWord 4 3 7, 98784000),
    (snapshotWord 4 3 8, 2963520000),
    (snapshotWord 4 3 10, -889056000),
    (snapshotWord 4 3 11, -296352000),
    (snapshotWord 4 3 12, 444528000),
    (snapshotWord 4 3 13, 296352000),
    (snapshotWord 4 3 14, -98784000),
    (snapshotWord 4 2 1, 1185408000),
    (snapshotWord 4 2 2, -3556224000),
    (snapshotWord 4 2 4, 3556224000),
    (snapshotWord 4 2 8, -1185408000),
    (snapshotWord 4 1 1, -197568000),
    (snapshotWord 4 1 2, 592704000),
    (snapshotWord 4 1 4, -592704000),
    (snapshotWord 4 1 8, 197568000),
    (snapshotWord 4 0 1, 12348000),
    (snapshotWord 4 0 2, -37044000),
    (snapshotWord 4 0 4, 37044000),
    (snapshotWord 4 0 8, -12348000)
  ]

/-- The stage-5 degree-3 table is the actual integer recurrence coefficient. -/
theorem stage5Degree3_eq :
    defectCoeffTable (prefixTables 5) 3 = stage5Degree3 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage4Degree0_eq, stage4Degree1_eq, stage4Degree2_eq,
    stage4Degree3_eq]
  decide +kernel

/-- The complete integer degree-4 coefficient after half-stage 5. -/
def stage5Degree4 : ParamTable :=
  [
    (snapshotWord 5 5 1, 1063162800000),
    (snapshotWord 5 5 2, -4252651200000),
    (snapshotWord 5 5 3, 394148160000),
    (snapshotWord 5 5 4, 6378976800000),
    (snapshotWord 5 5 5, -871274880000),
    (snapshotWord 5 5 6, -311169600000),
    (snapshotWord 5 5 7, 165957120000),
    (snapshotWord 5 5 8, -4252651200000),
    (snapshotWord 5 5 9, 248935680000),
    (snapshotWord 5 5 10, 1244678400000),
    (snapshotWord 5 5 11, -746807040000),
    (snapshotWord 5 5 12, -311169600000),
    (snapshotWord 5 5 13, 1244678400000),
    (snapshotWord 5 5 14, -829785600000),
    (snapshotWord 5 5 15, 207446400000),
    (snapshotWord 5 5 16, 1063162800000),
    (snapshotWord 5 5 17, -165957120000),
    (snapshotWord 5 5 18, 248935680000),
    (snapshotWord 5 5 19, 248935680000),
    (snapshotWord 5 5 20, -871274880000),
    (snapshotWord 5 5 21, -995742720000),
    (snapshotWord 5 5 22, 1244678400000),
    (snapshotWord 5 5 23, -829785600000),
    (snapshotWord 5 5 24, 394148160000),
    (snapshotWord 5 5 25, 248935680000),
    (snapshotWord 5 5 26, -746807040000),
    (snapshotWord 5 5 27, 1244678400000),
    (snapshotWord 5 5 28, 165957120000),
    (snapshotWord 5 5 29, -829785600000),
    (snapshotWord 5 5 30, 207446400000),
    (snapshotWord 5 4 1, -1452124800000),
    (snapshotWord 5 4 2, 5808499200000),
    (snapshotWord 5 4 3, -331914240000),
    (snapshotWord 5 4 4, -8712748800000),
    (snapshotWord 5 4 5, 622339200000),
    (snapshotWord 5 4 6, 373403520000),
    (snapshotWord 5 4 7, -207446400000),
    (snapshotWord 5 4 8, 5808499200000),
    (snapshotWord 5 4 9, 124467840000),
    (snapshotWord 5 4 10, -1493614080000),
    (snapshotWord 5 4 11, 497871360000),
    (snapshotWord 5 4 12, 373403520000),
    (snapshotWord 5 4 13, -248935680000),
    (snapshotWord 5 4 14, 165957120000),
    (snapshotWord 5 4 15, 82978560000),
    (snapshotWord 5 4 16, -1452124800000),
    (snapshotWord 5 4 17, -82978560000),
    (snapshotWord 5 4 18, 124467840000),
    (snapshotWord 5 4 19, 124467840000),
    (snapshotWord 5 4 20, 622339200000),
    (snapshotWord 5 4 21, -497871360000),
    (snapshotWord 5 4 22, -248935680000),
    (snapshotWord 5 4 23, -331914240000),
    (snapshotWord 5 4 24, -331914240000),
    (snapshotWord 5 4 25, 124467840000),
    (snapshotWord 5 4 26, 497871360000),
    (snapshotWord 5 4 27, 497871360000),
    (snapshotWord 5 4 28, -207446400000),
    (snapshotWord 5 4 29, -331914240000),
    (snapshotWord 5 4 30, 82978560000),
    (snapshotWord 5 3 1, 777924000000),
    (snapshotWord 5 3 2, -3111696000000),
    (snapshotWord 5 3 3, 124467840000),
    (snapshotWord 5 3 4, 4667544000000),
    (snapshotWord 5 3 5, -248935680000),
    (snapshotWord 5 3 6, -124467840000),
    (snapshotWord 5 3 7, -41489280000),
    (snapshotWord 5 3 8, -3111696000000),
    (snapshotWord 5 3 10, 497871360000),
    (snapshotWord 5 3 11, 124467840000),
    (snapshotWord 5 3 12, -124467840000),
    (snapshotWord 5 3 13, -124467840000),
    (snapshotWord 5 3 14, 82978560000),
    (snapshotWord 5 3 16, 777924000000),
    (snapshotWord 5 3 20, -248935680000),
    (snapshotWord 5 3 22, -124467840000),
    (snapshotWord 5 3 24, 124467840000),
    (snapshotWord 5 3 26, 124467840000),
    (snapshotWord 5 3 28, -41489280000),
    (snapshotWord 5 2 1, -207446400000),
    (snapshotWord 5 2 2, 829785600000),
    (snapshotWord 5 2 4, -1244678400000),
    (snapshotWord 5 2 8, 829785600000),
    (snapshotWord 5 2 16, -207446400000),
    (snapshotWord 5 1 1, 25930800000),
    (snapshotWord 5 1 2, -103723200000),
    (snapshotWord 5 1 4, 155584800000),
    (snapshotWord 5 1 8, -103723200000),
    (snapshotWord 5 1 16, 25930800000),
    (snapshotWord 5 0 1, -1296540000),
    (snapshotWord 5 0 2, 5186160000),
    (snapshotWord 5 0 4, -7779240000),
    (snapshotWord 5 0 8, 5186160000),
    (snapshotWord 5 0 16, -1296540000)
  ]

/-- The stage-5 degree-4 table is the actual integer recurrence coefficient. -/
theorem stage5Degree4_eq :
    defectCoeffTable (prefixTables 5) 4 = stage5Degree4 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage4Degree0_eq, stage4Degree1_eq, stage4Degree2_eq,
    stage4Degree3_eq, stage4Degree4_eq]
  decide +kernel

/-- The parameter-degree-6 slice of half-stage 5, degree 5. -/
def stage5Degree5Parameter6 : ParamTable :=
  [
    (snapshotWord 6 6 1, 318886606080000),
    (snapshotWord 6 6 2, -1594433030400000),
    (snapshotWord 6 6 3, 191680473600000),
    (snapshotWord 6 6 4, 3188866060800000),
    (snapshotWord 6 6 5, -418211942400000),
    (snapshotWord 6 6 6, -348509952000000),
    (snapshotWord 6 6 7, 69701990400000),
    (snapshotWord 6 6 8, -3188866060800000),
    (snapshotWord 6 6 9, 104552985600000),
    (snapshotWord 6 6 10, 1045529856000000),
    (snapshotWord 6 6 11, -418211942400000),
    (snapshotWord 6 6 13, 627317913600000),
    (snapshotWord 6 6 14, -418211942400000),
    (snapshotWord 6 6 15, 69701990400000),
    (snapshotWord 6 6 16, 1594433030400000),
    (snapshotWord 6 6 17, -69701990400000),
    (snapshotWord 6 6 19, 418211942400000),
    (snapshotWord 6 6 20, -1045529856000000),
    (snapshotWord 6 6 21, -836423884800000),
    (snapshotWord 6 6 22, 836423884800000),
    (snapshotWord 6 6 23, -557615923200000),
    (snapshotWord 6 6 24, 348509952000000),
    (snapshotWord 6 6 25, 209105971200000),
    (snapshotWord 6 6 26, -836423884800000),
    (snapshotWord 6 6 27, 1254635827200000),
    (snapshotWord 6 6 28, 418211942400000),
    (snapshotWord 6 6 29, -836423884800000),
    (snapshotWord 6 6 31, 83642388480000),
    (snapshotWord 6 6 32, -318886606080000),
    (snapshotWord 6 6 34, 69701990400000),
    (snapshotWord 6 6 35, -209105971200000),
    (snapshotWord 6 6 36, -104552985600000),
    (snapshotWord 6 6 37, 418211942400000),
    (snapshotWord 6 6 38, -209105971200000),
    (snapshotWord 6 6 39, 278807961600000),
    (snapshotWord 6 6 40, 418211942400000),
    (snapshotWord 6 6 41, -418211942400000),
    (snapshotWord 6 6 42, 836423884800000),
    (snapshotWord 6 6 43, -836423884800000),
    (snapshotWord 6 6 44, -627317913600000),
    (snapshotWord 6 6 46, 836423884800000),
    (snapshotWord 6 6 47, -418211942400000),
    (snapshotWord 6 6 48, -191680473600000),
    (snapshotWord 6 6 49, 209105971200000),
    (snapshotWord 6 6 50, -418211942400000),
    (snapshotWord 6 6 52, 418211942400000),
    (snapshotWord 6 6 53, 836423884800000),
    (snapshotWord 6 6 54, -1254635827200000),
    (snapshotWord 6 6 55, 836423884800000),
    (snapshotWord 6 6 56, -69701990400000),
    (snapshotWord 6 6 57, -278807961600000),
    (snapshotWord 6 6 58, 557615923200000),
    (snapshotWord 6 6 59, -836423884800000),
    (snapshotWord 6 6 60, -69701990400000),
    (snapshotWord 6 6 61, 418211942400000),
    (snapshotWord 6 6 62, -83642388480000)
  ]

/-- The parameter-degree-5 slice of half-stage 5, degree 5. -/
def stage5Degree5Parameter5 : ParamTable :=
  [
    (snapshotWord 6 5 1, -535834051200000),
    (snapshotWord 6 5 2, 2679170256000000),
    (snapshotWord 6 5 3, -206927784000000),
    (snapshotWord 6 5 4, -5358340512000000),
    (snapshotWord 6 5 5, 444350188800000),
    (snapshotWord 6 5 6, 383360947200000),
    (snapshotWord 6 5 7, -78414739200000),
    (snapshotWord 6 5 8, 5358340512000000),
    (snapshotWord 6 5 9, -91483862400000),
    (snapshotWord 6 5 10, -1150082841600000),
    (snapshotWord 6 5 11, 261382464000000),
    (snapshotWord 6 5 13, -444350188800000),
    (snapshotWord 6 5 14, 418211942400000),
    (snapshotWord 6 5 15, -104552985600000),
    (snapshotWord 6 5 16, -2679170256000000),
    (snapshotWord 6 5 17, 60989241600000),
    (snapshotWord 6 5 19, 104552985600000),
    (snapshotWord 6 5 20, 1150082841600000),
    (snapshotWord 6 5 21, 104552985600000),
    (snapshotWord 6 5 22, -836423884800000),
    (snapshotWord 6 5 23, 243956966400000),
    (snapshotWord 6 5 24, -383360947200000),
    (snapshotWord 6 5 25, -26138246400000),
    (snapshotWord 6 5 26, 836423884800000),
    (snapshotWord 6 5 27, -104552985600000),
    (snapshotWord 6 5 28, -418211942400000),
    (snapshotWord 6 5 29, 69701990400000),
    (snapshotWord 6 5 31, 45306293760000),
    (snapshotWord 6 5 32, 535834051200000),
    (snapshotWord 6 5 34, -60989241600000),
    (snapshotWord 6 5 35, -130691232000000),
    (snapshotWord 6 5 36, 91483862400000),
    (snapshotWord 6 5 37, 261382464000000),
    (snapshotWord 6 5 38, 26138246400000),
    (snapshotWord 6 5 39, 174254976000000),
    (snapshotWord 6 5 40, -444350188800000),
    (snapshotWord 6 5 41, -261382464000000),
    (snapshotWord 6 5 42, -104552985600000),
    (snapshotWord 6 5 43, -522764928000000),
    (snapshotWord 6 5 44, 444350188800000),
    (snapshotWord 6 5 46, -69701990400000),
    (snapshotWord 6 5 47, -226531468800000),
    (snapshotWord 6 5 48, 206927784000000),
    (snapshotWord 6 5 49, 130691232000000),
    (snapshotWord 6 5 50, -104552985600000),
    (snapshotWord 6 5 52, -261382464000000),
    (snapshotWord 6 5 53, 522764928000000),
    (snapshotWord 6 5 54, 104552985600000),
    (snapshotWord 6 5 55, 453062937600000),
    (snapshotWord 6 5 56, 78414739200000),
    (snapshotWord 6 5 57, -174254976000000),
    (snapshotWord 6 5 58, -243956966400000),
    (snapshotWord 6 5 59, -453062937600000),
    (snapshotWord 6 5 60, 104552985600000),
    (snapshotWord 6 5 61, 226531468800000),
    (snapshotWord 6 5 62, -45306293760000)
  ]

/-- The parameter-degree-4 slice of half-stage 5, degree 5. -/
def stage5Degree5Parameter4 : ParamTable :=
  [
    (snapshotWord 6 4 1, 365935449600000),
    (snapshotWord 6 4 2, -1829677248000000),
    (snapshotWord 6 4 3, 87127488000000),
    (snapshotWord 6 4 4, 3659354496000000),
    (snapshotWord 6 4 5, -156829478400000),
    (snapshotWord 6 4 6, -191680473600000),
    (snapshotWord 6 4 7, 52276492800000),
    (snapshotWord 6 4 8, -3659354496000000),
    (snapshotWord 6 4 9, -52276492800000),
    (snapshotWord 6 4 10, 575041420800000),
    (snapshotWord 6 4 11, -104552985600000),
    (snapshotWord 6 4 14, -52276492800000),
    (snapshotWord 6 4 15, -34850995200000),
    (snapshotWord 6 4 16, 1829677248000000),
    (snapshotWord 6 4 17, 34850995200000),
    (snapshotWord 6 4 19, -52276492800000),
    (snapshotWord 6 4 20, -575041420800000),
    (snapshotWord 6 4 21, 209105971200000),
    (snapshotWord 6 4 22, 104552985600000),
    (snapshotWord 6 4 23, 139403980800000),
    (snapshotWord 6 4 24, 191680473600000),
    (snapshotWord 6 4 25, -52276492800000),
    (snapshotWord 6 4 26, -104552985600000),
    (snapshotWord 6 4 27, -209105971200000),
    (snapshotWord 6 4 28, 52276492800000),
    (snapshotWord 6 4 29, 139403980800000),
    (snapshotWord 6 4 32, -365935449600000),
    (snapshotWord 6 4 34, -34850995200000),
    (snapshotWord 6 4 36, 52276492800000),
    (snapshotWord 6 4 38, 52276492800000),
    (snapshotWord 6 4 40, 156829478400000),
    (snapshotWord 6 4 42, -209105971200000),
    (snapshotWord 6 4 46, -139403980800000),
    (snapshotWord 6 4 48, -87127488000000),
    (snapshotWord 6 4 50, 52276492800000),
    (snapshotWord 6 4 52, 104552985600000),
    (snapshotWord 6 4 54, 209105971200000),
    (snapshotWord 6 4 56, -52276492800000),
    (snapshotWord 6 4 58, -139403980800000),
    (snapshotWord 6 4 60, 34850995200000)
  ]

/-- The parameter-degree-3 slice of half-stage 5, degree 5. -/
def stage5Degree5Parameter3 : ParamTable :=
  [
    (snapshotWord 6 3 1, -130691232000000),
    (snapshotWord 6 3 2, 653456160000000),
    (snapshotWord 6 3 3, -21781872000000),
    (snapshotWord 6 3 4, -1306912320000000),
    (snapshotWord 6 3 5, 43563744000000),
    (snapshotWord 6 3 6, 43563744000000),
    (snapshotWord 6 3 7, 8712748800000),
    (snapshotWord 6 3 8, 1306912320000000),
    (snapshotWord 6 3 10, -130691232000000),
    (snapshotWord 6 3 11, -26138246400000),
    (snapshotWord 6 3 13, 26138246400000),
    (snapshotWord 6 3 14, -26138246400000),
    (snapshotWord 6 3 16, -653456160000000),
    (snapshotWord 6 3 20, 130691232000000),
    (snapshotWord 6 3 22, 52276492800000),
    (snapshotWord 6 3 24, -43563744000000),
    (snapshotWord 6 3 26, -52276492800000),
    (snapshotWord 6 3 28, 26138246400000),
    (snapshotWord 6 3 32, 130691232000000),
    (snapshotWord 6 3 40, -43563744000000),
    (snapshotWord 6 3 44, -26138246400000),
    (snapshotWord 6 3 48, 21781872000000),
    (snapshotWord 6 3 52, 26138246400000),
    (snapshotWord 6 3 56, -8712748800000)
  ]

/-- The parameter-degree-2 slice of half-stage 5, degree 5. -/
def stage5Degree5Parameter2 : ParamTable :=
  [
    (snapshotWord 6 2 1, 26138246400000),
    (snapshotWord 6 2 2, -130691232000000),
    (snapshotWord 6 2 4, 261382464000000),
    (snapshotWord 6 2 8, -261382464000000),
    (snapshotWord 6 2 16, 130691232000000),
    (snapshotWord 6 2 32, -26138246400000)
  ]

/-- The parameter-degree-1 slice of half-stage 5, degree 5. -/
def stage5Degree5Parameter1 : ParamTable :=
  [
    (snapshotWord 6 1 1, -2613824640000),
    (snapshotWord 6 1 2, 13069123200000),
    (snapshotWord 6 1 4, -26138246400000),
    (snapshotWord 6 1 8, 26138246400000),
    (snapshotWord 6 1 16, -13069123200000),
    (snapshotWord 6 1 32, 2613824640000)
  ]

/-- The parameter-degree-0 slice of half-stage 5, degree 5. -/
def stage5Degree5Parameter0 : ParamTable :=
  [
    (snapshotWord 6 0 1, 108909360000),
    (snapshotWord 6 0 2, -544546800000),
    (snapshotWord 6 0 4, 1089093600000),
    (snapshotWord 6 0 8, -1089093600000),
    (snapshotWord 6 0 16, 544546800000),
    (snapshotWord 6 0 32, -108909360000)
  ]

/-- The complete integer degree-5 coefficient after half-stage 5. -/
def stage5Degree5 : ParamTable :=
  stage5Degree5Parameter6 ++ stage5Degree5Parameter5 ++
    stage5Degree5Parameter4 ++ stage5Degree5Parameter3 ++
    stage5Degree5Parameter2 ++ stage5Degree5Parameter1 ++
    stage5Degree5Parameter0

/-- The stage-5 degree-5 table is the actual integer recurrence coefficient. -/
theorem stage5Degree5_eq :
    defectCoeffTable (prefixTables 5) 5 = stage5Degree5 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage4Degree0_eq, stage4Degree1_eq, stage4Degree2_eq,
    stage4Degree3_eq, stage4Degree4_eq, stage4Degree5_eq]
  decide +kernel

/-- The parameter-degree-7 slice of half-stage 5, degree 6. -/
def stage5Degree6Parameter7 : ParamTable :=
  [
    (snapshotWord 7 7 1, 77913756144000000),
    (snapshotWord 7 7 2, -467482536864000000),
    (snapshotWord 7 7 3, 68246961350400000),
    (snapshotWord 7 7 4, 1168706342160000000),
    (snapshotWord 7 7 5, -140885148096000000),
    (snapshotWord 7 7 6, -200349658656000000),
    (snapshotWord 7 7 7, 34153975296000000),
    (snapshotWord 7 7 8, -1558275122880000000),
    (snapshotWord 7 7 9, 21956126976000000),
    (snapshotWord 7 7 10, 519628338432000000),
    (snapshotWord 7 7 11, -182967724800000000),
    (snapshotWord 7 7 12, 140885148096000000),
    (snapshotWord 7 7 13, 226879978752000000),
    (snapshotWord 7 7 14, -180528155136000000),
    (snapshotWord 7 7 15, 13417633152000000),
    (snapshotWord 7 7 16, 1168706342160000000),
    (snapshotWord 7 7 17, -43912253952000000),
    (snapshotWord 7 7 18, 65868380928000000),
    (snapshotWord 7 7 19, 241517396736000000),
    (snapshotWord 7 7 20, -845310888576000000),
    (snapshotWord 7 7 21, -439122539520000000),
    (snapshotWord 7 7 22, 504990920448000000),
    (snapshotWord 7 7 23, -278110941696000000),
    (snapshotWord 7 7 24, 140885148096000000),
    (snapshotWord 7 7 25, 65868380928000000),
    (snapshotWord 7 7 26, -373254158592000000),
    (snapshotWord 7 7 27, 680639936256000000),
    (snapshotWord 7 7 28, 204923851776000000),
    (snapshotWord 7 7 29, -512309629440000000),
    (snapshotWord 7 7 30, 69527735424000000),
    (snapshotWord 7 7 31, 29274835968000000),
    (snapshotWord 7 7 32, -467482536864000000),
    (snapshotWord 7 7 33, 43912253952000000),
    (snapshotWord 7 7 34, -87824507904000000),
    (snapshotWord 7 7 35, -204923851776000000),
    (snapshotWord 7 7 36, 65868380928000000),
    (snapshotWord 7 7 37, 526947047424000000),
    (snapshotWord 7 7 38, -395210285568000000),
    (snapshotWord 7 7 39, 380572867584000000),
    (snapshotWord 7 7 40, 519628338432000000),
    (snapshotWord 7 7 41, -351298031616000000),
    (snapshotWord 7 7 42, 526947047424000000),
    (snapshotWord 7 7 43, -878245079040000000),
    (snapshotWord 7 7 44, -373254158592000000),
    (snapshotWord 7 7 45, 175649015808000000),
    (snapshotWord 7 7 46, 497672211456000000),
    (snapshotWord 7 7 47, -307385777664000000),
    (snapshotWord 7 7 48, -200349658656000000),
    (snapshotWord 7 7 49, 204923851776000000),
    (snapshotWord 7 7 50, -395210285568000000),
    (snapshotWord 7 7 51, -43912253952000000),
    (snapshotWord 7 7 52, 504990920448000000),
    (snapshotWord 7 7 53, 878245079040000000),
    (snapshotWord 7 7 54, -1273455364608000000),
    (snapshotWord 7 7 55, 848970243072000000),
    (snapshotWord 7 7 56, -180528155136000000),
    (snapshotWord 7 7 57, -263473523712000000),
    (snapshotWord 7 7 58, 497672211456000000),
    (snapshotWord 7 7 59, -907519915008000000),
    (snapshotWord 7 7 60, 69527735424000000),
    (snapshotWord 7 7 61, 512309629440000000),
    (snapshotWord 7 7 62, -204923851776000000),
    (snapshotWord 7 7 63, 26347352371200000),
    (snapshotWord 7 7 64, 77913756144000000),
    (snapshotWord 7 7 65, -17564901580800000),
    (snapshotWord 7 7 66, 43912253952000000),
    (snapshotWord 7 7 67, 43912253952000000),
    (snapshotWord 7 7 68, -43912253952000000),
    (snapshotWord 7 7 69, -175649015808000000),
    (snapshotWord 7 7 70, 204923851776000000),
    (snapshotWord 7 7 71, -156132458496000000),
    (snapshotWord 7 7 72, 21956126976000000),
    (snapshotWord 7 7 73, 175649015808000000),
    (snapshotWord 7 7 74, -351298031616000000),
    (snapshotWord 7 7 75, 351298031616000000),
    (snapshotWord 7 7 76, 65868380928000000),
    (snapshotWord 7 7 78, -263473523712000000),
    (snapshotWord 7 7 79, 161011597824000000),
    (snapshotWord 7 7 80, -140885148096000000),
    (snapshotWord 7 7 81, -175649015808000000),
    (snapshotWord 7 7 82, 526947047424000000),
    (snapshotWord 7 7 83, -175649015808000000),
    (snapshotWord 7 7 84, -439122539520000000),
    (snapshotWord 7 7 85, -351298031616000000),
    (snapshotWord 7 7 86, 878245079040000000),
    (snapshotWord 7 7 87, -468397375488000000),
    (snapshotWord 7 7 88, 226879978752000000),
    (snapshotWord 7 7 90, 175649015808000000),
    (snapshotWord 7 7 91, 175649015808000000),
    (snapshotWord 7 7 92, -512309629440000000),
    (snapshotWord 7 7 93, -234198687744000000),
    (snapshotWord 7 7 94, 512309629440000000),
    (snapshotWord 7 7 95, -158084114227200000),
    (snapshotWord 7 7 96, 68246961350400000),
    (snapshotWord 7 7 97, 43912253952000000),
    (snapshotWord 7 7 98, -204923851776000000),
    (snapshotWord 7 7 99, 146374179840000000),
    (snapshotWord 7 7 100, 241517396736000000),
    (snapshotWord 7 7 101, -175649015808000000),
    (snapshotWord 7 7 102, -43912253952000000),
    (snapshotWord 7 7 103, -87824507904000000),
    (snapshotWord 7 7 104, -182967724800000000),
    (snapshotWord 7 7 105, 351298031616000000),
    (snapshotWord 7 7 106, -878245079040000000),
    (snapshotWord 7 7 107, 526947047424000000),
    (snapshotWord 7 7 108, 680639936256000000),
    (snapshotWord 7 7 109, 175649015808000000),
    (snapshotWord 7 7 110, -907519915008000000),
    (snapshotWord 7 7 111, 395210285568000000),
    (snapshotWord 7 7 112, 34153975296000000),
    (snapshotWord 7 7 113, -156132458496000000),
    (snapshotWord 7 7 114, 380572867584000000),
    (snapshotWord 7 7 115, -87824507904000000),
    (snapshotWord 7 7 116, -278110941696000000),
    (snapshotWord 7 7 117, -468397375488000000),
    (snapshotWord 7 7 118, 848970243072000000),
    (snapshotWord 7 7 119, -526947047424000000),
    (snapshotWord 7 7 120, 13417633152000000),
    (snapshotWord 7 7 121, 161011597824000000),
    (snapshotWord 7 7 122, -307385777664000000),
    (snapshotWord 7 7 123, 395210285568000000),
    (snapshotWord 7 7 124, 29274835968000000),
    (snapshotWord 7 7 125, -158084114227200000),
    (snapshotWord 7 7 126, 26347352371200000)
  ]

/-- The parameter-degree-6 slice of half-stage 5, degree 6. -/
def stage5Degree6Parameter6 : ParamTable :=
  [
    (snapshotWord 7 6 1, -156254436979200000),
    (snapshotWord 7 6 2, 937526621875200000),
    (snapshotWord 7 6 3, -96606958694400000),
    (snapshotWord 7 6 4, -2343816554688000000),
    (snapshotWord 7 6 5, 206753529024000000),
    (snapshotWord 7 6 6, 276281264448000000),
    (snapshotWord 7 6 7, -32324298048000000),
    (snapshotWord 7 6 8, 3125088739584000000),
    (snapshotWord 7 6 9, -32934190464000000),
    (snapshotWord 7 6 10, -761145735168000000),
    (snapshotWord 7 6 11, 161011597824000000),
    (snapshotWord 7 6 12, -171989661312000000),
    (snapshotWord 7 6 13, -226879978752000000),
    (snapshotWord 7 6 14, 195165573120000000),
    (snapshotWord 7 6 15, -31714405632000000),
    (snapshotWord 7 6 16, -2343816554688000000),
    (snapshotWord 7 6 17, -3659354496000000),
    (snapshotWord 7 6 18, 109780634880000000),
    (snapshotWord 7 6 19, -87824507904000000),
    (snapshotWord 7 6 20, 1031937967872000000),
    (snapshotWord 7 6 21, 153692888832000000),
    (snapshotWord 7 6 22, -461078666496000000),
    (snapshotWord 7 6 23, 153692888832000000),
    (snapshotWord 7 6 24, -171989661312000000),
    (snapshotWord 7 6 25, -76846444416000000),
    (snapshotWord 7 6 26, 680639936256000000),
    (snapshotWord 7 6 27, -329341904640000000),
    (snapshotWord 7 6 28, -402528994560000000),
    (snapshotWord 7 6 29, 168330306816000000),
    (snapshotWord 7 6 30, 102461925888000000),
    (snapshotWord 7 6 31, -40984770355200000),
    (snapshotWord 7 6 32, 937526621875200000),
    (snapshotWord 7 6 33, 38423222208000000),
    (snapshotWord 7 6 34, -146374179840000000),
    (snapshotWord 7 6 35, -14637417984000000),
    (snapshotWord 7 6 36, 109780634880000000),
    (snapshotWord 7 6 37, 131736761856000000),
    (snapshotWord 7 6 38, 87824507904000000),
    (snapshotWord 7 6 39, 102461925888000000),
    (snapshotWord 7 6 40, -761145735168000000),
    (snapshotWord 7 6 41, 21956126976000000),
    (snapshotWord 7 6 42, -614771555328000000),
    (snapshotWord 7 6 43, -87824507904000000),
    (snapshotWord 7 6 44, 680639936256000000),
    (snapshotWord 7 6 45, 131736761856000000),
    (snapshotWord 7 6 46, -556221883392000000),
    (snapshotWord 7 6 47, 73187089920000000),
    (snapshotWord 7 6 48, 276281264448000000),
    (snapshotWord 7 6 49, 14637417984000000),
    (snapshotWord 7 6 50, 87824507904000000),
    (snapshotWord 7 6 51, -43912253952000000),
    (snapshotWord 7 6 52, -461078666496000000),
    (snapshotWord 7 6 53, 131736761856000000),
    (snapshotWord 7 6 54, 702596063232000000),
    (snapshotWord 7 6 55, 43912253952000000),
    (snapshotWord 7 6 56, 195165573120000000),
    (snapshotWord 7 6 57, -21956126976000000),
    (snapshotWord 7 6 58, -556221883392000000),
    (snapshotWord 7 6 59, -87824507904000000),
    (snapshotWord 7 6 60, 102461925888000000),
    (snapshotWord 7 6 61, 87824507904000000),
    (snapshotWord 7 6 62, -35129803161600000),
    (snapshotWord 7 6 63, 18540729446400000),
    (snapshotWord 7 6 64, -156254436979200000),
    (snapshotWord 7 6 65, -15369288883200000),
    (snapshotWord 7 6 66, 38423222208000000),
    (snapshotWord 7 6 67, 38423222208000000),
    (snapshotWord 7 6 68, -3659354496000000),
    (snapshotWord 7 6 69, -153692888832000000),
    (snapshotWord 7 6 70, 14637417984000000),
    (snapshotWord 7 6 71, -129297192192000000),
    (snapshotWord 7 6 72, -32934190464000000),
    (snapshotWord 7 6 73, 153692888832000000),
    (snapshotWord 7 6 74, 21956126976000000),
    (snapshotWord 7 6 75, 285429650688000000),
    (snapshotWord 7 6 76, -76846444416000000),
    (snapshotWord 7 6 77, 21956126976000000),
    (snapshotWord 7 6 78, -21956126976000000),
    (snapshotWord 7 6 79, 131736761856000000),
    (snapshotWord 7 6 80, 206753529024000000),
    (snapshotWord 7 6 81, -153692888832000000),
    (snapshotWord 7 6 82, 131736761856000000),
    (snapshotWord 7 6 83, -131736761856000000),
    (snapshotWord 7 6 84, 153692888832000000),
    (snapshotWord 7 6 85, -351298031616000000),
    (snapshotWord 7 6 86, 131736761856000000),
    (snapshotWord 7 6 87, -380572867584000000),
    (snapshotWord 7 6 88, -226879978752000000),
    (snapshotWord 7 6 89, 21956126976000000),
    (snapshotWord 7 6 90, 131736761856000000),
    (snapshotWord 7 6 91, 131736761856000000),
    (snapshotWord 7 6 92, 168330306816000000),
    (snapshotWord 7 6 93, -175649015808000000),
    (snapshotWord 7 6 94, 87824507904000000),
    (snapshotWord 7 6 95, -111244376678400000),
    (snapshotWord 7 6 96, -96606958694400000),
    (snapshotWord 7 6 97, 38423222208000000),
    (snapshotWord 7 6 98, -14637417984000000),
    (snapshotWord 7 6 99, 117099343872000000),
    (snapshotWord 7 6 100, -87824507904000000),
    (snapshotWord 7 6 101, -131736761856000000),
    (snapshotWord 7 6 102, -43912253952000000),
    (snapshotWord 7 6 103, -73187089920000000),
    (snapshotWord 7 6 104, 161011597824000000),
    (snapshotWord 7 6 105, 285429650688000000),
    (snapshotWord 7 6 106, -87824507904000000),
    (snapshotWord 7 6 107, 439122539520000000),
    (snapshotWord 7 6 108, -329341904640000000),
    (snapshotWord 7 6 109, 131736761856000000),
    (snapshotWord 7 6 110, -87824507904000000),
    (snapshotWord 7 6 111, 278110941696000000),
    (snapshotWord 7 6 112, -32324298048000000),
    (snapshotWord 7 6 113, -129297192192000000),
    (snapshotWord 7 6 114, 102461925888000000),
    (snapshotWord 7 6 115, -73187089920000000),
    (snapshotWord 7 6 116, 153692888832000000),
    (snapshotWord 7 6 117, -380572867584000000),
    (snapshotWord 7 6 118, 43912253952000000),
    (snapshotWord 7 6 119, -370814588928000000),
    (snapshotWord 7 6 120, -31714405632000000),
    (snapshotWord 7 6 121, 131736761856000000),
    (snapshotWord 7 6 122, 73187089920000000),
    (snapshotWord 7 6 123, 278110941696000000),
    (snapshotWord 7 6 124, -40984770355200000),
    (snapshotWord 7 6 125, -111244376678400000),
    (snapshotWord 7 6 126, 18540729446400000)
  ]

/-- The parameter-degree-5 slice of half-stage 5, degree 6. -/
def stage5Degree6Parameter5 : ParamTable :=
  [
    (snapshotWord 7 5 1, 131279342544000000),
    (snapshotWord 7 5 2, -787676055264000000),
    (snapshotWord 7 5 3, 52145801568000000),
    (snapshotWord 7 5 4, 1969190138160000000),
    (snapshotWord 7 5 5, -109780634880000000),
    (snapshotWord 7 5 6, -150948372960000000),
    (snapshotWord 7 5 7, 18296772480000000),
    (snapshotWord 7 5 8, -2625586850880000000),
    (snapshotWord 7 5 9, 16467095232000000),
    (snapshotWord 7 5 10, 406188349056000000),
    (snapshotWord 7 5 11, -43912253952000000),
    (snapshotWord 7 5 12, 98802571392000000),
    (snapshotWord 7 5 13, 76846444416000000),
    (snapshotWord 7 5 14, -106121280384000000),
    (snapshotWord 7 5 15, 25615481472000000),
    (snapshotWord 7 5 16, 1969190138160000000),
    (snapshotWord 7 5 17, -10978063488000000),
    (snapshotWord 7 5 18, -16467095232000000),
    (snapshotWord 7 5 19, -65868380928000000),
    (snapshotWord 7 5 20, -592815428352000000),
    (snapshotWord 7 5 21, 43912253952000000),
    (snapshotWord 7 5 22, 219561269760000000),
    (snapshotWord 7 5 23, -29274835968000000),
    (snapshotWord 7 5 24, 98802571392000000),
    (snapshotWord 7 5 25, -10978063488000000),
    (snapshotWord 7 5 26, -252495460224000000),
    (snapshotWord 7 5 27, -65868380928000000),
    (snapshotWord 7 5 28, 175649015808000000),
    (snapshotWord 7 5 29, 43912253952000000),
    (snapshotWord 7 5 30, -25615481472000000),
    (snapshotWord 7 5 31, -19028643379200000),
    (snapshotWord 7 5 32, -787676055264000000),
    (snapshotWord 7 5 34, 21956126976000000),
    (snapshotWord 7 5 35, 54890317440000000),
    (snapshotWord 7 5 36, -16467095232000000),
    (snapshotWord 7 5 37, -109780634880000000),
    (snapshotWord 7 5 38, 76846444416000000),
    (snapshotWord 7 5 39, -73187089920000000),
    (snapshotWord 7 5 40, 406188349056000000),
    (snapshotWord 7 5 41, 109780634880000000),
    (snapshotWord 7 5 42, -87824507904000000),
    (snapshotWord 7 5 43, 219561269760000000),
    (snapshotWord 7 5 44, -252495460224000000),
    (snapshotWord 7 5 46, -14637417984000000),
    (snapshotWord 7 5 47, 95143216896000000),
    (snapshotWord 7 5 48, -150948372960000000),
    (snapshotWord 7 5 49, -54890317440000000),
    (snapshotWord 7 5 50, 76846444416000000),
    (snapshotWord 7 5 52, 219561269760000000),
    (snapshotWord 7 5 53, -219561269760000000),
    (snapshotWord 7 5 54, 131736761856000000),
    (snapshotWord 7 5 55, -190286433792000000),
    (snapshotWord 7 5 56, -106121280384000000),
    (snapshotWord 7 5 57, 73187089920000000),
    (snapshotWord 7 5 58, -14637417984000000),
    (snapshotWord 7 5 59, 190286433792000000),
    (snapshotWord 7 5 60, -25615481472000000),
    (snapshotWord 7 5 61, -95143216896000000),
    (snapshotWord 7 5 62, 38057286758400000),
    (snapshotWord 7 5 64, 131279342544000000),
    (snapshotWord 7 5 68, -10978063488000000),
    (snapshotWord 7 5 70, -54890317440000000),
    (snapshotWord 7 5 72, 16467095232000000),
    (snapshotWord 7 5 74, 109780634880000000),
    (snapshotWord 7 5 76, -10978063488000000),
    (snapshotWord 7 5 78, 73187089920000000),
    (snapshotWord 7 5 80, -109780634880000000),
    (snapshotWord 7 5 82, -109780634880000000),
    (snapshotWord 7 5 84, 43912253952000000),
    (snapshotWord 7 5 86, -219561269760000000),
    (snapshotWord 7 5 88, 76846444416000000),
    (snapshotWord 7 5 92, 43912253952000000),
    (snapshotWord 7 5 94, -95143216896000000),
    (snapshotWord 7 5 96, 52145801568000000),
    (snapshotWord 7 5 98, 54890317440000000),
    (snapshotWord 7 5 100, -65868380928000000),
    (snapshotWord 7 5 104, -43912253952000000),
    (snapshotWord 7 5 106, 219561269760000000),
    (snapshotWord 7 5 108, -65868380928000000),
    (snapshotWord 7 5 110, 190286433792000000),
    (snapshotWord 7 5 112, 18296772480000000),
    (snapshotWord 7 5 114, -73187089920000000),
    (snapshotWord 7 5 116, -29274835968000000),
    (snapshotWord 7 5 118, -190286433792000000),
    (snapshotWord 7 5 120, 25615481472000000),
    (snapshotWord 7 5 122, 95143216896000000),
    (snapshotWord 7 5 124, -19028643379200000)
  ]

/-- The parameter-degree-4 slice of half-stage 5, degree 6. -/
def stage5Degree6Parameter4 : ParamTable :=
  [
    (snapshotWord 7 4 1, -59769456768000000),
    (snapshotWord 7 4 2, 358616740608000000),
    (snapshotWord 7 4 3, -14637417984000000),
    (snapshotWord 7 4 4, -896541851520000000),
    (snapshotWord 7 4 5, 25615481472000000),
    (snapshotWord 7 4 6, 47571608448000000),
    (snapshotWord 7 4 7, -8538493824000000),
    (snapshotWord 7 4 8, 1195389135360000000),
    (snapshotWord 7 4 9, 10978063488000000),
    (snapshotWord 7 4 10, -124418052864000000),
    (snapshotWord 7 4 11, 14637417984000000),
    (snapshotWord 7 4 12, -32934190464000000),
    (snapshotWord 7 4 13, 7318708992000000),
    (snapshotWord 7 4 14, 12197848320000000),
    (snapshotWord 7 4 15, 7318708992000000),
    (snapshotWord 7 4 16, -896541851520000000),
    (snapshotWord 7 4 17, -7318708992000000),
    (snapshotWord 7 4 18, -10978063488000000),
    (snapshotWord 7 4 19, 10978063488000000),
    (snapshotWord 7 4 20, 197605142784000000),
    (snapshotWord 7 4 21, -43912253952000000),
    (snapshotWord 7 4 22, -21956126976000000),
    (snapshotWord 7 4 23, -29274835968000000),
    (snapshotWord 7 4 24, -32934190464000000),
    (snapshotWord 7 4 25, 10978063488000000),
    (snapshotWord 7 4 27, 43912253952000000),
    (snapshotWord 7 4 28, -7318708992000000),
    (snapshotWord 7 4 29, -29274835968000000),
    (snapshotWord 7 4 30, -7318708992000000),
    (snapshotWord 7 4 32, 358616740608000000),
    (snapshotWord 7 4 34, 14637417984000000),
    (snapshotWord 7 4 36, -10978063488000000),
    (snapshotWord 7 4 38, -21956126976000000),
    (snapshotWord 7 4 40, -124418052864000000),
    (snapshotWord 7 4 42, 87824507904000000),
    (snapshotWord 7 4 46, 58549671936000000),
    (snapshotWord 7 4 48, 47571608448000000),
    (snapshotWord 7 4 50, -21956126976000000),
    (snapshotWord 7 4 52, -21956126976000000),
    (snapshotWord 7 4 54, -87824507904000000),
    (snapshotWord 7 4 56, 12197848320000000),
    (snapshotWord 7 4 58, 58549671936000000),
    (snapshotWord 7 4 60, -7318708992000000),
    (snapshotWord 7 4 64, -59769456768000000),
    (snapshotWord 7 4 68, -7318708992000000),
    (snapshotWord 7 4 72, 10978063488000000),
    (snapshotWord 7 4 76, 10978063488000000),
    (snapshotWord 7 4 80, 25615481472000000),
    (snapshotWord 7 4 84, -43912253952000000),
    (snapshotWord 7 4 88, 7318708992000000),
    (snapshotWord 7 4 92, -29274835968000000),
    (snapshotWord 7 4 96, -14637417984000000),
    (snapshotWord 7 4 100, 10978063488000000),
    (snapshotWord 7 4 104, 14637417984000000),
    (snapshotWord 7 4 108, 43912253952000000),
    (snapshotWord 7 4 112, -8538493824000000),
    (snapshotWord 7 4 116, -29274835968000000),
    (snapshotWord 7 4 120, 7318708992000000)
  ]

/-- The parameter-degree-3 slice of half-stage 5, degree 6. -/
def stage5Degree6Parameter3 : ParamTable :=
  [
    (snapshotWord 7 3 1, 16009675920000000),
    (snapshotWord 7 3 2, -96058055520000000),
    (snapshotWord 7 3 3, 2744515872000000),
    (snapshotWord 7 3 4, 240145138800000000),
    (snapshotWord 7 3 5, -5489031744000000),
    (snapshotWord 7 3 6, -8233547616000000),
    (snapshotWord 7 3 7, -1219784832000000),
    (snapshotWord 7 3 8, -320193518400000000),
    (snapshotWord 7 3 10, 21956126976000000),
    (snapshotWord 7 3 11, 3659354496000000),
    (snapshotWord 7 3 12, 5489031744000000),
    (snapshotWord 7 3 13, -3659354496000000),
    (snapshotWord 7 3 14, 4879139328000000),
    (snapshotWord 7 3 16, 240145138800000000),
    (snapshotWord 7 3 20, -32934190464000000),
    (snapshotWord 7 3 22, -10978063488000000),
    (snapshotWord 7 3 24, 5489031744000000),
    (snapshotWord 7 3 26, 10978063488000000),
    (snapshotWord 7 3 28, -7318708992000000),
    (snapshotWord 7 3 32, -96058055520000000),
    (snapshotWord 7 3 40, 21956126976000000),
    (snapshotWord 7 3 44, 10978063488000000),
    (snapshotWord 7 3 48, -8233547616000000),
    (snapshotWord 7 3 52, -10978063488000000),
    (snapshotWord 7 3 56, 4879139328000000),
    (snapshotWord 7 3 64, 16009675920000000),
    (snapshotWord 7 3 80, -5489031744000000),
    (snapshotWord 7 3 88, -3659354496000000),
    (snapshotWord 7 3 96, 2744515872000000),
    (snapshotWord 7 3 104, 3659354496000000),
    (snapshotWord 7 3 112, -1219784832000000)
  ]

/-- The parameter-degree-2 slice of half-stage 5, degree 6. -/
def stage5Degree6Parameter2 : ParamTable :=
  [
    (snapshotWord 7 2 1, -2561548147200000),
    (snapshotWord 7 2 2, 15369288883200000),
    (snapshotWord 7 2 4, -38423222208000000),
    (snapshotWord 7 2 8, 51230962944000000),
    (snapshotWord 7 2 16, -38423222208000000),
    (snapshotWord 7 2 32, 15369288883200000),
    (snapshotWord 7 2 64, -2561548147200000)
  ]

/-- The parameter-degree-1 slice of half-stage 5, degree 6. -/
def stage5Degree6Parameter1 : ParamTable :=
  [
    (snapshotWord 7 1 1, 213462345600000),
    (snapshotWord 7 1 2, -1280774073600000),
    (snapshotWord 7 1 4, 3201935184000000),
    (snapshotWord 7 1 8, -4269246912000000),
    (snapshotWord 7 1 16, 3201935184000000),
    (snapshotWord 7 1 32, -1280774073600000),
    (snapshotWord 7 1 64, 213462345600000)
  ]

/-- The parameter-degree-0 slice of half-stage 5, degree 6. -/
def stage5Degree6Parameter0 : ParamTable :=
  [
    (snapshotWord 7 0 1, -7623655200000),
    (snapshotWord 7 0 2, 45741931200000),
    (snapshotWord 7 0 4, -114354828000000),
    (snapshotWord 7 0 8, 152473104000000),
    (snapshotWord 7 0 16, -114354828000000),
    (snapshotWord 7 0 32, 45741931200000),
    (snapshotWord 7 0 64, -7623655200000)
  ]

/-- The complete integer degree-6 coefficient after half-stage 5. -/
def stage5Degree6 : ParamTable :=
  stage5Degree6Parameter7 ++ stage5Degree6Parameter6 ++
    stage5Degree6Parameter5 ++ stage5Degree6Parameter4 ++
    stage5Degree6Parameter3 ++ stage5Degree6Parameter2 ++
    stage5Degree6Parameter1 ++ stage5Degree6Parameter0

/-- The stage-5 degree-6 table is the actual integer recurrence coefficient. -/
theorem stage5Degree6_eq :
    defectCoeffTable (prefixTables 5) 6 = stage5Degree6 := by
  rw [defectCoeffTable, prefixTables_castSucc]
  simp only [List.range_succ, List.range_zero, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
    Nat.reduceSub, Nat.reduceAdd]
  rw [stage4Degree0_eq, stage4Degree1_eq, stage4Degree2_eq,
    stage4Degree3_eq, stage4Degree4_eq, stage4Degree5_eq,
    stage4Degree6_eq]
  decide +kernel

end FQFP.SuzukiSepticCertificate
