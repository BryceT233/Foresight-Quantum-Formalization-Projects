/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Word.SuzukiSepticCertificate

/-!
# Coordinate certificates relating the three septic presentations

The quintic polynomial has denominator `144000`. Reducing its product with
the quadratic half-transport coefficient gives integer coordinate tables for
the difference of the centered and defect septic polynomials. The difference
between centered and BCH data is a double commutator with the total generator.

## Main definitions

* `quinticData`: the six nonzero quintic right-nested rows.
* `scaledOmegaTriple`: exact integer reduction of the transport correction.
* `centeredDefectMatches`, `centeredBchMatches`: complete coordinate checks.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

open WordTable

/-- The six quintic right-nested rows, with common denominator `144000`. -/
def quinticData : Rows :=
  [([0, 0, 0, 1, 0], (-6, 52, 127)),
    ([0, 0, 1, 1, 0], (-36, 312, 12)),
    ([0, 1, 1, 1, 0], (-72, 624, -976)),
    ([1, 0, 0, 1, 0], (12, -104, 496)),
    ([1, 0, 1, 1, 0], (36, -312, 1488)),
    ([1, 1, 1, 1, 0], (-24, 208, 8))]

/-- The three reduced coordinates of `31500 (1 - 8p + 16p²)` times an input triple. -/
def scaledOmegaTriple (c : Triple) : Triple :=
  let d3 := -8 * c.2.2 + 16 * c.2.1
  let d4 := 16 * c.2.2
  (31500 * c.1 + 525 * d3 + 420 * d4,
    31500 * (c.2.1 - 8 * c.1) - 6300 * d3 - 4515 * d4,
    31500 * (c.2.2 - 8 * c.2.1 + 16 * c.1) + 25200 * d3 + 13860 * d4)

/-- The transport correction before applying the outer binary commutator. -/
def scaledOmegaQuinticData : Rows :=
  quinticData.map fun r ↦ (r.1, scaledOmegaTriple r.2)

/-- The associative commutator of two binary integer tables. -/
def binaryBracketTable (s t : Table (Fin 2)) : Table (Fin 2) :=
  mul s t ++ smul (-1) (mul t s)

/-- The integer table of the basic binary commutator `[a,b]`. -/
def binaryCommutatorTable : Table (Fin 2) := [([0, 1], 1), ([1, 0], -1)]

/-- The integer table of the total generator `a+b`. -/
def binarySumTable : Table (Fin 2) := [([0], 1), ([1], 1)]

/-- Check the entire centered-minus-defect correction in one parameter coordinate. -/
def centeredDefectMatches (q : Fin 3) : Bool :=
  BinaryWordTable.isZero (BinaryWordTable.collect
    (readCoordinate q expandedCenteredData ++ smul (-1) (readCoordinate q expandedDefectData) ++
      smul (-1) (binaryBracketTable binaryCommutatorTable
        (expandCoordinate q scaledOmegaQuinticData))))

/-- Check the entire centered-minus-BCH double commutator in one parameter coordinate. -/
def centeredBchMatches (q : Fin 3) : Bool :=
  BinaryWordTable.isZero (BinaryWordTable.collect
    (readCoordinate q expandedCenteredData ++ smul (-1) (readCoordinate q expandedBchData) ++
      smul (-14700) (binaryBracketTable binarySumTable
        (binaryBracketTable binarySumTable (expandCoordinate q quinticData)))))

/-- The constant coordinate of the centered transport correction agrees. -/
theorem centered_defect_constant_matches : centeredDefectMatches 0 = true := by
  decide +kernel

/-- The linear coordinate of the centered transport correction agrees. -/
theorem centered_defect_linear_matches : centeredDefectMatches 1 = true := by
  decide +kernel

/-- The quadratic coordinate of the centered transport correction agrees. -/
theorem centered_defect_quadratic_matches : centeredDefectMatches 2 = true := by
  decide +kernel

/-- The constant coordinate of the centered-to-BCH correction agrees. -/
theorem centered_bch_constant_matches : centeredBchMatches 0 = true := by
  decide +kernel

/-- The linear coordinate of the centered-to-BCH correction agrees. -/
theorem centered_bch_linear_matches : centeredBchMatches 1 = true := by
  decide +kernel

/-- The quadratic coordinate of the centered-to-BCH correction agrees. -/
theorem centered_bch_quadratic_matches : centeredBchMatches 2 = true := by
  decide +kernel

/-- All three coordinates of the centered transport correction agree. -/
theorem centered_defect_matches (q : Fin 3) : centeredDefectMatches q = true := by
  fin_cases q
  · exact centered_defect_constant_matches
  · exact centered_defect_linear_matches
  · exact centered_defect_quadratic_matches

/-- All three coordinates of the centered-to-BCH correction agree. -/
theorem centered_bch_matches (q : Fin 3) : centeredBchMatches q = true := by
  fin_cases q
  · exact centered_bch_constant_matches
  · exact centered_bch_linear_matches
  · exact centered_bch_quadratic_matches

end FQFP.SuzukiSepticCertificate
