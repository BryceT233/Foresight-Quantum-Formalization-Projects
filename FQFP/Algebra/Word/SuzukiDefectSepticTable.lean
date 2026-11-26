/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Word.SuzukiDefectSepticData

/-!
# The integer half-defect recurrence for the Suzuki septic coefficient

Scaling the ordinary letters by `1/840` clears all exponential factorials
through degree six. Grouped coefficients are retained before collecting words.

## Main definitions

* `defectCoeffTable`: integer conjugation-and-kick coefficients.
* `septicCoordinateTable`: the three given parameter coordinates as a central table.
* `defectSepticResidual`: the actual coefficient minus its target and cubic quotient.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

open CoeffWordTable

/-- The six integer half-generators at ordinary letter scale `840`. -/
def halfTables : Fin 6 → ParamTable :=
  ![[([none, some 0], 1)], [([none, some 1], 2)],
    [([none, some 0], 2)], [([none, some 1], 2)],
    [([some 0], 1), ([none, some 0], -3)],
    [([some 1], 1), ([none, some 1], -4)]]

/-- The integer seed whose evaluation multiplied by `420` is `-G/2`. -/
def defectSeedTable : ParamTable := [([some 0], -1), ([some 1], -1)]

/-- The collected associative commutator of two integer parameter tables. -/
def bracketTable (s t : ParamTable) : ParamTable :=
  CentralBinaryWordTable.collect (mul s t ++ smul (-1) (mul t s))

/-- Repeated adjoint action in integer word tables. -/
def adTable (s : ParamTable) : ℕ → ParamTable → ParamTable
  | 0, t => t
  | n + 1, t => bracketTable s (adTable s n t)

/-- Integral exponential weights through degree six, including the conjugation sign. -/
def defectExpWeight (q : ℕ) : ℤ := (-420) ^ q / (Nat.factorial q : ℤ)

/-- The grouped half-defect coefficient recursion at letter scale `840`. -/
def defectCoeffTable {s : ℕ} (Z : Fin s → ParamTable) (n : ℕ) : ParamTable :=
  match s with
  | 0 => if n = 0 then defectSeedTable else []
  | s + 1 => CentralBinaryWordTable.collect
      (((List.range (n + 1)).flatMap fun q ↦
        smul (defectExpWeight q)
          (adTable (Z (Fin.last s)) q
            (defectCoeffTable (fun i ↦ Z i.castSucc) (n - q)))) ++
              if n = 0 then Z (Fin.last s) else [])

/-- The reduced target coordinates as a central-parameter word table. -/
def septicCoordinateTable (rows : Rows) : ParamTable :=
  rows.flatMap fun row ↦
    [(row.1.map some, row.2.1), (none :: row.1.map some, row.2.2.1),
      (none :: none :: row.1.map some, row.2.2.2)]

/-- The parameter's integral cubic relation. -/
def cubicRelationTable : ParamTable :=
  [([], 1), ([none], -12), ([none, none], 48), ([none, none, none], -60)]

/-- The first `s` half-tables; only the first six prefixes are used by the certificate. -/
def prefixTables (s : ℕ) (i : Fin s) : ParamTable := halfTables (Fin.ofNat 6 i.val)

/-- Removing the last prefix index preserves the preceding half-generators. -/
lemma prefixTables_castSucc (s : ℕ) :
    (fun i : Fin s ↦ prefixTables (s + 1) i.castSucc) = prefixTables s := rfl

/-- Encode a fixed-length binary word after its central parameter prefix. -/
def snapshotWord (n q code : ℕ) : List (Option (Fin 2)) :=
  List.replicate q none ++
    ((List.range n).reverse.map fun k ↦ some (Fin.ofNat 2 (code / 2 ^ k)))

/-- At length six the prefix is the complete half-generator family. -/
lemma prefixTables_six : prefixTables 6 = halfTables := by
  funext i
  change halfTables (Fin.ofNat 6 i.val) = halfTables i
  exact congrArg halfTables (Fin.ext (Nat.mod_eq_of_lt i.isLt))

/-- The exact difference of the coefficient, target, and cubic multiple. -/
def defectSepticResidual : ParamTable :=
  CentralBinaryWordTable.collect
    (defectCoeffTable halfTables 6 ++
      smul (-48404160) (septicCoordinateTable expandedDefectData) ++
        smul (-1) (mul cubicRelationTable defectSepticQuotient))

end FQFP.SuzukiSepticCertificate
