module

public import FQFP.BCH.QuinticTaylor2

/-!
# Spike: the numeric facts behind the taylor2 norm bounds, by `decide`

Scratch file, not part of the library.
`lake env lean artifacts/examples/quintic-counts-spike.lean`

`bchQuinticGroupSubsets` sums over `(aPos i).powersetCard k`, which has
`((aPos i).card).choose k` elements. The per-group totals below are what turns the piece bounds
into the numeric factors `384/720`, `136/720`, `16/720` (all below the source's `1680/720`,
`720/720`, `30/720`).
-/

@[expose] public section

open Finset

namespace FQFP.BCH

example :
    (∑ i : Fin 4, ((wordAPositions (wordEvalPattern (bchQuinticGroup1Words i))).card).choose 2)
      = 12 := by decide

example :
    (∑ i : Fin 10, ((wordAPositions (wordEvalPattern (bchQuinticGroup4Words i))).card).choose 2)
      = 24 := by decide

example :
    (∑ i : Fin 14, ((wordAPositions (wordEvalPattern (bchQuinticGroup6Words i))).card).choose 2)
      = 30 := by decide

example :
    (∑ i : Fin 2, ((wordAPositions (wordEvalPattern (bchQuinticGroup24Words i))).card).choose 2)
      = 4 := by decide

example :
    (∑ i : Fin 4, ((wordAPositions (wordEvalPattern (bchQuinticGroup1Words i))).card).choose 3)
      = 8 := by decide

example :
    (∑ i : Fin 10, ((wordAPositions (wordEvalPattern (bchQuinticGroup4Words i))).card).choose 3)
      = 11 := by decide

example :
    (∑ i : Fin 14, ((wordAPositions (wordEvalPattern (bchQuinticGroup6Words i))).card).choose 3)
      = 10 := by decide

example :
    (∑ i : Fin 2, ((wordAPositions (wordEvalPattern (bchQuinticGroup24Words i))).card).choose 3)
      = 1 := by decide

example :
    (∑ i : Fin 4, ((wordAPositions (wordEvalPattern (bchQuinticGroup1Words i))).card).choose 4)
      = 2 := by decide

example :
    (∑ i : Fin 10, ((wordAPositions (wordEvalPattern (bchQuinticGroup4Words i))).card).choose 4)
      = 2 := by decide

example :
    (∑ i : Fin 14, ((wordAPositions (wordEvalPattern (bchQuinticGroup6Words i))).card).choose 4)
      = 1 := by decide

example :
    (∑ i : Fin 2, ((wordAPositions (wordEvalPattern (bchQuinticGroup24Words i))).card).choose 4)
      = 0 := by decide

-- No word of the coefficient-1 group is the all-`a` word, so no subset has five elements.
example : ∀ i : Fin 4, (wordAPositions (wordEvalPattern (bchQuinticGroup1Words i))).card ≤ 4 := by
  intro i
  fin_cases i <;> decide

#print axioms FQFP.BCH.bchQuinticTermTaylor2Decomp

end FQFP.BCH
