/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.ProductFormula.Basic
public import FQFP.TrotterError.ProductFormula.Analysis

/-!
# Product formulas (compatibility entry point)

We define the general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of arXiv:1912.08854 (§2.3), its operations and estimates.
The associated `p`-th order condition is defined in `OrderCondition.Basic`.

Following the paper's convention (`papers/prelim.tex` §2.1), the product
`∏_{γ=1}^{Γ} A_γ` denotes `A_Γ ⋯ A_2 A_1`, i.e. increasing indices from right to
left; we implement this with a reversed `List.finRange`. Since the factors
`e^{t a H}` do not commute, the product is taken with `List.prod` (ordered) rather
than `prod` (commutative) or `noncommProd` (which requires pairwise
commutativity).

## Main definitions

* `ProductFormulaData`: the data of a product formula `𝒮(t)` (stages `Υ`, summands `Γ`,
  coefficients `coeff`, permutations `perm`).
* `evalFactor`, `eval`, `generator`: the single factor, the full product, and the generator
  `a_{(υ,γ)} H_{π_υ(γ)}`.
* `evalIndexList`: the flattened factor-index order used by `eval`.
* `orderedSummands`, `orderedSummandsEval`: coefficient-free summands in canonical and evaluation
  order, respectively. `reverseStages` relates these orders without changing coefficients.
* `orderedGenerators`, `suffixGenerators`, `fullGenerators`: the generators of the product
  formula in `evalIndexList` order.

## Main results

* `ProductFormulaData.eval_iteratedDeriv_succ`: the `(p + 1)`-st iterated derivative
  of `eval`, expanded as a multinomial Leibniz sum over `Fin Υ × Fin Γ`.
* `evalIndexList_eq_ofFn`, `evalIndexList_length`: the flattened index list as `List.ofFn`.

**Assisted by Deepseek Harness**
-/
