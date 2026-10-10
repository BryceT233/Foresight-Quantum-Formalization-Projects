/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.ProductFormula.Basic
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# The order condition for a product formula

The paper's definition `P.IsOrderOf p H`, independent of derivative criteria,
time-ordered evolution, and the equivalent error-kernel conditions.
-/

@[expose] public section

namespace TrotterError

open Asymptotics
open scoped Topology

/-! ### The `p`-th order condition (`P.IsOrderOf`) -/

namespace ProductFormulaData

open NormedSpace

/-- `P` is a `p`-th order formula on summands `H` if `‖𝒮(t) − e^{tH}‖ = O(t^{p+1})`
as `t → 0` (`prelim.tex:150`). -/
def IsOrderOf {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (p : ℕ) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) : Prop :=
  (fun t : ℝ => ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖)
    =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1))

end ProductFormulaData

end TrotterError
