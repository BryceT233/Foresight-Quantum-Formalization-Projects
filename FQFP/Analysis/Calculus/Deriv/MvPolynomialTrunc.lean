/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Calculus.Deriv.MvPolynomial
public import FQFP.RingTheory.MvPolynomial.DerivationCompression

/-!
# Derivative residual for truncated polynomial observables

## Main results

* `MvPolynomial.hasDerivAt_aeval_compressed_with_residual`: compression leaves exactly the
  evaluation of the discarded part as derivative residual.
-/

@[expose] public section
noncomputable section

namespace MvPolynomial
variable {σ 𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The discarded part of the polynomial derivation gives the exact residual after truncation. -/
lemma hasDerivAt_aeval_compressed_with_residual
    (F : σ → MvPolynomial σ 𝕜) (x : 𝕜 → σ → 𝕜) (t : 𝕜)
    (hx : ∀ i, HasDerivAt (fun s ↦ x s i) (aeval (x t) (F i)) t)
    (n : ℕ) (p : (truncTotal σ 𝕜 n).range) :
    let D := mkDerivation 𝕜 F
    let Y := (aeval (x t)).toLinearMap.comp (truncTotal σ 𝕜 n).range.subtype
    HasDerivAt (fun s ↦ aeval (x s) (p : MvPolynomial σ 𝕜))
      ((compressedDerivation D n).dualMap Y p +
        aeval (x t) (D p - truncTotal σ 𝕜 n (D p))) t := by
  apply (hasDerivAt_aeval_of_hasDerivAt_coordinates F x t hx p).congr_deriv
  exact LinearMap.congr_fun (sub_eq_iff_eq_add'.mp
    (dualMap_restriction_sub_compressed (mkDerivation 𝕜 F) n (aeval (x t)).toLinearMap)) p

end MvPolynomial
