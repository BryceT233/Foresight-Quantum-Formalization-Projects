/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Extending orthonormal families

Matching orthonormal families in finite-dimensional spaces of equal dimension extends
to a linear isometric equivalence, including when the families do not span the spaces.
Standard orthonormal bases also give an isometric embedding whenever the source dimension
is at most the target dimension, by extending coordinates by zero.

## Main definitions and results

* `LinearIsometry.ofFinrankLE` embeds a space into one of at least its dimension.
* `Orthonormal.exists_linearIsometryEquiv` extends matching orthonormal families to an isometric
  equivalence of equal-dimensional spaces.
-/

@[expose] public section

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Embed a finite-dimensional inner product space into a space of at least its dimension,
using standard orthonormal coordinates and extending them by zero. -/
noncomputable def LinearIsometry.ofFinrankLE
    (hdim : Module.finrank 𝕜 E ≤ Module.finrank 𝕜 F) : E →ₗᵢ[𝕜] F :=
  (stdOrthonormalBasis 𝕜 F).repr.symm.toLinearIsometry.comp
    ((LinearIsometry.piLpExtendByZero 2 𝕜 𝕜 (Fin.castLEEmb hdim)).comp
      (stdOrthonormalBasis 𝕜 E).repr.toLinearIsometry)

/-- Matching orthonormal families extend to an isometric equivalence of equal-dimensional
finite-dimensional spaces. Neither family is required to be a basis. -/
lemma Orthonormal.exists_linearIsometryEquiv {u : ι → E} {v : ι → F}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F) :
    ∃ U : E ≃ₗᵢ[𝕜] F, ∀ i, U (u i) = v i := by
  classical
  let e₀ : E ≃ₗᵢ[𝕜] F := (stdOrthonormalBasis 𝕜 E).repr.trans
    ((stdOrthonormalBasis 𝕜 F).reindex (finCongr hdim.symm)).repr.symm
  let w : ι → E := e₀.symm ∘ v
  have hw : Orthonormal 𝕜 w := hv.comp_linearIsometryEquiv e₀.symm
  let bu := Module.Basis.span hu.linearIndependent
  let bw := Module.Basis.span hw.linearIndependent
  have hspan {z : ι → E} (hz : Orthonormal 𝕜 z) :
      Orthonormal 𝕜 (Module.Basis.span hz.linearIndependent) := by
    convert! orthonormal_span hz using 1
    funext i
    simp [Module.Basis.span_apply]
  have hbu : Orthonormal 𝕜 bu := hspan hu
  have hbw : Orthonormal 𝕜 bw := hspan hw
  let e := hbu.equiv hbw (Equiv.refl ι)
  let L := (Submodule.span 𝕜 (Set.range w)).subtypeₗᵢ.comp e.toLinearIsometry
  let U := LinearIsometryEquiv.ofSurjective L.extend
    (LinearMap.surjective_of_injective L.extend.injective)
  refine ⟨U.trans e₀, fun i ↦ ?_⟩
  have hi := L.extend_apply (bu i)
  change L.extend (bu i) = (e (bu i) : E) at hi
  rw [show e (bu i) = bw i from hbu.equiv_apply hbw (Equiv.refl ι) i] at hi
  have hui : U (u i) = e₀.symm (v i) := by simpa [U, bu, bw, w] using hi
  change e₀ (U (u i)) = v i
  rw [hui, e₀.apply_symm_apply]
