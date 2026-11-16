/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Extending maps with equal Gram forms

Two linear maps with the same inner products differ by an isometric embedding of their
codomains whenever the target codomain is large enough.

## Main results

* `LinearMap.exists_linearIsometry_comp_eq` factors maps with equal Gram forms through an isometric
  embedding when the codomain dimensions allow it.
-/

@[expose] public section

noncomputable section

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G]

/-- Equal Gram forms give an isometry between the images, extended to the whole codomain. -/
lemma LinearMap.exists_linearIsometry_comp_eq (f : G →ₗ[𝕜] E) (g : G →ₗ[𝕜] F)
    (h : ∀ x y, inner 𝕜 (f x) (f y) = inner 𝕜 (g x) (g y))
    (hdim : Module.finrank 𝕜 E ≤ Module.finrank 𝕜 F) :
    ∃ V : E →ₗᵢ[𝕜] F, V.toLinearMap ∘ₗ f = g := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
    rw [← h, LinearMap.mem_ker.mp hx, inner_zero_left]
  let l := (f.ker.liftQ g hker).comp f.quotKerEquivRange.symm.toLinearMap
  have hl (x : G) : l (f.rangeRestrict x) = g x := by
    change (f.ker.liftQ g hker) (f.quotKerEquivRange.symm ⟨f x, _⟩) = g x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let L : f.range →ₗᵢ[𝕜] F := l.isometryOfInner (by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    change inner 𝕜 (l (f.rangeRestrict x)) (l (f.rangeRestrict y)) = inner 𝕜 (f x) (f y)
    rw [hl, hl, h])
  let b := stdOrthonormalBasis 𝕜 f.range
  let J : E →ₗᵢ[𝕜] F := LinearIsometry.ofFinrankLE hdim
  have hb := b.orthonormal.comp_linearIsometry (J.comp f.range.subtypeₗᵢ)
  have hc := b.orthonormal.comp_linearIsometry L
  obtain ⟨U, hU⟩ := hb.exists_linearIsometryEquiv hc rfl
  refine ⟨U.toLinearIsometry.comp J, ?_⟩
  have he : U.toLinearMap ∘ₗ J.toLinearMap ∘ₗ f.range.subtype = l := by
    apply b.toBasis.ext
    exact hU
  ext x
  exact (LinearMap.congr_fun he (f.rangeRestrict x)).trans (hl x)

end
