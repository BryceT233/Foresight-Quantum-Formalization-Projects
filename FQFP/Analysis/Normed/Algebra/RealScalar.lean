/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.UniformRing

/-!
# Real scalars on a complete normed `ℚ`-algebra

A complete normed ring `𝔸` with a `NormedAlgebra ℚ 𝔸` structure carries a `NormedAlgebra ℝ 𝔸`
structure, and that structure is unique.

## Main results

* `normedAlgebraReal` — the `NormedAlgebra ℝ 𝔸` structure, obtained by extending the continuous
  ring homomorphism `algebraMap ℚ 𝔸` along the dense inclusion `ℚ → ℝ`.
* `NormedAlgebra.ext_real` — any two normed real algebra structures on a normed ring agree.
* `realNormedAlgebraUnique` — that structure is unique.

Use `open scoped RealScalar` to synthesize the canonical real structure from the rational
structure and completeness. This opt-in instance has low priority, so an existing real
structure is preferred. Statements elaborated with the canonical structure use its scalar
action; when applying them with another real structure, use `Subsingleton.elim` to identify
the two structures first.

-/

@[expose] public noncomputable section

/-- Two normed real algebra structures on a fixed normed ring are equal. -/
theorem NormedAlgebra.ext_real {𝔸 : Type*} [NormedRing 𝔸] (P Q : NormedAlgebra ℝ 𝔸) : P = Q := by
  have continuousMap (A : NormedAlgebra ℝ 𝔸) : Continuous A.toAlgebra.algebraMap := by
    let := A
    exact continuous_algebraMap ℝ 𝔸
  have hmap := (Rat.denseRange_cast (𝕜 := ℝ)).equalizer (continuousMap P) (continuousMap Q) (by
    change ⇑(P.toAlgebra.algebraMap.comp (Rat.castHom ℝ)) =
      ⇑(Q.toAlgebra.algebraMap.comp (Rat.castHom ℝ))
    exact congrArg (fun f : ℚ →+* 𝔸 => ⇑f) (Subsingleton.elim _ _))
  have hAlg := Algebra.algebra_ext P.toAlgebra Q.toAlgebra (congrFun hmap)
  cases P
  cases Q
  cases hAlg
  rfl

variable (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

private lemma uniformContinuous_algebraMap : UniformContinuous (algebraMap ℚ 𝔸) := by
  have h : ⇑(algebraMap ℚ 𝔸) =
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℚ ℚ) (1 : 𝔸)) := by
    ext q
    simp [Algebra.algebraMap_eq_smul_one]
  exact h ▸ (ContinuousLinearMap.smulRight ..).uniformContinuous

private abbrev realAlgebraMap [CompleteSpace 𝔸] : ℝ →+* 𝔸 :=
  IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (uniformContinuous_algebraMap 𝔸)

private lemma continuous_realAlgebraMap [CompleteSpace 𝔸] : Continuous (realAlgebraMap 𝔸) :=
  (uniformContinuous_uniformly_extend Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.denseRange_cast (uniformContinuous_algebraMap 𝔸)).continuous

private lemma realAlgebraMap_ratCast [CompleteSpace 𝔸] (q : ℚ) :
    realAlgebraMap 𝔸 (q : ℝ) = algebraMap ℚ 𝔸 q :=
  RingHom.congr_fun
    (Subsingleton.elim ((realAlgebraMap 𝔸).comp (Rat.castHom ℝ)) (algebraMap ℚ 𝔸)) q

/-- Extend normed algebras over `ℚ` to normed algebras over `ℝ` on Banach algebras. -/
@[no_expose]
abbrev normedAlgebraReal [CompleteSpace 𝔸] : NormedAlgebra ℝ 𝔸 where
  __ := (realAlgebraMap 𝔸).toAlgebra' fun r x ↦ by
    have h := continuous_realAlgebraMap 𝔸
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r ?_ fun q ↦ ?_
    · exact isClosed_eq (h.mul continuous_const) (continuous_const.mul h)
    · rw [realAlgebraMap_ratCast, Algebra.commutes']
  norm_smul_le r x := by
    change ‖realAlgebraMap 𝔸 r * x‖ ≤ ‖r‖ * ‖x‖
    have h := continuous_realAlgebraMap 𝔸
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r ?_ fun q ↦ ?_
    · exact isClosed_le (h.mul continuous_const).norm (continuous_norm.mul continuous_const)
    · rw [realAlgebraMap_ratCast, ← Algebra.smul_def]
      simpa only [Rat.norm_cast_real] using norm_smul_le q x

namespace RealScalar

attribute [scoped instance 100] normedAlgebraReal

end RealScalar

/-- A complete normed `ℚ`-algebra carries a unique `NormedAlgebra ℝ` structure. -/
noncomputable instance realNormedAlgebraUnique [CompleteSpace 𝔸] :
    Unique (NormedAlgebra ℝ 𝔸) where
  default := normedAlgebraReal 𝔸
  uniq h := h.ext_real (normedAlgebraReal 𝔸)
