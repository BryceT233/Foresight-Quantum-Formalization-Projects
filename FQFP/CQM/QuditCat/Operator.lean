/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.QuditCat.Dagger
public import FQFP.Analysis.InnerProductSpace.PositiveTrace

/-!
# Operators on a qudit

`Operator H` uses Mathlib's linear endomorphisms, with their existing algebra, adjoint
and positivity APIs. The category-to-operator bridge is `Hom.hom` in one direction and
`ofHom` in the other. `outer v w` is the linear map `x ↦ inner ℂ w x • v`.
Its trace is `inner ℂ w v`, and `outer v v` is positive without any normalization assumption.

Coordinates use Mathlib's `LinearMap.toMatrixOrthonormal`; no second matrix algebra is defined.
-/

@[expose] public section

open CategoryTheory CategoryTheory.DaggerCategory
open scoped ComplexOrder

namespace QuditCat

/-- The algebra of linear operators on a qudit. -/
abbrev Operator (H : QuditCat) := Module.End ℂ H.state

namespace Operator

variable {H : QuditCat}

/-- The basis-independent complex trace. -/
noncomputable abbrev trace (A : Operator H) : ℂ := LinearMap.trace ℂ H.state A

/-- The outer product `∣v⟩⟨w∣`, allowing unnormalized vectors. -/
noncomputable def outer (v w : H.state) : Operator H := (bra w).smulRight v

/-- An outer product acts by an inner product followed by scalar multiplication. -/
@[simp]
lemma outer_apply (v w x : H.state) : outer v w x = inner ℂ w x • v := rfl

/-- An outer product is the composite of a bra followed by a ket. -/
lemma outer_eq_ket_comp_bra (v w : H.state) : outer v w = ket v ∘ₗ bra w := rfl

/-- The adjoint of an outer product exchanges its vectors. -/
@[simp]
lemma adjoint_outer (v w : H.state) : (outer v w).adjoint = outer w v := by
  simp only [outer_eq_ket_comp_bra, LinearMap.adjoint_comp,
    bra, ket, LinearMap.adjoint_innerₛₗ_apply, LinearMap.adjoint_toSpanSingleton]

/-- The trace of an outer product is the corresponding inner product. -/
@[simp]
lemma trace_outer (v w : H.state) : (outer v w).trace = inner ℂ w v :=
  LinearMap.trace_smulRight (bra w) v

/-- The outer square of any vector is positive. -/
lemma isPositive_outer (v : H.state) : (outer v v).IsPositive := by
  rw [outer_eq_ket_comp_bra]
  have h : (ket v).adjoint = bra v := LinearMap.adjoint_toSpanSingleton v
  rw [← h]
  exact LinearMap.isPositive_self_comp_adjoint (ket v)

/-- Multiplying an outer product on the left applies the operator to its ket. -/
lemma mul_outer (A : Operator H) (v w : H.state) : A * outer v w = outer (A v) w := by
  ext x
  simp only [Module.End.mul_apply, outer_apply, map_smul]

/-- The trace pairing against an outer product is a matrix coefficient. -/
@[simp]
lemma trace_mul_outer (A : Operator H) (v w : H.state) :
    (A * outer v w).trace = inner ℂ w (A v) := by
  rw [mul_outer, trace_outer]

/-- Scaling both vectors of an outer square scales it by the squared modulus. -/
lemma outer_smul_self (c : ℂ) (v : H.state) :
    outer (c • v) (c • v) = (‖c‖ ^ 2 : ℂ) • outer v v := by
  ext x
  simp only [outer_apply, inner_smul_left, smul_smul, LinearMap.smul_apply]
  congr 1
  calc
    (starRingEnd ℂ c * inner ℂ v x) * c =
        (c * starRingEnd ℂ c) * inner ℂ v x := by ring
    _ = _ := by rw [Complex.mul_conj']

/-- Multiplying a vector by a global phase does not change its outer square. -/
lemma outer_smul_self_of_norm_eq_one (c : ℂ) (hc : ‖c‖ = 1) (v : H.state) :
    outer (c • v) (c • v) = outer v v := by
  rw [outer_smul_self, hc]
  simp

/-- Orthonormal coordinates preserve positivity in both directions. -/
lemma posSemidef_toMatrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) :
    (LinearMap.toMatrixOrthonormal b A).PosSemidef ↔ A.IsPositive :=
  LinearMap.posSemidef_toMatrix_iff b

/-- Orthonormal coordinates preserve the trace. -/
lemma trace_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) :
    (LinearMap.toMatrixOrthonormal b A).trace = A.trace :=
  (LinearMap.trace_eq_matrix_trace ℂ b.toBasis A).symm

/-- The trace of an adjoint is the conjugate trace. -/
lemma trace_adjoint (A : Operator H) : trace A.adjoint = star A.trace := by
  classical
  let b := stdOrthonormalBasis ℂ H.state
  change LinearMap.trace ℂ H.state A.adjoint = star (LinearMap.trace ℂ H.state A)
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis,
    LinearMap.trace_eq_matrix_trace ℂ b.toBasis,
    LinearMap.toMatrix_adjoint b b, Matrix.trace_conjTranspose]

end Operator

end QuditCat
