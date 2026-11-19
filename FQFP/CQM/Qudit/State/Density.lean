/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/

/-
Physlib reference for density states, pure states, mixtures and expectations.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/MState.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Operator
public import FQFP.CQM.Qudit.State.UnitState

/-!
# Density operators on qudits

A density operator is a positive linear endomorphism with trace one, including singular
operators. This is the coordinate-free counterpart of physlib's `MState`, built directly
from Mathlib rather than importing a second state representation.

Pure states, convex mixtures and expectations are provided here. Positivity retains the
self-adjointness requirement of `LinearMap.IsPositive`. No inhabitant is chosen for every
state space: a zero-dimensional space has no density operators.

## Main definitions

* `Qudit.Density`: positive operators of trace one.
* `Qudit.Density.map`: transport of density operators along isometries.
* `Qudit.Density.mixture`: finite probabilistic mixtures of density operators.
* `Qudit.Density.expectation`: the real expectation of an operator in a density state.
-/

@[expose] public section

open CategoryTheory CategoryTheory.DaggerCategory
open scoped ComplexOrder BigOperators

namespace Qudit

/-- A positive operator of trace one on a finite-dimensional complex Hilbert space. -/
@[ext]
structure Density (H : Qudit) where
  /-- The underlying linear operator. -/
  op : Operator H
  /-- Positivity, including self-adjointness. -/
  positive : op.IsPositive
  /-- The total mass is one. -/
  trace_one : op.trace = 1

namespace Density

noncomputable section

variable {H : Qudit}

attribute [simp] trace_one

/-- A density operator is self-adjoint. -/
@[simp]
lemma adjoint_op (ρ : Density H) : ρ.op.adjoint = ρ.op := ρ.positive.adjoint_eq

/-- A density operator cannot be zero. -/
lemma op_ne_zero (ρ : Density H) : ρ.op ≠ 0 := by
  intro h
  have := ρ.trace_one
  simp [h, Operator.trace] at this

/-- There are no density operators on a zero-dimensional state space. -/
instance [Subsingleton H.state] : IsEmpty (Density H) :=
  ⟨fun ρ => ρ.op_ne_zero (Subsingleton.elim _ _)⟩

/-- A unit vector determines its pure density operator. -/
def pure (v : UnitState H) : Density H where
  op := Operator.outer v v
  positive := Operator.isPositive_outer (H := H) v.val
  trace_one := by rw [Operator.trace_outer]; exact v.inner_self

/-- The operator underlying a pure state. -/
@[simp]
lemma op_pure (v : UnitState H) : (pure v).op = Operator.outer v v := rfl

/-- A pure state acts by its rank-one outer product. -/
@[simp]
lemma pure_apply (v : UnitState H) (x : H.state) :
    (pure v).op x = inner ℂ (v : H.state) x • (v : H.state) := rfl

/-- A pure density operator is an idempotent operator. -/
lemma pure_mul_self (v : UnitState H) : (pure v).op * (pure v).op = (pure v).op := by
  ext x
  simp

/-- Pure density operators are invariant under global phase. -/
@[simp]
lemma pure_phase (c : ℂ) (hc : ‖c‖ = 1) (v : UnitState H) :
    pure (v.phase c hc) = pure v := by
  apply Density.ext
  exact Operator.outer_smul_self_of_norm_eq_one (H := H) c hc v.val

/-- Isometric evolution of a density operator, including unitary evolution. -/
def map {K : Qudit} (f : H ⟶ K) [IsIsometry f] (ρ : Density H) : Density K where
  op := f.hom ∘ₗ ρ.op ∘ₗ f.hom.adjoint
  positive := ρ.positive.conj_adjoint f.hom
  trace_one := by
    rw [Operator.trace, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    rw [hom_adjoint_comp_of_isIsometry, LinearMap.comp_id]
    exact ρ.trace_one

/-- The operator of an isometric image is the conjugated operator. -/
@[simp]
lemma op_map {K : Qudit} (f : H ⟶ K) [IsIsometry f] (ρ : Density H) :
    (map f ρ).op = f.hom ∘ₗ ρ.op ∘ₗ f.hom.adjoint := rfl

/-- An isometrically transported density intertwines with the original operator. -/
lemma op_map_apply {K : Qudit} (ρ : Density H) (U : H ⟶ K) [IsIsometry U] (v : H.state) :
    (ρ.map U).op (U.hom v) = U.hom (ρ.op v) := by
  change U.hom (ρ.op (U.hom.adjoint (U.hom v))) = _
  rw [hom_adjoint_apply_of_isIsometry]

/-- Pure-state embedding commutes with isometric evolution. -/
lemma map_pure {K : Qudit} (f : H ⟶ K) [IsIsometry f] (v : UnitState H) :
    (pure v).map f = pure (v.map f) := by
  apply Density.ext
  ext x
  simp only [op_map, op_pure, LinearMap.comp_apply, Operator.outer_apply,
    map_smul, UnitState.coe_map, LinearMap.adjoint_inner_right]

/-- A convex combination of two density operators. -/
def mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ρ σ : Density H) : Density H where
  op := (p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • σ.op
  positive := (ρ.positive.smul_of_nonneg (by exact_mod_cast hp₀)).add
    (σ.positive.smul_of_nonneg (by exact_mod_cast sub_nonneg.mpr hp₁))
  trace_one := by simp [Operator.trace, map_add, map_smul, ρ.trace_one, σ.trace_one]

/-- The operator of a convex combination. -/
@[simp]
lemma op_mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ρ σ : Density H) :
    (mix p hp₀ hp₁ ρ σ).op = (p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • σ.op := rfl

/-- Weight zero selects the second state. -/
@[simp]
lemma mix_zero (ρ σ : Density H) : mix 0 (by positivity) (by norm_num) ρ σ = σ := by
  ext
  simp

/-- Weight one selects the first state. -/
@[simp]
lemma mix_one (ρ σ : Density H) : mix 1 (by positivity) (by norm_num) ρ σ = ρ := by
  ext
  simp

/-- Exchanging the states complements the mixing probability. -/
lemma mix_comm (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ρ σ : Density H) :
    mix p hp₀ hp₁ ρ σ = mix (1 - p) (sub_nonneg.mpr hp₁) (by linarith) σ ρ := by
  apply Density.ext
  simp only [op_mix, sub_sub_cancel, add_comm]

/-- A finite probabilistic mixture of density operators. -/
def mixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (ρ : ι → Density H) : Density H where
  op := ∑ i, (w i : ℂ) • (ρ i).op
  positive := LinearMap.isPositive_sum _ fun i _ =>
    (ρ i).positive.smul_of_nonneg (by exact_mod_cast hw i)
  trace_one := by
    simp only [map_sum, map_smul, trace_one, smul_eq_mul,
      mul_one, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]

/-- The operator of a finite mixture is its weighted sum. -/
@[simp]
lemma op_mixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (ρ : ι → Density H) :
    (mixture w hw hsum ρ).op = ∑ i, (w i : ℂ) • (ρ i).op := rfl

/-- A two-label probability mixture agrees with binary mixing, including both endpoints. -/
lemma mixture_fin_two (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ρ σ : Density H) :
    mixture ![p, 1 - p] (by
      intro i
      fin_cases i
      · exact hp₀
      · exact sub_nonneg.mpr hp₁) (by simp) ![ρ, σ] = mix p hp₀ hp₁ ρ σ := by
  apply Density.ext
  simp only [op_mixture, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, op_mix]

/-- The operator of a finite mixture, expressed using the real scalar action. -/
lemma op_mixture_real {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (ρ : ι → Density H) :
    (mixture w hw hs ρ).op = ∑ i, w i • (ρ i).op := by
  rw [op_mixture]
  apply Finset.sum_congr rfl
  intro i _
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (w i) _).symm

/-- The complex trace pairing of an observable with a density operator. -/
def expectationComplex (ρ : Density H) (A : Operator H) : ℂ := (A * ρ.op).trace

/-- The real expectation of an observable, defined on all operators by taking real part. -/
def expectation (ρ : Density H) (A : Operator H) : ℝ := (ρ.expectationComplex A).re

/-- For a self-adjoint observable the complex expectation is real. -/
lemma expectationComplex_im_eq_zero (ρ : Density H) {A : Operator H}
    (hA : IsSelfAdjoint A) : (ρ.expectationComplex A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star (A * ρ.op).trace = (A * ρ.op).trace
  rw [← Operator.trace_adjoint]
  change Operator.trace (A ∘ₗ ρ.op).adjoint = (A * ρ.op).trace
  rw [LinearMap.adjoint_comp, ρ.adjoint_op, show A.adjoint = A from hA]
  exact LinearMap.trace_mul_comm ℂ _ _

/-- The expectation in a pure state is its vector matrix coefficient. -/
@[simp]
lemma expectationComplex_pure (v : UnitState H) (A : Operator H) :
    (pure v).expectationComplex A = inner ℂ (v : H.state) (A v) :=
  Operator.trace_mul_outer A v v

/-- The real expectation in a pure state. -/
@[simp]
lemma expectation_pure (v : UnitState H) (A : Operator H) :
    (pure v).expectation A = (inner ℂ (v : H.state) (A v)).re := by
  rw [expectation, expectationComplex_pure]

/-- The identity observable has expectation one. -/
@[simp]
lemma expectationComplex_one (ρ : Density H) : ρ.expectationComplex 1 = 1 := by
  simpa only [expectationComplex, one_mul] using ρ.trace_one

/-- The identity observable has real expectation one. -/
@[simp]
lemma expectation_one (ρ : Density H) : ρ.expectation 1 = 1 := by
  simp [expectation]

/-- Expectation is additive in the observable. -/
@[simp]
lemma expectation_add (ρ : Density H) (A B : Operator H) :
    ρ.expectation (A + B) = ρ.expectation A + ρ.expectation B := by
  simp [expectation, expectationComplex, Operator.trace, add_mul]

/-- Expectation commutes with finite sums of observables. -/
lemma expectation_sum {ι : Type*} (ρ : Density H) (s : Finset ι) (A : ι → Operator H) :
    ρ.expectation (∑ i ∈ s, A i) = ∑ i ∈ s, ρ.expectation (A i) := by
  simp [expectation, expectationComplex, Operator.trace, Finset.sum_mul]

/-- Expectation respects subtraction of observables. -/
@[simp]
lemma expectation_sub (ρ : Density H) (A B : Operator H) :
    ρ.expectation (A - B) = ρ.expectation A - ρ.expectation B := by
  simp [expectation, expectationComplex, Operator.trace, sub_mul]

/-- Expectation is homogeneous for real scalars. -/
@[simp]
lemma expectation_smul (ρ : Density H) (r : ℝ) (A : Operator H) :
    ρ.expectation (r • A) = r * ρ.expectation A := by
  simp [expectation, expectationComplex, Operator.trace]

/-- Expectation commutes with finite probabilistic mixing. -/
lemma expectation_mixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (ρ : ι → Density H) (A : Operator H) :
    (mixture w hw hsum ρ).expectation A = ∑ i, w i * (ρ i).expectation A := by
  simp [expectation, expectationComplex, Operator.trace, Finset.mul_sum]

/-- The expectation of a positive observable is nonnegative. -/
lemma expectation_nonneg (ρ : Density H) {A : Operator H} (hA : A.IsPositive) :
    0 ≤ ρ.expectation A :=
  (Complex.nonneg_iff.mp (hA.trace_mul_nonneg ρ.positive)).1

/-- An observable bounded above by the identity has expectation at most one. -/
lemma expectation_le_one (ρ : Density H) {A : Operator H} (hA : A ≤ 1) :
    ρ.expectation A ≤ 1 := by
  have h := ρ.expectation_nonneg (LinearMap.le_def.mp hA)
  simpa only [expectation_sub, expectation_one, sub_nonneg] using h

/-- An operator effect has an expectation in the unit interval. -/
lemma expectation_mem_Icc (ρ : Density H) {A : Operator H} (h₀ : 0 ≤ A) (h₁ : A ≤ 1) :
    ρ.expectation A ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ρ.expectation_nonneg (LinearMap.nonneg_iff_isPositive.mp h₀), ρ.expectation_le_one h₁⟩

/-- Taking an expectation commutes with a convex mixture. -/
lemma expectation_mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ σ : Density H) (A : Operator H) :
    (mix p hp₀ hp₁ ρ σ).expectation A =
      p * ρ.expectation A + (1 - p) * σ.expectation A := by
  simp [expectation, expectationComplex, Operator.trace, mul_add]

/-- The coordinate matrix of a density operator in an explicit orthonormal basis. -/
def toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Density H) (b : OrthonormalBasis ι ℂ H.state) : Matrix ι ι ℂ :=
  LinearMap.toMatrixOrthonormal b ρ.op

/-- Every orthonormal coordinate matrix of a density operator is positive semidefinite. -/
lemma posSemidef_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Density H) (b : OrthonormalBasis ι ℂ H.state) : (ρ.toMatrix b).PosSemidef :=
  (Operator.posSemidef_toMatrix_iff b ρ.op).mpr ρ.positive

/-- Every orthonormal coordinate matrix of a density operator has trace one. -/
@[simp]
lemma trace_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Density H) (b : OrthonormalBasis ι ℂ H.state) : (ρ.toMatrix b).trace = 1 := by
  rw [toMatrix, Operator.trace_toMatrix, ρ.trace_one]

/-- Build a density operator from a PSD trace-one matrix in an orthonormal basis. -/
def ofMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (htr : M.trace = 1) : Density H where
  op := (LinearMap.toMatrixOrthonormal b).symm M
  positive := (Operator.posSemidef_toMatrix_iff b _).mp (by simpa using hM)
  trace_one := by
    rw [← Operator.trace_toMatrix b]
    simpa using htr

/-- Reading the matrix used to construct a density operator returns that matrix. -/
@[simp]
lemma toMatrix_ofMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (htr : M.trace = 1) :
    (ofMatrix b M hM htr).toMatrix b = M :=
  (LinearMap.toMatrixOrthonormal b).apply_symm_apply M

/-- Reconstruction from any orthonormal coordinate matrix returns the original density. -/
@[simp]
lemma ofMatrix_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H) :
    ofMatrix b (ρ.toMatrix b) (ρ.posSemidef_toMatrix b) (ρ.trace_toMatrix b) = ρ := by
  apply Density.ext
  exact (LinearMap.toMatrixOrthonormal b).symm_apply_apply ρ.op

end

end Density

end Qudit
