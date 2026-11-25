/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for POVMs and the outcome distribution.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Measurements/POVM.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Density
public import FQFP.CQM.Qudit.Measurement.Basic
public import FQFP.CQM.Category.ProjectiveMeasurement

/-!
# Finite positive operator-valued measurements

A `POVM H ι` is a finite family of positive operators summing to the identity.
Its mixed-state Born probabilities are real, nonnegative and sum to one.
Orthonormal and computational basis measurements recover the existing categorical
Born scalars on pure states. Operator effects here are distinct from amplitude
effects `CategoryTheory.MonoidalCategory.Effect`; their `Complete` predicate is unchanged.

The mathematical convention is Watrous, *The Theory of Quantum Information*,
Definition 2.34 and equations (2.199)-(2.201). The corresponding upstream definitions
are physlib's `POVM` and `POVM.measure` at commit
`76e1b4f0171d27a0d35334a633263a40ecf24fd5`. This implementation uses FQFP operators
and Mathlib positivity directly. A POVM specifies outcome probabilities, not an instrument.

## Main definitions and results

* `Qudit.POVM`: finite positive operator-valued measurements summing to the identity.
* `Qudit.POVM.probability`: Born probabilities for density states.
* `Qudit.POVM.ofBasis`: the projective POVM of an orthonormal basis.
* `Qudit.POVM.sum_probability`: outcome probabilities sum to one.
-/

@[expose] public section

open CategoryTheory
open scoped ComplexOrder BigOperators

namespace Qudit

/-- A finite family of positive operator effects resolving the identity. -/
@[ext]
structure POVM (H : Qudit) (ι : Type*) [Fintype ι] where
  /-- The operator associated with each outcome. -/
  op : ι → Operator H
  /-- Every outcome operator is positive, including self-adjointness. -/
  positive : ∀ i, (op i).IsPositive
  /-- The outcome operators sum to the identity. -/
  sum_op : ∑ i, op i = 1

namespace POVM

noncomputable section

variable {H : Qudit} {ι : Type*} [Fintype ι]

/-- Every projection-valued measure is a POVM with the same outcome operators (§0.3.4). -/
def ofOrthogonalResolution (P : OrthogonalResolution H ι) : POVM H ι where
  op i := (P.proj i).hom
  positive i := hom_isPositive_of_isPositive (P.isPositive i)
  sum_op := by
    change ∑ i, (P.proj i).hom = LinearMap.id
    rw [← hom_sum, P.sum_proj, hom_id]

/-- The projection-valued measure associated to an orthonormal basis (Lemma 0.62). -/
def basisResolution (b : OrthonormalBasis ι ℂ H.state) : OrthogonalResolution H ι :=
  CQM.projectiveMeasurementOfEffects (fun i ↦ braArrow (b i))
    (disjoint_braArrow_orthonormalBasis b) (by simpa using sum_braArrow_comp_ketArrow b)

/-- Each basis projection is the outer square of its basis vector. -/
lemma hom_basisResolution_proj (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    ((basisResolution b).proj i).hom = Operator.outer (b i) (b i) := by
  change (braArrow (b i) ≫ (braArrow (b i))†).hom = _
  rw [braArrow_dagger]
  rfl

/-- A basis measurement is nondegenerate in the sense of Definition 0.61. -/
theorem trace_basisResolution_proj (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    Operator.trace ((basisResolution b).proj i).hom = 1 := by
  rw [hom_basisResolution_proj, Operator.trace_outer, b.inner_eq_one]

/-- Each outcome operator is nonnegative in the Loewner order. -/
lemma op_nonneg (M : POVM H ι) (i : ι) : 0 ≤ M.op i :=
  LinearMap.nonneg_iff_isPositive.mpr (M.positive i)

/-- Normalization bounds every individual operator effect by the identity. -/
lemma op_le_one (M : POVM H ι) (i : ι) : M.op i ≤ 1 := by
  rw [← M.sum_op]
  exact Finset.single_le_sum (fun j _ => M.op_nonneg j) (Finset.mem_univ i)

/-- The mixed-state Born probability of an outcome. -/
def probability (M : POVM H ι) (ρ : Density H) (i : ι) : ℝ :=
  ρ.expectation (M.op i)

/-- The complex trace pairing is exactly the real Born probability. -/
lemma probability_eq_trace (M : POVM H ι) (ρ : Density H) (i : ι) :
    (M.probability ρ i : ℂ) = (M.op i * ρ.op).trace := by
  apply Complex.ext
  · rfl
  · exact (ρ.expectationComplex_im_eq_zero (M.positive i).isSelfAdjoint).symm

/-- Born probabilities are nonnegative. -/
lemma probability_nonneg (M : POVM H ι) (ρ : Density H) (i : ι) :
    0 ≤ M.probability ρ i := ρ.expectation_nonneg (M.positive i)

/-- Born probabilities are at most one. -/
lemma probability_le_one (M : POVM H ι) (ρ : Density H) (i : ι) :
    M.probability ρ i ≤ 1 := ρ.expectation_le_one (M.op_le_one i)

/-- A finite POVM produces a normalized probability distribution on every density state. -/
lemma sum_probability (M : POVM H ι) (ρ : Density H) : ∑ i, M.probability ρ i = 1 := by
  simp only [probability, ← Density.expectation_sum, M.sum_op, Density.expectation_one]

/-- Born probabilities respect convex mixing of input states. -/
lemma probability_mix (M : POVM H ι) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ σ : Density H) (i : ι) :
    M.probability (Density.mix p hp₀ hp₁ ρ σ) i =
      p * M.probability ρ i + (1 - p) * M.probability σ i :=
  Density.expectation_mix p hp₀ hp₁ ρ σ (M.op i)

/-- Born probabilities respect arbitrary finite probabilistic mixtures. -/
lemma probability_mixture {κ : Type*} [Fintype κ] (M : POVM H ι)
    (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (ρ : κ → Density H) (i : ι) :
    M.probability (Density.mixture w hw hsum ρ) i = ∑ j, w j * M.probability (ρ j) i :=
  Density.expectation_mixture w hw hsum ρ (M.op i)

/-- On a pure input, the Born trace reduces to the vector expectation. -/
lemma probability_pure (M : POVM H ι) (v : UnitState H) (i : ι) :
    M.probability (Density.pure v) i = (inner ℂ (v : H.state) (M.op i v)).re :=
  Density.expectation_pure v (M.op i)

/-- For a pure input the POVM probability is the categorical Born weight of the
unnormalized projected state. This includes projections onto degenerate eigenspaces. -/
theorem probability_ofOrthogonalResolution_pure (P : OrthogonalResolution H ι)
    (v : UnitState H) (i : ι) :
    (ofOrthogonalResolution P).probability (Density.pure v) i =
      (scalarRingEquiv (CQM.overlap
        (ketArrow v.val ≫ P.proj i) (ketArrow v.val ≫ P.proj i))).re := by
  rw [probability_pure, CQM.overlap_comp_proj, ketArrow_dagger]
  change _ = (inner ℂ v.val ((P.proj i) ((1 : ℂ) • v.val))).re
  rw [one_smul]
  rfl

/-- The binary projective measurement testing membership in a subspace.
The outcome `true` corresponds to the projection onto `S`. -/
def ofSubmodule (S : Submodule ℂ H.state) : POVM H Bool where
  op b := if b then S.starProjection.toLinearMap else 1 - S.starProjection.toLinearMap
  positive := by
    intro b
    cases b
    · change (1 - S.starProjection.toLinearMap).IsPositive
      have h := Sᗮ.isSymmetricProjection_starProjection.isPositive
      rwa [S.starProjection_orthogonal'] at h
    · exact S.isSymmetricProjection_starProjection.isPositive
  sum_op := by simp

/-- The projective POVM associated with any explicit orthonormal basis. -/
def ofBasis (b : OrthonormalBasis ι ℂ H.state) : POVM H ι where
  op i := Operator.outer (b i) (b i)
  positive i := Operator.isPositive_outer (b i)
  sum_op := by
    simpa only [ofOrthogonalResolution, hom_basisResolution_proj] using
      (ofOrthogonalResolution (basisResolution b)).sum_op

/-- Interpreting the basis resolution recovers the existing basis POVM. -/
lemma ofOrthogonalResolution_basisResolution (b : OrthonormalBasis ι ℂ H.state) :
    ofOrthogonalResolution (basisResolution b) = ofBasis b := by
  apply POVM.ext
  funext i
  exact hom_basisResolution_proj b i

/-- The computational basis POVM, including the empty basis in dimension zero. -/
def computational (n : ℕ) : POVM (std n) (Fin n) := ofBasis (ZBasis n)

/-- A basis outcome reads the corresponding diagonal matrix coefficient of a density. -/
lemma probability_ofBasis (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H) (i : ι) :
    (ofBasis b).probability ρ i = (inner ℂ (b i) (ρ.op (b i))).re := by
  change (Operator.trace (Operator.outer (b i) (b i) * ρ.op)).re = _
  rw [Operator.trace, LinearMap.trace_mul_comm]
  exact congrArg Complex.re (Operator.trace_mul_outer ρ.op (b i) (b i))

/-- In orthonormal coordinates, basis probabilities are the real diagonal entries. -/
lemma probability_ofBasis_eq_toMatrix [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H) (i : ι) :
    (ofBasis b).probability ρ i = (ρ.toMatrix b i i).re := by
  rw [probability_ofBasis, Density.toMatrix, LinearMap.toMatrixOrthonormal_apply_apply]

/-- Pure-state basis probabilities are squared inner-product amplitudes. -/
lemma probability_ofBasis_pure (b : OrthonormalBasis ι ℂ H.state)
    (v : UnitState H) (i : ι) :
    (ofBasis b).probability (Density.pure v) i = ‖inner ℂ (b i) (v : H.state)‖ ^ 2 := by
  rw [probability_pure]
  change (inner ℂ (v : H.state) (Operator.outer (b i) (b i) v)).re = _
  simp only [Operator.outer_apply, inner_smul_right]
  rw [← inner_conj_symm v.val (b i), Complex.mul_conj']
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- The new Born probabilities recover the existing categorical amplitude measurement. -/
lemma probability_ofBasis_pure_eq_scalar (b : OrthonormalBasis ι ℂ H.state)
    (v : UnitState H) (i : ι) :
    ((ofBasis b).probability (Density.pure v) i : ℂ) =
      scalarRingEquiv (MonoidalCategory.probability (ketArrow v.val) (braArrow (b i))) := by
  rw [probability_ofBasis_pure, scalarRingEquiv_probability_ketArrow_braArrow]
  exact Complex.ofReal_pow _ _

/-- Computational-basis measurement is normalized for arbitrary mixed inputs. -/
lemma sum_probability_computational (n : ℕ) (ρ : Density (std n)) :
    ∑ i, (computational n).probability ρ i = 1 := (computational n).sum_probability ρ

end

end POVM

end Qudit
