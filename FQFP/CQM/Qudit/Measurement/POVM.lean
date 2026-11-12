/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Density
public import FQFP.CQM.Qudit.Measurement.Basic

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

/-- The projective POVM associated with any explicit orthonormal basis. -/
def ofBasis (b : OrthonormalBasis ι ℂ H.state) : POVM H ι where
  op i := Operator.outer (b i) (b i)
  positive i := Operator.isPositive_outer (b i)
  sum_op := by
    ext x
    simpa only [LinearMap.sum_apply, Operator.outer_apply, Module.End.one_apply]
      using b.sum_repr' x

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
