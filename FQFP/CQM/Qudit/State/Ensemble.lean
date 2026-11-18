/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Composite.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Finite ensembles of density states

An ensemble retains both its classical probability distribution and its labelled states.
Its mixture uses the existing density operator representation. Pure ensembles are obtained
from unit vectors; no choice of global phase is made. This adapts the finite ensemble API
of physlib's `QuantumInfo/States/Ensemble` to qudits and Mathlib's probability simplex.

## Main definitions and results

* `Qudit.Ensemble`: a finite probability distribution with a density at each label.
* `Qudit.Ensemble.mix`: the density obtained by forgetting the label.
* `Qudit.Ensemble.ofPure`: ensembles whose component states come from unit vectors.
* `Qudit.Ensemble.mix_tensor`: mixing commutes with tensor products of independent ensembles.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory MonoidalCategory

namespace Qudit

/-- A finite probability distribution together with a density state at each label. -/
@[ext]
structure Ensemble (H : Qudit) (ι : Type*) [Fintype ι] where
  /-- The classical probabilities, allowing zero weights. -/
  distribution : Convexity.StdSimplex ℝ ι
  /-- The state prepared at each label. -/
  state : ι → Density H

namespace Ensemble

noncomputable section

variable {H : Qudit} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The probability of a label. -/
def weight (e : Ensemble H ι) (i : ι) : ℝ := e.distribution.weights i

/-- Every label has nonnegative probability. -/
lemma weight_nonneg (e : Ensemble H ι) (i : ι) : 0 ≤ e.weight i :=
  e.distribution.weights_nonneg i

/-- The total probability is one. -/
@[simp]
lemma sum_weight (e : Ensemble H ι) : ∑ i, e.weight i = 1 :=
  e.distribution.total_of_fintype

/-- Construct an ensemble from a normalized family of real probabilities. -/
def ofWeights (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ρ : ι → Density H) : Ensemble H ι where
  distribution :=
    { weights := Finsupp.equivFunOnFinite.symm w
      nonneg i := by simpa using hw i
      total := by simpa [Finsupp.sum_fintype] using hs }
  state := ρ

/-- Forget the classical label and form the density mixture. -/
def mix (e : Ensemble H ι) : Density H :=
  Density.mixture e.weight e.weight_nonneg e.sum_weight e.state

/-- The operator of an ensemble is its probability-weighted sum. -/
@[simp]
lemma op_mix (e : Ensemble H ι) : e.mix.op = ∑ i, (e.weight i : ℂ) • (e.state i).op := rfl

/-- An ensemble of unit vectors defines an ensemble of pure density states. -/
def ofPure (w : Convexity.StdSimplex ℝ ι) (v : ι → UnitState H) : Ensemble H ι :=
  ⟨w, fun i => Density.pure (v i)⟩

/-- Pure ensembles are mixtures of outer squares. -/
lemma op_mix_ofPure (w : Convexity.StdSimplex ℝ ι) (v : ι → UnitState H) :
    (ofPure w v).mix.op = ∑ i, (w.weights i : ℂ) • Operator.outer (v i) (v i) := rfl

/-- Mixing basis states acts diagonally, with the probabilities as eigenvalues. -/
lemma op_mix_ofPure_ofBasis_apply (b : OrthonormalBasis ι ℂ H.state)
    (p : Convexity.StdSimplex ℝ ι) (i : ι) :
    (ofPure p (UnitState.ofBasis b)).mix.op (b i) = (p.weights i : ℂ) • b i := by
  classical
  simp only [op_mix_ofPure, LinearMap.sum_apply, LinearMap.smul_apply,
    UnitState.coe_ofBasis, Operator.outer_apply, b.inner_eq_ite]
  simp

/-- Relabel an ensemble by an equivalence, without changing its probabilities. -/
def reindex (e : Ensemble H ι) (f : κ ≃ ι) : Ensemble H κ :=
  ofWeights (fun j => e.weight (f j)) (fun j => e.weight_nonneg (f j))
    ((Equiv.sum_comp f e.weight).trans e.sum_weight) (fun j => e.state (f j))

/-- A bijective relabelling does not change the density mixture. -/
@[simp]
lemma mix_reindex (e : Ensemble H ι) (f : κ ≃ ι) : (e.reindex f).mix = e.mix := by
  apply Density.ext
  exact Equiv.sum_comp f (fun i => (e.weight i : ℂ) • (e.state i).op)

/-- Expectations commute with forgetting the classical label. -/
lemma expectation_mix (e : Ensemble H ι) (A : Operator H) :
    e.mix.expectation A = ∑ i, e.weight i * (e.state i).expectation A :=
  Density.expectation_mixture _ _ _ _ _

/-- Mixing a constant family returns that state, including when some weights vanish. -/
lemma mix_const (w : Convexity.StdSimplex ℝ ι) (ρ : Density H) :
    (Ensemble.mk w (fun _ => ρ)).mix = ρ := by
  apply Density.ext
  simp only [op_mix, weight, ← Finset.sum_smul, ← Complex.ofReal_sum, w.total_of_fintype,
    Complex.ofReal_one, one_smul]

/-- Independent preparation of two ensembles, retaining both classical labels. -/
def tensor {K : Qudit} (e : Ensemble H ι) (f : Ensemble K κ) : Ensemble (H ⊗ K) (ι × κ) :=
  ofWeights (fun i => e.weight i.1 * f.weight i.2)
    (fun i => mul_nonneg (e.weight_nonneg i.1) (f.weight_nonneg i.2))
    (by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, sum_weight, mul_one])
    (fun i => (e.state i.1).tensor (f.state i.2))

/-- Forgetting the two independent labels gives the product of the two mixtures. -/
lemma mix_tensor {K : Qudit} (e : Ensemble H ι) (f : Ensemble K κ) :
    (e.tensor f).mix = e.mix.tensor f.mix := by
  apply Density.ext
  change (∑ i : ι × κ, ((e.weight i.1 * f.weight i.2 : ℝ) : ℂ) •
    TensorProduct.map (e.state i.1).op (f.state i.2).op) =
      TensorProduct.map (∑ i, (e.weight i : ℂ) • (e.state i).op)
        (∑ j, (f.weight j : ℂ) • (f.state j).op)
  change _ = TensorProduct.mapBilinear _ _ _ _ _
    (∑ i, (e.weight i : ℂ) • (e.state i).op) (∑ j, (f.weight j : ℂ) • (f.state j).op)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul, Fintype.sum_prod_type, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]
  rfl

end

end Ensemble

end Qudit
