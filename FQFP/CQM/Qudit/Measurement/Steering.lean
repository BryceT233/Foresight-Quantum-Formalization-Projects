/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Measurement.POVM
public import FQFP.CQM.Qudit.State.Purification.Minimal
public import FQFP.CQM.Qudit.State.Ensemble
public import FQFP.CQM.Qudit.State.Purification.Mixture
public import FQFP.Analysis.InnerProductSpace.TraceNorm

/-!
# Auxiliary measurements and finite pure ensembles

Measuring the auxiliary half of a purification gives unnormalized states on the retained
system. These depend only on the POVM effects. Finite pure ensembles are characterized
by such measurements on the minimal purification (the Hughston-Jozsa-Wootters theorem).
Zero weights are retained; conditional states are asserted only at positive probability.

## Main definitions and results

* `Qudit.Density.steeringMap`: auxiliary effects mapped to unnormalized retained operators.
* `Qudit.POVM.steeredState`: the retained state conditioned on an outcome of positive probability.
* `Qudit.Density.exists_rankOne_povm_of_ensemble`: realization by rank-at-most-one auxiliary
  effects.
* `Qudit.Density.mix_ofPure_eq_iff_exists_povm`: the finite pure-ensemble HJW characterization.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct BigOperators ComplexOrder

namespace Qudit

noncomputable section

variable {H K L : Qudit} {ι : Type*} [Fintype ι]

namespace UnitState

/-- Contract the auxiliary leg of a bipartite vector against a specified vector. -/
def contractRight (ψ : UnitState (H ⊗ K)) (a : K.state) : H.state :=
  ((TensorProduct.mk ℂ H.state K.state).flip a).adjoint ψ.val

/-- Inner products characterize contraction on the right tensor factor. -/
lemma inner_contractRight (ψ : UnitState (H ⊗ K)) (a : K.state) (x : H.state) :
    inner ℂ x (ψ.contractRight a) = inner ℂ (x ⊗ₜ[ℂ] a) ψ.val :=
  LinearMap.adjoint_inner_right _ _ _

/-- Contraction after an auxiliary isometry pulls its argument back by the adjoint. -/
lemma contractRight_map_isometry (ψ : UnitState (H ⊗ K)) (V : K ⟶ L) [IsIsometry V]
    (a : L.state) : (ψ.map (𝟙 H ⊗ₘ V)).contractRight a = ψ.contractRight (V† a) := by
  apply ext_inner_left ℂ
  intro x
  rw [inner_contractRight, inner_contractRight]
  change inner ℂ (x ⊗ₜ[ℂ] a) ((𝟙 H ⊗ₘ V).hom ψ.val) = _
  rw [hom_tensorHom, hom_id, ← LinearMap.adjoint_inner_left, TensorProduct.adjoint_map,
    TensorProduct.map_tmul, LinearMap.adjoint_id, LinearMap.id_apply]
  rfl

end UnitState

namespace POVM

/-- Pull a POVM back along an isometry by compressing each effect. -/
def comap (M : POVM L ι) (V : K ⟶ L) [IsIsometry V] : POVM K ι where
  op i := V.hom.adjoint ∘ₗ M.op i ∘ₗ V.hom
  positive i := (M.positive i).adjoint_conj V.hom
  sum_op := by
    ext x
    have h := congrArg (fun A : Operator L => V.hom.adjoint (A (V.hom x))) M.sum_op
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, one_apply_eq_self,
      hom_id, LinearMap.id_apply]
      using h.trans (hom_adjoint_apply_of_isIsometry V x)

/-- Pulling back a basis effect gives the outer square of the pulled-back basis vector. -/
lemma op_comap_ofBasis (b : OrthonormalBasis ι ℂ L.state) (V : K ⟶ L) [IsIsometry V]
    (i : ι) : ((ofBasis b).comap V).op i = Operator.outer (V† (b i)) (V† (b i)) := by
  ext x
  simp only [comap, ofBasis, LinearMap.comp_apply, Operator.outer_apply, map_smul]
  rw [← LinearMap.adjoint_inner_left]
  rfl

end POVM

namespace Density

/-- An auxiliary effect determines the unnormalized state retained after that outcome. -/
def steeringMap (ρ : Density (H ⊗ K)) : Operator K →ₗ[ℂ] Operator H where
  toFun E := Operator.partialTraceRight (Operator.tensor 1 E * ρ.op)
  map_add' E F := by
    simp only [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_add, add_mul]
  map_smul' c E := by
    simp only [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_smul, smul_mul_assoc]
    rfl

/-- The identity auxiliary effect recovers the retained marginal. -/
lemma steeringMap_one (ρ : Density (H ⊗ K)) : ρ.steeringMap 1 = ρ.partialTraceRight.op := by
  change Operator.partialTraceRight (TensorProduct.map LinearMap.id LinearMap.id * ρ.op) = _
  rw [TensorProduct.map_id]
  rfl

/-- A rank-one auxiliary effect is compression by its amplitude map. -/
lemma steeringMap_outer (ρ : Density (H ⊗ K)) (a : K.state) :
    ρ.steeringMap (Operator.outer a a) =
      ((TensorProduct.mk ℂ H.state K.state).flip a).adjoint ∘ₗ ρ.op ∘ₗ
        (TensorProduct.mk ℂ H.state K.state).flip a := by
  let b := stdOrthonormalBasis ℂ K.state
  ext y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (Operator.partialTraceRight
    (TensorProduct.map LinearMap.id (Operator.outer a a) * ρ.op) y) = _
  rw [Operator.inner_partialTraceRight b]
  simp only [mul_apply_eq_comp, LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  have he (z : K.state) :
      inner ℂ (x ⊗ₜ[ℂ] z)
        ((TensorProduct.map LinearMap.id (Operator.outer a a)) (ρ.op (y ⊗ₜ[ℂ] z))) =
      inner ℂ z a * inner ℂ (x ⊗ₜ[ℂ] a) (ρ.op (y ⊗ₜ[ℂ] z)) := by
    rw [← LinearMap.adjoint_inner_left, TensorProduct.adjoint_map,
      LinearMap.adjoint_id, Operator.adjoint_outer, TensorProduct.map_tmul,
      LinearMap.id_apply, Operator.outer_apply, TensorProduct.tmul_smul]
    change inner ℂ ((inner ℂ a z) • (x ⊗ₜ[ℂ] a)) _ = _
    rw [inner_smul_left (x ⊗ₜ[ℂ] a) (ρ.op (y ⊗ₜ[ℂ] z)) (inner ℂ a z),
      inner_conj_symm]
  simp_rw [he]
  have hb := congrArg (fun z => inner ℂ (x ⊗ₜ[ℂ] a) (ρ.op (y ⊗ₜ[ℂ] z))) (b.sum_repr' a)
  simpa only [TensorProduct.tmul_sum, map_sum, inner_sum, TensorProduct.tmul_smul,
    map_smul, inner_smul_right, mul_comm, LinearMap.flip_apply, TensorProduct.mk_apply] using hb

/-- Positive auxiliary effects give positive unnormalized retained states. -/
lemma steeringMap_positive (ρ : Density (H ⊗ K)) {E : Operator K} (hE : E.IsPositive) :
    (ρ.steeringMap E).IsPositive := by
  obtain ⟨a, ha⟩ := Operator.exists_sum_outer_of_isPositive E hE
  rw [ha, map_sum]
  apply LinearMap.isPositive_sum
  intro i _
  rw [steeringMap_outer]
  exact ρ.positive.adjoint_conj _

/-- On a pure bipartite state, a rank-one auxiliary effect produces a contracted outer square. -/
lemma steeringMap_pure_outer (ψ : UnitState (H ⊗ K)) (a : K.state) :
    (pure ψ).steeringMap (Operator.outer a a) =
      Operator.outer (ψ.contractRight a) (ψ.contractRight a) := by
  rw [steeringMap_outer]
  ext x
  simp only [LinearMap.comp_apply, op_pure, UnitState.contractRight,
    Operator.outer_apply (H := H ⊗ K), Operator.outer_apply (H := H),
    map_smul, LinearMap.adjoint_inner_left]

end Density

namespace POVM

/-- The unnormalized retained state for an auxiliary measurement outcome. -/
def steeredOperator (M : POVM K ι) (ρ : Density (H ⊗ K)) (i : ι) : Operator H :=
  ρ.steeringMap (M.op i)

/-- Each steered operator is positive. -/
lemma steeredOperator_positive (M : POVM K ι) (ρ : Density (H ⊗ K)) (i : ι) :
    (M.steeredOperator ρ i).IsPositive := ρ.steeringMap_positive (M.positive i)

/-- Forgetting the auxiliary outcome leaves the retained marginal unchanged. -/
lemma sum_steeredOperator (M : POVM K ι) (ρ : Density (H ⊗ K)) :
    ∑ i, M.steeredOperator ρ i = ρ.partialTraceRight.op := by
  simp only [steeredOperator, ← map_sum, M.sum_op, Density.steeringMap_one]

/-- The branch trace is the existing Born probability on the auxiliary marginal. -/
lemma probability_eq_trace_steeredOperator (M : POVM K ι) (ρ : Density (H ⊗ K)) (i : ι) :
    (M.probability ρ.partialTraceLeft i : ℂ) = (M.steeredOperator ρ i).trace := by
  change _ = (Operator.partialTraceRight (Operator.tensor 1 (M.op i) * ρ.op)).trace
  rw [Operator.trace, LinearMap.trace_partialTraceRight]
  exact (M.probability_eq_trace ρ.partialTraceLeft i).trans
    (ρ.expectationComplex_partialTraceLeft (M.op i))

/-- The normalized retained state conditioned on a positive-probability auxiliary outcome. -/
def steeredState (M : POVM K ι) (ρ : Density (H ⊗ K)) (i : ι)
    (hp : 0 < M.probability ρ.partialTraceLeft i) : Density H :=
  Density.normalize (M.steeredOperator_positive ρ i)
    (M.probability_eq_trace_steeredOperator ρ i).symm (by exact_mod_cast hp.ne')

/-- An auxiliary outcome has zero probability exactly when its retained operator vanishes. -/
lemma probability_eq_zero_iff_steeredOperator_eq_zero (M : POVM K ι)
    (ρ : Density (H ⊗ K)) (i : ι) :
    M.probability ρ.partialTraceLeft i = 0 ↔ M.steeredOperator ρ i = 0 := by
  calc
    _ ↔ (M.steeredOperator ρ i).trace.re = 0 := by
      rw [← M.probability_eq_trace_steeredOperator, Complex.ofReal_re]
    _ ↔ _ := (M.steeredOperator_positive ρ i).re_trace_eq_zero_iff

/-- Impossible auxiliary outcomes have zero unnormalized retained state. -/
lemma steeredOperator_eq_zero_of_probability_eq_zero (M : POVM K ι)
    (ρ : Density (H ⊗ K)) (i : ι) (hp : M.probability ρ.partialTraceLeft i = 0) :
    M.steeredOperator ρ i = 0 :=
  (M.probability_eq_zero_iff_steeredOperator_eq_zero ρ i).mp hp

/-- A branch equal to a weighted density has exactly that Born probability. -/
lemma probability_eq_of_steeredOperator_eq_smul (M : POVM K ι)
    (ρ : Density (H ⊗ K)) (i : ι) (p : ℝ) (σ : Density H)
    (h : M.steeredOperator ρ i = (p : ℂ) • σ.op) :
    M.probability ρ.partialTraceLeft i = p := by
  apply Complex.ofReal_injective
  rw [M.probability_eq_trace_steeredOperator, h, σ.trace_smul_op]

/-- At positive probability, a prescribed weighted branch yields the prescribed density. -/
lemma steeredState_eq_of_steeredOperator_eq_smul (M : POVM K ι)
    (ρ : Density (H ⊗ K)) (i : ι) (p : ℝ) (σ : Density H)
    (h : M.steeredOperator ρ i = (p : ℂ) • σ.op)
    (hp : 0 < M.probability ρ.partialTraceLeft i) : M.steeredState ρ i hp = σ :=
  Density.normalize_eq_of_eq_smul _ _ _ h

end POVM

namespace Ensemble

/-- The coherent ensemble sum has the ensemble mixture as its retained marginal. -/
lemma partialTraceRight_outer_sum_ofPure (w : Convexity.StdSimplex ℝ ι)
    (v : ι → UnitState H) (b : OrthonormalBasis ι ℂ K.state) :
    Operator.partialTraceRight
      (Operator.outer (∑ i, ((Real.sqrt (w.weights i) : ℂ) • (v i).val) ⊗ₜ[ℂ] b i)
        (∑ i, ((Real.sqrt (w.weights i) : ℂ) • (v i).val) ⊗ₜ[ℂ] b i)) =
      (ofPure w v).mix.op :=
  UnitState.partialTraceRight_outer_sum_sqrt_smul b w.weights w.weights_nonneg v

/-- Purify a pure ensemble by coherently recording its label in an auxiliary basis. -/
def purifyOfPureWith (w : Convexity.StdSimplex ℝ ι) (v : ι → UnitState H)
    (b : OrthonormalBasis ι ℂ K.state) : UnitState (H ⊗ K) :=
  UnitState.purifyMixture b w.weights w.weights_nonneg w.total_of_fintype v

/-- Discarding the coherent label recovers the ensemble mixture. -/
lemma partialTraceRight_pure_purifyOfPureWith (w : Convexity.StdSimplex ℝ ι)
    (v : ι → UnitState H) (b : OrthonormalBasis ι ℂ K.state) :
    (Density.pure (purifyOfPureWith w v b)).partialTraceRight = (ofPure w v).mix :=
  UnitState.partialTraceRight_pure_purifyMixture b w.weights w.weights_nonneg
    w.total_of_fintype v

/-- Contracting a coherent label gives the exact square-root-weighted ensemble vector. -/
lemma contractRight_purifyOfPureWith (w : Convexity.StdSimplex ℝ ι)
    (v : ι → UnitState H) (b : OrthonormalBasis ι ℂ K.state) (i : ι) :
    (purifyOfPureWith w v b).contractRight (b i) = (Real.sqrt (w.weights i) : ℂ) • (v i).val := by
  classical
  apply ext_inner_left ℂ
  intro x
  rw [UnitState.inner_contractRight]
  change inner ℂ (x ⊗ₜ[ℂ] b i) (∑ j, _ ⊗ₜ[ℂ] b j) = _
  simp only [inner_sum, TensorProduct.inner_tmul, b.inner_eq_ite, mul_ite, mul_one, mul_zero]
  simp

end Ensemble

namespace Density

/-- Every finite pure decomposition is obtained by rank-at-most-one effects on the minimal
auxiliary system. The amplitude equality retains the phases of the chosen unit vectors. -/
theorem exists_rankOne_povm_of_ensemble (ρ : Density H) (w : Convexity.StdSimplex ℝ ι)
    (v : ι → UnitState H) (hmix : (Ensemble.ofPure w v).mix = ρ) :
    ∃ (M : POVM (std (Module.finrank ℂ (LinearMap.range ρ.op))) ι)
      (a : ι → (std (Module.finrank ℂ (LinearMap.range ρ.op))).state),
      (∀ i, M.op i = Operator.outer (a i) (a i)) ∧
      ∀ i, ρ.purifyMinimal.contractRight (a i) =
        (Real.sqrt (w.weights i) : ℂ) • (v i).val := by
  let b : OrthonormalBasis ι ℂ (std (Fintype.card ι)).state :=
    (ZBasis _).reindex (Fintype.equivFin ι).symm
  let ψ := Ensemble.purifyOfPureWith w v b
  obtain ⟨V, hV, hψ⟩ := ρ.exists_eq_map_purifyMinimal ψ
    ((Ensemble.partialTraceRight_pure_purifyOfPureWith w v b).trans hmix)
  let := hV
  refine ⟨(POVM.ofBasis b).comap V, fun i => V† (b i),
    fun i => POVM.op_comap_ofBasis b V i, ?_⟩
  intro i
  rw [← UnitState.contractRight_map_isometry, ← hψ]
  exact Ensemble.contractRight_purifyOfPureWith w v b i

/-- **Hughston–Jozsa–Wootters theorem**: finite pure ensembles of a density are exactly the branches
of auxiliary POVMs on its minimal purification. The unnormalized formulation includes
zero-weight labels. -/
theorem mix_ofPure_eq_iff_exists_povm (ρ : Density H) (w : Convexity.StdSimplex ℝ ι)
    (v : ι → UnitState H) :
    (Ensemble.ofPure w v).mix = ρ ↔
      ∃ M : POVM (std (Module.finrank ℂ (LinearMap.range ρ.op))) ι,
        ∀ i, M.steeredOperator (pure ρ.purifyMinimal) i =
          (w.weights i : ℂ) • (pure (v i)).op := by
  constructor
  · intro hmix
    obtain ⟨M, a, hM, ha⟩ := ρ.exists_rankOne_povm_of_ensemble w v hmix
    refine ⟨M, fun i => ?_⟩
    change (pure ρ.purifyMinimal).steeringMap (M.op i) = _
    rw [hM, steeringMap_pure_outer, ha, Operator.outer_smul_self,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      ← Complex.ofReal_pow, Real.sq_sqrt (w.weights_nonneg i)]
    rfl
  · rintro ⟨M, hM⟩
    apply Density.ext
    have h := M.sum_steeredOperator (pure ρ.purifyMinimal)
    rw [partialTraceRight_pure_purifyMinimal] at h
    simpa only [hM, Ensemble.op_mix_ofPure, op_pure] using h

/-- The ensemble-interface form of HJW, with no global-phase choices in the conclusion. -/
theorem mix_eq_iff_exists_povm (ρ : Density H) (e : Ensemble H ι)
    (he : ∀ i, (e.state i).IsPure) :
    e.mix = ρ ↔
      ∃ M : POVM (std (Module.finrank ℂ (LinearMap.range ρ.op))) ι,
        ∀ i, M.steeredOperator (pure ρ.purifyMinimal) i =
          (e.weight i : ℂ) • (e.state i).op := by
  choose v hv using he
  have heq : e = Ensemble.ofPure e.distribution v := Ensemble.ext rfl (funext hv)
  rw [heq]
  exact ρ.mix_ofPure_eq_iff_exists_povm _ v

end Density

end

end Qudit
