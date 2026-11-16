/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Process.Environment

/-!
# Heisenberg duality of completely positive processes

The dual is characterized by the trace pairing on all operators. Its construction uses
Kraus completeness, but uniqueness makes the result independent of that representation.
It defines a dagger on `CPQudit`. Trace preservation is dual to unitality.

## Main definitions and results

* `Qudit.CPMap.dual`: the Heisenberg dual of a completely positive map.
* `Qudit.CPMap.trace_dual`: duality for the bilinear trace pairing.
* `Qudit.CPMap.dual_dual`: duality is involutive.
* `Qudit.CPMap.isTracePreserving_iff_dual_one`: trace preservation is unitality of the dual.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit

noncomputable section

namespace Superoperator

/-- A global unit-modulus phase disappears in CP semantics. -/
lemma conjugate_smul_of_norm_eq_one {H K : Qudit} (f : H.state →ₗ[ℂ] K.state)
    (c : ℂ) (hc : ‖c‖ = 1) : conjugate (c • f) = conjugate f := by
  ext A x
  simp only [conjugate_apply, map_smulₛₗ, LinearMap.comp_apply,
    LinearMap.smul_apply, smul_smul, RingHom.id_apply]
  rw [mul_comm, Complex.mul_conj', hc]
  simp

/-- Moving a pure process across the trace pairing takes its adjoint. -/
lemma trace_conjugate_adjoint {H K : Qudit} (f : H.state →ₗ[ℂ] K.state)
    (A : Operator H) (B : Operator K) :
    (conjugate f.adjoint B * A).trace = (B * conjugate f A).trace := by
  simp only [conjugate_apply, LinearMap.adjoint_adjoint, Module.End.mul_eq_comp]
  simpa only [LinearMap.comp_assoc] using
    (LinearMap.trace_comp_comm' f.adjoint (B ∘ₗ f ∘ₗ A)).symm

/-- Adjoint Kraus operators give the dual of a finite Kraus process. -/
lemma trace_kraus_adjoint {H K : Qudit} {ι : Type*} [Fintype ι]
    (f : ι → H.state →ₗ[ℂ] K.state) (A : Operator H) (B : Operator K) :
    (kraus (fun i => (f i).adjoint) B * A).trace = (B * kraus f A).trace := by
  simp only [kraus, LinearMap.sum_apply, Finset.sum_mul, Finset.mul_sum, Operator.trace, map_sum]
  exact Finset.sum_congr rfl fun i _ => trace_conjugate_adjoint (f i) A B

end Superoperator

namespace CPMap

variable {H K : Qudit}

/-- The full-matrix CP condition is equivalent to positive Choi data in any chosen
orthonormal coordinates. No claim about general Frobenius algebra objects is made. -/
def choiPositiveEquiv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) :
    CPMap H K ≃ {Φ : Superoperator H K // (Superoperator.choi b Φ).IsPositive} where
  toFun f := ⟨f.toSuperoperator, f.completelyPositive.choi_positive b⟩
  invFun f := ⟨f.1, (Superoperator.isCompletelyPositive_iff_choi_positive b f.1).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every CP process has a CP trace-pairing dual. -/
lemma exists_dual (f : CPMap H K) :
    ∃ g : CPMap K H, ∀ A B,
      (g.toSuperoperator B * A).trace = (B * f.toSuperoperator A).trace := by
  obtain ⟨n, a, ha⟩ := f.completelyPositive.exists_kraus
  refine ⟨⟨Superoperator.kraus (fun i => (a i).adjoint),
    Superoperator.isCompletelyPositive_kraus _⟩, ?_⟩
  intro A B
  rw [ha]
  exact Superoperator.trace_kraus_adjoint a A B

/-- The Heisenberg dual, uniquely determined by the trace pairing. -/
def dual (f : CPMap H K) : CPMap K H := f.exists_dual.choose

/-- The defining trace-pairing identity, for arbitrary operators. -/
lemma trace_dual (f : CPMap H K) (A : Operator H) (B : Operator K) :
    (f.dual.toSuperoperator B * A).trace = (B * f.toSuperoperator A).trace :=
  f.exists_dual.choose_spec A B

/-- Characterize the dual without reference to a chosen Kraus decomposition. -/
lemma dual_eq_iff (f : CPMap H K) (g : CPMap K H) :
    f.dual = g ↔ ∀ A B,
      (g.toSuperoperator B * A).trace = (B * f.toSuperoperator A).trace := by
  constructor
  · rintro rfl
    exact f.trace_dual
  · intro h
    apply CPMap.ext
    apply LinearMap.ext
    intro B
    apply Operator.ext_trace
    intro A
    exact (f.trace_dual A B).trans (h A B).symm

/-- Taking the Heisenberg dual twice returns the original CP process. -/
@[simp]
lemma dual_dual (f : CPMap H K) : f.dual.dual = f := by
  apply (dual_eq_iff _ _).mpr
  intro B A
  rw [Operator.trace, LinearMap.trace_mul_comm]
  exact (f.trace_dual A B).symm.trans (LinearMap.trace_mul_comm ℂ _ _)

/-- Trace preservation is equivalent to unitality of the Heisenberg dual. -/
lemma isTracePreserving_iff_dual_one (f : CPMap H K) :
    f.toSuperoperator.IsTracePreserving ↔ f.dual.toSuperoperator 1 = 1 := by
  constructor
  · intro h
    apply Operator.ext_trace
    intro A
    rw [f.trace_dual, one_mul, one_mul, h A]
  · intro h A
    have e := f.trace_dual A 1
    simpa only [h, one_mul] using e.symm

end CPMap

namespace CPQudit

instance : DaggerCategory CPQudit where
  dagger f := f.dual
  dagger_comp f g := by
    apply (CPMap.dual_eq_iff _ _).mpr
    intro A B
    change (f.dual.toSuperoperator (g.dual.toSuperoperator B) * A).trace =
      (B * g.toSuperoperator (f.toSuperoperator A)).trace
    rw [f.trace_dual, Operator.trace, LinearMap.trace_mul_comm,
      ← g.trace_dual, LinearMap.trace_mul_comm]
  dagger_id H := by
    apply (CPMap.dual_eq_iff _ _).mpr
    intro A B
    rfl
  involutive_dagger f := f.dual_dual

/-- The CP dagger extends the pure adjoint. -/
lemma dagger_pure {H K : Qudit} (f : H ⟶ K) : (pure.map f)† = pure.map f† := by
  apply (CPMap.dual_eq_iff _ _).mpr
  intro A B
  exact Superoperator.trace_conjugate_adjoint f.hom A B

/-- The adjoint of discarding prepares the unnormalized identity operator. -/
lemma dagger_discard_apply (H : CPQudit) (B : Operator (of ℂ)) :
    (discard H)†.toSuperoperator B = B.trace • (1 : Operator H.toQudit) := by
  apply Operator.ext_trace
  intro A
  change ((discard H).dual.toSuperoperator B * A).trace = _
  rw [(discard H).trace_dual]
  change (B * Superoperator.discard H.toQudit A).trace = _
  rw [Superoperator.discard_apply]
  simp only [mul_smul_comm, mul_one, smul_mul_assoc, one_mul, Operator.trace, map_smul,
    smul_eq_mul, mul_comm]

/-- The Heisenberg dual respects independent tensor products. -/
lemma dagger_tensor {H K L M : CPQudit} (f : H ⟶ K) (g : L ⟶ M) :
    (f ⊗ₘ g)† = f† ⊗ₘ g† := by
  apply (CPMap.dual_eq_iff _ _).mpr
  intro A B
  change (Superoperator.tensor f.dual.toSuperoperator g.dual.toSuperoperator B * A).trace =
    (B * Superoperator.tensor f.toSuperoperator g.toSuperoperator A).trace
  induction A using Operator.tensor_induction_on with
  | htensor A C =>
    induction B using Operator.tensor_induction_on with
    | htensor B D =>
      rw [Superoperator.tensor_apply f.dual.toSuperoperator g.dual.toSuperoperator B D,
        Superoperator.tensor_apply f.toSuperoperator g.toSuperoperator A C]
      simp only [Operator.tensor, Module.End.mul_eq_comp,
        ← TensorProduct.map_comp]
      change (Operator.tensor (f.dual.toSuperoperator B * A)
        (g.dual.toSuperoperator D * C)).trace =
        (Operator.tensor (B * f.toSuperoperator A) (D * g.toSuperoperator C)).trace
      rw [Operator.trace_tensor, Operator.trace_tensor, f.trace_dual, g.trace_dual]
    | hadd B D hB hD =>
      simpa only [map_add, add_mul, Operator.trace] using congrArg₂ (· + ·) hB hD
  | hadd A C hA hC =>
    simpa only [map_add, mul_add, Operator.trace] using congrArg₂ (· + ·) hA hC

/-- The pure functor takes unitary processes to unitary CP processes. -/
instance isUnitary_pure {H K : Qudit} (f : H ⟶ K) [IsUnitary f] :
    IsUnitary (pure.map f) where
  comp_dagger_eq_id := by
    rw [dagger_pure, ← pure.map_comp, IsIsometry.comp_dagger_eq_id, pure.map_id]
  dagger_comp_eq_id := by
    rw [dagger_pure, ← pure.map_comp, IsUnitary.dagger_comp_eq_id, pure.map_id]

instance : MonoidalDaggerCategory CPQudit where
  toDaggerCategory := inferInstance
  toMonoidalCategory := inferInstance
  dagger_tensor := dagger_tensor
  isUnitary_associator H K L := isUnitary_pure (α_ H.toQudit K.toQudit L.toQudit).hom
  isUnitary_leftUnitor H := isUnitary_pure (λ_ H.toQudit).hom
  isUnitary_rightUnitor H := isUnitary_pure (ρ_ H.toQudit).hom

instance : SymmetricMonoidalDaggerCategory CPQudit where
  isUnitary_braiding H K := isUnitary_pure (β_ H.toQudit K.toQudit).hom
/-- A pure process preserves the trace exactly when it is an isometry. -/
lemma isCausal_pure_iff {H K : Qudit} (f : H ⟶ K) :
    IsCausal (pure.map f) ↔ IsIsometry f := by
  change pure.map f ≫ discard ⟨K⟩ = discard ⟨H⟩ ↔ IsIsometry f
  have h := pure_comp_discard_iff f (𝟙 H)
  simp only [pure.map_id, Category.id_comp, dagger_id] at h
  dsimp only [pure] at h ⊢
  rw [Category.id_comp] at h
  rw [h]
  exact ⟨fun h => ⟨by simpa using h⟩, fun h => by simp⟩

end CPQudit

end

end Qudit
