/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/SuperOp/LiftSO.lean (liftSO_formsoOf, liftSO_kraussoOf, liftSO_liftF_compl/compr)
Qhl/Program/Step.lean (initLift and initLift_isQC)
Qhl/Program/LocalConjugation.lean (mapSO_liftSO_conj and mapSO_initLift_conj)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.OrderedRegister
public import FQFP.CQM.Qudit.Channel.Choi
import FQFP.CQM.Qudit.State.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# Channels on ordered subregisters

In Choi coordinates a single Kraus operator is represented by the outer square of its
vectorization. Conjugating the Choi operator by the vectorized register embedding extends
the operation linearly. Thus different Kraus representations give the same extension.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit Superoperator
open scoped TensorProduct

namespace QuantumProgram

noncomputable section

private def vectorEquiv (H : Qudit) : Operator H ≃ₗ[ℂ] (H ⊗ H).state := by
  let b := stdOrthonormalBasis ℂ H.state
  have hd : Module.finrank ℂ (Operator H) = Module.finrank ℂ (H ⊗ H).state :=
    (Module.finrank_linearMap ℂ ℂ H.state H.state).trans Module.finrank_tensorProduct.symm
  have hs : Function.Surjective (vectorize (K := H) b) :=
    fun v => ⟨unvectorize b v, vectorize_unvectorize b v⟩
  exact LinearEquiv.ofBijective (vectorize b)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs, hs⟩

private def choiEquiv (H : Qudit) : Superoperator H H ≃ₗ[ℂ] Operator (H ⊗ H) :=
  LinearEquiv.ofInjectiveOfFinrankEq (choi (stdOrthonormalBasis ℂ H.state)) (choi_injective _) (by
    have hd := (vectorEquiv H).finrank_eq
    change Module.finrank ℂ (Operator H →ₗ[ℂ] Operator H) =
      Module.finrank ℂ ((H ⊗ H).state →ₗ[ℂ] (H ⊗ H).state)
    rw [Module.finrank_linearMap ℂ ℂ (Operator H) (Operator H),
      Module.finrank_linearMap ℂ ℂ (H ⊗ H).state (H ⊗ H).state, hd])

private def vectorLift {n k : ℕ} (D : Fin n → Qudit) (r : Fin k ↪ Fin n) :=
  (vectorEquiv (tensorMemory D)).toLinearMap ∘ₗ (orderedLift D r).toAlgHom.toLinearMap ∘ₗ
    (vectorEquiv (tensorMemory (D ∘ r))).symm.toLinearMap

variable {n k l : ℕ} (D : Fin n → Qudit) (r : Fin k ↪ Fin n)

/-- Extend a linear operation on the selected sites to the whole memory in Choi coordinates. -/
@[no_expose] def orderedSuperoperator :
    Superoperator (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)) →ₗ[ℂ]
      Superoperator (tensorMemory D) (tensorMemory D) :=
  (choiEquiv _).symm.toLinearMap ∘ₗ Superoperator.conjugate (vectorLift D r) ∘ₗ
    (choiEquiv _).toLinearMap

/-- A lifted conjugation uses precisely the lifted local operator. -/
theorem orderedSuperoperator_conjugate (X : Operator (tensorMemory (D ∘ r))) :
    orderedSuperoperator D r (conjugate X) = conjugate (orderedLift D r X) := by
  apply (choiEquiv _).injective
  rw [orderedSuperoperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  change conjugate (vectorLift D r)
    (choi (stdOrthonormalBasis ℂ (tensorMemory (D ∘ r)).state) (conjugate X)) =
      choi (stdOrthonormalBasis ℂ (tensorMemory D).state) (conjugate (orderedLift D r X))
  rw [choi_conjugate, choi_conjugate, conjugate_outer]
  have h : vectorLift D r ((vectorEquiv _) X) = (vectorEquiv _) (orderedLift D r X) := by
    simp [vectorLift]
  exact congrArg₂ Operator.outer h h

/-- The extension of a Kraus sum is the sum of the lifted conjugations. -/
theorem orderedSuperoperator_kraus {ι : Type*} [Fintype ι]
    (M : ι → Operator (tensorMemory (D ∘ r))) :
    orderedSuperoperator D r (kraus M) = kraus (fun i => orderedLift D r (M i)) := by
  simp only [kraus, map_sum, orderedSuperoperator_conjugate]

/-- Complete positivity is preserved under ordered-register extension. -/
theorem orderedSuperoperator_cp {Φ : Superoperator (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r))}
    (h : Φ.IsCompletelyPositive) : (orderedSuperoperator D r Φ).IsCompletelyPositive := by
  obtain ⟨_, M, rfl⟩ := h.exists_kraus
  rw [orderedSuperoperator_kraus]
  exact isCompletelyPositive_kraus _

/-- Run a channel on the selected sites, including joint channels on nonadjacent sites. -/
def orderedChannel (Φ : QuantumChannel (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r))) :
    QuantumChannel (tensorMemory D) (tensorMemory D) where
  toSuperoperator := orderedSuperoperator D r Φ.toSuperoperator
  completelyPositive := orderedSuperoperator_cp D r Φ.completelyPositive
  tracePreserving := by
    obtain ⟨_, M, he, hc⟩ := Φ.exists_kraus
    rw [he, orderedSuperoperator_kraus, isTracePreserving_kraus_iff]
    exact orderedLift_complete D r M hc

/-- The identity channel on any selection acts as the identity on memory. -/
theorem orderedChannel_id :
    orderedChannel D r (QuantumChannel.id _) = QuantumChannel.id _ := by
  apply QuantumChannel.ext
  change orderedSuperoperator D r LinearMap.id = LinearMap.id
  rw [← conjugate_id (tensorMemory (D ∘ r)), orderedSuperoperator_conjugate]
  change conjugate (orderedLift D r 1) = LinearMap.id
  rw [map_one]
  exact conjugate_id _

/-- Apply a local instrument with all its original branches, including multi-Kraus outcomes. -/
def orderedInstrument {ι : Type*} [Fintype ι]
    (I : Instrument (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)) ι) :
    Instrument (tensorMemory D) (tensorMemory D) ι where
  branch i := orderedSuperoperator D r (I.branch i)
  completelyPositive i := orderedSuperoperator_cp D r (I.completelyPositive i)
  tracePreserving := by
    rw [← map_sum]
    exact (orderedChannel D r I.toChannel).tracePreserving

/-- Each original outcome acts by the lift of its local branch superoperator. -/
@[simp] theorem orderedInstrument_branch {ι : Type*} [Fintype ι]
    (I : Instrument (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)) ι) (i : ι) :
    (orderedInstrument D r I).branch i = orderedSuperoperator D r (I.branch i) := rfl

/-- Forgetting the outcome commutes with lifting an instrument to the whole memory. -/
@[simp] theorem orderedInstrument_toChannel {ι : Type*} [Fintype ι]
    (I : Instrument (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)) ι) :
    (orderedInstrument D r I).toChannel = orderedChannel D r I.toChannel := by
  apply QuantumChannel.ext
  exact (map_sum (orderedSuperoperator D r) I.branch Finset.univ).symm

/-- Lifting a local gate induces the lifted local unitary channel. -/
theorem toChannel_liftGate_orderedLift
    (U : End (tensorMemory (D ∘ r))) [DaggerCategory.IsUnitary U.asHom] :
    (UnitaryProgram.liftGate (orderedLift D r) U).toChannel =
      orderedChannel D r (QuantumChannel.ofIsometry U.asHom) := by
  apply QuantumChannel.ext
  exact (orderedSuperoperator_conjugate D r (endAlgEquiv _ U)).symm

/-- Channel semantics of an ordered lift supplied as a unitary morphism. -/
theorem toChannel_liftGateHom_orderedLift
    (U : tensorMemory (D ∘ r) ⟶ tensorMemory (D ∘ r)) [DaggerCategory.IsUnitary U] :
    (UnitaryProgram.liftGateHom (orderedLift D r) U).toChannel =
      orderedChannel D r (QuantumChannel.ofIsometry U) :=
  toChannel_liftGate_orderedLift D r (.of U)

/-- Initialize an ordered selection, possibly noncontiguous, to the given joint density. -/
def orderedInitialize (τ : Density (tensorMemory (D ∘ r))) :
    QuantumChannel (tensorMemory D) (tensorMemory D) :=
  orderedChannel D r (QuantumChannel.replacement _ τ)

/-- An empty selection has only its scalar state, so initialization acts as the identity. -/
theorem orderedInitialize_empty (s : Fin 0 ↪ Fin n) (τ : Density (tensorMemory (D ∘ s))) :
    orderedInitialize D s τ = QuantumChannel.id _ := by
  have scalar (X : Operator (tensorMemory (D ∘ s))) : X = X.trace • 1 :=
    (Operator.scalar_eq X).trans (congrArg (· • (1 : Operator _)) (Operator.trace_scalar X).symm)
  have hτ : τ.op = 1 := by simpa only [τ.trace_one, one_smul] using scalar τ.op
  have he : QuantumChannel.replacement _ τ = QuantumChannel.id _ := by
    apply QuantumChannel.ext
    apply LinearMap.ext
    intro X
    rw [QuantumChannel.replacement_apply, hτ]
    exact (scalar X).symm
  rw [orderedInitialize, he, orderedChannel_id]

/-- A local channel acts on a product of a selected operator and a disjoint spectator by
transforming only the selected operator. -/
theorem orderedChannel_apply_mul (s : Fin l ↪ Fin n) (hd : ∀ i j, r i ≠ s j)
    (Φ : QuantumChannel (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)))
    (X : Operator (tensorMemory (D ∘ r))) (Y : Operator (tensorMemory (D ∘ s))) :
    (orderedChannel D r Φ).toSuperoperator (orderedLift D r X * orderedLift D s Y) =
      orderedLift D r (Φ.toSuperoperator X) * orderedLift D s Y := by
  obtain ⟨_, M, he, _⟩ := Φ.exists_kraus
  change orderedSuperoperator D r Φ.toSuperoperator _ = _
  rw [he, orderedSuperoperator_kraus, kraus_apply, kraus_apply]
  change (∑ i, orderedLift D r (M i) * (orderedLift D r X * orderedLift D s Y) *
      star (orderedLift D r (M i))) = orderedLift D r (∑ i, M i * X * star (M i)) * _
  simp only [map_sum, Finset.sum_mul, map_mul, ← map_star, mul_assoc]
  exact Finset.sum_congr rfl fun i _ => congrArg (orderedLift D r (M i) * ·)
    (congrArg (orderedLift D r X * ·) (commute_orderedLift D r s hd (star (M i)) Y).eq.symm)

/-- Resetting the selection replaces its operator by the prepared state times its input trace. -/
theorem orderedInitialize_apply_mul (s : Fin l ↪ Fin n) (hd : ∀ i j, r i ≠ s j)
    (τ : Density (tensorMemory (D ∘ r))) (X : Operator (tensorMemory (D ∘ r)))
    (Y : Operator (tensorMemory (D ∘ s))) :
    (orderedInitialize D r τ).toSuperoperator (orderedLift D r X * orderedLift D s Y) =
      X.trace • (orderedLift D r τ.op * orderedLift D s Y) := by
  rw [orderedInitialize, orderedChannel_apply_mul D r s hd, QuantumChannel.replacement_apply,
    map_smul, smul_mul_assoc]

/-- A map commuting with all lifted conjugations commutes with every lifted linear operation.
Positive Choi operators span the full space of Choi operators. -/
private theorem commute_of_conjugations (Ψ : Superoperator (tensorMemory D) (tensorMemory D))
    (hc : ∀ X, Commute (conjugate (orderedLift D r X)) Ψ)
    (Φ : Superoperator (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r))) :
    Commute (orderedSuperoperator D r Φ) Ψ := by
  let A := tensorMemory (D ∘ r)
  let C := choiEquiv A
  suffices ∀ X, Commute (orderedSuperoperator D r (C.symm X)) Ψ by
    simpa only [LinearEquiv.symm_apply_apply] using this (C Φ)
  intro X
  have hx : X ∈ Submodule.span ℂ {Y : Operator (A ⊗ A) | 0 ≤ Y} := by
    rw [CStarAlgebra.span_nonneg]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem Y hY =>
    have hp : (C.symm Y).IsCompletelyPositive := by
      apply (isCompletelyPositive_iff_choi_positive (stdOrthonormalBasis ℂ A.state) _).mpr
      change (C (C.symm Y)).IsPositive
      rw [C.apply_symm_apply]
      exact LinearMap.nonneg_iff_isPositive.mp hY
    obtain ⟨_, M, he⟩ := hp.exists_kraus
    rw [he, orderedSuperoperator_kraus]
    apply LinearMap.ext
    intro ρ
    change kraus _ (Ψ ρ) = Ψ (kraus _ ρ)
    simp only [kraus, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (hc (M i)).eq ρ
  | zero => simp only [map_zero, Commute.zero_left]
  | add _ _ _ _ ha hb => simpa only [map_add] using ha.add_left hb
  | smul a _ _ h => simpa only [map_smul] using h.smul_left a

/-- Conjugating by an operator in the commutant of the selected register preserves its action. -/
theorem orderedSuperoperator_commute_of_commute (K : Operator (tensorMemory D))
    (hc : ∀ X, Commute (orderedLift D r X) K)
    (Φ : Superoperator (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r))) :
    Commute (orderedSuperoperator D r Φ) (conjugate K) :=
  commute_of_conjugations D r _ (fun X =>
    LinearMap.ext fun ρ => commute_conjugate_of_commute (hc X) ρ) Φ

/-- Left multiplication by a disjoint operator passes through every lifted linear operation. -/
theorem orderedSuperoperator_mul_left (s : Fin l ↪ Fin n) (hd : ∀ i j, r i ≠ s j)
    (Φ : Superoperator (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)))
    (K : Operator (tensorMemory (D ∘ s))) (ρ : Operator (tensorMemory D)) :
    orderedSuperoperator D r Φ (orderedLift D s K * ρ) =
      orderedLift D s K * orderedSuperoperator D r Φ ρ := by
  apply LinearMap.congr_fun (commute_of_conjugations D r (LinearMap.mulLeft ℂ (orderedLift D s K))
    _ Φ).eq ρ
  intro X
  apply LinearMap.ext
  intro Y
  change orderedLift D r X * (orderedLift D s K * Y) * _ = orderedLift D s K * (_ * Y * _)
  rw [← mul_assoc, (commute_orderedLift D r s hd X K).eq]
  simp only [mul_assoc]

/-- Right multiplication by a disjoint operator passes through every lifted linear operation. -/
theorem orderedSuperoperator_mul_right (s : Fin l ↪ Fin n) (hd : ∀ i j, r i ≠ s j)
    (Φ : Superoperator (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)))
    (K : Operator (tensorMemory (D ∘ s))) (ρ : Operator (tensorMemory D)) :
    orderedSuperoperator D r Φ (ρ * orderedLift D s K) =
      orderedSuperoperator D r Φ ρ * orderedLift D s K := by
  apply LinearMap.congr_fun (commute_of_conjugations D r (LinearMap.mulRight ℂ (orderedLift D s K))
    _ Φ).eq ρ
  intro X
  apply LinearMap.ext
  intro Y
  change orderedLift D r X * (Y * orderedLift D s K) * star (orderedLift D r X) =
    (orderedLift D r X * Y * star (orderedLift D r X)) * orderedLift D s K
  simp only [mul_assoc, ← map_star, (commute_orderedLift D r s hd (star X) K).eq]

/-- Disjointness of the selected cells suffices for covariance on every full-memory input. -/
theorem orderedSuperoperator_commute_conjugate (s : Fin l ↪ Fin n) (hd : ∀ i j, r i ≠ s j)
    (Φ : Superoperator (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)))
    (K : Operator (tensorMemory (D ∘ s))) :
    Function.Commute (orderedSuperoperator D r Φ) (conjugate (orderedLift D s K)) :=
  fun ρ => LinearMap.congr_fun (orderedSuperoperator_commute_of_commute D r _
    (fun X => commute_orderedLift D r s hd X K) Φ).eq ρ

/-- Arbitrary linear operations on disjoint ordered selections commute on full memory. -/
theorem commute_orderedSuperoperator (s : Fin l ↪ Fin n) (hd : ∀ i j, r i ≠ s j)
    (Φ : Superoperator (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)))
    (Ψ : Superoperator (tensorMemory (D ∘ s)) (tensorMemory (D ∘ s))) :
    Commute (orderedSuperoperator D r Φ) (orderedSuperoperator D s Ψ) :=
  commute_of_conjugations D r _ (fun X => (orderedSuperoperator_commute_of_commute D s _
    (fun Y => (commute_orderedLift D r s hd X Y).symm) Ψ).symm) Φ

namespace Command

variable {S : Type*} (cells : S → Fin k → Fin n)

/-- Evaluate an ordered register and run a joint unitary when its operands are distinct. -/
def unitaryOn (U : ∀ σ, Function.Injective (cells σ) → End (tensorMemory (D ∘ cells σ)))
    [∀ σ hi, DaggerCategory.IsUnitary (U σ hi).asHom] : Command S (Fin n) (tensorMemory D) :=
  unitary cells fun σ hi => .liftGate (orderedLift D ⟨cells σ, hi⟩) (U σ hi)

/-- Measure a joint register, using the original instruction's alias check and outcome writes. -/
def measureOn {m : ℕ} (I : ∀ σ, Function.Injective (cells σ) →
    Instrument (tensorMemory (D ∘ cells σ)) (tensorMemory (D ∘ cells σ)) (Fin m))
    (upd : Fin m → S → S) : Command S (Fin n) (tensorMemory D) :=
  measure cells (fun σ hi => orderedInstrument D ⟨cells σ, hi⟩ (I σ hi)) upd

/-- Run a joint gate on a fixed ordered tuple of distinct sites. -/
def unitaryOnRegister (U : End (tensorMemory (D ∘ r)))
    [DaggerCategory.IsUnitary U.asHom] : Command S (Fin n) (tensorMemory D) :=
  unitaryOn D (fun _ => r) (fun _ _ => U)

/-- Run a local instrument on a fixed ordered tuple and write back its original outcome. -/
def measureOnRegister {m : ℕ} (I : Instrument (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)) (Fin m))
    (upd : Fin m → S → S) : Command S (Fin n) (tensorMemory D) :=
  measureOn D (fun _ => r) (fun _ _ => I) upd

/-- A whole-memory Kraus frame follows from commutation with the acted-on register algebra. -/
theorem KrausFrame.measureOn {m : ℕ} (I : ∀ σ, Function.Injective (cells σ) →
    Instrument (tensorMemory (D ∘ cells σ)) (tensorMemory (D ∘ cells σ)) (Fin m))
    (upd : Fin m → S → S) (K : S → Operator (tensorMemory D))
    (hc : ∀ σ (hi : Function.Injective (cells σ)) X, Commute (orderedLift D ⟨cells σ, hi⟩ X) (K σ))
    (hw : ∀ i σ, K (upd i σ) = K σ) : (Command.measureOn D cells I upd).KrausFrame K :=
  ⟨fun σ hi i ρ => LinearMap.congr_fun (orderedSuperoperator_commute_of_commute D
    ⟨cells σ, hi⟩ (K σ) (hc σ hi) ((I σ hi).branch i)).eq ρ, hw⟩

/-- The unitary frame only checks the lifted local gate on stores with distinct operands. -/
theorem KrausFrame.unitaryOn (U : ∀ σ, Function.Injective (cells σ) →
    End (tensorMemory (D ∘ cells σ)))
    [∀ σ hi, DaggerCategory.IsUnitary (U σ hi).asHom] (K : S → Operator (tensorMemory D))
    (hc : ∀ σ (hi : Function.Injective (cells σ)),
      Commute (orderedLift D ⟨cells σ, hi⟩ (endAlgEquiv _ (U σ hi))) (K σ)) :
    (Command.unitaryOn D cells U).KrausFrame K :=
  unitary_of_commute cells (fun σ hi => .liftGate (orderedLift D ⟨cells σ, hi⟩) (U σ hi)) K hc

/-- Initialize the evaluated injection to its specified joint state. -/
def initializeOn (p : S → Fin k ↪ Fin n) (τ : (σ : S) → Density (tensorMemory (D ∘ p σ))) :
    Command S (Fin n) (tensorMemory D) := channel fun σ => orderedInitialize D (p σ) (τ σ)

/-- Initialization preserves any frame commuting with its selected register algebra. -/
theorem KrausFrame.initializeOn (p : S → Fin k ↪ Fin n)
    (τ : (σ : S) → Density (tensorMemory (D ∘ p σ))) (K : S → Operator (tensorMemory D))
    (hc : ∀ σ X, Commute (orderedLift D (p σ) X) (K σ)) :
    (Command.initializeOn D p τ).KrausFrame K :=
  fun σ ρ => LinearMap.congr_fun (orderedSuperoperator_commute_of_commute D (p σ) (K σ)
    (hc σ) (QuantumChannel.replacement _ (τ σ)).toSuperoperator).eq ρ

end Command

end

end QuantumProgram
