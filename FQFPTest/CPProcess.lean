/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Channel.Classical
import FQFP.CQM.Qudit.Channel.Compact

/-!
# CP process category clients

Categorical composition, complex phase loss, Heisenberg duality, causal effects,
zero-dimensional purification, compact environments and classical communication.
-/

open CategoryTheory MonoidalCategory DaggerCategory Qudit

noncomputable section

-- The two process categories have independent symmetric monoidal instances.
example : SymmetricCategory CPQudit := inferInstance
example : SymmetricCategory CausalQudit := inferInstance
example : SymmetricMonoidalDaggerCategory CPQudit := inferInstance
example : CPQudit.pure.Monoidal := inferInstance
example : CausalQudit.inclusion.Faithful := inferInstance

-- Composition/tensor interchange is available to ordinary categorical clients.
example {H K L R S T : CPQudit} (f : H ⟶ K) (g : K ⟶ L)
    (h : R ⟶ S) (k : S ⟶ T) :
    (f ⊗ₘ h) ≫ (g ⊗ₘ k) = (f ≫ g) ⊗ₘ (h ≫ k) := tensorHom_comp_tensorHom _ _ _ _

-- Choi positivity characterizes the actual arbitrary-ancilla CP definition.
example (H K : Qudit) :
    CPMap H K ≃ {Φ : Superoperator H K //
      (Superoperator.choi (stdOrthonormalBasis ℂ H.state) Φ).IsPositive} :=
  CPMap.choiPositiveEquiv _

-- Complex phase really disappears, on every operator including off-diagonal ones.
example (H K : Qudit) (f : H.state →ₗ[ℂ] K.state) :
    Superoperator.conjugate (Complex.I • f) = Superoperator.conjugate f :=
  Superoperator.conjugate_smul_of_norm_eq_one f _ Complex.norm_I

-- Thus the pure-process functor cannot distinguish even two different scalar arrows.
example : CPQudit.pure.map (ofHom (-LinearMap.id) : of ℂ ⟶ of ℂ) =
    CPQudit.pure.map (𝟙 (of ℂ)) := by
  apply CPMap.ext
  change Superoperator.conjugate (H := of ℂ) (K := of ℂ) (-LinearMap.id) =
    Superoperator.conjugate LinearMap.id
  simpa only [neg_one_smul] using
    Superoperator.conjugate_smul_of_norm_eq_one (H := of ℂ) (K := of ℂ)
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (-1) (by simp)

example : (ofHom (-LinearMap.id) : of ℂ ⟶ of ℂ) ≠ 𝟙 (of ℂ) := by
  intro h
  have e := congrArg (fun f : of ℂ ⟶ of ℂ => f.hom 1) h
  norm_num at e

-- Dagger reverses composition and respects tensor, with the trace-pairing direction fixed.
example {H K L : CPQudit} (f : H ⟶ K) (g : K ⟶ L) : (f ≫ g)† = g† ≫ f† := by simp

example {H K L M : CPQudit} (f : H ⟶ K) (g : L ⟶ M) :
    (f ⊗ₘ g)† = f† ⊗ₘ g† := CPQudit.dagger_tensor f g

example {H K : Qudit} (f : CPMap H K) (ρ : Density H) (E : Operator K) :
    (f.dual.toSuperoperator E * ρ.op).trace = (E * f.toSuperoperator ρ.op).trace :=
  f.trace_dual ρ.op E

-- The adjoint of qubit discarding is not trace preserving; CPTP has no inherited dagger.
example : ¬ (CPQudit.discard ⟨Qubit⟩)†.toSuperoperator.IsTracePreserving := by
  intro h
  have e := h (1 : Operator (of ℂ))
  rw [CPQudit.dagger_discard_apply] at e
  change (LinearMap.trace ℂ (std 2).state) ((LinearMap.trace ℂ ℂ) 1 • 1) =
    (LinearMap.trace ℂ ℂ) 1 at e
  norm_num at e

-- Causality is exactly TP, and deterministic scalar effects are unique.
example {H K : CausalQudit} (f : H ⟶ K) :
    CPQudit.IsCausal (CausalQudit.inclusion.map f) := CausalQudit.isCausal_inclusion f

example {H : CausalQudit} (f g : H ⟶ 𝟙_ CausalQudit) : f = g :=
  (CausalQudit.eq_discard f).trans (CausalQudit.eq_discard g).symm

-- Purification also handles the zero-dimensional input and output without extra hypotheses.
example (f : (⟨std 0⟩ : CPQudit) ⟶ ⟨std 0⟩) :
    ∃ (n : ℕ) (V : (std 0) ⟶ std 0 ⊗ std n),
      f = CPQudit.pure.map V ≫
        (𝟙 (⟨std 0⟩ : CPQudit) ⊗ₘ CPQudit.discard ⟨std n⟩) ≫ (ρ_ (⟨std 0⟩ : CPQudit)).hom :=
  CPQudit.exists_pure_comp_discard f

-- The separation law allows different output dimensions.
example (H : Qudit) (f : H ⟶ std 2) (g : H ⟶ std 3) :
    CPQudit.pure.map f ≫ CPQudit.discard ⟨std 2⟩ =
      CPQudit.pure.map g ≫ CPQudit.discard ⟨std 3⟩ ↔ f ≫ f† = g ≫ g† :=
  CPQudit.pure_comp_discard_iff f g

-- Basis-dependent compact pairings include the empty basis.
example : ExactPairing (⟨std 0⟩ : CPQudit) ⟨std 0⟩ :=
  CPQudit.exactPairingOfOrthonormalBasis (ZBasis 0)

example (n : ℕ) :
    (ρ_ (⟨std n⟩ : CPQudit)).inv ≫
      (𝟙 (⟨std n⟩ : CPQudit) ⊗ₘ (CPQudit.discard ⟨std n⟩)†) ≫
      CPQudit.pure.map (basisEvaluation (ZBasis n)) = CPQudit.discard ⟨std n⟩ :=
  CPQudit.discard_dual (ZBasis n)

-- The classical bridge has mathematical content: off-diagonal entries vanish.
example : (QuantumChannel.dephase (ZBasis 2)).toSuperoperator
    (Operator.outer (ZBasis 2 0) (ZBasis 2 1)) = 0 := by
  rw [QuantumChannel.dephase_apply]
  simp [Fin.sum_univ_two, (ZBasis 2).inner_eq_ite]

example (H : Qudit) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) :
    (QuantumChannel.dephase b).comp (QuantumChannel.dephase b) = QuantumChannel.dephase b :=
  QuantumChannel.dephase_idempotent b

-- Actual Bell measurement, recording, controlled corrections and forgetting compose to identity.
example :
    (teleportationMeasurement.record (ZBasis 4) :
      (⟨Qubit⟩ : CausalQudit) ⟶ ⟨Qubit ⊗ std 4⟩) ≫
      QuantumChannel.controlled (ZBasis 4) (fun i => QuantumChannel.ofIsometry (corrections i)) ≫
      QuantumChannel.partialTraceRight Qubit (std 4) = 𝟙 (⟨Qubit⟩ : CausalQudit) :=
  teleportation_causal_composite

-- The measured register is stable under decoherence before classical processing.
example :
    ((QuantumChannel.id Qubit).tensor (QuantumChannel.dephase (ZBasis 4))).comp
      (teleportationMeasurement.record (ZBasis 4)) = teleportationMeasurement.record (ZBasis 4) :=
  Instrument.record_dephase _ _

-- The full categorical protocol also preserves an arbitrary reference system.
example (R : CausalQudit) :
    ((teleportationMeasurement.record (ZBasis 4) :
      (⟨Qubit⟩ : CausalQudit) ⟶ ⟨Qubit ⊗ std 4⟩) ≫
      QuantumChannel.controlled (ZBasis 4) (fun i => QuantumChannel.ofIsometry (corrections i)) ≫
      QuantumChannel.partialTraceRight Qubit (std 4)) ⊗ₘ 𝟙 R = 𝟙 ((⟨Qubit⟩ : CausalQudit) ⊗ R) := by
  exact (congrArg (fun f : (⟨Qubit⟩ : CausalQudit) ⟶ ⟨Qubit⟩ => f ⊗ₘ 𝟙 R)
    teleportation_causal_composite).trans (id_tensorHom_id _ _)

open scoped ComplexOrder in
private def coin : POVM Qubit (Fin 2) where
  op _ := (1 / 2 : ℂ) • 1
  positive _ := LinearMap.isPositive_one.smul_of_nonneg
    (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  sum_op := by simp only [Fin.sum_univ_two, ← add_smul]; norm_num

-- A nonprojective POVM pulls a classical projection back to a nonprojective effect.
example (i : Fin 2) :
    (coin.outcomeChannel (ZBasis 2)).toCPMap.dual.toSuperoperator
      (Operator.outer (ZBasis 2 i) (ZBasis 2 i)) = (1 / 2 : ℂ) • 1 :=
  POVM.dual_outcomeChannel_projection coin (ZBasis 2) i

-- Its Heisenberg map is unital, by the channel's normalization on all operators.
example : (coin.outcomeChannel (ZBasis 2)).toCPMap.dual.toSuperoperator 1 = 1 :=
  (CPMap.isTracePreserving_iff_dual_one _).mp (coin.outcomeChannel (ZBasis 2)).tracePreserving
