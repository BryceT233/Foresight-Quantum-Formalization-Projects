/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/LocalConjugation.lean (liftSO_conj_liftF, conj_regLift_conj, mapSO_initLift_conj)
Qhl/Program/KrausFrame.lean (frame obligations for local program primitives)

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Frame.Kraus
public import FQFP.QuantumProgram.Register.Tensor
public import FQFP.CQM.Qudit.Channel.MeasurePrepare
public import FQFP.CQM.Qudit.Measurement.Ensemble

/-!
# Local operations on disjoint tensor registers

Paths in the same tensor decomposition are disjoint when they diverge at a tensor node.
Arbitrary superoperators lifted along such paths commute on the full operator space.
This supplies Kraus frames for channels, including local replacement, and for individual
measurement outcomes on entangled inputs.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit

namespace QuantumProgram.Register

/-- Two paths in a tensor decomposition diverge at some tensor node. -/
inductive Disjoint : {H A B : Qudit} → Register H A → Register H B → Prop where
  /-- The first path goes left and the second goes right. -/
  | leftRight {A B L R : Qudit} (p : Register L A) (q : Register R B) : Disjoint p.left q.right
  /-- The first path goes right and the second goes left. -/
  | rightLeft {A B L R : Qudit} (p : Register R A) (q : Register L B) : Disjoint p.right q.left
  /-- Both paths enter the same left subtree and diverge inside it. -/
  | left {H A B R : Qudit} {p : Register H A} {q : Register H B} (h : Disjoint p q) :
      Disjoint (p.left (B := R)) q.left
  /-- Both paths enter the same right subtree and diverge inside it. -/
  | right {H A B L : Qudit} {p : Register H A} {q : Register H B} (h : Disjoint p q) :
      Disjoint (p.right (A := L)) q.right

/-- Distinct indices in a heterogeneous tensor memory give disjoint register paths. -/
theorem disjoint_site {n : ℕ} (D : Fin n → Qudit) {i j : Fin n} (h : i ≠ j) :
    Disjoint (site D i) (site D j) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact (h rfl).elim
    · exact .leftRight _ _
    · exact .rightLeft _ _
    · exact .right (ih (Fin.tail D) (fun e => h (congrArg Fin.succ e)))

noncomputable section

variable {H A B : Qudit}

/-- Extend an operator by identities along the register path, preserving its star algebra. -/
def liftOperator : {H A : Qudit} → Register H A → Operator A →⋆ₐ[ℂ] Operator H
  | _, _, .whole => StarAlgHom.id ℂ _
  | _, _, .left r => (Operator.tensorOneHom _ _).comp r.liftOperator
  | _, _, .right r => (Operator.oneTensorHom _ _).comp r.liftOperator

/-- The operator embedding acts on a morphism by the circuit's register extension. -/
theorem liftOperator_hom (r : Register H A) (f : A ⟶ A) :
    r.liftOperator f.hom = (r.liftHom f).hom := by
  induction r with
  | whole => rfl
  | left r ih => exact congrArg (Operator.tensorOneHom _ _) (ih f)
  | right r ih => exact congrArg (Operator.oneTensorHom _ _) (ih f)

/-- Operators lifted along disjoint paths commute before taking state conjugations. -/
theorem Disjoint.commute_liftOperator {p : Register H A} {q : Register H B} (h : Disjoint p q)
    (X : Operator A) (Y : Operator B) : Commute (p.liftOperator X) (q.liftOperator Y) := by
  induction h with
  | leftRight => exact Operator.commute_tensor_one_one_tensor _ _
  | rightLeft => exact (Operator.commute_tensor_one_one_tensor _ _).symm
  | left _ ih => exact (ih X Y).map (Operator.tensorOneHom _ _)
  | right _ ih => exact (ih X Y).map (Operator.oneTensorHom _ _)

/-- Extend a local operation by the identity superoperator on every spectator. -/
def liftSuperoperator : {H A : Qudit} → Register H A → Superoperator A A → Superoperator H H
  | _, _, .whole, Φ => Φ
  | _, _, .left r, Φ => Superoperator.tensor (r.liftSuperoperator Φ) LinearMap.id
  | _, _, .right r, Φ => Superoperator.tensor LinearMap.id (r.liftSuperoperator Φ)

/-- Conjugation by a lifted operator is the lift of the local conjugation. -/
theorem conjugate_liftOperator (r : Register H A) (K : Operator A) :
    Superoperator.conjugate (r.liftOperator K) =
      r.liftSuperoperator (Superoperator.conjugate K) := by
  induction r with
  | whole => rfl
  | left r ih =>
    exact (Superoperator.conjugate_tensor (r.liftOperator K) LinearMap.id).trans
      (congrArg₂ Superoperator.tensor (ih K) (Superoperator.conjugate_id _))
  | right r ih =>
    exact (Superoperator.conjugate_tensor LinearMap.id (r.liftOperator K)).trans
      (congrArg₂ Superoperator.tensor (Superoperator.conjugate_id _) (ih K))

/-- Disjoint local operations commute on every operator on the full memory. -/
theorem Disjoint.commute_liftSuperoperator {p : Register H A} {q : Register H B}
    (h : Disjoint p q) (Φ : Superoperator A A) (Ψ : Superoperator B B) :
    Commute (p.liftSuperoperator Φ) (q.liftSuperoperator Ψ) := by
  induction h with
  | leftRight | rightLeft =>
    simp only [Commute, SemiconjBy, Module.End.mul_eq_comp, liftSuperoperator,
      ← Superoperator.tensor_comp, LinearMap.id_comp, LinearMap.comp_id]
  | left _ ih | right _ ih =>
    simp only [Commute, SemiconjBy, Module.End.mul_eq_comp, liftSuperoperator,
      ← Superoperator.tensor_comp, LinearMap.id_comp]
    congr 1
    exact (ih Φ Ψ).eq

/-- A channel on a register extends to a channel on its enclosing memory. -/
def liftChannel : {H A : Qudit} → Register H A → QuantumChannel A A → QuantumChannel H H
  | _, _, .whole, Φ => Φ
  | _, _, .left r, Φ => (r.liftChannel Φ).tensor (.id _)
  | _, _, .right r, Φ => (QuantumChannel.id _).tensor (r.liftChannel Φ)

/-- The lifted channel uses the same extension as its underlying superoperator. -/
theorem liftChannel_toSuperoperator (r : Register H A) (Φ : QuantumChannel A A) :
    (r.liftChannel Φ).toSuperoperator = r.liftSuperoperator Φ.toSuperoperator := by
  induction r with
  | whole => rfl
  | left r ih => exact congrArg (Superoperator.tensor · LinearMap.id) (ih Φ)
  | right r ih => exact congrArg (Superoperator.tensor LinearMap.id ·) (ih Φ)

/-- Lift every branch of a local instrument and retain its original outcome type. -/
def liftInstrument {ι : Type*} [Fintype ι] :
    {H A : Qudit} → Register H A → Instrument A A ι → Instrument H H ι
  | _, _, .whole, I => I
  | _, _, .left r, I => (r.liftInstrument I).tensorRight (.id _)
  | _, _, .right r, I => (r.liftInstrument I).tensorLeft (.id _)

/-- Each full-memory branch is the extension of the corresponding local operation. -/
theorem liftInstrument_branch {ι : Type*} [Fintype ι] (r : Register H A) (I : Instrument A A ι)
    (i : ι) : (r.liftInstrument I).branch i = r.liftSuperoperator (I.branch i) := by
  induction r with
  | whole => rfl
  | left r ih => exact congrArg (Superoperator.tensor · LinearMap.id) (ih I)
  | right r ih => exact congrArg (Superoperator.tensor LinearMap.id ·) (ih I)

/-- Reset the selected register to a density state while acting identically on spectators. -/
def initializeTo (p : Register H A) (τ : Density A) : QuantumChannel H H :=
  p.liftChannel (QuantumChannel.replacement A τ)

/-- Resetting the left factor retains the right marginal, including for entangled inputs. -/
theorem initializeTo_left_apply (τ : Density A) (ρ : Operator (A ⊗ B)) :
    ((whole.left : Register (A ⊗ B) A).initializeTo τ).toSuperoperator ρ =
      Operator.tensor τ.op (Operator.partialTraceLeft ρ) := by
  induction ρ using Operator.tensor_induction_on with
  | htensor X Y =>
    change Superoperator.tensor (QuantumChannel.replacement A τ).toSuperoperator LinearMap.id
      (Operator.tensor X Y) = _
    rw [Superoperator.tensor_apply, QuantumChannel.replacement_apply, LinearMap.id_apply,
      Operator.partialTraceLeft_tensor]
    simp only [Operator.tensor, TensorProduct.map_smul_left, TensorProduct.map_smul_right]
  | hadd X Y hX hY =>
    simp only [map_add, hX, hY, Operator.tensor, TensorProduct.map_add_right]

/-- Resetting the right factor retains the left marginal at its original weight. -/
theorem initializeTo_right_apply (τ : Density B) (ρ : Operator (A ⊗ B)) :
    ((whole.right : Register (A ⊗ B) B).initializeTo τ).toSuperoperator ρ =
      Operator.tensor (Operator.partialTraceRight ρ) τ.op := by
  induction ρ using Operator.tensor_induction_on with
  | htensor X Y =>
    change Superoperator.tensor LinearMap.id (QuantumChannel.replacement B τ).toSuperoperator
      (Operator.tensor X Y) = _
    rw [Superoperator.tensor_apply, QuantumChannel.replacement_apply, LinearMap.id_apply,
      Operator.partialTraceRight_tensor]
    simp only [Operator.tensor, TensorProduct.map_smul_left, TensorProduct.map_smul_right]
  | hadd X Y hX hY =>
    simp only [map_add, hX, hY, Operator.tensor, TensorProduct.map_add_left]

/-- Local action on a disjoint path preserves conjugation by any frame operator. -/
theorem Disjoint.commute_conjugate {p : Register H A} {q : Register H B} (h : Disjoint p q)
    (Φ : Superoperator A A) (K : Operator B) :
    Function.Commute (p.liftSuperoperator Φ) (Superoperator.conjugate (q.liftOperator K)) := by
  rw [conjugate_liftOperator]
  exact fun ρ => LinearMap.congr_fun (h.commute_liftSuperoperator Φ _).eq ρ

end

end QuantumProgram.Register

namespace QuantumProgram.Command.KrausFrame

variable {S Cell : Type*} {H : Qudit} {A B : S → Qudit}
    {q : (σ : S) → Register H (B σ)} (K : (σ : S) → Operator (B σ))

/-- Disjointness at each store gives the channel frame, including for local replacement. -/
theorem liftChannel {p : (σ : S) → Register H (A σ)} (Φ : (σ : S) → QuantumChannel (A σ) (A σ))
    (h : ∀ σ, (p σ).Disjoint (q σ)) :
    (channel (Cell := Cell) (fun σ => (p σ).liftChannel (Φ σ))).KrausFrame
      (fun σ => (q σ).liftOperator (K σ)) := by
  intro σ
  rw [Register.liftChannel_toSuperoperator]
  exact (h σ).commute_conjugate _ _

/-- A local unitary supplies its frame from disjointness on each executable store. -/
theorem gateHom {k : ℕ} (r : S → Fin k → Cell)
    (p : ∀ σ, Function.Injective (r σ) → Register H (A σ))
    (U : ∀ σ, Function.Injective (r σ) → (A σ ⟶ A σ)) [∀ σ hi, DaggerCategory.IsUnitary (U σ hi)]
    (h : ∀ σ hi, (p σ hi).Disjoint (q σ)) :
    (unitary r (fun σ hi => .gateHom (p σ hi) (U σ hi))).KrausFrame
      (fun σ => (q σ).liftOperator (K σ)) := by
  intro σ hi
  change Function.Commute (Superoperator.conjugate ((p σ hi).liftHom (U σ hi)).hom) _
  rw [← Register.liftOperator_hom, Register.conjugate_liftOperator]
  exact (h σ hi).commute_conjugate _ _

/-- Every outcome of a disjoint local instrument preserves the frame if its write-back does. -/
theorem liftInstrument {k m : ℕ} (r : S → Fin k → Cell)
    (p : ∀ σ, Function.Injective (r σ) → Register H (A σ))
    (I : ∀ σ, Function.Injective (r σ) → Instrument (A σ) (A σ) (Fin m)) (upd : Fin m → S → S)
    (h : ∀ σ hi, (p σ hi).Disjoint (q σ))
    (hw : ∀ i σ, (q (upd i σ)).liftOperator (K (upd i σ)) = (q σ).liftOperator (K σ)) :
    (measure r (fun σ hi => (p σ hi).liftInstrument (I σ hi)) upd).KrausFrame
      (fun σ => (q σ).liftOperator (K σ)) := by
  refine ⟨?_, hw⟩
  intro σ hi i
  rw [Register.liftInstrument_branch]
  exact (h σ hi).commute_conjugate _ _

end QuantumProgram.Command.KrausFrame
