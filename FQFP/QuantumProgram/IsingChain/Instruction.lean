/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the field and coupling rotations in a first-order Ising slice.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/TrotterTFIMTriple.lean
Qhl/Gate/Rx.lean
Qhl/Gate/Rzz.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.CQM.Qudit.State.Pure.Qubit
public import FQFP.CQM.Qudit.TensorPower
public import FQFP.QuantumProgram.Logic.ExactExpectation
public import FQFP.QuantumProgram.Logic.For
public import FQFP.QuantumProgram.Logic.SourceUnitary
public import FQFP.QuantumProgram.Trotter

/-!
# Physical gates of the open transverse-field Ising chain

With `e` edges the register has `e + 1` sites. Each slice executes the transverse fields
in site order and then the Ising couplings in edge order. Its instruction list supplies
the unitary program, the Hoare command and the resource count.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit

namespace QuantumProgram

noncomputable section

/-- Pauli X as a self-adjoint single-qubit Hamiltonian. -/
def pauliXHamiltonian : selfAdjoint (Operator Qubit) :=
  ⟨_, isSelfAdjoint_hom Qubit.isSelfAdjoint_pauliX⟩

/-- Pauli Z as a self-adjoint single-qubit Hamiltonian. -/
def pauliZHamiltonian : selfAdjoint (Operator Qubit) :=
  ⟨_, isSelfAdjoint_hom Qubit.isSelfAdjoint_pauliZ⟩

/-- The rotation `exp(-i θ X/2)` on one qubit. -/
def rx (θ : ℝ) : End Qubit :=
  (hamiltonianGate pauliXHamiltonian (θ / 2)).denoteEnd

instance (θ : ℝ) : IsUnitary (rx θ).asHom := by unfold rx; infer_instance

/-- The rotation `exp(-i θ Z/2)` on one qubit. -/
def rz (θ : ℝ) : End Qubit :=
  (hamiltonianGate pauliZHamiltonian (θ / 2)).denoteEnd

instance (θ : ℝ) : IsUnitary (rz θ).asHom := by unfold rz; infer_instance

namespace IsingChain

variable {e : ℕ}

/-- One native rotation or a nearest-neighbor CNOT directed from left to right. -/
inductive Gate (e : ℕ) where
  /-- Rotate a site about the X axis. -/
  | rx (site : Fin (e + 1)) (angle : ℝ)
  /-- Rotate a site about the Z axis. -/
  | rz (site : Fin (e + 1)) (angle : ℝ)
  /-- Add the left endpoint bit to the right endpoint modulo two. -/
  | cnot (edge : Fin e)

/-- Interpret an instruction using the single-site and adjacent-pair operator embeddings. -/
def Gate.program : Gate e → UnitaryProgram (tensorPower Qubit e)
  | .rx i θ => .liftGate (siteOp Qubit e i) (QuantumProgram.rx θ)
  | .rz i θ => .liftGate (siteOp Qubit e i) (QuantumProgram.rz θ)
  | .cnot j => .liftGateHom (adjacentOp Qubit e j) Qubit.CNOT

/-- Emit the compute-rotate-uncompute implementation of an edge rotation. -/
def edgeGates (j : Fin e) (θ : ℝ) : List (Gate e) :=
  [.cnot j, .rz j.succ θ, .cnot j]

/-- All transverse-field rotations in site order. -/
def fieldGates (h : Fin (e + 1) → ℝ) (δ : ℝ) : List (Gate e) :=
  List.ofFn (fun i => .rx i (2 * h i * δ))

/-- All parity rotations in edge order. -/
def interactionGates (J : Fin e → ℝ) (δ : ℝ) : List (Gate e) :=
  (List.ofFn (fun j => edgeGates j (2 * J j * δ))).flatten

/-- One Lie–Trotter slice, with signed coefficients and the physical half-angle convention. -/
def slice (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (δ : ℝ) : List (Gate e) :=
  fieldGates h δ ++ interactionGates J δ

/-- The physical instructions for `r` equal steps over time `t`. -/
def circuit (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) (r : ℕ) : List (Gate e) :=
  (List.replicate r (slice h J (t / r))).flatten

/-- Execute a physical instruction list in order. -/
def program (gs : List (Gate e)) : UnitaryProgram (tensorPower Qubit e) :=
  .sequence (gs.map Gate.program)

/-- Later instructions multiply on the left. -/
theorem toOperator_append (xs ys : List (Gate e)) :
    (program (xs ++ ys)).toOperator =
      (program ys).toOperator * (program xs).toOperator := by
  simp [program, UnitaryProgram.toOperator_sequence]

/-- Interpreting a repeated instruction list raises its operator to the same power. -/
theorem toOperator_replicate (k : ℕ) (gs : List (Gate e)) :
    (program (List.replicate k gs).flatten).toOperator = (program gs).toOperator ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, toOperator_append, ih, pow_succ]

/-- Ordered physical operands: a rotation site, or the control and target of a CNOT. -/
def Gate.operands : Gate e → (k : ℕ) × (Fin k ↪ Fin (e + 1))
  | .rx i _ | .rz i _ => ⟨1, ⟨fun _ => i, Function.injective_of_subsingleton _⟩⟩
  | .cnot j => ⟨2, ⟨fun k => ⟨j.val + k.val, by lia⟩, fun a b h =>
      Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩⟩

variable {Store : Type*}

/-- Execute the instruction with its physical operand register in the command language. -/
def Gate.command (g : Gate e) : Command Store (Fin (e + 1)) (tensorPower Qubit e) :=
  .unitary (fun _ => g.operands.2) (fun _ _ => g.program)

/-- A native gate preserves the classical condition and pulls back the final effect. -/
theorem Gate.sourceDeriv_command (g : Gate e) (A : Assertion Store (tensorPower Qubit e))
    (φ : Store → Prop) :
    SourceDerivTot (.ofEffect (A.channelPre fun _ => g.program.toChannel) φ) g.command
      (.ofEffect A φ) := by
  unfold Gate.command
  apply SourceDerivTot.unitary_of_le _ _ (fun _ h => h) (fun _ _ => g.operands.2.injective)
  intro σ _
  simp [Assertion.channelPre, Assertion.unitaryPre, g.operands.2.injective]

/-- Execute exactly the native instructions in the list being costed. -/
def command (gs : List (Gate e)) : Command Store (Fin (e + 1)) (tensorPower Qubit e) :=
  .forList gs Gate.command

/-- The total Hoare precondition of the native list pulls any final effect through its channel. -/
theorem derivTot_command (gs : List (Gate e)) (A : Assertion Store (tensorPower Qubit e)) :
    DerivTot (A.channelPre fun _ => (program gs).toChannel) (command gs) A := by
  let pre (g : Gate e) (B : Assertion Store (tensorPower Qubit e)) :=
    B.channelPre fun _ => g.program.toChannel
  have hgate (g : Gate e) (B : Assertion Store (tensorPower Qubit e)) :
      DerivTot (pre g B) g.command B := by
    simpa only [CQAssertion.toAssn_ofEffect_true] using
      (g.sourceDeriv_command B (fun _ => True)).toDerivTot
  have hpre : gs.foldr pre A = A.channelPre fun _ => (program gs).toChannel := by
    induction gs with
    | nil =>
      funext σ
      apply Subtype.ext
      change _ = (CPQudit.pure.map (𝟙 _))†.toSuperoperator _
      rw [CategoryTheory.Functor.map_id, dagger_id]
      rfl
    | cons g gs ih =>
      rw [List.foldr_cons, ih]
      funext σ
      apply Subtype.ext
      have hc : (program (g :: gs)).denoteHom = g.program.denoteHom ≫ (program gs).denoteHom := by
        simp only [program, List.map_cons, UnitaryProgram.denoteHom_sequence, List.foldr_cons]
      change _ = (CPQudit.pure.map (program (g :: gs)).denoteHom)†.toSuperoperator _
      rw [hc, CategoryTheory.Functor.map_comp, dagger_comp]
      rfl
  rw [← hpre]
  exact DerivTot.forList hgate gs A

/-- For every weighted input the command has exactly the native circuit's post-expectation. -/
theorem postH_command (gs : List (Gate e)) (A : Assertion Store (tensorPower Qubit e))
    (s : CQState Store (tensorPower Qubit e)) :
    (Configuration.mk (some (command gs)) s).PostH (fun σ => A σ) =
      ENNReal.ofReal ((s.map (program gs).toChannel).expectation (A s.store)) := by
  rw [PostH_eq_of_complement (derivTot_command gs A).sound
    (by rw [← Assertion.channelPre_compl]; exact (derivTot_command gs A.compl).sound)]
  exact congrArg (fun z : ℂ => ENNReal.ofReal z.re)
    ((program gs).toChannel.toCPMap.trace_dual s.op (A s.store))

/-- A terminal Born test on a normalized input reads the native circuit's outcome probability. -/
theorem postH_command_probability {ι : Type*} [Fintype ι] (gs : List (Gate e))
    (M : POVM (tensorPower Qubit e) ι) (ρ : Density (tensorPower Qubit e)) (i : ι) (σ : Store) :
    let c := Configuration.mk (some (command gs)) ⟨σ, ρ.op, ρ.positive⟩
    (c.PostH (fun _ => M.op i)).toReal = M.probability (ρ.map (program gs).denoteHom) i := by
  intro c
  let A : Assertion Store (tensorPower Qubit e) := fun _ => ⟨M.op i, M.op_nonneg i, M.op_le_one i⟩
  have he : c.PostH (fun _ => M.op i) =
      ENNReal.ofReal (M.probability (ρ.map (program gs).denoteHom) i) :=
    postH_command gs A ⟨σ, ρ.op, ρ.positive⟩
  exact (congrArg ENNReal.toReal he).trans (ENNReal.toReal_ofReal (M.probability_nonneg _ _))

end IsingChain

end

end QuantumProgram
