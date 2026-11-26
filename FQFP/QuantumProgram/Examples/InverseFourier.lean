/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the inverse circuit operator and phase readout.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/InverseQFTTriple.lean
Qhl/Register/Fourier.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Examples.FourierArbitrary

/-!
# The inverse Fourier circuit

The mirror network runs first. Stage `k` of the inverse visits forward stage
`n - 1 - k`, undoing its rungs from last to first with negative angles before
applying Hadamard. Both counters increase, as in the forward program.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit

namespace QuantumProgram

noncomputable section

/-- An increasing counter can undo a gate sequence by visiting its inverses in reverse order. -/
theorem UnitaryProgram.gatePrefix_cancel_reverse {H : Qudit} (g u : ℕ → UnitaryProgram H) (m : ℕ)
    (undo : ∀ k < m, ∀ v : H.state, (u k).toOperator ((g (m - 1 - k)).toOperator v) = v)
    (v : H.state) :
    (gatePrefix u m).toOperator ((gatePrefix g m).toOperator v) = v := by
  have walk := toOperator_gatePrefix_apply u m (fun k => (gatePrefix g (m - k)).toOperator v)
    (by
      intro k hk
      have h : m - k = (m - 1 - k) + 1 := by lia
      rw [h, toOperator_gatePrefix_succ, mul_apply_eq_comp, undo k hk,
        show m - (k + 1) = m - 1 - k by lia])
  simpa only [Nat.sub_zero, Nat.sub_self, toOperator_gatePrefix_zero, one_apply_eq_self] using walk

namespace InverseFourier

open FourierIteration

/-- The mathematical inverse transform, the adjoint of the normalized DFT. -/
def iqftOp (n : ℕ) : Operator (Memory n) := (qftOp n).adjoint

/-- The inverse DFT applied as one gate on the complete register. -/
def wholeGate (n : ℕ) : Command Unit (Fin n) (Memory n) :=
  .unitary (fun _ => id) (fun _ _ => .gateHom .whole (qftGate n)†)

/-- The whole-register inverse gate recovers any unit vector from its DFT, even at width zero. -/
theorem sourceDeriv_wholeGate {n : ℕ} (v : UnitState (Memory n)) :
    SourceDerivTot (.ofEffect (Assertion.pure (UnitState.map (qftGate n) v)) fun _ => True)
      (wholeGate n) (.ofEffect (Assertion.pure v) fun _ => True) :=
  SourceDerivTot.unitary_pure _ _ (fun _ => UnitState.map (qftGate n) v) (fun _ => v)
    (fun _ _ => Function.injective_id) (fun _ _ => hom_adjoint_apply_of_isIsometry (qftGate n) v)

/-- Total correctness of the single-gate inverse on an arbitrary transformed unit vector. -/
theorem validTot_wholeGate {n : ℕ} (v : UnitState (Memory n)) :
    validTot (Assertion.pure (UnitState.map (qftGate n) v)) (wholeGate n) (Assertion.pure v) := by
  simpa only [CQAssertion.toAssn_ofEffect_true] using (sourceDeriv_wholeGate v).sound

variable (n : ℕ) [NeZero n]

/-- The negative-angle rung selected by the two inverse counters. -/
def inverseRungGate (k t : ℕ) : UnitaryProgram (Memory n) :=
  FourierLadder.phaseGate (control n (n - 1 - k)) (control n (n - 1 - t)) (-angle (k - 1 - t))

/-- Run one negative-angle rung on the two counter-selected wires. -/
def inverseRung : Command Store (Fin n) (Memory n) :=
  .unitary (fun σ => ![control n (n - 1 - σ.1), control n (n - 1 - σ.2)])
    (fun σ _ => inverseRungGate n σ.1 σ.2)

/-- Undo the current stage's ladder using the stage counter as the inner bound. -/
def inverseLadder : Command Store (Fin n) (Memory n) :=
  .counted rungCounter Prod.fst (inverseRung n)

/-- Hadamard on the stage head counted from the right. -/
def inverseHadamard : Command Store (Fin n) (Memory n) :=
  .unitary (fun σ (_ : Fin 1) => control n (n - 1 - σ.1))
    (fun σ _ => hadamardGate n (n - 1 - σ.1))

/-- Undo all stages, starting on the rightmost wire. -/
def inverseIteration : Command Store (Fin n) (Memory n) :=
  .counted stageCounter (fun _ => n) ((inverseLadder n).seq (inverseHadamard n))

/-- The counted inverse circuit reuses the forward mirror network before undoing the stages. -/
def inverseCircuit : Command Store (Fin n) (Memory n) := (reversal n).seq (inverseIteration n)

/-- Gate sequence of a reversed stage, in execution order. -/
def inverseStageProgram (k : ℕ) : UnitaryProgram (Memory n) :=
  (UnitaryProgram.gatePrefix (inverseRungGate n k) k).seq (hadamardGate n (n - 1 - k))

/-- Unrolled gate sequence of the counted inverse circuit. -/
def inverseProgram : UnitaryProgram (Memory n) :=
  (UnitaryProgram.gatePrefix (mirrorGate n) (n / 2)).seq
    (.gatePrefix (inverseStageProgram n) n)

/-- Amplitude operator assembled from the reversed circuit's individual gates. -/
def iqftRevCirOp : Operator (Memory n) := (inverseProgram n).toOperator

variable {n}

private theorem inverseRung_adjoint {k t : ℕ} (hk : k < n) (ht : t < k) :
    (inverseRungGate n k t).denoteHom = (rungGate n (n - 1 - k) (k - 1 - t)).denoteHom† := by
  have hj : n - 1 - t = (n - 1 - k) + 1 + (k - 1 - t) := by lia
  rw [inverseRungGate, hj, FourierLadder.phaseGate_neg]
  rfl

/-- One active inverse rung undoes the corresponding positive-angle gate. -/
theorem inverseRung_cancel {k t : ℕ} (hk : k < n) (ht : t < k) (v : (Memory n).state) :
    (inverseRungGate n k t).toOperator
      ((rungGate n (n - 1 - k) (k - 1 - t)).toOperator v) = v := by
  change (inverseRungGate n k t).denoteHom.hom
    ((rungGate n (n - 1 - k) (k - 1 - t)).denoteHom.hom v) = v
  rw [inverseRung_adjoint hk ht]
  exact hom_adjoint_apply_of_isIsometry _ _

/-- A second Hadamard on the same wire restores the input. -/
theorem hadamardGate_twice (k : ℕ) (v : (Memory n).state) :
    (hadamardGate n k).toOperator ((hadamardGate n k).toOperator v) = v := by
  let H := hadamardGate n k
  have h : H.denoteHom.hom.adjoint = H.denoteHom.hom :=
    (isSelfAdjoint_hom (Register.isSelfAdjoint_liftEnd _ Qubit.isSelfAdjoint_H)).star_eq
  change H.denoteHom.hom (H.denoteHom.hom v) = v
  simpa only [h] using hom_adjoint_apply_of_isIsometry H.denoteHom v

/-- An inverse stage cancels the corresponding forward stage on the entire state space. -/
theorem inverseStage_cancel (k : ℕ) (hk : k < n) (v : (Memory n).state) :
    (inverseStageProgram n k).toOperator ((stageProgram n (n - 1 - k)).toOperator v) = v := by
  let H := hadamardGate n (n - 1 - k)
  let R := rungGate n (n - 1 - k)
  change H.toOperator ((UnitaryProgram.gatePrefix (inverseRungGate n k) k).toOperator
    ((UnitaryProgram.gatePrefix R (n - 1 - (n - 1 - k))).toOperator (H.toOperator v))) = v
  rw [show n - 1 - (n - 1 - k) = k by lia, UnitaryProgram.gatePrefix_cancel_reverse]
  · exact hadamardGate_twice _ _
  · exact fun _ ht w => inverseRung_cancel hk ht w

private theorem mirrorPrefix_twice (v : (Memory n).state) :
    let U := (UnitaryProgram.gatePrefix (mirrorGate n) (n / 2)).toOperator
    U (U v) = v := by
  let U := (UnitaryProgram.gatePrefix (mirrorGate n) (n / 2)).toOperator
  have h : U ∘ₗ U = LinearMap.id := by
    apply (registerBasis (ZBasis 2) n).toBasis.ext
    intro x
    rw [OrthonormalBasis.coe_toBasis, registerBasis_apply, LinearMap.comp_apply]
    change (UnitaryProgram.gatePrefix _ _).toOperator
      ((UnitaryProgram.gatePrefix _ _).toOperator _) = _
    rw [mirrorPrefix_product, mirrorPrefix_product]
    apply congrArg (fun w => (product w).val)
    funext i
    simp [Function.comp_def]
  exact LinearMap.congr_fun h v

/-- Running the gate-level inverse after the gate-level forward transform recovers every vector. -/
theorem iqftRevCirOp_qftCirOp (v : (Memory n).state) : iqftRevCirOp n (qftCirOp n v) = v := by
  let S := (UnitaryProgram.gatePrefix (stageProgram n) n).toOperator
  let M := (UnitaryProgram.gatePrefix (mirrorGate n) (n / 2)).toOperator
  change (UnitaryProgram.gatePrefix (inverseStageProgram n) n).toOperator (M (M (S v))) = v
  rw [mirrorPrefix_twice (S v)]
  exact UnitaryProgram.gatePrefix_cancel_reverse _ _ n (inverseStage_cancel (n := n)) v

/-- The reversed circuit realizes the mathematical inverse DFT on arbitrary inputs. -/
theorem iqftRevCirOp_eq_iqftOp : iqftRevCirOp n = iqftOp n := by
  apply LinearMap.ext
  intro v
  have h := iqftRevCirOp_qftCirOp (iqftOp n v)
  rw [qftCirOp_apply_eq] at h
  have cancel : qftOp n (iqftOp n v) = v :=
    LinearMap.congr_fun (congrArg Qudit.Hom.hom (IsUnitary.dagger_comp_eq_id (qftGate n))) v
  rwa [cancel] at h

/-- The circuit decodes the full suffix-phase product to the original computational word. -/
theorem iqftRevCirOp_fourierState (x : Fin n → Fin 2) :
    iqftRevCirOp n (fourierState x).val = registerBasis (ZBasis 2) n x := by
  rw [← qftCirOp_basis]
  exact iqftRevCirOp_qftCirOp _

/-- Circuit-certified readout of a reversed suffix-phase product by the inverse DFT. -/
theorem iqftOp_product_phaseState (x : Fin n → Fin 2) :
    iqftOp n (product fun i => Qubit.phaseState (suffixAngle x i.rev)).val =
      (product fun i => UnitState.ofBasis (ZBasis 2) (x i)).val := by
  rw [← iqftRevCirOp_eq_iqftOp]
  exact (iqftRevCirOp_fourierState x).trans (registerBasis_apply _ _)

end InverseFourier

end

end QuantumProgram
