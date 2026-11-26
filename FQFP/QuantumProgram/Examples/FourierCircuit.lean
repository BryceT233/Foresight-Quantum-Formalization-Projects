/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the reversal loop and its composition with the Fourier stages.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/QFTTriple.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Examples.FourierIteration
public import FQFP.QuantumProgram.RegisterPermutation

/-!
# The Fourier circuit with final wire reversal

After the Fourier stages, a counted loop swaps pairs from the outside in.
The reversal rule works for any product of qubit states. Composing the two loops
places the phase of the suffix beginning at wire `i.rev` on output wire `i`.
-/

@[expose] public section

open Qudit

namespace QuantumProgram.FourierIteration

noncomputable section

section

variable (n : ℕ) [NeZero n]

/-- Exchange wire `k` and its mirror image in the full register. -/
def mirrorGate (k : ℕ) : UnitaryProgram (Memory n) :=
  .permuteSites (ZBasis 2) (Equiv.swap (control n k) (control n k).rev)

/-- Exchange the wire selected by the stage counter with its mirror image. -/
def mirrorSwap : Command Store (Fin n) (Memory n) :=
  .unitary (fun σ => ![control n σ.1, (control n σ.1).rev])
    (fun σ _ => mirrorGate n σ.1)

/-- Reverse wire order by counting from zero to half the register width. -/
def reversal : Command Store (Fin n) (Memory n) :=
  .counted stageCounter (fun _ => n / 2) (mirrorSwap n)

/-- The Fourier stages followed by the counted SWAP network. -/
def circuit : Command Store (Fin n) (Memory n) := (iteration n).seq (reversal n)

end

variable {n : ℕ}

/-- After `k` mirror swaps the two outer runs of length `k` hold their final factors. -/
def reversalFactors (v : Fin n → UnitState Qubit) (k : ℕ) (i : Fin n) : UnitState Qubit :=
  if i.val < k ∨ i.rev.val < k then v i.rev else v i

/-- Before the first swap each factor is in its original position. -/
theorem reversalFactors_zero (v : Fin n → UnitState Qubit) : reversalFactors v 0 = v := by
  funext i
  simp [reversalFactors]

/-- Half the width in mirror swaps reverses every factor. -/
theorem reversalFactors_full (v : Fin n → UnitState Qubit) :
    reversalFactors v (n / 2) = v ∘ Fin.rev := by
  funext i
  unfold reversalFactors
  split
  · rfl
  · rename_i h
    have hm : i = i.rev := Fin.ext (by have := i.isLt; simp only [Fin.val_rev] at *; lia)
    exact congrArg v hm

variable [NeZero n]

private theorem control_val {k : ℕ} (hk : k < n / 2) : (control n k).val = k :=
  Nat.mod_eq_of_lt (by lia)

private theorem control_lt_rev {k : ℕ} (hk : k < n / 2) : control n k < (control n k).rev := by
  change (control n k).val < (control n k).rev.val
  rw [Fin.val_rev, control_val hk]
  lia

/-- The mirror wires are distinct at every iteration of the reversal loop. -/
theorem swap_injective {σ : Store} (hk : σ.1 < n / 2) :
    Function.Injective ![control n σ.1, (control n σ.1).rev] := by
  have hne := (control_lt_rev hk).ne
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

private theorem reversalFactors_step (v : Fin n → UnitState Qubit) {k : ℕ} (hk : k < n / 2) :
    reversalFactors v k ∘ (Equiv.swap (control n k) (control n k).rev).symm =
      reversalFactors v (k + 1) := by
  let c := control n k
  have hc : c.val = k := control_val hk
  have hr : ¬n - (k + 1) < k := by lia
  funext i
  change reversalFactors v k (Equiv.swap c c.rev i) = reversalFactors v (k + 1) i
  by_cases h : i = c
  · subst i
    simp [reversalFactors, hc, hr]
  by_cases h' : i = c.rev
  · subst i
    simp [reversalFactors, hc, hr]
  have h₁ : i.val ≠ k := fun hi => h (Fin.ext (hi.trans hc.symm))
  have h₂ : i.rev.val ≠ k := by
    intro hi
    have he : i.rev = c := Fin.ext (hi.trans hc.symm)
    exact h' (by rw [← he, Fin.rev_rev])
  rw [Equiv.swap_apply_of_ne_of_ne h h']
  simp only [reversalFactors, show i.val < k + 1 ↔ i.val < k by lia,
    show i.rev.val < k + 1 ↔ i.rev.val < k by lia]

/-- The physical swap advances the product vector in the reversal loop. -/
theorem mirrorGate_product (v : Fin n → UnitState Qubit) {k : ℕ} (hk : k < n / 2) :
    (mirrorGate n k).toOperator (product (reversalFactors v k)).val =
      (product (reversalFactors v (k + 1))).val :=
  (UnitaryProgram.permuteSites_productState (ZBasis 2) _ (reversalFactors v k)).trans
    (congrArg (fun w => (product w).val) (reversalFactors_step v hk))

/-- The counted reversal reverses every product input and records its exact exit counter. -/
theorem sourceDeriv_reversal (v : Fin n → UnitState Qubit) :
    SourceDerivTot (Store := Store) (H := Memory n)
      (.ofEffect (Assertion.pure (product v)) fun _ => True) (reversal n)
      (.ofEffect (Assertion.pure (product (v ∘ Fin.rev))) fun σ => σ.1 = n / 2) := by
  let J := fun k => Assertion.pure (Store := Store) (product (reversalFactors v k))
  have d : SourceDerivTot (.ofEffect (J 0) fun _ => True) (reversal n)
      (.ofEffect (J (n / 2)) fun σ => True ∧ σ.1 = n / 2) := by
    apply SourceDerivTot.countedFamily stageCounter (fun _ => n / 2) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) J (fun _ _ _ => rfl) (mirrorSwap n)
    · apply SourceDerivTot.unitary_pure (Store := Store) (k := 2) _ _
        (fun σ => product (reversalFactors v σ.1)) (fun σ => product (reversalFactors v (σ.1 + 1)))
        (fun _ h => swap_injective h.2)
      intro σ h
      exact mirrorGate_product v h.2
    · exact fun _ => SourceDerivTot.unitary_identity _ _ _ (fun _ h => swap_injective h.2.1)
  simp only [J, reversalFactors_zero, reversalFactors_full] at d
  exact .conseq (fun _ h => ⟨h, le_rfl⟩) d (fun _ h => ⟨h.2, le_rfl⟩)

variable (x : Fin n → Fin 2)

/-- On a basis input the full circuit leaves the suffix phases in reverse wire order. -/
theorem sourceDeriv_circuit :
    SourceDerivTot (.ofEffect (Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2)
      (x i))) fun _ => True) (circuit n)
      (.ofEffect (Assertion.pure (product fun i => Qubit.phaseState (suffixAngle x i.rev)))
        fun σ => σ.1 = n / 2) := by
  have d := sourceDeriv_iteration x
  rw [stageState_zero, stageState_full] at d
  apply SourceDerivTot.seq d
  refine .conseq ?_ (sourceDeriv_reversal fun i => Qubit.phaseState (suffixAngle x i)) ?_
  · exact fun _ _ => ⟨trivial, le_rfl⟩
  · exact fun _ h => ⟨h, le_rfl⟩

/-- Semantic total correctness of the Fourier circuit in product form. -/
theorem validTot_circuit :
    validTot (Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2) (x i))) (circuit n)
      ((Assertion.pure (product fun i => Qubit.phaseState (suffixAngle x i.rev))).mask
        fun σ => σ.1 = n / 2) := by
  have d := (sourceDeriv_circuit x).sound
  rw [CQAssertion.toAssn_ofEffect_true] at d
  exact d

end

end QuantumProgram.FourierIteration
