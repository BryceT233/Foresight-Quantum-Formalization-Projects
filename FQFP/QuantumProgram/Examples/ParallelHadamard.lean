/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Measurement.Basic
public import FQFP.CQM.Qudit.TensorPower
public import FQFP.QuantumProgram.CountedLoop
public import FQFP.QuantumProgram.Semantics.Correctness
import FQFP.CQM.Qudit.Channel.Choi

/-!
# Parallel Hadamard preparation

We unroll the counted loop of QHL⁺'s `Qhl/Examples/ParallelHadamardTriple.lean` in the
unitary circuit language. The prefix theorem realizes its `plusAt` invariant and the amplitude
theorem realizes `allPlus_apply` from `Qhl/Register/Qubits.lean` (qedia/quantum-formal-verification
revision `3dfe80b893e2ab949a0428a2e18c06153b310bd0`). The register `tensorPower Qubit n` has
`n + 1` sites. The small-step counted loop realizes the same channel on every weighted input.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

noncomputable section

/-- Execute Hadamard on sites zero through `k - 1`, in increasing order. -/
def hadamardPrefix (n : ℕ) : (k : ℕ) → k ≤ n + 1 → UnitaryProgram (tensorPower Qubit n)
  | 0, _ => .sequence []
  | k + 1, hk => (hadamardPrefix n k (by lia)).seq
      (.liftGate (siteOp Qubit n ⟨k, hk⟩) Qubit.H.asHom)

/-- After `k` gates the visited sites are in the plus state and the rest are in the zero state. -/
theorem hadamardPrefix_apply_zero (n k : ℕ) (hk : k ≤ n + 1) :
    (hadamardPrefix n k hk).toOperator (productVector Qubit n fun _ => ZBasis 2 0) =
      productVector Qubit n (fun i => if i.val < k then hadamardZero else ZBasis 2 0) := by
  induction k with
  | zero =>
    change productVector Qubit n _ = _
    simp
  | succ k ih =>
    let i : Fin (n + 1) := ⟨k, hk⟩
    change (siteOp Qubit n i Qubit.H.asHom.hom)
      ((hadamardPrefix n k _).toOperator _) = _
    rw [ih, siteOp_productVector]
    apply congrArg (productVector Qubit n)
    funext j
    by_cases hj : j = i
    · subst j
      simp [i, hadamardZero]
    · rw [Function.update_of_ne hj]
      have hne : j.val ≠ k := fun h => hj (Fin.ext h)
      simp only [show (j.val < k + 1) ↔ j.val < k by lia]

/-- Applying Hadamard once at every site prepares the tensor product of plus states. -/
theorem parallelHadamard_apply_zero (n : ℕ) :
    (hadamardPrefix n (n + 1) le_rfl).toOperator (productVector Qubit n fun _ => ZBasis 2 0) =
      productVector Qubit n (fun _ => hadamardZero) := by
  simp only [hadamardPrefix_apply_zero, Fin.is_lt, ite_true]

/-- Every bit string has amplitude `(1 / √2)^(n + 1)` in the prepared state. -/
theorem parallelHadamard_amplitude (n : ℕ) (bits : Fin (n + 1) → Fin 2) :
    inner ℂ (productVector Qubit n (fun i => ZBasis 2 (bits i)))
      ((hadamardPrefix n (n + 1) le_rfl).toOperator (productVector Qubit n fun _ => ZBasis 2 0)) =
      ((√2)⁻¹ : ℂ) ^ (n + 1) := by
  rw [parallelHadamard_apply_zero, inner_productVector]
  have h (b : Fin 2) : inner ℂ (ZBasis 2 b) hadamardZero = ((√2)⁻¹ : ℂ) := by
    rw [hadamardZero, hadamard_zero_apply, inner_smul_right, inner_add_right]
    fin_cases b <;> simp
  simp [h]

/-- The register expression of the loop selects the site named by the classical counter. -/
def hadamardBody (n : ℕ) : Command ℕ (Fin (n + 1)) (tensorPower Qubit n) :=
  let cell := Fin.ofNat (n + 1)
  .unitary (fun k (_ : Fin 1) => cell k)
    (fun k _ => .liftGate (siteOp Qubit n (cell k)) Qubit.H.asHom)

/-- Reset the counter, then apply Hadamard and increment until all sites have been visited. -/
def hadamardLoop (n : ℕ) : Command ℕ (Fin (n + 1)) (tensorPower Qubit n) :=
  .counted CounterLens.nat (fun _ => n + 1) (hadamardBody n)

/-- The loop terminates at the exact exit counter with the channel output of the unrolled circuit.
This holds for every initial counter and every positive input operator. -/
theorem frontier_hadamardLoop (n : ℕ) (input : CQState ℕ (tensorPower Qubit n)) :
    (Configuration.mk (some (hadamardLoop n)) input).frontier (3 * (n + 1) + 2) =
      [⟨none, { input.map (hadamardPrefix n (n + 1) le_rfl).toChannel with store := n + 1 }⟩] := by
  let s (k : ℕ) (hk : k ≤ n + 1) :=
    { input.map (hadamardPrefix n k hk).toChannel with store := k }
  apply Command.frontier_counted CounterLens.nat _ _ input (n + 1) s
  · change _ = { input.map (QuantumChannel.ofIsometry (CategoryTheory.CategoryStruct.id _))
        with store := 0 }
    rw [QuantumChannel.ofIsometry_id]
    rfl
  · exact fun _ _ => rfl
  · exact fun _ _ => rfl
  · intro k hk
    have hi : Fin.ofNat (n + 1) k = (⟨k, hk⟩ : Fin (n + 1)) :=
      Fin.ext (Nat.mod_eq_of_lt hk)
    let gate := UnitaryProgram.liftGate (siteOp Qubit n ⟨k, hk⟩) Qubit.H.asHom
    refine ⟨(s k hk.le).map gate.toChannel, ?_, ?_⟩
    · simp only [hadamardBody, Command.step, s, dite_eq_left (Function.injective_of_subsingleton _),
        hi, gate]
    · simp only [s, hadamardPrefix, UnitaryProgram.toChannel_seq]
      rfl

/-- Every input's full trace terminates in the counted Hadamard loop. -/
theorem terminatingMass_hadamardLoop (n : ℕ) (input : CQState ℕ (tensorPower Qubit n)) :
    (Configuration.mk (some (hadamardLoop n)) input).terminatingMass = input.mass := by
  apply Configuration.terminatingMass_eq_of_frontier (frontier_hadamardLoop n input)
  exact input.mass_map _

/-- Starting in the all-zero projector, the sole terminal branch carries the all-plus projector. -/
theorem frontier_hadamardLoop_zero (n initialCounter : ℕ) :
    let zero := productVector Qubit n (fun _ => ZBasis 2 0)
    let plus := productVector Qubit n (fun _ => hadamardZero)
    let input := CQState.mk initialCounter (Operator.outer zero zero) (Operator.isPositive_outer _)
    (Configuration.mk (some (hadamardLoop n)) input).frontier (3 * (n + 1) + 2) =
      [⟨none, ⟨n + 1, Operator.outer plus plus, Operator.isPositive_outer _⟩⟩] := by
  dsimp only
  rw [frontier_hadamardLoop]
  congr 3
  apply CQState.ext
  · rfl
  change Superoperator.conjugate (hadamardPrefix n (n + 1) le_rfl).toOperator _ = _
  rw [Superoperator.conjugate_outer, parallelHadamard_apply_zero]

/-- Semantic total correctness of parallel Hadamard from the all-zero to the all-plus projector
(`phValid` in `Qhl/Examples/ParallelHadamardTriple.lean`). -/
theorem validTot_hadamardLoop (n : ℕ) :
    let zero := UnitState.ofBasis (ZBasis 2) 0
    let plus := UnitState.map Qubit.H.asHom zero
    validTot (Assertion.pure (UnitState.productVector n fun _ => zero)) (hadamardLoop n)
      (Assertion.pure (UnitState.productVector n fun _ => plus)) := by
  intro zero plus input
  let p := hadamardPrefix n (n + 1) le_rfl
  let z := productVector Qubit n (fun _ => ZBasis 2 0)
  let v := productVector Qubit n (fun _ => hadamardZero)
  have hp : p.denoteHom z = v := parallelHadamard_apply_zero n
  have he : (input.map p.toChannel).expectation (Operator.outer v v) =
      input.expectation (Operator.outer z z) := by
    rw [← hp]
    exact input.expectation_outer_map p.denoteHom z
  exact (congrArg ENNReal.ofReal he).symm.le.trans
    (Configuration.ofReal_expectation_le_PostH_of_frontier (frontier_hadamardLoop n input)
      (fun _ => Operator.outer v v))

end

end QuantumProgram
