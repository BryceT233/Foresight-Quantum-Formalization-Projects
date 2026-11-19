/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for the field and interaction layers of the open Ising chain.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Register/TFIM.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.IsingChain.Circuit

/-!
# Operator semantics of an Ising slice

The two commuting layers of the physical circuit implement the exponentials of the
transverse field and the nearest-neighbor interaction, respectively.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit NormedSpace

namespace QuantumProgram.IsingChain

noncomputable section

variable {e : ℕ}

/-- Pauli X on one site, expressed in the qudit operator algebra. -/
def siteX (i : Fin (e + 1)) : Operator (tensorPower Qubit e) :=
  siteOp Qubit e i Qubit.pauliX.asHom.hom

/-- Pauli Z on one site. -/
def siteZ (i : Fin (e + 1)) : Operator (tensorPower Qubit e) :=
  siteOp Qubit e i Qubit.pauliZ.asHom.hom

/-- The interaction on an open edge has one Pauli Z on each endpoint. -/
def edgeZZ (j : Fin e) : Operator (tensorPower Qubit e) := siteZ j.castSucc * siteZ j.succ

/-- Transverse field with independent signed coefficients. -/
def fieldHamiltonian (h : Fin (e + 1) → ℝ) : Operator (tensorPower Qubit e) :=
  ∑ i, (h i : ℂ) • siteX i

/-- Open-chain interaction with independent signed nearest-neighbor couplings. -/
def interactionHamiltonian (J : Fin e → ℝ) : Operator (tensorPower Qubit e) :=
  ∑ j, (J j : ℂ) • edgeZZ j

private theorem commute_same_pauli (A : Operator Qubit) (i j : Fin (e + 1)) :
    Commute (siteOp Qubit e i A) (siteOp Qubit e j A) := by
  rcases eq_or_ne i j with rfl | h
  · exact Commute.refl _
  · exact commute_siteOp e h A A

private theorem commute_edges (j k : Fin e) : Commute (edgeZZ j) (edgeZZ k) :=
  ((commute_same_pauli _ _ _).mul_right (commute_same_pauli _ _ _)).mul_left
    ((commute_same_pauli _ _ _).mul_right (commute_same_pauli _ _ _))

private theorem adjacent_zz (j : Fin e) :
    adjacentOp Qubit e j TransverseFieldIsing.zz.val = edgeZZ j := by
  let Z := Qubit.pauliZ.asHom.hom
  have h : TransverseFieldIsing.zz.val =
      Operator.tensor Z (1 : Operator Qubit) * Operator.tensor (1 : Operator Qubit) Z := by
    apply TensorProduct.ext'
    intros
    rfl
  rw [h, map_mul, adjacentOp_left, adjacentOp_right]
  rfl

private theorem lift_exp {S H : Qudit} (F : Operator S →⋆ₐ[ℂ] Operator H)
    (c : ℂ) (A : Operator S) : F (exp (c • A)) = exp (c • F A) := by
  let : NormedAlgebra ℚ (Operator S) := .restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ (Operator H) := .restrictScalars ℚ ℂ _
  rw [map_exp F F.toAlgHom.toLinearMap.continuous_of_finiteDimensional, map_smul]

local notation "phase" => fun (δ : ℝ) => (-Complex.I) * (δ : ℂ)

private theorem site_rotation (i : Fin (e + 1)) (c δ : ℝ) :
    (Gate.program (.rx i (2 * c * δ))).toOperator =
      exp (phase δ • ((c : ℂ) • siteX i)) := by
  change siteOp Qubit e i
    (exp ((2 * c * δ / 2) • ((-Complex.I) • pauliXHamiltonian.val))) = _
  rw [← Complex.coe_smul, smul_smul, lift_exp, smul_smul]
  congr 2
  push_cast
  ring

private theorem edge_rotation (j : Fin e) (c δ : ℝ) :
    (program (edgeGates j (2 * c * δ))).toOperator =
      exp (phase δ • ((c : ℂ) • edgeZZ j)) := by
  let F := adjacentOp Qubit e j
  let R := (QuantumProgram.rz (2 * c * δ)).hom
  let C := controlledNot.hom
  have ht := adjacentOp_right Qubit e j R
  have h := congrArg F (TransverseFieldIsing.controlledNot_rz_controlledNot c δ)
  rw [lift_exp, adjacent_zz] at h
  simp only [program, edgeGates, List.map_cons, List.map_nil,
    UnitaryProgram.toOperator_sequence, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
  change F C * (siteOp Qubit e j.succ R * F C) = _
  rw [← ht, ← map_mul, ← map_mul, ← mul_assoc, smul_smul]
  exact h

private theorem amplitude_empty :
    (program ([] : List (Gate e))).toOperator = 1 := rfl

/-- A list of commuting local evolutions realizes the exponential of their sum. -/
private theorem amplitude_layer {m : ℕ} (gs : Fin m → List (Gate e))
    (A : Fin m → Operator (tensorPower Qubit e))
    (hgate : ∀ i, (program (gs i)).toOperator = exp (A i))
    (hc : ∀ i j, Commute (A i) (A j)) :
    (program (List.ofFn gs).flatten).toOperator = exp (∑ i, A i) := by
  let : NormedAlgebra ℚ (Operator (tensorPower Qubit e)) :=
    .restrictScalars ℚ ℂ _
  induction m with
  | zero => simp [amplitude_empty]
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, toOperator_append, hgate, Fin.sum_univ_succ,
      add_comm (A 0), exp_add_of_commute]
    · rw [ih (fun i => gs i.succ) (fun i => A i.succ) (fun i => hgate i.succ)
        (fun i j => hc i.succ j.succ)]
    · exact Commute.sum_left _ _ _ fun i _ => hc i.succ 0

private theorem singleton_amplitude (g : Gate e) :
    (program [g]).toOperator = g.program.toOperator := rfl

/-- The native site rotations realize the full field exponential. -/
theorem toOperator_fieldGates (h : Fin (e + 1) → ℝ) (δ : ℝ) :
    (program (fieldGates h δ)).toOperator = exp (phase δ • fieldHamiltonian h) := by
  have fields := amplitude_layer (fun i => [Gate.rx i (2 * h i * δ)])
    (fun i => phase δ • ((h i : ℂ) • siteX i))
    (fun i => (singleton_amplitude _).trans (site_rotation i (h i) δ))
    (fun i j => ((commute_same_pauli Qubit.pauliX.asHom.hom i j).smul_left
      (h i : ℂ)).smul_right (h j : ℂ) |>.smul_left (phase δ) |>.smul_right (phase δ))
  have hx : (List.ofFn (fun i => [Gate.rx i (2 * h i * δ)])).flatten =
      List.ofFn (fun i => Gate.rx i (2 * h i * δ)) := by
    rw [List.ofFn_comp' (fun i => Gate.rx i (2 * h i * δ)) (fun g => [g])]
    rw [← List.flatMap_def, List.flatMap_singleton']
  simpa only [fieldGates, hx, fieldHamiltonian, Finset.smul_sum] using fields

/-- The parity gadgets realize the full interaction exponential. -/
theorem toOperator_interactionGates (J : Fin e → ℝ) (δ : ℝ) :
    (program (interactionGates J δ)).toOperator = exp (phase δ • interactionHamiltonian J) := by
  have edges := amplitude_layer (fun j => edgeGates j (2 * J j * δ))
    (fun j => phase δ • ((J j : ℂ) • edgeZZ j))
    (fun j => edge_rotation j (J j) δ)
    (fun i j => ((commute_edges i j).smul_left (J i : ℂ)).smul_right (J j : ℂ)
      |>.smul_left (phase δ) |>.smul_right (phase δ))
  simpa only [interactionGates, interactionHamiltonian, Finset.smul_sum] using edges

/-- A physical slice applies the field exponential first and the interaction exponential second. -/
theorem toOperator_slice (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (δ : ℝ) :
    (program (slice h J δ)).toOperator =
      exp (phase δ • interactionHamiltonian J) *
        exp (phase δ • fieldHamiltonian h) := by
  rw [slice, toOperator_append, toOperator_fieldGates, toOperator_interactionGates]

/-- Repeating the same instruction list realizes the corresponding operator power. -/
theorem toOperator_circuit (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) (r : ℕ) :
    (program (circuit h J t r)).toOperator =
      (exp (phase (t / r) • interactionHamiltonian J) *
        exp (phase (t / r) • fieldHamiltonian h)) ^ r := by
  rw [circuit, toOperator_replicate, toOperator_slice]

end

end QuantumProgram.IsingChain
