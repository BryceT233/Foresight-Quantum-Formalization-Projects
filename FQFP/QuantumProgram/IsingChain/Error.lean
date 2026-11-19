/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for the commutator locality and coefficient-only first-order error bound.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Register/TFIMLocality.lean
Qhl/Register/TFIMApprox.lean
Qhl/Examples/TrotterTFIMTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.IsingChain.Evolution

/-!
# Coefficient bound for open-chain Ising simulation

Only the two endpoint fields contribute to the commutator with a given edge. This
gives the coefficient-only first-order bound of QEDIA's `tfimValidApprox_of_coefficients`
for the operator of the physical Rx/Rz/CNOT circuit, for either sign of time.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit NormedSpace TrotterError
open DaggerCategory (IsUnitary)

namespace QuantumProgram.IsingChain

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

variable {e : ℕ}

private theorem norm_local_le_one {S H : Qudit} (F : Operator S →⋆ₐ[ℂ] Operator H)
    (U : S ⟶ S) [IsUnitary U] : ‖F U.hom‖ ≤ 1 :=
  (LIOfIsIsometry (UnitaryProgram.liftGate F U).denoteHom).norm_toContinuousLinearMap_le

private theorem norm_edgeZZ_le_one (j : Fin e) : ‖edgeZZ j‖ ≤ 1 := by
  unfold edgeZZ
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
    (norm_local_le_one (siteOp Qubit e j.castSucc) Qubit.pauliZ.asHom)).trans
      (norm_local_le_one (siteOp Qubit e j.succ) Qubit.pauliZ.asHom))

/-- The transverse-field Hamiltonian is self-adjoint for signed real fields. -/
theorem isSelfAdjoint_fieldHamiltonian (h : Fin (e + 1) → ℝ) :
    IsSelfAdjoint (fieldHamiltonian h) := by
  apply isSelfAdjoint_sum
  intro i _
  exact (show IsSelfAdjoint (h i : ℂ) by simp [IsSelfAdjoint]).smul
    (IsSelfAdjoint.map (siteOp Qubit e i)
      ((isSelfAdjoint_iff_hom Qubit.pauliX.asHom).1 inferInstance))

/-- The interaction Hamiltonian is self-adjoint for signed real couplings. -/
theorem isSelfAdjoint_interactionHamiltonian (J : Fin e → ℝ) :
    IsSelfAdjoint (interactionHamiltonian J) := by
  apply isSelfAdjoint_sum
  intro j _
  have hz (i : Fin (e + 1)) : IsSelfAdjoint (siteZ i) :=
    IsSelfAdjoint.map (siteOp Qubit e i) ((isSelfAdjoint_iff_hom Qubit.pauliZ.asHom).1
      inferInstance)
  exact (show IsSelfAdjoint (J j : ℂ) by simp [IsSelfAdjoint]).smul
    ((hz j.castSucc).commute_iff (hz j.succ) |>.mp (commute_siteOp e (by
      exact Fin.ne_of_val_ne (by simp)) _ _))

/-- The field norm is bounded by the sum of the absolute site coefficients. -/
theorem norm_fieldHamiltonian_le (h : Fin (e + 1) → ℝ) :
    ‖fieldHamiltonian h‖ ≤ ∑ i, |h i| := by
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_local_le_one _ Qubit.pauliX.asHom)

/-- The interaction norm is bounded by the sum of the absolute edge coefficients. -/
theorem norm_interactionHamiltonian_le (J : Fin e → ℝ) :
    ‖interactionHamiltonian J‖ ≤ ∑ j, |J j| := by
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_edgeZZ_le_one _)

/-- Sum of absolute edge couplings weighted by the fields at their endpoints. -/
def couplingBound (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) : ℝ :=
  ∑ j, |J j| * (|h j.castSucc| + |h j.succ|)

private theorem edge_field_bound (h : Fin (e + 1) → ℝ) (j : Fin e) :
    ‖⁅edgeZZ j, fieldHamiltonian h⁆‖ ≤ 2 * (|h j.castSucc| + |h j.succ|) := by
  classical
  let term (i : Fin (e + 1)) := ⁅edgeZZ j, (h i : ℂ) • siteX i⁆
  have endpoint (i : Fin (e + 1)) : ‖term i‖ ≤ 2 * |h i| := by
    simp only [term, lie_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hb := norm_commutator_le (edgeZZ j) (siteX i)
    have hz := norm_edgeZZ_le_one j
    have hx := norm_local_le_one (siteOp Qubit e i) Qubit.pauliX.asHom
    change ‖siteX i‖ ≤ 1 at hx
    calc
      _ ≤ |h i| * (2 * ‖edgeZZ j‖ * ‖siteX i‖) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |h i| * (2 * 1 * 1) := by gcongr
      _ = _ := by ring
  have off (i : Fin (e + 1)) (hl : j.castSucc ≠ i) (hr : j.succ ≠ i) : term i = 0 := by
    have hc : Commute (edgeZZ j) (siteX i) :=
      (commute_siteOp e hl _ _).mul_left (commute_siteOp e hr _ _)
    exact sub_eq_zero.mpr (hc.smul_right (h i : ℂ)).eq
  have ne : j.castSucc ≠ j.succ := Fin.ne_of_val_ne (by simp)
  simp only [fieldHamiltonian, lie_sum]
  change ‖∑ i, term i‖ ≤ _
  rw [← Finset.sum_subset (Finset.subset_univ ({j.castSucc, j.succ} : Finset _))
    (fun i _ hi => off i (fun eq => hi (by simp [eq])) (fun eq => hi (by simp [eq]))),
    Finset.sum_pair ne]
  exact (norm_add_le _ _).trans ((add_le_add (endpoint _) (endpoint _)).trans_eq (mul_add ..).symm)

/-- The commutator of the two physical layers has a coefficient-only norm bound. -/
theorem norm_commutator_le_coefficients (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) :
    ‖⁅interactionHamiltonian J, fieldHamiltonian h⁆‖ ≤ 2 * couplingBound h J := by
  simp only [interactionHamiltonian, sum_lie, smul_lie,
    couplingBound, Finset.mul_sum]
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (edge_field_bound h j) (abs_nonneg _)

private theorem two_layer_error {H : Qudit} (A B : selfAdjoint (Operator H))
    (t : ℝ) {r : ℕ} (hr : 0 < r) :
    ‖(exp (((-Complex.I) * ((t / r : ℝ) : ℂ)) • B.val) *
        exp (((-Complex.I) * ((t / r : ℝ) : ℂ)) • A.val)) ^ r -
      exp (((-Complex.I) * (t : ℂ)) • (A.val + B.val))‖ ≤
        t ^ 2 / 2 * ‖⁅B.val, A.val⁆‖ / r := by
  let terms : Fin 2 → selfAdjoint (Operator H) := ![A, B]
  have bound := trotterProgram_error_le (S := H) terms t hr
  have hlist : List.finRange 2 = [0, 1] := by decide
  rw [toOperator_trotterProgram] at bound
  simpa [terms, hlist, Fin.sum_univ_two, schrodingerGenerator, ← Complex.coe_smul,
    smul_smul, mul_comm ((t : ℂ) / r) Complex.I, trotterErrorConstant, upperSum,
    Finset.sum_filter] using bound

/-- Coefficient-only operator norm error for the physical first-order circuit on the open chain. -/
theorem circuit_error_le (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) {r : ℕ} (hr : 0 < r) :
    ‖(program (circuit h J t r)).toOperator -
      exp (((-Complex.I) * (t : ℂ)) • (fieldHamiltonian h + interactionHamiltonian J))‖ ≤
        t ^ 2 / r * couplingBound h J := by
  rw [toOperator_circuit]
  have bound := two_layer_error (H := tensorPower Qubit e)
    ⟨_, isSelfAdjoint_fieldHamiltonian h⟩ ⟨_, isSelfAdjoint_interactionHamiltonian J⟩ t hr
  apply bound.trans
  calc
    _ ≤ t ^ 2 / 2 * (2 * couplingBound h J) / r := by
      gcongr
      exact norm_commutator_le_coefficients h J
    _ = _ := by ring

/-- Exact evolution of the entire signed Ising Hamiltonian, used as the measurement reference. -/
def exactEvolution (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) :
    UnitaryProgram (tensorPower Qubit e) :=
  hamiltonianGate ⟨_, (isSelfAdjoint_fieldHamiltonian h).add
    (isSelfAdjoint_interactionHamiltonian J)⟩ t

/-- The reference program acts by the exponential of the complete signed Hamiltonian. -/
theorem toOperator_exactEvolution (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) :
    (exactEvolution h J t).toOperator =
      exp (((-Complex.I) * (t : ℂ)) • (fieldHamiltonian h + interactionHamiltonian J)) := by
  change exp (t • ((-Complex.I) • _)) = _
  rw [← Complex.coe_smul, smul_smul, mul_comm]

/-- A positive step count selected directly from the time, tolerance, and input coefficients. -/
def steps (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t ε : ℝ) : ℕ :=
  max 1 ⌈t ^ 2 * couplingBound h J / ε⌉₊

/-- At the selected tolerance, approximation and CNOT count hold for the same instruction list. -/
theorem circuit_spec (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    let r := steps h J t ε
    let gs := circuit h J t r
    ‖(program gs).toOperator -
      exp (((-Complex.I) * (t : ℂ)) • (fieldHamiltonian h + interactionHamiltonian J))‖ ≤ ε ∧
      cnotCount gs = 2 * r * e := by
  dsimp only
  have hr : 0 < steps h J t ε := lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)
  refine ⟨(circuit_error_le h J t hr).trans ?_, cnotCount_circuit ..⟩
  have hc : t ^ 2 * couplingBound h J / ε ≤ (steps h J t ε : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
  rw [div_mul_eq_mul_div, div_le_iff₀ (Nat.cast_pos.mpr hr)]
  simpa [mul_comm] using (div_le_iff₀ hε).mp hc

/-- Each terminal outcome of the first-order command inherits the commutator error bound. -/
theorem abs_postH_circuit_sub_probability_le {Store ι : Type*} [Fintype ι]
    (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) {r : ℕ} (hr : 0 < r)
    (M : POVM (tensorPower Qubit e) ι) (ρ : Density (tensorPower Qubit e)) (i : ι) (σ : Store) :
    let c := Configuration.mk (some (command (circuit h J t r))) ⟨σ, ρ.op, ρ.positive⟩
    |(c.PostH (fun _ => M.op i)).toReal - M.probability (ρ.map (exactEvolution h J t).denoteHom) i|
      ≤ t ^ 2 / r * couplingBound h J := by
  dsimp only
  rw [postH_command_probability _ M ρ i σ]
  apply M.abs_probability_map_sub_le
  change ‖(program _).toOperator - (exactEvolution h J t).toOperator‖ ≤ _
  rw [toOperator_exactEvolution]
  exact circuit_error_le h J t hr

end

end QuantumProgram.IsingChain
