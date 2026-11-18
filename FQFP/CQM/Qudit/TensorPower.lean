/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Superoperator

/-!
# Local operators on a finite tensor power

A nonempty register with `n` adjacent pairs has `n + 1` sites. The site and adjacent-pair
embeddings preserve products and adjoints, the local form of the finite tensor product
composition law used by Physlib QuantumInfo.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace Qudit

noncomputable section

/-- Right-associated tensor product of `n + 1` copies of a quantum system. -/
def tensorPower (H : Qudit) : ℕ → Qudit
  | 0 => H
  | n + 1 => H ⊗ tensorPower H n

/-- Embed the operators of one site into the full tensor power. -/
def siteOp (H : Qudit) : (n : ℕ) → Fin (n + 1) →
    Operator H →⋆ₐ[ℂ] Operator (tensorPower H n)
  | 0, _ => StarAlgHom.id _ _
  | n + 1, i => Fin.cases (Operator.tensorOneHom H (tensorPower H n))
      (fun j => (Operator.oneTensorHom H (tensorPower H n)).comp (siteOp H n j)) i

/-- The product vector with the specified factor at each site of a nonempty register. -/
def productVector (H : Qudit) : (n : ℕ) → (Fin (n + 1) → H.state) → (tensorPower H n).state
  | 0, v => v 0
  | n + 1, v => v 0 ⊗ₜ[ℂ] productVector H n (Fin.tail v)

/-- The inner product of two product vectors factors into the local inner products. -/
theorem inner_productVector (H : Qudit) (n : ℕ) (v w : Fin (n + 1) → H.state) :
    inner ℂ (productVector H n v) (productVector H n w) = ∏ i, inner ℂ (v i) (w i) := by
  induction n with
  | zero =>
    change inner ℂ (v 0) (w 0) = ∏ i, inner ℂ (v i) (w i)
    simp
  | succ n ih =>
    change inner ℂ (v 0 ⊗ₜ[ℂ] productVector H n (Fin.tail v))
      (w 0 ⊗ₜ[ℂ] productVector H n (Fin.tail w)) = _
    rw [Fin.prod_univ_succ, TensorProduct.inner_tmul, ih]
    rfl

/-- A product of local unit vectors is a unit state on the nonempty register. -/
def UnitState.productVector {H : Qudit} (n : ℕ) (v : Fin (n + 1) → UnitState H) :
    UnitState (tensorPower H n) :=
  ⟨Qudit.productVector H n (fun i => (v i).val), by
    change inner ℂ _ _ = 1
    rw [inner_productVector]
    simp only [UnitState.inner_self, Finset.prod_const_one]⟩

/-- A one-site operator changes exactly the corresponding factor of a product vector. -/
theorem siteOp_productVector (H : Qudit) (n : ℕ) (i : Fin (n + 1))
    (A : Operator H) (v : Fin (n + 1) → H.state) :
    siteOp H n i A (productVector H n v) =
      productVector H n (Function.update v i (A (v i))) := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.ext (by lia)
    change A (v 0) = Function.update v 0 (A (v 0)) 0
    rw [Function.update_self]
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      change Operator.tensor A 1 (_ ⊗ₜ[ℂ] _) = _
      simp [productVector, Fin.tail_update_zero]
    | succ j =>
      change Operator.tensor 1 (siteOp H n j A) (_ ⊗ₜ[ℂ] _) = _
      simp [productVector, Fin.tail_update_succ, ih, Ne.symm (Fin.succ_ne_zero j), Fin.tail]

/-- Operators acting at distinct sites commute on the tensor power. -/
theorem commute_siteOp {H : Qudit} (n : ℕ) {i j : Fin (n + 1)} (h : i ≠ j)
    (A B : Operator H) : Commute (siteOp H n i A) (siteOp H n j B) := by
  induction n with
  | zero => exact (h (Fin.ext (by lia))).elim
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (h rfl).elim
      | succ j => exact Operator.commute_tensor_one_one_tensor A (siteOp H n j B)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Operator.commute_tensor_one_one_tensor B (siteOp H n i A)).symm
      | succ j => exact (ih (fun he => h (congrArg Fin.succ he))).map (Operator.oneTensorHom H _)

/-- Embed a two-site operator on the first two sites, reassociating the spectators. -/
def firstPairOp (H : Qudit) : (n : ℕ) →
    Operator (H ⊗ H) →⋆ₐ[ℂ] Operator (tensorPower H (n + 1))
  | 0 => StarAlgHom.id _ _
  | n + 1 =>
    let K := tensorPower H n
    (Superoperator.relabelEquiv (H := (H ⊗ H) ⊗ K) (K := H ⊗ (H ⊗ K))
      (TensorProduct.assocIsometry ℂ H.state H.state K.state)).toStarAlgHom.comp
      (Operator.tensorOneHom (H ⊗ H) K)

/-- Embed a gate at adjacent sites `j.castSucc` and `j.succ`. -/
def adjacentOp (H : Qudit) : (n : ℕ) → Fin n →
    Operator (H ⊗ H) →⋆ₐ[ℂ] Operator (tensorPower H n)
  | 0, j => j.elim0
  | n + 1, j => Fin.cases (firstPairOp H n)
      (fun k => (Operator.oneTensorHom H (tensorPower H n)).comp (adjacentOp H n k)) j

private theorem firstPairOp_left (H : Qudit) (n : ℕ) (A : Operator H) :
    firstPairOp H n (Operator.tensorOneHom H H A) = siteOp H (n + 1) 0 A := by
  cases n with
  | zero => rfl
  | succ n =>
    let K := tensorPower H n
    exact (Superoperator.relabel_assoc_tensor A (1 : Operator H) (1 : Operator K)).trans
      (congrArg (Operator.tensor A) (map_one (Operator.tensorOneHom H K)))

private theorem firstPairOp_right (H : Qudit) (n : ℕ) (A : Operator H) :
    firstPairOp H n (Operator.oneTensorHom H H A) = siteOp H (n + 1) (Fin.succ 0) A := by
  cases n with
  | zero => rfl
  | succ n =>
    exact Superoperator.relabel_assoc_tensor (1 : Operator H) A (1 : Operator (tensorPower H n))

/-- Restricting an adjacent pair to its left endpoint selects that site. -/
theorem adjacentOp_left (H : Qudit) (n : ℕ) (j : Fin n) (A : Operator H) :
    adjacentOp H n j (Operator.tensor A 1) = siteOp H n j.castSucc A := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero => exact firstPairOp_left H n A
    | succ j => exact congrArg (Operator.oneTensorHom H _) (ih j)

/-- Restricting an adjacent pair to its right endpoint selects that site. -/
theorem adjacentOp_right (H : Qudit) (n : ℕ) (j : Fin n) (A : Operator H) :
    adjacentOp H n j (Operator.tensor 1 A) = siteOp H n j.succ A := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero => exact firstPairOp_right H n A
    | succ j => exact congrArg (Operator.oneTensorHom H _) (ih j)

end

end Qudit
