/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.TensorPower
public import FQFP.QuantumProgram.Register.Ordered

/-!
# Nonempty tensor powers as ordered registers

The nonempty tensor power ends with its last site, whereas the ordered memory ends with a
tensor unit. Inserting that unit identifies their operators and their one- and two-site gates.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Qudit
open scoped TensorProduct

namespace QuantumProgram

/-- Insert the trailing tensor unit used by the ordered memory on a nonempty register. -/
def tensorPowerMemoryIsometry (H : Qudit) : (e : ℕ) → (tensorPower H e).state ≃ₗᵢ[ℂ]
    (tensorMemory (fun _ : Fin (e + 1) => H)).state
  | 0 => (TensorProduct.ridIsometry ℂ H.state).symm
  | e + 1 => (tensorPowerMemoryIsometry H e).lTensor H.state

/-- Transport operators on a nonempty tensor power to ordered-memory coordinates. -/
def tensorPowerMemoryEquiv (H : Qudit) (e : ℕ) : Operator (tensorPower H e) ≃⋆ₐ[ℂ]
    Operator (tensorMemory (fun _ : Fin (e + 1) => H)) :=
  Superoperator.relabelEquiv (tensorPowerMemoryIsometry H e)

variable {H : Qudit}

private theorem memoryEquiv_zero (A : Operator H) :
    tensorPowerMemoryEquiv H 0 A = Operator.tensor A (1 : Operator (𝟙_ Qudit)) := by
  apply TensorProduct.ext'
  intro x z
  change ℂ at z
  change A (z • x) ⊗ₜ[ℂ] (1 : ℂ) = A x ⊗ₜ[ℂ] z
  rw [map_smul, TensorProduct.smul_tmul, smul_eq_mul, mul_one]

private theorem memoryEquiv_tensor (e : ℕ) (A : Operator H) (B : Operator (tensorPower H e)) :
    tensorPowerMemoryEquiv H (e + 1) (Operator.tensor A B) =
      Operator.tensor A (tensorPowerMemoryEquiv H e B) := by
  apply TensorProduct.ext'
  intro x y
  rfl

/-- Single-site embeddings agree under the change of memory coordinates. -/
theorem tensorPowerMemoryEquiv_siteOp (e : ℕ) (i : Fin (e + 1)) (A : Operator H) :
    tensorPowerMemoryEquiv H e (siteOp H e i A) =
      (Register.site (fun _ => H) i).liftOperator A := by
  induction e with
  | zero =>
    obtain rfl : i = 0 := Fin.ext (by lia)
    exact memoryEquiv_zero A
  | succ e ih =>
    cases i using Fin.cases with
    | zero => exact (memoryEquiv_tensor e A 1).trans (by rw [map_one]; rfl)
    | succ i => exact (memoryEquiv_tensor e 1 _).trans (congrArg (Operator.tensor 1) (ih i))

/-- Lifting a one-site operator recovers its tensor-power embedding. -/
theorem orderedLift_tensorPowerMemoryEquiv_single {e : ℕ} (r : Fin 1 ↪ Fin (e + 1))
    (A : Operator H) :
    orderedLift (fun _ => H) r (tensorPowerMemoryEquiv H 0 A) =
      tensorPowerMemoryEquiv H e (siteOp H e (r 0) A) := by
  rw [memoryEquiv_zero, tensorPowerMemoryEquiv_siteOp]
  exact (orderedLift_tensor (fun _ => H) r A 1).trans (by rw [map_one, mul_one])

/-- A two-site operator on adjacent ordered wires agrees with the tensor-power pair embedding. -/
theorem orderedLift_tensorPowerMemoryEquiv_pair {e : ℕ} (r : Fin 2 ↪ Fin (e + 1)) (j : Fin e)
    (h₀ : r 0 = j.castSucc) (h₁ : r 1 = j.succ) (A : Operator (H ⊗ H)) :
    orderedLift (fun _ => H) r (tensorPowerMemoryEquiv H 1 A) =
      tensorPowerMemoryEquiv H e (adjacentOp H e j A) := by
  induction A using Operator.tensor_induction_on with
  | htensor X Y =>
    have hf : Operator.tensor X Y = Operator.tensor X (1 : Operator H) * Operator.tensor 1 Y := by
      rw [Operator.tensor_mul_tensor, mul_one, one_mul]
    calc
      _ = _ := congrArg (orderedLift (fun _ => H) r) (memoryEquiv_tensor 0 X Y)
      _ = _ := orderedLift_tensor (fun _ => H) r X (tensorPowerMemoryEquiv H 0 Y)
      _ = _ := by
        rw [hf, map_mul, adjacentOp_left, adjacentOp_right, map_mul,
          tensorPowerMemoryEquiv_siteOp, ← h₀, ← h₁]
        exact congrArg (_ * ·)
          (orderedLift_tensorPowerMemoryEquiv_single ((Fin.succEmb 1).trans r) Y)
  | hadd X Y hX hY =>
    let F := (orderedLift (fun _ => H) r).comp (tensorPowerMemoryEquiv H 1).toStarAlgHom
    exact (map_add F X Y).trans ((congrArg₂ (· + ·) hX hY).trans (by rw [map_add, map_add]))

end QuantumProgram
