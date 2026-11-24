/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/Step.lean (regLift for an ordered register)
Qhl/Program/Spec.lean (isQMeasure_regLift)
Qhl/Program/LocalConjugation.lean (conj_regLift_conj on disjoint cells)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.RegisterLocality

/-!
# Operators on ordered subregisters

An injection selects an ordered tuple of sites of a heterogeneous tensor memory. On products
of local operators, its lift multiplies their site embeddings in tuple order. The tensor product
universal property extends this action to all operators, including entangling gates.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit
open scoped TensorProduct

namespace QuantumProgram

noncomputable section

variable {A B H : Qudit}

private def tensorAlgEquiv (A B : Qudit) :
    Operator A ⊗[ℂ] Operator B ≃ₐ[ℂ] Operator (A ⊗ B) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (Operator.tensorEquiv A B)
    (fun _ _ _ _ => TensorProduct.map_mul ..) TensorProduct.map_one

private def pairAlg (F : Operator A →⋆ₐ[ℂ] Operator H) (G : Operator B →⋆ₐ[ℂ] Operator H)
    (h : ∀ X Y, Commute (F X) (G Y)) : Operator (A ⊗ B) →ₐ[ℂ] Operator H :=
  (Algebra.TensorProduct.lift F.toAlgHom G.toAlgHom h).comp (tensorAlgEquiv A B).symm.toAlgHom

private theorem pairAlg_tensor (F : Operator A →⋆ₐ[ℂ] Operator H) (G : Operator B →⋆ₐ[ℂ] Operator H)
    (h : ∀ X Y, Commute (F X) (G Y)) (X : Operator A) (Y : Operator B) :
    pairAlg F G h (Operator.tensor X Y) = F X * G Y := by
  change Algebra.TensorProduct.lift F.toAlgHom G.toAlgHom h
    ((tensorAlgEquiv A B).symm ((tensorAlgEquiv A B) (X ⊗ₜ Y))) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

private def pairHom (F : Operator A →⋆ₐ[ℂ] Operator H) (G : Operator B →⋆ₐ[ℂ] Operator H)
    (h : ∀ X Y, Commute (F X) (G Y)) : Operator (A ⊗ B) →⋆ₐ[ℂ] Operator H where
  toAlgHom := pairAlg F G h
  map_star' X := by
    induction X using Operator.tensor_induction_on with
    | htensor X Y =>
      change pairAlg F G h (TensorProduct.map X Y).adjoint = star (pairAlg F G h (X.tensor Y))
      rw [TensorProduct.adjoint_map]
      change pairAlg F G h ((star X).tensor (star Y)) = _
      rw [pairAlg_tensor, pairAlg_tensor, star_mul, map_star, map_star]
      simpa only [map_star] using (h (star X) (star Y)).eq
    | hadd X Y hX hY =>
      change pairAlg F G h (star (X + Y)) = star (pairAlg F G h (X + Y))
      rw [star_add, map_add, map_add, star_add]
      exact congrArg₂ (· + ·) hX hY

private theorem commute_pairHom (F : Operator A →⋆ₐ[ℂ] Operator H)
    (G : Operator B →⋆ₐ[ℂ] Operator H)
    (h : ∀ X Y, Commute (F X) (G Y)) (Z : Operator H) (hF : ∀ X, Commute (F X) Z)
    (hG : ∀ Y, Commute (G Y) Z) (X : Operator (A ⊗ B)) : Commute (pairHom F G h X) Z := by
  induction X using Operator.tensor_induction_on with
  | htensor X Y =>
    change Commute (pairAlg F G h (X.tensor Y)) Z
    rw [pairAlg_tensor]
    exact (hF X).mul_left (hG Y)
  | hadd X Y hX hY =>
    rw [map_add]
    exact hX.add_left hY

private def scalarValue : Operator (𝟙_ Qudit) →⋆ₐ[ℂ] ℂ where
  toAlgHom := AlgHom.ofLinearMap (LinearMap.trace ℂ ℂ) (Operator.trace_scalar 1)
    (fun (X Y : ℂ →ₗ[ℂ] ℂ) => by
      calc
        _ = X (Y 1) := Operator.trace_scalar (X * Y)
        _ = X 1 * Y 1 := by simp
        _ = _ := congrArg₂ (· * ·) (Operator.trace_scalar X).symm (Operator.trace_scalar Y).symm)
  map_star' := Operator.trace_adjoint

private def orderedLiftAux {n : ℕ} (D : Fin n → Qudit) :
    {k : ℕ} → (r : Fin k ↪ Fin n) →
      { F : Operator (tensorMemory (D ∘ r)) →⋆ₐ[ℂ] Operator (tensorMemory D) //
        ∀ Z, (∀ i X, Commute ((Register.site D (r i)).liftOperator X) Z) →
          ∀ X, Commute (F X) Z }
  | 0, _ =>
    ⟨(StarAlgHom.ofId ℂ _).comp scalarValue,
      fun Z _ X => Algebra.commutes (scalarValue X) Z⟩
  | k + 1, r => by
    let t := (Fin.succEmb k).trans r
    let G := orderedLiftAux D t
    let F := (Register.site D (r 0)).liftOperator
    have hc (X Y) : Commute (F X) (G.val Y) := by
      apply Commute.symm
      apply G.property
      intro i V
      have hd := Register.disjoint_site D (i := t i) (j := r 0)
        (fun e => Fin.succ_ne_zero i (r.injective e))
      exact hd.commute_liftOperator V X
    refine ⟨pairHom F G.val hc, ?_⟩
    intro Z hz X
    exact commute_pairHom F G.val hc Z (hz 0) (G.property Z (fun i => hz i.succ)) X

/-- Lift an arbitrary joint operator from the selected sites into the full memory. -/
@[no_expose] def orderedLift {n k : ℕ} (D : Fin n → Qudit) (r : Fin k ↪ Fin n) :
    Operator (tensorMemory (D ∘ r)) →⋆ₐ[ℂ] Operator (tensorMemory D) := (orderedLiftAux D r).val

/-- An operation on an empty register acts by its scalar value on the full memory. -/
theorem orderedLift_empty {n : ℕ} (D : Fin n → Qudit) (r : Fin 0 ↪ Fin n)
    (X : Operator (tensorMemory (D ∘ r))) : orderedLift D r X = X.trace • 1 :=
  Algebra.algebraMap_eq_smul_one (R := ℂ) (A := Operator (tensorMemory D)) _

/-- Product operators lift to the product of the head-site action and the ordered tail action. -/
theorem orderedLift_tensor {n k : ℕ} (D : Fin n → Qudit) (r : Fin (k + 1) ↪ Fin n)
    (X : Operator (D (r 0))) (Y : Operator (tensorMemory (D ∘ (Fin.succEmb k).trans r))) :
    orderedLift D r (Operator.tensor X Y) =
      (Register.site D (r 0)).liftOperator X * orderedLift D ((Fin.succEmb k).trans r) Y :=
  pairAlg_tensor (Register.site D (r 0)).liftOperator (orderedLiftAux D _).val _ X Y

/-- Disjoint ordered selections commute for arbitrary joint operators on either selection. -/
theorem commute_orderedLift {n k l : ℕ} (D : Fin n → Qudit) (r : Fin k ↪ Fin n) (s : Fin l ↪ Fin n)
    (h : ∀ i j, r i ≠ s j) (X : Operator (tensorMemory (D ∘ r)))
    (Y : Operator (tensorMemory (D ∘ s))) : Commute (orderedLift D r X) (orderedLift D s Y) := by
  apply (orderedLiftAux D r).property
  intro i U
  apply Commute.symm
  apply (orderedLiftAux D s).property
  intro j V
  exact ((Register.disjoint_site D (h i j)).commute_liftOperator U V).symm

/-- Lifting a complete local Kraus family preserves completeness on the whole memory. -/
theorem orderedLift_complete {n k : ℕ} (D : Fin n → Qudit) (r : Fin k ↪ Fin n)
    {ι : Type*} [Fintype ι] (M : ι → Operator (tensorMemory (D ∘ r)))
    (h : ∑ i, (M i).adjoint ∘ₗ M i = 1) :
    ∑ i, (orderedLift D r (M i)).adjoint ∘ₗ orderedLift D r (M i) = 1 := by
  change ∑ i, star (orderedLift D r (M i)) * orderedLift D r (M i) = 1
  change ∑ i, star (M i) * M i = 1 at h
  simpa only [map_sum, map_mul, map_star, map_one] using congrArg (orderedLift D r) h

end

end QuantumProgram
