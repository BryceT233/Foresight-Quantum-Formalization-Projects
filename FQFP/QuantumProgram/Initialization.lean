/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/InitComposition.lean (initLift_empty and initLift_union)
Qhl/Program/Step.lean (initLift on a finite block)
Qhl/Logic/Source/Initialization.lean (singleton reset matrix units)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.OrderedChannel
import FQFP.CQM.Qudit.Channel.Degradation.Basic
import FQFP.CQM.Qudit.Channel.EntanglementBreaking.RankOneKraus

/-!
# Initialization of finite sets of sites

Each selected site is replaced by its designated density. Spectators carry the identity channel.
The parallel channel acts on all input operators, including entangled states. A site occurring
in both blocks is replaced twice by the same state.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit

namespace QuantumProgram

noncomputable section

/-- Parallel composition of a family of site channels, in tensor-memory order. -/
def registerChannels : {n : ℕ} → (D : Fin n → Qudit) → ((i : Fin n) → QuantumChannel (D i) (D i)) →
    QuantumChannel (tensorMemory D) (tensorMemory D)
  | 0, _, _ => .id _
  | _ + 1, D, f => (f 0).tensor (registerChannels (Fin.tail D) (Fin.tail f))

/-- Running the identity at every site acts identically on the full memory. -/
theorem registerChannels_id {n : ℕ} (D : Fin n → Qudit) :
    registerChannels D (fun i => .id (D i)) = .id _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (congrArg ((QuantumChannel.id (D 0)).tensor ·) (ih (Fin.tail D))).trans
      (QuantumChannel.tensor_id_id ..)

/-- Sitewise composition agrees with composition on the entire register. -/
theorem registerChannels_comp {n : ℕ} (D : Fin n → Qudit)
    (f g : (i : Fin n) → QuantumChannel (D i) (D i)) :
    registerChannels D (fun i => (g i).comp (f i)) =
      (registerChannels D g).comp (registerChannels D f) := by
  induction n with
  | zero => exact (QuantumChannel.id_comp _).symm
  | succ n ih =>
    exact (congrArg (((g 0).comp (f 0)).tensor ·) (ih (Fin.tail D) (Fin.tail f) (Fin.tail g))).trans
      (QuantumChannel.tensor_comp ..)

variable {n : ℕ} (D : Fin n → Qudit) (τ : (i : Fin n) → Density (D i))

/-- Reset the selected set to the product of its designated site densities. -/
def initializeCells (s : Finset (Fin n)) : QuantumChannel (tensorMemory D) (tensorMemory D) :=
  registerChannels D fun i => if i ∈ s then QuantumChannel.replacement (D i) (τ i) else .id _

/-- One channel instruction resets the finite block selected by the current classical store. -/
def Command.initializeCellsOn {S : Type*} {D : Fin n → Qudit} (τ : (i : Fin n) → Density (D i))
    (s : S → Finset (Fin n)) : Command S (Fin n) (tensorMemory D) :=
  .channel fun σ => initializeCells D τ (s σ)

/-- Resetting the empty block is the identity channel. -/
theorem initializeCells_empty : initializeCells D τ ∅ = QuantumChannel.id _ := by
  simp [initializeCells, registerChannels_id]

/-- Resetting two blocks in sequence resets their union, even if they overlap. -/
theorem initializeCells_union (s t : Finset (Fin n)) :
    initializeCells D τ (s ∪ t) = (initializeCells D τ s).comp (initializeCells D τ t) := by
  unfold initializeCells
  rw [← registerChannels_comp]
  congr 1
  funext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [hs, ht, QuantumChannel.replacement_comp, QuantumChannel.id_comp, QuantumChannel.comp_id]

/-- Resetting a singleton is the existing replacement channel lifted along its site path. -/
theorem initializeCells_singleton (i : Fin n) :
    initializeCells D τ {i} = (Register.site D i).initializeTo (τ i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      change QuantumChannel.tensor (if (0 : Fin (n + 1)) ∈ ({0} : Finset _) then
        QuantumChannel.replacement (D 0) (τ 0) else .id _)
        (registerChannels (Fin.tail D) _) = _
      have ht : (Fin.tail (fun j : Fin (n + 1) => if j ∈ ({0} : Finset _) then
          QuantumChannel.replacement (D j) (τ j) else .id _)) =
          fun j : Fin n => QuantumChannel.id (D j.succ) := by
        funext j
        simp [Fin.tail, Fin.succ_ne_zero]
      exact congrArg₂ QuantumChannel.tensor (ite_eq_left (Finset.mem_singleton_self _))
        ((congrArg (registerChannels (Fin.tail D)) ht).trans (registerChannels_id _))
    | succ j =>
      change QuantumChannel.tensor (if (0 : Fin (n + 1)) ∈ ({j.succ} : Finset _) then
        QuantumChannel.replacement (D 0) (τ 0) else .id _)
        (registerChannels (Fin.tail D) _) = _
      apply congrArg₂ QuantumChannel.tensor (ite_eq_right (by simp [Ne.symm (Fin.succ_ne_zero j)]))
      refine Eq.trans ?_ (ih (Fin.tail D) (Fin.tail τ) j)
      unfold initializeCells
      congr 1
      funext a
      simp [Fin.tail, Fin.succ_inj]

/-- Lifting a finite Kraus sum along a static path lifts each operator in the family. -/
theorem Register.liftSuperoperator_kraus {H A : Qudit} (p : Register H A)
    {ι : Type*} [Fintype ι] (M : ι → Operator A) :
    p.liftSuperoperator (Superoperator.kraus M) =
      Superoperator.kraus (fun i => p.liftOperator (M i)) := by
  simp only [Superoperator.kraus, Register.conjugate_liftOperator]
  induction p with
  | whole => rfl
  | left p ih =>
    simp only [liftSuperoperator, ih M, Superoperator.tensor_sum_left]
  | right p ih =>
    simp only [liftSuperoperator, ih M, Superoperator.tensor_sum_right]

private theorem replacement_pure_eq_kraus {A : Qudit} {ι : Type*} [Fintype ι]
    (v : UnitState A) (b : OrthonormalBasis ι ℂ A.state) :
    (QuantumChannel.replacement A (Density.pure v)).toSuperoperator =
      Superoperator.kraus (fun j => Operator.outer v.val (b j)) := by
  apply LinearMap.ext
  intro X
  have h : ∑ j, Operator.outer (b j) (b j) = 1 := by
    simpa using Operator.sum_outer_basis b (1 : Operator A)
  simp only [Operator.outer_eq_ket_comp_bra] at h
  rw [QuantumChannel.replacement_apply, Density.op_pure]
  simp only [Superoperator.kraus, LinearMap.sum_apply, Operator.outer_eq_ket_comp_bra,
    Superoperator.conjugate_ket_comp_bra]
  rw [← Finset.sum_smul, Operator.trace, ← map_sum, ← Finset.sum_mul, h, one_mul]

/-- Preparing a pure state on one site has one lifted matrix unit for each local basis label. -/
theorem initializeCells_singleton_kraus (v : (i : Fin n) → UnitState (D i)) (i : Fin n)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (D i).state) :
    (initializeCells D (fun j => Density.pure (v j)) {i}).toSuperoperator =
      Superoperator.kraus (fun j => (Register.site D i).liftOperator
        (Operator.outer (v i).val (b j))) := by
  rw [initializeCells_singleton, Register.initializeTo, Register.liftChannel_toSuperoperator,
    replacement_pure_eq_kraus (v i) b, Register.liftSuperoperator_kraus]

private theorem tensor_kraus {A B : Qudit} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → Operator A) (g : κ → Operator B) :
    Superoperator.tensor (Superoperator.kraus f) (Superoperator.kraus g) =
      Superoperator.kraus (fun x : ι × κ => (f x.1).tensor (g x.2)) := by
  simp only [Superoperator.kraus, Superoperator.tensor_sum_left, Superoperator.tensor_sum_right,
    Fintype.sum_prod_type, Operator.tensor, Superoperator.conjugate_tensor]
  exact Finset.sum_comm

/-- On a product channel the ordered lift factors into the first site's channel and
the lift on the remaining sites. -/
theorem orderedChannel_tensor {k : ℕ} (r : Fin (k + 1) ↪ Fin n)
    (Φ : QuantumChannel (D (r 0)) (D (r 0)))
    (Ψ : QuantumChannel (tensorMemory (D ∘ (Fin.succEmb k).trans r))
      (tensorMemory (D ∘ (Fin.succEmb k).trans r))) :
    orderedChannel D r (Φ.tensor Ψ) =
      ((Register.site D (r 0)).liftChannel Φ).comp
        (orderedChannel D ((Fin.succEmb k).trans r) Ψ) := by
  let t := (Fin.succEmb k).trans r
  let p := Register.site D (r 0)
  obtain ⟨_, f, hf, _⟩ := Φ.exists_kraus
  obtain ⟨_, g, hg, _⟩ := Ψ.exists_kraus
  apply QuantumChannel.ext
  change orderedSuperoperator D r (Superoperator.tensor Φ.toSuperoperator Ψ.toSuperoperator) =
    (p.liftChannel Φ).toSuperoperator ∘ₗ orderedSuperoperator D t Ψ.toSuperoperator
  rw [Register.liftChannel_toSuperoperator, hf, hg, Register.liftSuperoperator_kraus,
    orderedSuperoperator_kraus]
  refine (congrArg (orderedSuperoperator D r) (tensor_kraus (A := D (r 0))
    (B := tensorMemory (D ∘ t)) f g)).trans ((orderedSuperoperator_kraus D r _).trans ?_)
  apply LinearMap.ext
  intro X
  simp only [Superoperator.kraus, LinearMap.sum_apply, LinearMap.comp_apply, Fintype.sum_prod_type,
    map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have he := orderedLift_tensor D r (f i) (g j)
  exact LinearMap.congr_fun ((congrArg Superoperator.conjugate he).trans
    (Superoperator.conjugate_comp (orderedLift D t (g j)) (p.liftOperator (f i)))) X

/-- A joint replacement by a product density is a tensor product of replacements. -/
private theorem replacement_tensor {A B : Qudit} (a : Density A) (b : Density B) :
    QuantumChannel.replacement (A ⊗ B) (a.tensor b) =
      (QuantumChannel.replacement A a).tensor (QuantumChannel.replacement B b) := by
  apply QuantumChannel.ext
  apply Operator.tensor_ext
  intro X Y
  change _ = Superoperator.tensor _ _ (X.tensor Y)
  rw [QuantumChannel.replacement_apply, Superoperator.tensor_apply,
    QuantumChannel.replacement_apply, QuantumChannel.replacement_apply,
    Operator.trace_tensor, Density.op_tensor]
  simp only [Operator.tensor, TensorProduct.map_smul_left, TensorProduct.map_smul_right, mul_smul]
  exact smul_comm _ _ _

/-- The product density in register order, with the unique scalar state on an empty tuple. -/
def registerProductDensity : {n : ℕ} → (D : Fin n → Qudit) → ((i : Fin n) → Density (D i)) →
    Density (tensorMemory D)
  | 0, D, _ => Density.pure (registerProductState D fun i => i.elim0)
  | _ + 1, D, τ => (τ 0).tensor (registerProductDensity (Fin.tail D) (Fin.tail τ))

/-- The density of the existing register product vector is the product of its local densities. -/
theorem registerProductDensity_pure (v : (i : Fin n) → UnitState (D i)) :
    registerProductDensity D (fun i => Density.pure (v i)) =
      Density.pure (registerProductState D v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (congrArg ((Density.pure (v 0)).tensor ·) (ih (Fin.tail D) (Fin.tail v))).trans
      (Density.tensor_pure ..)

/-- A single joint initialization of a product density agrees with the finite-set channel.
Consequently its action is independent of how the selected sites are enumerated. -/
theorem orderedInitialize_product {k : ℕ} (r : Fin k ↪ Fin n) :
    orderedInitialize D r (registerProductDensity (D ∘ r) (fun i => τ (r i))) =
      initializeCells D τ (Finset.univ.map r) := by
  induction k with
  | zero =>
    rw [orderedInitialize_empty, Finset.univ_eq_empty, Finset.map_empty, initializeCells_empty]
  | succ k ih =>
    let t := (Fin.succEmb k).trans r
    have hs : Finset.univ.map r = {r 0} ∪ Finset.univ.map t := by
      ext i
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨j, rfl⟩
        cases j using Fin.cases with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨j, rfl⟩
      · rintro (rfl | ⟨j, rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨j.succ, rfl⟩
    rw [hs, initializeCells_union, initializeCells_singleton, ← ih t]
    exact (congrArg (orderedChannel D r) (replacement_tensor (τ (r 0))
      (registerProductDensity (D ∘ t) (fun i => τ (t i))))).trans (orderedChannel_tensor D r _ _)

end

end QuantumProgram
