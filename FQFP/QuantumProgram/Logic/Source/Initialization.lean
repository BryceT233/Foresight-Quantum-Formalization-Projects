/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/InitComposition.lean (initPre_empty and initPre_union)
Qhl/Logic/Source/Initialization.lean (singleton, finite-block and dynamic-block initialization)
Qhl/Logic/InitBlock.lean (initPre_ancCells_op for a pure ancillary block)

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Command.Initialization
public import FQFP.QuantumProgram.Logic.PredicateGuard
public import FQFP.QuantumProgram.Logic.Iteration.For
import FQFP.CQM.Qudit.Measurement.ClassicalRegister

/-!
# Source derivations for finite-block initialization

The block transformer preserves the classical condition and the quantum operand domain.
Singleton sequences can select addresses from the store, and a conditional scan can select
a block whose size depends on the store.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit

namespace QuantumProgram

noncomputable section

variable {S : Type*} {n : ℕ} {D : Fin n → Qudit} (τ : (i : Fin n) → Density (D i))

/-- The backward transformer for a store-dependent block reset. -/
def SourceAssertion.initializePre (A : SourceAssertion S (tensorMemory D))
    (s : S → Finset (Fin n)) : SourceAssertion S (tensorMemory D) :=
  ⟨A.classical, A.quantum.defined, A.quantum.effect.channelPre (fun σ => initializeCells D τ (s σ))⟩

/-- Resetting a right-hand ancilla to a pure vector compresses the post-effect to that vector
and tensors the resulting system observable with the ancillary identity. -/
theorem Register.initializeTo_right_pullbackEffect {H R : Qudit} (v : UnitState R)
    (E : Set.Icc (0 : Operator (H ⊗ R)) 1) :
    let V := (TensorProduct.mk ℂ H.state R.state).flip v.val
    (((whole.right : Register (H ⊗ R) R).initializeTo (Density.pure v)).pullbackEffect E).val =
      Operator.tensor (V.adjoint ∘ₗ E.val ∘ₗ V) (1 : Operator R) := by
  intro V
  let Φ := (whole.right : Register (H ⊗ R) R).initializeTo (Density.pure v)
  apply Operator.ext_trace
  intro X
  change (Φ.toCPMap.dual.toSuperoperator E.val * X).trace = _
  rw [Φ.toCPMap.trace_dual]
  have he : Φ.toSuperoperator X = Superoperator.conjugate V (Operator.partialTraceRight X) :=
    (initializeTo_right_apply (Density.pure v) X).trans
      (Superoperator.conjugate_tensorInsertion v.val (Operator.partialTraceRight X)).symm
  refine (congrArg (fun Y => (E.val * Y).trace) he).trans
    ((Superoperator.trace_conjugate_adjoint V (Operator.partialTraceRight X) E.val).symm.trans ?_)
  rw [Superoperator.conjugate_apply, LinearMap.adjoint_adjoint]
  exact LinearMap.trace_mul_partialTraceRight X (V.adjoint ∘ₗ E.val ∘ₗ V)

/-- An empty block preserves the source assertion, including its original domain. -/
theorem SourceAssertion.initializePre_empty (A : SourceAssertion S (tensorMemory D)) :
    A.initializePre τ (fun _ => ∅) = A := by
  have he : A.quantum.effect.channelPre (fun _ => initializeCells D τ ∅) = A.quantum.effect :=
    funext fun σ => (congrArg (fun f : QuantumChannel _ _ => f.pullbackEffect (A.quantum.effect σ))
      (initializeCells_empty D τ)).trans (QuantumChannel.pullbackEffect_id _ _)
  simp only [initializePre, he]

/-- Composing two backward transformers collects their selected sites into a union. -/
theorem SourceAssertion.initializePre_union (A : SourceAssertion S (tensorMemory D))
    (s t : S → Finset (Fin n)) :
    (A.initializePre τ t).initializePre τ s = A.initializePre τ (fun σ => s σ ∪ t σ) := by
  suffices (A.quantum.effect.channelPre (fun σ => initializeCells D τ (t σ))).channelPre
      (fun σ => initializeCells D τ (s σ)) =
      A.quantum.effect.channelPre (fun σ => initializeCells D τ (s σ ∪ t σ)) by
    simp only [initializePre, this]
  funext σ
  change (initializeCells D τ (s σ)).pullbackEffect
    ((initializeCells D τ (t σ)).pullbackEffect _) =
      (initializeCells D τ (s σ ∪ t σ)).pullbackEffect _
  rw [Finset.union_comm (s σ) (t σ), initializeCells_union, QuantumChannel.pullbackEffect_comp]

/-- Both source calculi admit the exact finite-block precondition for the atomic reset. -/
theorem initializeCells_derivations (A : SourceAssertion S (tensorMemory D))
    (s : S → Finset (Fin n)) :
    SourceDerivPar (A.initializePre τ s).toCQAssertion (.initializeCellsOn τ s) A.toCQAssertion ∧
    SourceDerivTot (A.initializePre τ s).toCQAssertion (.initializeCellsOn τ s) A.toCQAssertion :=
  ⟨.channel _ _ _, .channel _ _ _⟩

/-- For a pure singleton reset the precondition is a sum over the selected site's own basis. -/
theorem SourceAssertion.initializePre_singleton_op (A : SourceAssertion S (tensorMemory D))
    (v : (i : Fin n) → UnitState (D i)) (q : S → Fin n) (σ : S)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (D (q σ)).state) :
    let K := fun j => (Register.site D (q σ)).liftOperator (Operator.outer (v (q σ)).val (b j))
    ((A.initializePre (fun j => Density.pure (v j)) (fun s => {q s})).quantum.effect σ).val =
      ∑ j, (K j).adjoint ∘ₗ (A.quantum.effect σ).val ∘ₗ K j := by
  intro K
  let Φ := initializeCells D (fun j => Density.pure (v j)) {q σ}
  have he : Φ.toSuperoperator = Superoperator.kraus K := initializeCells_singleton_kraus D v _ b
  change Φ.toCPMap.dual.toSuperoperator (A.quantum.effect σ).val = _
  rw [Φ.toCPMap.dual_toSuperoperator_eq_kraus he]
  simp only [Superoperator.kraus_apply, LinearMap.adjoint_adjoint]

/-- Execute singleton resets in list order, evaluating each address in the current store. -/
def Command.initializeSingles (qs : List (S → Fin n)) : Command S (Fin n) (tensorMemory D) :=
  forList qs fun q => initializeCellsOn τ (fun σ => {q σ})

/-- Sequential initialization leaves every classical parameter unchanged. -/
theorem Command.initializeSingles_preservesParameters {E : Type*} (qs : List (S → Fin n))
    (e : S → E) : (initializeSingles τ qs).PreservesParameters e := by
  induction qs with
  | nil => trivial
  | cons q qs ih => exact ⟨trivial, ih⟩

/-- The compositional precondition for a singleton sequence is the precondition for one block. -/
theorem SourceAssertion.initializeSinglesPre_eq_block (A : SourceAssertion S (tensorMemory D))
    (qs : List (S → Fin n)) :
    qs.foldr (fun q B => B.initializePre τ (fun σ => {q σ})) A =
      A.initializePre τ (fun σ => (qs.map (fun q => q σ)).toFinset) := by
  induction qs with
  | nil => exact (A.initializePre_empty τ).symm
  | cons q qs ih =>
    simp only [List.foldr_cons, ih, SourceAssertion.initializePre_union, List.map_cons,
      List.toFinset_cons, Finset.singleton_union]

/-- Singleton instructions implement a block reset even when addresses coincide at a store. -/
theorem initializeSingles_derivations (A : SourceAssertion S (tensorMemory D))
    (qs : List (S → Fin n)) :
    let B := A.initializePre τ (fun σ => (qs.map (fun q => q σ)).toFinset)
    SourceDerivPar B.toCQAssertion (.initializeSingles τ qs) A.toCQAssertion ∧
    SourceDerivTot B.toCQAssertion (.initializeSingles τ qs) A.toCQAssertion := by
  dsimp only
  rw [← A.initializeSinglesPre_eq_block τ qs]
  induction qs with
  | nil => exact ⟨.skip _, .skip _⟩
  | cons q qs ih =>
    have h := initializeCells_derivations τ
      (qs.foldr (fun q B => B.initializePre τ (fun σ => {q σ})) A) (fun σ => {q σ})
    exact ⟨.seq h.1 ih.1, .seq h.2 ih.2⟩

/-- Enumerating a constant block implements its transformer in both source calculi. -/
theorem initializeFiniteBlock_derivations (A : SourceAssertion S (tensorMemory D))
    (s : Finset (Fin n)) :
    let p := Command.initializeSingles τ (s.toList.map (fun i (_ : S) => i))
    SourceDerivPar (A.initializePre τ (fun _ => s)).toCQAssertion p A.toCQAssertion ∧
    SourceDerivTot (A.initializePre τ (fun _ => s)).toCQAssertion p A.toCQAssertion := by
  simpa [List.map_map, Function.comp_def] using
    initializeSingles_derivations τ A (s.toList.map (fun i (_ : S) => i))

/-- Scan the list, resetting precisely those sites selected at the current store. -/
def Command.initializeSelected (s : S → Finset (Fin n)) (qs : List (Fin n)) :
    Command S (Fin n) (tensorMemory D) :=
  forList qs fun i => .ite (fun σ => decide (i ∈ s σ)) (initializeCellsOn τ (fun _ => {i})) .skip

/-- A conditional reset scan preserves the store used by later membership tests. -/
theorem Command.initializeSelected_preservesParameters {E : Type*} (s : S → Finset (Fin n))
    (qs : List (Fin n)) (e : S → E) : (initializeSelected τ s qs).PreservesParameters e := by
  induction qs with
  | nil => trivial
  | cons q qs ih => exact ⟨⟨trivial, trivial⟩, ih⟩

private theorem branch_entails (A : SourceAssertion S (tensorMemory D)) (s t : S → Finset (Fin n))
    (P : S → Prop) (h : ∀ σ, P σ → s σ = t σ) :
    ((A.initializePre τ s).toCQAssertion.restrict P).Entails
      (A.initializePre τ t).toCQAssertion := by
  intro σ hσ
  refine ⟨hσ.1, ?_⟩
  change (channelEffect (initializeCells D τ (s σ)) _).val ≤
    (channelEffect (initializeCells D τ (t σ)) _).val
  rw [h σ hσ.2]

/-- Pull back along each guarded singleton instruction of the scan. -/
def SourceAssertion.initializeSelectedPre (A : SourceAssertion S (tensorMemory D))
    (s : S → Finset (Fin n)) (qs : List (Fin n)) : SourceAssertion S (tensorMemory D) :=
  ⟨A.classical, A.quantum.defined, qs.foldr (fun i B => Assertion.guard
    (fun σ => decide (i ∈ s σ)) (B.channelPre (fun _ => initializeCells D τ {i})) B)
    A.quantum.effect⟩

/-- The scan's backward transformer and its block precondition agree, including off the
classical support and outside the original operand's domain. -/
theorem SourceAssertion.initializeSelectedPre_eq_block (A : SourceAssertion S (tensorMemory D))
    (s : S → Finset (Fin n)) (qs : List (Fin n)) :
    A.initializeSelectedPre τ s qs = A.initializePre τ (fun σ => s σ ∩ qs.toFinset) := by
  suffices (A.initializeSelectedPre τ s qs).quantum.effect =
      (A.initializePre τ (fun σ => s σ ∩ qs.toFinset)).quantum.effect from
    congrArg (fun E => (⟨A.classical, A.quantum.defined, E⟩ :
      SourceAssertion S (tensorMemory D))) this
  change qs.foldr _ A.quantum.effect = _
  induction qs with
  | nil => simpa using congrArg (fun B => B.quantum.effect) (A.initializePre_empty τ).symm
  | cons i qs ih =>
    rw [List.foldr_cons, ih]
    let t := fun σ => s σ ∩ qs.toFinset
    have he := A.initializePre_union τ (fun _ => {i}) t
    funext σ
    by_cases hm : i ∈ s σ
    · have hu : s σ ∩ (i :: qs).toFinset = {i} ∪ t σ := by
        simp only [List.toFinset_cons, Finset.inter_insert_of_mem hm, Finset.singleton_union, t]
      simp only [Assertion.guard, decide_eq_true hm, ite_true]
      change ((A.initializePre τ t).initializePre τ (fun _ => {i})).quantum.effect σ = _
      rw [he]
      change channelEffect _ _ = channelEffect (initializeCells D τ (s σ ∩ (i :: qs).toFinset)) _
      rw [hu]
    · have hu : s σ ∩ (i :: qs).toFinset = t σ := by
        simp only [List.toFinset_cons, Finset.inter_insert_of_notMem hm, t]
      simp only [Assertion.guard, decide_eq_false hm, Bool.false_eq_true, ite_false]
      change channelEffect _ _ = channelEffect (initializeCells D τ (s σ ∩ (i :: qs).toFinset)) _
      rw [hu]

/-- Each conditional singleton scan has partial and total source derivations with the
single-block precondition. The visited list may contain repetitions. -/
theorem initializeSelected_derivations (A : SourceAssertion S (tensorMemory D))
    (s : S → Finset (Fin n)) (qs : List (Fin n)) :
    let B := A.initializePre τ (fun σ => s σ ∩ qs.toFinset)
    SourceDerivPar B.toCQAssertion (.initializeSelected τ s qs) A.toCQAssertion ∧
    SourceDerivTot B.toCQAssertion (.initializeSelected τ s qs) A.toCQAssertion := by
  dsimp only
  induction qs with
  | nil =>
    simpa [Command.initializeSelected, A.initializePre_empty τ] using
      And.intro (SourceDerivPar.skip (Cell := Fin n) A.toCQAssertion)
        (SourceDerivTot.skip (Cell := Fin n) A.toCQAssertion)
  | cons i qs ih =>
    let t := fun σ => s σ ∩ qs.toFinset
    let u := fun σ => s σ ∩ (i :: qs).toFinset
    let P := fun σ => i ∈ s σ
    let B := A.initializePre τ t
    have hyes := branch_entails τ A u (fun σ => {i} ∪ t σ) P (by
      intro σ hm
      simp only [u, t, List.toFinset_cons, Finset.inter_insert_of_mem hm, Finset.singleton_union])
    rw [← A.initializePre_union τ (fun _ => {i}) t] at hyes
    have hno := branch_entails τ A u t (fun σ => ¬ P σ) (by
      intro σ hm
      simp only [u, t, List.toFinset_cons, Finset.inter_insert_of_notMem hm])
    have h := initializeCells_derivations τ B (fun _ => {i})
    have refl : B.toCQAssertion.Entails B.toCQAssertion := fun _ h => ⟨h, le_rfl⟩
    exact ⟨.seq (.cond_decide P (.conseq hyes h.1 refl) (.conseq hno (.skip _) refl)) ih.1,
      .seq (.cond_decide P (.conseq hyes h.2 refl) (.conseq hno (.skip _) refl)) ih.2⟩

/-- Scanning all sites implements a store-dependent block of any size. -/
theorem initializeDynamicBlock_derivations (A : SourceAssertion S (tensorMemory D))
    (s : S → Finset (Fin n)) :
    let p := Command.initializeSelected τ s (List.finRange n)
    SourceDerivPar (A.initializePre τ s).toCQAssertion p A.toCQAssertion ∧
    SourceDerivTot (A.initializePre τ s).toCQAssertion p A.toCQAssertion := by
  simpa using initializeSelected_derivations τ A s (List.finRange n)

end

end QuantumProgram
