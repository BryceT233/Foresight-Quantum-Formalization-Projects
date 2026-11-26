/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the counted Hadamard program on a subregister.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/ParallelHadamardTriple.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.CQM.Qudit.Measurement.Basic
public import FQFP.CQM.Qudit.TensorPower
public import FQFP.QuantumProgram.Logic.Source.Counted
public import FQFP.QuantumProgram.Logic.Source.Unitary

/-!
# Parallel Hadamard on a subregister

An embedding orders the selected sites of a qubit tensor power. The loop turns their zero
factors into plus factors in that order, preserving the given product state on all other sites.
The counter may be one coordinate of a larger classical store.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

noncomputable section

variable {Store : Type*} {n m : ℕ} (r : Fin n ↪ Fin (m + 1)) (g : Fin (m + 1) → UnitState Qubit)

/-- Local factors after the first `k` selected sites have been visited. -/
def hadamardFactors (k : ℕ) : Fin (m + 1) → UnitState Qubit :=
  let zero := UnitState.ofBasis (ZBasis 2) 0
  Function.extend r (fun i => if i.val < k then UnitState.map Qubit.H.asHom zero else zero) g

/-- On a selected site the factor depends only on its position in the register. -/
theorem hadamardFactors_apply (k : ℕ) (i : Fin n) :
    hadamardFactors r g k (r i) = let zero := UnitState.ofBasis (ZBasis 2) 0
      if i.val < k then UnitState.map Qubit.H.asHom zero else zero := by
  simp only [hadamardFactors, r.injective.extend_apply]

/-- An unselected site retains its original factor at every iteration. -/
theorem hadamardFactors_of_notMem (k : ℕ) {j : Fin (m + 1)} (hj : j ∉ Set.range r) :
    hadamardFactors r g k j = g j := by
  unfold hadamardFactors
  exact Function.extend_apply' _ g j hj

/-- At entry the selected sites carry zero and each spectator carries its given factor. -/
theorem hadamardFactors_zero :
    hadamardFactors r g 0 = Function.extend r (fun _ => UnitState.ofBasis (ZBasis 2) 0) g := by
  simp [hadamardFactors]

/-- At exit the selected sites carry plus and each spectator carries its given factor. -/
theorem hadamardFactors_full :
    hadamardFactors r g n = Function.extend r
      (fun _ => UnitState.map Qubit.H.asHom (UnitState.ofBasis (ZBasis 2) 0)) g := by
  simp only [hadamardFactors, Fin.is_lt, ite_true]

/-- Applying the gate at the next selected site advances the whole product vector. -/
theorem siteOp_hadamardFactors (i : Fin n) :
    siteOp Qubit m (r i) Qubit.H.asHom.hom (UnitState.productVector m (hadamardFactors r g i.val)) =
      (UnitState.productVector m (hadamardFactors r g (i.val + 1))).val := by
  change siteOp Qubit m _ _ (productVector Qubit m _) = productVector Qubit m _
  rw [siteOp_productVector]
  apply congrArg (productVector Qubit m)
  funext j
  by_cases hj : j = r i
  · subst j
    simp only [Function.update_self, hadamardFactors_apply, lt_irrefl, ite_false, Nat.lt_succ_self,
      ite_true, UnitState.coe_map]
  · rw [Function.update_of_ne hj]
    by_cases h : j ∈ Set.range r
    · obtain ⟨l, rfl⟩ := h
      have hne : l.val ≠ i.val := fun e => hj (congrArg r (Fin.ext e))
      simp only [hadamardFactors_apply, show l.val < i.val + 1 ↔ l.val < i.val by lia]
    · rw [hadamardFactors_of_notMem r g _ h, hadamardFactors_of_notMem r g _ h]

variable [NeZero n] (c : CounterLens Store)

/-- Apply one Hadamard to the selected site indexed by the current counter. -/
def hadamardBodyOn : Command Store (Fin (m + 1)) (tensorPower Qubit m) :=
  let site := fun σ => r (Fin.ofNat n (c.get σ))
  .unitary (fun σ (_ : Fin 1) => site σ)
    (fun σ _ => .liftGate (siteOp Qubit m (site σ)) Qubit.H)

/-- Traverse the selected register in its given order, starting at counter zero. -/
def hadamardLoopOn : Command Store (Fin (m + 1)) (tensorPower Qubit m) :=
  .counted c (fun _ => n) (hadamardBodyOn r c)

/-- The source derivation preserves a classical condition stable under counter writes and
establishes the exact exit counter. Spectator factors may be arbitrary unit states. -/
theorem sourceDeriv_hadamardLoopOn (φ : Store → Prop) (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ) :
    SourceDerivTot
      (.ofEffect (Assertion.pure (UnitState.productVector m (hadamardFactors r g 0))) φ)
      (hadamardLoopOn r c)
      (.ofEffect (Assertion.pure (UnitState.productVector m (hadamardFactors r g n)))
        fun σ => φ σ ∧ c.get σ = n) := by
  let state := fun k => UnitState.productVector m (hadamardFactors r g k)
  apply SourceDerivTot.countedFamily c (fun _ => n) φ hφ (fun _ _ => rfl)
    (fun k => Assertion.pure (state k)) (fun _ _ _ => rfl) (hadamardBodyOn r c)
  · apply SourceDerivTot.unitary_pure _ _ (fun σ => state (c.get σ)) (fun σ => state (c.get σ + 1))
      (fun _ _ => Function.injective_of_subsingleton _)
    intro σ h
    let i : Fin n := ⟨c.get σ, h.2⟩
    have hi : Fin.ofNat n (c.get σ) = i := Fin.ext (Nat.mod_eq_of_lt h.2)
    change siteOp Qubit m (r (Fin.ofNat n (c.get σ))) _ _ = _
    rw [hi]
    exact siteOp_hadamardFactors r g i
  · exact fun _ => SourceDerivTot.unitary_identity _ _ _
      (fun _ _ => Function.injective_of_subsingleton _)

/-- The total derivation carries the prepared projector masked by the exact exit counter. -/
theorem derivTot_hadamardLoopOn :
    DerivTot (Assertion.pure (UnitState.productVector m (hadamardFactors r g 0)))
      (hadamardLoopOn r c)
      ((Assertion.pure (UnitState.productVector m (hadamardFactors r g n))).mask
        fun σ => c.get σ = n) := by
  have d := sourceDeriv_hadamardLoopOn r g c (fun _ => True) (fun _ _ => Iff.rfl)
  simp only [true_and] at d
  apply DerivTot.conseq _ d.toDerivTot le_rfl
  intro σ
  exact (Assertion.mask_of_pos _ (φ := fun _ => True) (σ := σ) trivial).ge

/-- Semantic total correctness on the selected register, with the exact counter at exit. -/
theorem validTot_hadamardLoopOn :
    validTot (Assertion.pure (UnitState.productVector m (hadamardFactors r g 0)))
      (hadamardLoopOn r c)
      ((Assertion.pure (UnitState.productVector m (hadamardFactors r g n))).mask
        fun σ => c.get σ = n) :=
  (derivTot_hadamardLoopOn r g c).sound

end

end QuantumProgram
