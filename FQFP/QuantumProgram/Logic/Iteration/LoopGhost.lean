/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/LoopGhost.lean (integer rank assertions and their fixed-value slices)
Qhl/Logic/Source/Rules.lean (total loop with a ghost rank premise)
Qhl/Logic/Source/RulesSoundness.lean (soundness of the ghost rank premise)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.GhostStore
public import FQFP.QuantumProgram.Logic.Source.Rules

/-!
# Total loops with the old integer rank in the classical store

The loop body may update the original store. The additional component records the rank on
entry. Restricting a source proof to each fixed old rank supplies the ordinary loop rule.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {S R Cell : Type*} {H : Qudit}

/-- Evaluate reads at a fixed ghost value and keep the first component of each write. -/
def StoreLens.slice (z : R) : StoreLens S (S × R) := ⟨fun σ => (σ, z), fun _ v => v.1⟩

/-- Slicing recovers the original command after extending its store by a ghost. -/
theorem Command.mapStore_fst_slice (p : Command S Cell H) (z : R) :
    (p.mapStore StoreLens.fst).mapStore (StoreLens.slice z) = p := by
  induction p <;> simp_all [mapStore, StoreLens.fst, StoreLens.slice, Function.comp_def]

/-- A fixed-parameter slice inherits the quantum frame when classical writes preserve the ghost. -/
theorem Command.KrausFrame.slice {K : S × R → Operator H} {p : Command (S × R) Cell H}
    (hf : p.KrausFrame K) (hp : p.PreservesParameters Prod.snd) (z : R) :
    (p.mapStore (StoreLens.slice z)).KrausFrame (fun σ => K (σ, z)) := by
  induction p with
  | skip => trivial
  | assign f =>
    intro σ
    apply Eq.trans _ (hf (σ, z))
    exact congrArg K (Prod.ext rfl (hp (σ, z)).symm)
  | channel f => exact fun σ => hf (σ, z)
  | unitary r U => exact fun σ => hf (σ, z)
  | measure r I upd =>
    refine ⟨fun σ => hf.1 (σ, z), fun i σ => Eq.trans ?_ (hf.2 i (σ, z))⟩
    exact congrArg K (Prod.ext rfl (hp i (σ, z)).symm)
  | seq _ _ ih₁ ih₂ | ite _ _ _ ih₁ ih₂ => exact ⟨ih₁ hf.1 hp.1, ih₂ hf.2 hp.2⟩
  | whileDo _ _ ih => exact ih hf hp

/-- Read the classical condition and effect at one value of the ghost. -/
def CQAssertion.ghostSlice (A : CQAssertion (S × R) H) (z : R) : CQAssertion S H :=
  .ofEffect (fun σ => A.effect (σ, z)) fun σ => A.cls (σ, z)

private def sliceEffect (A : SourceEffect (S × R) H) (z : R) : SourceEffect S H :=
  ⟨fun σ => A.defined (σ, z), fun σ => A.effect (σ, z)⟩

private def sliceSource (A : SourceAssertion (S × R) H) (z : R) : SourceAssertion S H :=
  ⟨fun σ => A.classical (σ, z), sliceEffect A.quantum z⟩

private theorem entails_slice {A B : SourceAssertion (S × R) H} (h : A.Entails B) (z : R) :
    (sliceSource A z).Entails (sliceSource B z) :=
  ⟨fun σ => h.1 (σ, z), fun σ => h.2 (σ, z)⟩

/-- Specialize a total source proof at a parameter preserved by all classical writes. -/
theorem SourceDerivTot.ghostSlice {A B : CQAssertion (S × R) H} {p : Command (S × R) Cell H}
    (d : SourceDerivTot A p B) (z : R) (hp : p.PreservesParameters Prod.snd) :
    SourceDerivTot (A.ghostSlice z) (p.mapStore (StoreLens.slice z)) (B.ghostSlice z) := by
  let atZ := fun σ : S => (σ, z)
  induction d with
  | skip A => exact .skip (A.ghostSlice z)
  | cond b _ _ ih₁ ih₀ => exact .cond (b ∘ atZ) (ih₁ hp.1) (ih₀ hp.2)
  | assign f A φ =>
    have he (σ : S) : atZ (f (atZ σ)).1 = f (atZ σ) := Prod.ext rfl (hp (atZ σ)).symm
    change SourceDerivTot (.ofEffect (fun σ => A (f (atZ σ))) (fun σ => φ (f (atZ σ))))
      (.assign fun σ => (f (atZ σ)).1)
      (.ofEffect (A ∘ atZ) (φ ∘ atZ))
    simpa only [Function.comp_def, he] using
      (assign (Cell := Cell) (fun σ => (f (atZ σ)).1) (A ∘ atZ) (φ ∘ atZ))
  | channel f A φ => exact channel _ (A ∘ atZ) (φ ∘ atZ)
  | unitary r U A φ hr => exact unitary _ _ (A ∘ atZ) (φ ∘ atZ) fun σ => hr (atZ σ)
  | measureAll r I upd A φ =>
    let write := fun i σ => (upd i (atZ σ)).1
    have he (i) (σ : S) : atZ (write i σ) = upd i (atZ σ) := Prod.ext rfl (hp i (atZ σ)).symm
    change SourceDerivTot (.ofEffect (A.measurePre r I upd ∘ atZ)
      (fun σ => Function.Injective (r (atZ σ)) ∧ ∀ i, φ (upd i (atZ σ))))
        (.measure (r ∘ atZ) (fun σ => I (atZ σ)) write)
        (.ofEffect (A ∘ atZ) (φ ∘ atZ))
    have hpre : Assertion.measurePre (A ∘ atZ) (r ∘ atZ) (fun σ => I (atZ σ)) write =
        A.measurePre r I upd ∘ atZ := by
      funext σ
      simp only [Assertion.measurePre, Function.comp_apply, he]
    rw [← hpre]
    simpa only [Function.comp_def, he] using
      (measureAll (r ∘ atZ) (fun σ => I (atZ σ)) write (A ∘ atZ) (φ ∘ atZ))
  | @mask _ _ A φ χ _ ih => exact mask (A := A ∘ atZ) (φ := φ ∘ atZ) (χ := χ ∘ atZ) (ih hp)
  | seq _ _ ih₁ ih₂ => exact seq (ih₁ hp.1) (ih₂ hp.2)
  | @whileLoop b p A φ t hb _ _ ihInv ihRank =>
    exact whileLoop (A := A ∘ atZ) (φ := φ ∘ atZ) (t ∘ atZ) (fun σ => hb (atZ σ))
      (ihInv hp) (fun k => ihRank k hp)
  | convex1 φ χ A B w hw p hx _ ih =>
    exact convex1 (φ ∘ atZ) (fun i => χ i ∘ atZ) (fun i => sliceEffect (A i) z)
      (sliceEffect B z) w hw _ (fun σ => hx (atZ σ)) (fun i => ih i hp)
  | convex2 φ χ A B w hw p hd _ ih =>
    exact convex2 (φ ∘ atZ) (χ ∘ atZ) (fun i => sliceEffect (A i) z)
      (fun i => sliceEffect (B i) z) w hw _ (fun σ => hd (atZ σ)) (fun i => ih i hp)
  | accum2 φ ψ A B K hK p hf hd _ ih =>
    exact accum2 (φ ∘ atZ) (ψ ∘ atZ) (fun i => sliceEffect (A i) z)
      (fun i => sliceEffect (B i) z) (K ∘ atZ) (fun σ => hK (atZ σ)) _
      (fun i => (hf i).slice hp z) (fun σ => hd (atZ σ)) (fun i => ih i hp)
  | accum1 φ ψ A B K hK J hJ p hf hx hd _ ih =>
    exact accum1 (φ ∘ atZ) (fun i => ψ i ∘ atZ) (fun i => sliceEffect (A i) z)
      (sliceEffect B z) (K ∘ atZ) (fun σ => hK (atZ σ)) (J ∘ atZ) (fun σ => hJ (atZ σ))
      _ (fun i => (hf i).slice hp z) (fun σ => hx (atZ σ)) (fun σ => hd (atZ σ))
      (fun i => ih i hp)
  | @sourceConseq A A' B' B p h₁ _ h₂ ih =>
    exact sourceConseq (B' := sliceSource B' z) (entails_slice h₁ z) (ih hp) (entails_slice h₂ z)

/-- A source derivation for the transported command yields a proof for each fixed parameter. -/
theorem SourceDerivTot.of_mapStore_fst {A B : CQAssertion (S × R) H} {p : Command S Cell H}
    (d : SourceDerivTot A (p.mapStore StoreLens.fst) B) (z : R) :
    SourceDerivTot (A.ghostSlice z) p (B.ghostSlice z) := by
  simpa only [Command.mapStore_fst_slice] using
    d.ghostSlice z (p.preservesParameters_mapStore _ _ fun _ _ => rfl)

/-- At entry, the ghost contains the current rank and the loop guard holds. -/
def rankGhostPre (φ : S → Prop) (b : S → Bool) (t : S → ℤ) : CQAssertion (S × ℤ) H :=
  .ofEffect Assertion.identity fun σ => φ σ.1 ∧ b σ.1 = true ∧ t σ.1 = σ.2

/-- On return from the body the rank is strictly smaller than the recorded value. -/
def rankGhostPost (t : S → ℤ) : CQAssertion (S × ℤ) H :=
  .ofEffect Assertion.identity fun σ => t σ.1 < σ.2

/-- One ghost rank triple is equivalent to the family of fixed-rank semantic premises. -/
theorem validTot_rankGhost_iff (φ : S → Prop) (b : S → Bool) (t : S → ℤ) (p : Command S Cell H) :
    validTot (rankGhostPre φ b t).toAssn (p.mapStore StoreLens.fst) (rankGhostPost t).toAssn ↔
      ∀ z : ℤ, validTot (Assertion.identity.mask fun σ => φ σ ∧ b σ = true ∧ t σ = z)
        p (Assertion.identity.mask fun σ => t σ < z) :=
  validTot_mapStore_fst_iff _ _ p

/-- Total semantic loop rule with the decrease proved once over the extended store. -/
theorem validTot_while_ghost {b : S → Bool} {A : Assertion S H} {φ : S → Prop}
    {p : Command S Cell H} (t : S → ℤ) (hb : ∀ σ, φ σ → 0 ≤ t σ)
    (hInv : validTot ((A.mask φ).mand b) p (A.mask φ))
    (hRank : validTot (rankGhostPre φ b t).toAssn (p.mapStore StoreLens.fst)
      (rankGhostPost t).toAssn) :
    validTot (A.mask φ) (.whileDo b p) ((A.mask φ).mandNot b) :=
  validTot_while_source t hb hInv ((validTot_rankGhost_iff φ b t p).mp hRank)

/-- Total source loop rule with one ghost decrease derivation. The rank is bounded on the
classical invariant, even where its quantum operand is undefined. -/
theorem SourceDerivTot.whileLoopGhost {b : S → Bool} {A : SourceEffect S H} {φ : S → Prop}
    {p : Command S Cell H} (t : S → ℤ) (hb : ∀ σ, φ σ → 0 ≤ t σ)
    (hInv : SourceDerivTot (A.under fun σ => φ σ ∧ b σ = true) p (A.under φ))
    (hRank : SourceDerivTot (rankGhostPre φ b t) (p.mapStore StoreLens.fst) (rankGhostPost t)) :
    SourceDerivTot (A.under φ) (.whileDo b p) (A.under fun σ => φ σ ∧ b σ = false) := by
  have inv := whileLoop (p := p) (b := b) (A := A.effect) (φ := fun σ => φ σ ∧ A.defined σ) t
    (fun σ h => hb σ h.1) (by simpa only [SourceEffect.under, and_right_comm] using hInv)
    (fun z => conseq (A' := (rankGhostPre φ b t).ghostSlice z)
      (fun _ h => ⟨⟨h.1.1, h.2⟩, le_rfl⟩) (hRank.of_mapStore_fst z) (fun _ h => ⟨h, le_rfl⟩))
  simpa only [SourceEffect.under, and_right_comm] using inv

/-- Fixed-rank source proofs together validate the single ghost rank premise. -/
theorem SourceDerivTot.rankGhost_sound {b : S → Bool} {φ : S → Prop} (t : S → ℤ)
    {p : Command S Cell H} (d : ∀ z : ℤ, SourceDerivTot
      (.ofEffect Assertion.identity fun σ => φ σ ∧ b σ = true ∧ t σ = z) p
      (.ofEffect Assertion.identity fun σ => t σ < z)) :
    validTot (rankGhostPre φ b t).toAssn (p.mapStore StoreLens.fst) (rankGhostPost t).toAssn :=
  (validTot_rankGhost_iff φ b t p).mpr fun z => (d z).sound

end QuantumProgram
