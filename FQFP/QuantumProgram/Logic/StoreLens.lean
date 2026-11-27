/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Subroutine.lean (DerivTot.mapStore_pull)
Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Command.StoreLens
public import FQFP.QuantumProgram.Semantics.Termination.Lossless

/-!
# Verification of subprograms through a classical store lens

An assertion on the component store is read through `l.get` in the enclosing store. Provided
every write can be read back, this transports partial and total derivations and commutes with
both weakest preconditions. The loop case follows from equality at every finite unrolling.
-/

@[expose] public section

open Filter Qudit
open scoped ENNReal Topology

namespace QuantumProgram

variable {S T Cell : Type*} {H : Qudit}
variable (l : StoreLens T S) (hget : ∀ τ σ, l.get (l.put τ σ) = σ)
include hget

private theorem comp_write (A : Assertion S H) (f : S → S) :
    (A ∘ l.get) ∘ (fun τ => l.put τ (f (l.get τ))) = (A ∘ f) ∘ l.get := by
  funext τ
  simp only [Function.comp_apply, hget]

private theorem measurePre_mapStore (A : Assertion S H) {k m : ℕ} (r : S → Fin k → Cell)
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → S → S) :
    Assertion.measurePre (A ∘ l.get) (r ∘ l.get) (fun τ => I (l.get τ))
      (fun i τ => l.put τ (upd i (l.get τ))) = A.measurePre r I upd ∘ l.get := by
  funext τ
  simp only [Assertion.measurePre, Function.comp_apply, hget]

/-- A Kraus operator read from the component store frames the transported command. -/
theorem Command.KrausFrame.mapStore {K : S → Operator H} {p : Command S Cell H}
    (hf : p.KrausFrame K) : (p.mapStore l).KrausFrame (K ∘ l.get) := by
  induction p with
  | skip => trivial
  | assign f => exact fun τ => (congrArg K (hget ..)).trans (hf (l.get τ))
  | channel f => exact fun τ => hf (l.get τ)
  | unitary r U => exact fun τ => hf (l.get τ)
  | measure r I upd =>
    exact ⟨fun τ => hf.1 (l.get τ), fun i τ => (congrArg K (hget ..)).trans (hf.2 i (l.get τ))⟩
  | seq _ _ ih₁ ih₂ | ite _ _ _ ih₁ ih₂ => exact ⟨ih₁ hf.1, ih₂ hf.2⟩
  | whileDo _ _ ih => exact ih hf

/-- Reuse a partial derivation on a component of the enclosing store. -/
theorem DerivPar.mapStore {A B : Assertion S H} {p : Command S Cell H} (d : DerivPar A p B) :
    DerivPar (A ∘ l.get) (p.mapStore l) (B ∘ l.get) := by
  induction d with
  | skip A => exact .skip _
  | assign f A => rw [← comp_write l hget]; exact .assign _ _
  | channel f A => exact .channel _ (A ∘ l.get)
  | unitary r U A => exact .unitary _ _ (A ∘ l.get)
  | measure r I upd A => rw [← measurePre_mapStore l hget]; exact .measure _ _ _ _
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | cond _ _ ih₁ ih₀ => exact .cond ih₁ ih₀
  | whileLoop _ ih => exact .whileLoop ih
  | conseq hA _ hB ih => exact .conseq (fun τ => hA (l.get τ)) ih (fun τ => hB (l.get τ))

/-- Reuse a total derivation, including its loop ranks and framed Kraus rules. -/
theorem DerivTot.mapStore {A B : Assertion S H} {p : Command S Cell H} (d : DerivTot A p B) :
    DerivTot (A ∘ l.get) (p.mapStore l) (B ∘ l.get) := by
  induction d with
  | skip A => exact .skip _
  | assign f A => rw [← comp_write l hget]; exact .assign _ _
  | channel f A => exact .channel _ (A ∘ l.get)
  | unitary r U A => exact .unitary _ _ (A ∘ l.get)
  | measure r I upd A => rw [← measurePre_mapStore l hget]; exact .measure _ _ _ _
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | cond _ _ ih₁ ih₀ => exact .cond ih₁ ih₀
  | whileLoop t _ ih => exact .whileLoop (t ∘ l.get) ih
  | @whileLoopSource b A φ _ t hb _ _ ihInv ihRank =>
    exact .whileLoopSource (A := A ∘ l.get) (φ := φ ∘ l.get) (t ∘ l.get)
      (fun τ => hb (l.get τ)) ihInv ihRank
  | convex w hw _ ih => exact .convex w hw ih
  | kraus K hK hf _ ih =>
    exact .kraus (K ∘ l.get) (fun τ => hK (l.get τ)) (fun i => (hf i).mapStore l hget) ih
  | conseq hA _ hB ih => exact .conseq (fun τ => hA (l.get τ)) ih (fun τ => hB (l.get τ))

/-- Computing the total weakest precondition commutes with reading the component store. -/
theorem wp_mapStore (p : Command S Cell H) (B : Assertion S H) :
    wp (p.mapStore l) (B ∘ l.get) = wp p B ∘ l.get := by
  induction p generalizing B with
  | skip => simp only [Command.mapStore, wp_skip]
  | assign f => simpa only [Command.mapStore, wp_assign] using comp_write l hget B f
  | channel f => simp only [Command.mapStore, wp_channel]; rfl
  | unitary r U => simp only [Command.mapStore, wp_unitary]; rfl
  | measure r I upd =>
    simpa only [Command.mapStore, wp_measure] using measurePre_mapStore l hget B r I upd
  | seq p q hp hq => simp only [Command.mapStore, wp_seq, hq, hp]
  | ite b p q hp hq =>
    funext τ
    simp only [Command.mapStore, Function.comp_apply, wp_ite, hp, hq]
  | whileDo b p ih =>
    have approx (n : ℕ) : whileWpApprox (b ∘ l.get) (p.mapStore l) (B ∘ l.get) n =
        whileWpApprox b p B n ∘ l.get := by
      induction n with
      | zero => rfl
      | succ n hn =>
        funext τ
        simp only [whileWpApprox, whileWpStep, OrderHom.coe_mk, hn, ih, Function.comp_apply]
    apply wp_eq_of_expectation
    intro s
    let t : CQState S H := ⟨l.get s.store, s.op, s.positive⟩
    change _ = ENNReal.ofReal (t.expectation (wp (.whileDo b p) B t.store))
    rw [expectation_wp]
    apply tendsto_nhds_unique (tendsto_expectation_whileWpApprox _ _ _ s)
    simpa only [approx, Function.comp_apply, CQState.expectation, t] using
      tendsto_expectation_whileWpApprox b p B t

/-- Liberal weakest preconditions also commute with reading the component store. -/
theorem wlp_mapStore (p : Command S Cell H) (B : Assertion S H) :
    wlp (p.mapStore l) (B ∘ l.get) = wlp p B ∘ l.get := by
  change (wp (p.mapStore l) (B.compl ∘ l.get)).compl = _
  rw [wp_mapStore l hget]
  rfl

/-- Transport a semantic total triple, including triples obtained directly from execution. -/
theorem validTot.mapStore {A B : Assertion S H} {p : Command S Cell H} (h : validTot A p B) :
    validTot (A ∘ l.get) (p.mapStore l) (B ∘ l.get) := by
  rw [validTot_iff_le_wp, wp_mapStore l hget]
  exact fun τ => validTot_iff_le_wp.mp h (l.get τ)

/-- Transport partial validity with the same credit for blocked or diverging executions. -/
theorem validPar.mapStore {A B : Assertion S H} {p : Command S Cell H} (h : validPar A p B) :
    validPar (A ∘ l.get) (p.mapStore l) (B ∘ l.get) := by
  rw [validPar_iff_le_wlp, wlp_mapStore l hget]
  exact fun τ => validPar_iff_le_wlp.mp h (l.get τ)

/-- Running a lossless subprogram through the lens preserves the full input trace. -/
theorem Lossless.mapStore {p : Command S Cell H} (hp : Lossless p) : Lossless (p.mapStore l) := by
  apply lossless_iff_wp_identity.mpr
  change wp (p.mapStore l) (Assertion.identity ∘ l.get) = _
  rw [wp_mapStore l hget, lossless_iff_wp_identity.mp hp]
  rfl

end QuantumProgram
