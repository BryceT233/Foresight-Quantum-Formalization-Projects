/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/FrameParameters.lean (Prog.AvoidsRegister and krausFrame_of_parameters)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Initialization

/-!
# From register supports to program frames

The constructors witness the local implementation of each evaluated quantum instruction.
Sequential composition, conditionals and loops carry these witnesses through control flow.
-/

@[expose] public section

open CategoryTheory Qudit

namespace QuantumProgram.Command

variable {S E : Type*} {n : ℕ} (D : Fin n → Qudit)

/-- Every executed quantum primitive acts on cells outside the indicated support. -/
inductive AvoidsRegister (support : S → Set (Fin n)) : Command S (Fin n) (tensorMemory D) → Prop
  /-- Skipping touches no register. -/
  | skip : AvoidsRegister support .skip
  /-- A classical assignment touches no quantum cells. -/
  | assign (f : S → S) : AvoidsRegister support (.assign f)
  /-- A reset may select a different number of disjoint cells at each store. -/
  | initializeCells (τ : (i : Fin n) → Density (D i)) (s : S → Finset (Fin n))
      (hd : ∀ σ i, i ∈ s σ → i ∉ support σ) : AvoidsRegister support (initializeCellsOn τ s)
  /-- All cells on which the channel acts are outside the frame. -/
  | channel {k : ℕ} (p : S → Fin k ↪ Fin n)
      (Φ : (σ : S) → QuantumChannel (tensorMemory (D ∘ p σ)) (tensorMemory (D ∘ p σ)))
      (hd : ∀ σ j, p σ j ∉ support σ) :
      AvoidsRegister support (.channel (fun σ => orderedChannel D (p σ) (Φ σ)))
  /-- Check the support of the gate whenever the evaluated tuple is distinct. -/
  | unitary {k : ℕ} (p : S → Fin k → Fin n) (U : ∀ σ, Function.Injective (p σ) →
      End (tensorMemory (D ∘ p σ)))
      [∀ σ hi, DaggerCategory.IsUnitary (U σ hi).asHom]
      (hd : ∀ σ, Function.Injective (p σ) → ∀ j, p σ j ∉ support σ) :
      AvoidsRegister support (unitaryOn D p U)
  /-- The instrument operates on a disjoint register at each executable store. -/
  | measure {k m : ℕ} (p : S → Fin k → Fin n) (I : ∀ σ, Function.Injective (p σ) →
      Instrument (tensorMemory (D ∘ p σ)) (tensorMemory (D ∘ p σ)) (Fin m))
      (upd : Fin m → S → S) (hd : ∀ σ, Function.Injective (p σ) → ∀ j, p σ j ∉ support σ) :
      AvoidsRegister support (measureOn D p I upd)
  /-- Both commands of a sequence avoid the support. -/
  | seq {p q} : AvoidsRegister support p → AvoidsRegister support q →
      AvoidsRegister support (.seq p q)
  /-- Both conditional branches avoid the support. -/
  | ite {p q} (b : S → Bool) : AvoidsRegister support p → AvoidsRegister support q →
      AvoidsRegister support (.ite b p q)
  /-- Each execution of the body avoids the support. -/
  | whileDo {p} (b : S → Bool) : AvoidsRegister support p → AvoidsRegister support (.whileDo b p)

/-- Register disjointness and preservation of classical parameters establish a Kraus frame
for the whole program. The operator may depend on the value of those parameters. -/
theorem krausFrame_of_parameters {p : Command S (Fin n) (tensorMemory D)} (e : S → E)
    (support : E → Set (Fin n)) (K : E → Operator (tensorMemory D))
    (locality : ∀ a {k : ℕ} (r : Fin k ↪ Fin n), (∀ j, r j ∉ support a) →
      ∀ X, Commute (orderedLift D r X) (K a))
    (hq : p.AvoidsRegister D (support ∘ e)) (hp : p.PreservesParameters e) :
    p.KrausFrame (K ∘ e) := by
  induction hq with
  | skip => trivial
  | assign f => exact fun σ => congrArg K (hp σ)
  | initializeCells τ s hd =>
    intro σ
    let r := ((s σ).orderEmbOfFin rfl).toEmbedding
    have he : orderedInitialize D r (registerProductDensity (D ∘ r) (fun i => τ (r i))) =
        initializeCells D τ (s σ) := by
      rw [orderedInitialize_product, Finset.map_orderEmbOfFin_univ]
    change Function.Commute (initializeCells D τ (s σ)).toSuperoperator _
    rw [← he]
    exact fun ρ => LinearMap.congr_fun (orderedSuperoperator_commute_of_commute D r _
      (locality (e σ) r (fun j => hd σ _ ((s σ).orderEmbOfFin_mem rfl j))) _).eq ρ
  | channel p Φ hd =>
    exact fun σ ρ => LinearMap.congr_fun (orderedSuperoperator_commute_of_commute D (p σ) _
      (locality (e σ) (p σ) (hd σ)) (Φ σ).toSuperoperator).eq ρ
  | unitary p U hd =>
    exact KrausFrame.unitaryOn D p U _ fun σ hi =>
      locality (e σ) ⟨p σ, hi⟩ (hd σ hi) _
  | measure p I upd hd =>
    exact KrausFrame.measureOn D p I upd _ (fun σ hi => locality (e σ) ⟨p σ, hi⟩ (hd σ hi))
      (fun i σ => congrArg K (hp i σ))
  | seq _ _ ihp ihq | ite _ _ _ ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | whileDo _ _ ih => exact ih hp

end QuantumProgram.Command
