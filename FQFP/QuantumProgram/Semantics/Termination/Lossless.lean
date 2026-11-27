/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/ResourceCounting/Lossless.lean: Lossless, its primitive
and composition rules, of_wp_top and of_wp_eq_top. Here termination is measured on histories
and local instructions check the evaluated addresses.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026

Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FQFP.QuantumProgram.Semantics.Precondition.Liberal

/-!
# Lossless commands

A lossless command returns its entire input trace on terminating histories. This criterion
applies to unnormalized inputs and implies that partial and total correctness coincide.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Every input's full trace reaches terminal configurations. -/
def Lossless (p : Command Store Cell H) : Prop :=
  ∀ s : CQState Store H, (Configuration.mk (some p) s).terminatingMass = s.mass

/-- Returning all mass is equivalent to preserving the identity postcondition backwards. -/
theorem lossless_iff_wp_identity {p : Command Store Cell H} :
    Lossless p ↔ wp p Assertion.identity = Assertion.identity := by
  rw [Lossless, ← validTot_identity_iff, validTot_iff_le_wp]
  exact ⟨fun h => le_antisymm (fun σ => (wp p Assertion.identity σ).2.2) h, fun h => h.ge⟩

namespace Lossless

/-- Any postcondition established with the full input trace implies losslessness. -/
theorem of_wp_eq_identity {p : Command Store Cell H} {B : Assertion Store H}
    (h : wp p B = Assertion.identity) : Lossless p := by
  apply (validTot_identity_iff p).mp
  exact validTot_iff_le_wp.mpr (h.ge.trans (wp_mono p fun σ => (B σ).2.2))

/-- Skipping returns the input trace. -/
theorem skip : Lossless (.skip : Command Store Cell H) := lossless_iff_wp_identity.mpr (wp_skip _)

/-- Classical assignment preserves the input trace. -/
theorem assign (f : Store → Store) : Lossless (.assign f : Command Store Cell H) :=
  lossless_iff_wp_identity.mpr (wp_assign f _)

/-- Every quantum channel preserves the input trace. -/
theorem channel (f : Store → QuantumChannel H H) :
    Lossless (.channel f : Command Store Cell H) := by
  apply lossless_iff_wp_identity.mpr
  rw [wp_channel]
  exact funext fun σ => Subtype.ext (f σ).dual_one

/-- A unitary instruction is lossless when its evaluated addresses are always distinct. -/
theorem unitary {k : ℕ} {r : Store → Fin k → Cell}
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (hr : ∀ σ, Function.Injective (r σ)) :
    Lossless (.unitary r U) := by
  apply lossless_iff_wp_identity.mpr
  rw [wp_unitary]
  funext σ
  simpa only [Assertion.unitaryPre, dite_eq_left (hr σ)] using
    Subtype.ext ((U σ (hr σ)).toChannel.dual_one)

/-- A complete instrument returns all branch mass when the measured register is valid. -/
theorem measure {k m : ℕ} {r : Store → Fin k → Cell}
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
    (upd : Fin m → Store → Store) (hr : ∀ σ, Function.Injective (r σ)) :
    Lossless (.measure r I upd) := by
  apply lossless_iff_wp_identity.mpr
  rw [wp_measure]
  funext σ
  simp only [Assertion.measurePre, dite_eq_left (hr σ), Assertion.identity, instrumentEffect_const]
  exact Subtype.ext (I σ (hr σ)).toChannel.dual_one

/-- Two lossless commands compose sequentially. -/
theorem seq {p q : Command Store Cell H} (hp : Lossless p) (hq : Lossless q) :
    Lossless (p.seq q) :=
  fun s => ((Configuration.mk (some p) s).terminatingMass_seqWith_eq_of_mem_frontier q
    (fun _ t _ => hq t)).trans (hp s)

/-- Finite iteration preserves the input trace when each listed command does. -/
theorem forList {ι : Type*} (l : List ι) {body : ι → Command Store Cell H}
    (h : ∀ i ∈ l, Lossless (body i)) : Lossless (.forList l body) := by
  induction l with
  | nil => exact skip
  | cons i l ih =>
    exact (h i List.mem_cons_self).seq (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- A conditional with two lossless branches is lossless. -/
theorem ite (b : Store → Bool) {p q : Command Store Cell H} (hp : Lossless p) (hq : Lossless q) :
    Lossless (.ite b p q) := by
  apply lossless_iff_wp_identity.mpr
  funext σ
  simp [wp_ite, lossless_iff_wp_identity.mp hp, lossless_iff_wp_identity.mp hq]

/-- A lossless execution leaves zero residual mass on every input. -/
theorem nonterminatingMass_eq_zero {p : Command Store Cell H} (hp : Lossless p)
    (s : CQState Store H) : (Configuration.mk (some p) s).nonterminatingMass = 0 := by
  simp [Configuration.nonterminatingMass, hp s]

/-- A lossless command has the same total and liberal preconditions for every postcondition. -/
theorem wp_eq_wlp {p : Command Store Cell H} (hp : Lossless p) (B : Assertion Store H) :
    wp p B = wlp p B := by
  apply wp_eq_of_expectation
  intro s
  rw [expectation_wlp, hp.nonterminatingMass_eq_zero, add_zero]

/-- Partial and total validity agree for a lossless command. -/
theorem validPar_iff_validTot {p : Command Store Cell H} (hp : Lossless p)
    {A B : Assertion Store H} : validPar A p B ↔ validTot A p B := by
  rw [validPar_iff_le_wlp, validTot_iff_le_wp, hp.wp_eq_wlp]

end Lossless

/-- Agreement of the two preconditions for even one postcondition detects losslessness. -/
theorem wp_eq_wlp_iff_lossless (p : Command Store Cell H) (B : Assertion Store H) :
    wp p B = wlp p B ↔ Lossless p := by
  refine ⟨fun h s => ?_, fun hp => hp.wp_eq_wlp B⟩
  let c := Configuration.mk (some p) s
  have he := expectation_wlp p B s
  rw [← h, expectation_wp] at he
  have hfin := (c.PostH_le_mass (fun σ => (B σ).2.2)).trans_lt ENNReal.coe_lt_top
  have hz : 0 = c.nonterminatingMass := (ENNReal.add_right_inj hfin.ne).mp (by
    simpa only [add_zero] using he)
  simpa only [← hz, add_zero] using c.terminatingMass_add_nonterminatingMass

end QuantumProgram
