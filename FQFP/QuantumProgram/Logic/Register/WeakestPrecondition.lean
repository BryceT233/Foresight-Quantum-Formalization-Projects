/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.OrderedChannel
public import FQFP.QuantumProgram.Semantics.WeakestPrecondition
public import FQFP.QuantumProgram.Semantics.RegisterFrame
public import FQFP.QuantumProgram.Logic.Assertion.Kraus
import FQFP.CQM.Qudit.State.OperatorNorm

/-!
# Weakest preconditions on ordered registers

A local operation receives only the memory of its selected sites. A channel on one
register fixes every effect on a disjoint register under pullback. For an instrument this
applies to the sum over outcomes when the postcondition is independent of the write-back.
For a store-dependent register these laws require disjointness and distinct operands only
at the input store. Repeated operands block the command and give the zero precondition.

For a composite program avoiding the spectator, its precondition is the termination
effect sandwiched between the lifted square roots of the spectator effect.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit

namespace QuantumProgram

noncomputable section

variable {S : Type*} {n k l : ℕ} (D : Fin n → Qudit)

/-- Regard an effect on selected sites as an effect on the whole memory. -/
def orderedLiftEffect (r : Fin k ↪ Fin n) (E : Set.Icc (0 : Operator (tensorMemory (D ∘ r))) 1) :
    Set.Icc (0 : Operator (tensorMemory D)) 1 :=
  ⟨orderedLift D r E,
    by simpa only [map_zero] using OrderHomClass.mono (orderedLift D r) E.property.1,
    by simpa only [map_one] using OrderHomClass.mono (orderedLift D r) E.property.2⟩

/-- A trace-preserving local operation leaves every disjoint observable unchanged in the dual. -/
theorem orderedChannel_pullbackEffect_disjoint (r : Fin k ↪ Fin n) (s : Fin l ↪ Fin n)
    (hd : ∀ i j, r i ≠ s j) (Φ : QuantumChannel (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)))
    (E : Set.Icc (0 : Operator (tensorMemory (D ∘ s))) 1) :
    (orderedChannel D r Φ).pullbackEffect (orderedLiftEffect D s E) = orderedLiftEffect D s E := by
  apply Subtype.ext
  apply Operator.ext_trace
  intro X
  change (((orderedChannel D r Φ).toCPMap.dual.toSuperoperator (orderedLift D s E)) * X).trace = _
  rw [CPMap.trace_dual]
  change (orderedLift D s E * orderedSuperoperator D r Φ.toSuperoperator X).trace = _
  rw [← orderedSuperoperator_mul_left D r s hd]
  exact (orderedChannel D r Φ).tracePreserving _

section Dynamic

variable (cells : S → Fin k → Fin n)
variable (U : ∀ σ, Function.Injective (cells σ) → End (tensorMemory (D ∘ cells σ)))
  [∀ σ hi, IsUnitary (U σ hi).asHom]
variable {m : ℕ} (I : ∀ σ, Function.Injective (cells σ) →
  Instrument (tensorMemory (D ∘ cells σ)) (tensorMemory (D ∘ cells σ)) (Fin m))
variable (upd : Fin m → S → S)

/-- At a valid address tuple the local unitary pulls back through its lifted channel. -/
theorem wp_unitaryOn_of_injective (B : Assertion S (tensorMemory D)) (σ : S)
    (hi : Function.Injective (cells σ)) :
    wp (Command.unitaryOn D cells U) B σ =
      (orderedChannel D ⟨cells σ, hi⟩
        (QuantumChannel.ofIsometry (U σ hi).asHom)).pullbackEffect (B σ) := by
  simp only [Command.unitaryOn, wp_unitary, Assertion.unitaryPre, dite_eq_left hi, channelEffect,
    toChannel_liftGate_orderedLift]

/-- At a valid address tuple each outcome uses its own branch and updated postcondition. -/
theorem wp_measureOn_of_injective (B : Assertion S (tensorMemory D)) (σ : S)
    (hi : Function.Injective (cells σ)) :
    wp (Command.measureOn D cells I upd) B σ =
      instrumentEffect (orderedInstrument D ⟨cells σ, hi⟩ (I σ hi)) (fun i => B (upd i σ)) := by
  simp only [Command.measureOn, wp_measure, Assertion.measurePre, dite_eq_left hi]

/-- Repeated gate operands give the zero precondition for every postcondition. -/
@[simp] theorem wp_unitaryOn_of_not_injective (B : Assertion S (tensorMemory D)) (σ : S)
    (hi : ¬ Function.Injective (cells σ)) :
    wp (Command.unitaryOn D cells U) B σ = Assertion.zero σ := by
  simp only [Command.unitaryOn, wp_unitary, Assertion.unitaryPre, dite_eq_right hi, Assertion.zero]

/-- A blocked measurement contributes zero regardless of its postcondition and write-back. -/
@[simp] theorem wp_measureOn_of_not_injective (B : Assertion S (tensorMemory D)) (σ : S)
    (hi : ¬ Function.Injective (cells σ)) :
    wp (Command.measureOn D cells I upd) B σ = Assertion.zero σ := by
  simp only [Command.measureOn, wp_measure, Assertion.measurePre, dite_eq_right hi, Assertion.zero]

/-- A gate preserves the spectator effect when its current operands are distinct and disjoint. -/
theorem wp_unitaryOn_disjoint (σ : S) (hi : Function.Injective (cells σ)) (s : Fin l ↪ Fin n)
    (hd : ∀ i j, cells σ i ≠ s j) (E : Set.Icc (0 : Operator (tensorMemory (D ∘ s))) 1) :
    wp (Command.unitaryOn D cells U) (fun _ => orderedLiftEffect D s E) σ =
      orderedLiftEffect D s E := by
  rw [wp_unitaryOn_of_injective D cells U _ σ hi]
  exact orderedChannel_pullbackEffect_disjoint D ⟨cells σ, hi⟩ s hd _ E

/-- Summing all outcomes of a valid measurement preserves a disjoint spectator effect. -/
theorem wp_measureOn_disjoint (σ : S) (hi : Function.Injective (cells σ)) (s : Fin l ↪ Fin n)
    (hd : ∀ i j, cells σ i ≠ s j) (E : Set.Icc (0 : Operator (tensorMemory (D ∘ s))) 1) :
    wp (Command.measureOn D cells I upd) (fun _ => orderedLiftEffect D s E) σ =
      orderedLiftEffect D s E := by
  rw [wp_measureOn_of_injective D cells I upd _ σ hi, instrumentEffect_const,
    orderedInstrument_toChannel]
  exact orderedChannel_pullbackEffect_disjoint D ⟨cells σ, hi⟩ s hd _ E

end Dynamic

variable (r : Fin k ↪ Fin n)

/-- The precondition of a fixed local unitary has no address side condition. -/
@[simp] theorem wp_unitaryOnRegister
    (U : End (tensorMemory (D ∘ r))) [IsUnitary U.asHom]
    (B : Assertion S (tensorMemory D)) (σ : S) :
    wp (Command.unitaryOnRegister D r U) B σ =
      (orderedChannel D r (QuantumChannel.ofIsometry U.asHom)).pullbackEffect (B σ) :=
  wp_unitaryOn_of_injective D (fun _ => r) (fun _ _ => U) B σ r.injective

/-- The precondition of a fixed local instrument sums over its original outcomes. -/
@[simp] theorem wp_measureOnRegister {m : ℕ}
    (I : Instrument (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)) (Fin m))
    (upd : Fin m → S → S) (B : Assertion S (tensorMemory D)) (σ : S) :
    wp (Command.measureOnRegister D r I upd) B σ =
      instrumentEffect (orderedInstrument D r I) (fun i => B (upd i σ)) :=
  wp_measureOn_of_injective D (fun _ => r) (fun _ _ => I) upd B σ r.injective

/-- A gate preserves any effect supported on disjoint sites. -/
theorem wp_unitaryOnRegister_disjoint (s : Fin l ↪ Fin n) (hd : ∀ i j, r i ≠ s j)
    (U : End (tensorMemory (D ∘ r))) [IsUnitary U.asHom]
    (E : Set.Icc (0 : Operator (tensorMemory (D ∘ s))) 1) :
    wp (Command.unitaryOnRegister (S := S) D r U) (fun _ => orderedLiftEffect D s E) =
      fun _ => orderedLiftEffect D s E := by
  funext σ
  exact wp_unitaryOn_disjoint D (fun _ => r) (fun _ _ => U) σ r.injective s hd E

/-- Summing all measurement outcomes preserves disjoint effects for any classical write-back. -/
theorem wp_measureOnRegister_disjoint {m : ℕ} (s : Fin l ↪ Fin n) (hd : ∀ i j, r i ≠ s j)
    (I : Instrument (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)) (Fin m))
    (upd : Fin m → S → S) (E : Set.Icc (0 : Operator (tensorMemory (D ∘ s))) 1) :
    wp (Command.measureOnRegister D r I upd) (fun _ => orderedLiftEffect D s E) =
      fun _ => orderedLiftEffect D s E := by
  funext σ
  exact wp_measureOn_disjoint D (fun _ => r) (fun _ _ => I) upd σ r.injective s hd E

/-- A framed finite Kraus sum can be pulled through the weakest precondition of any command. -/
theorem wp_kraus {H : Qudit} {Cell ι : Type*} [Fintype ι] (p : Command S Cell H)
    (K : S → ι → Operator H) (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i ≤ 1)
    (hf : ∀ i, p.KrausFrame (fun σ => K σ i)) (B : ι → Assertion S H) :
    wp p (Assertion.kraus K hK B) = Assertion.kraus K hK (fun i => wp p (B i)) := by
  apply wp_eq_of_expectation
  intro x
  rw [Configuration.PostH_kraus _ K hK (fun i => (Configuration.frame_running _ _ _).2 (hf i)),
    x.ofReal_expectation_kraus]
  exact Finset.sum_congr rfl fun i _ => (expectation_wp p (B i) (x.krausMap (fun σ => K σ i))).symm

variable {p : Command S (Fin n) (tensorMemory D)} (s : Fin l ↪ Fin n)
variable (ha : p.AvoidsRegister D (fun _ => Set.range s))

include ha

/-- A program avoiding an ordered register frames each operator on that register. -/
theorem Command.AvoidsRegister.krausFrame_orderedLift
    (X : Operator (tensorMemory (D ∘ s))) : p.KrausFrame (fun _ => orderedLift D s X) := by
  apply Command.krausFrame_of_parameters D (fun _ => ()) (fun _ => Set.range s)
    (fun _ => orderedLift D s X) _ ha (p.preservesParameters_const ())
  intro _ k r hd Y
  exact commute_orderedLift D r s (fun i j h => hd i ⟨j, h.symm⟩) Y X

/-- A spectator effect is weighted by the actual termination effect, including blocked paths. -/
theorem wp_orderedLiftEffect (E : Set.Icc (0 : Operator (tensorMemory (D ∘ s))) 1) (σ : S) :
    let K := orderedLift D s E.val.sqrt
    (wp p (fun _ => orderedLiftEffect D s E) σ : Operator (tensorMemory D)) =
      K * (wp p Assertion.identity σ : Operator (tensorMemory D)) * K := by
  let K := orderedLift D s E.val.sqrt
  have hstar : star K = K := by
    change star (orderedLift D s E.val.sqrt) = _
    rw [← map_star]
    exact congrArg (orderedLift D s) (Operator.adjoint_sqrt E.val)
  have hsq : K * K = orderedLift D s E.val :=
    (map_mul (orderedLift D s) _ _).symm.trans (congrArg (orderedLift D s)
      (Operator.sqrt_mul_sqrt E.val (LinearMap.nonneg_iff_isPositive.mp E.property.1)))
  have hK (_ : S) : ∑ _ : Unit, K.adjoint ∘ₗ K ≤ 1 := by
    rw [Fintype.sum_unique]
    change star K * K ≤ 1
    rw [hstar, hsq]
    exact (orderedLiftEffect D s E).property.2
  have hidentity : Assertion.kraus (fun (_ : S) (_ : Unit) => K) hK
      (fun _ => Assertion.identity) = fun _ => orderedLiftEffect D s E := by
    funext τ
    apply Subtype.ext
    change (∑ _ : Unit, Superoperator.conjugate K.adjoint 1) = _
    rw [Fintype.sum_unique]
    change star K * 1 * star (star K) = _
    rw [mul_one, star_star, hstar]
    exact hsq
  have hw := wp_kraus p _ hK (fun (_ : Unit) => ha.krausFrame_orderedLift D s E.val.sqrt)
    (fun _ => Assertion.identity)
  rw [hidentity] at hw
  have hv := congrArg (fun A : Assertion S (tensorMemory D) => (A σ).val) hw
  change _ = ∑ _ : Unit, Superoperator.conjugate K.adjoint (wp p Assertion.identity σ) at hv
  rw [Fintype.sum_unique] at hv
  change _ = star K * (wp p Assertion.identity σ : Operator _) * star (star K) at hv
  simpa only [star_star, hstar] using hv

/-- A totally terminating program that avoids the spectator preserves its effects. -/
theorem wp_orderedLiftEffect_of_validTot_identity
    (ht : validTot Assertion.identity p Assertion.identity)
    (E : Set.Icc (0 : Operator (tensorMemory (D ∘ s))) 1) :
    wp p (fun _ => orderedLiftEffect D s E) = fun _ => orderedLiftEffect D s E := by
  funext σ
  apply Subtype.ext
  have h : (wp p Assertion.identity σ : Operator (tensorMemory D)) = 1 :=
    le_antisymm (wp p Assertion.identity σ).property.2 (validTot_iff_le_wp.mp ht σ)
  rw [wp_orderedLiftEffect D s ha E σ, h, mul_one, ← map_mul]
  exact congrArg (orderedLift D s)
    (Operator.sqrt_mul_sqrt E.val (LinearMap.nonneg_iff_isPositive.mp E.property.1))

end

end QuantumProgram
