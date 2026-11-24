/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/RegisterKraus.lean (registerKrausOps, registerKraus, registerSingletonOps,
registerKrausOne, normalization, the distinct-operand domain and krausFrame_register)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.RegisterFrame
public import FQFP.QuantumProgram.Logic.SourceDomain
import FQFP.CQM.Qudit.State.OperatorNorm

/-!
# Source Kraus predicates on evaluated register expressions

An aliased tuple is outside the quantum operand's domain. An identity/zero family makes the
Kraus operators total and normalized at those stores as well. Distinct tuples use their actual
ordered lift. Outcome types with a fallback branch are nonempty.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

noncomputable section

variable {S ι : Type*} {n k l : ℕ} (D : Fin n → Qudit) (r : S → Fin k → Fin n)
    (M : (σ : S) → ι → Operator (tensorMemory (D ∘ r σ)))

/-- Extend a family on a raw tuple by a normalized identity/zero family on aliased tuples. -/
def registerKrausOps [Nonempty ι] (σ : S) (i : ι) : Operator (tensorMemory D) := by
  classical
  exact if hi : Function.Injective (r σ) then orderedLift D ⟨r σ, hi⟩ (M σ i)
    else if i = Classical.choice (inferInstance : Nonempty ι) then 1 else 0

/-- The register family is normalized at every store, even outside the source domain. -/
theorem registerKrausOps_complete [Fintype ι] [Nonempty ι]
    (hc : ∀ σ, Function.Injective (r σ) → ∑ i, (M σ i).adjoint ∘ₗ M σ i = 1) (σ : S) :
    ∑ i, (registerKrausOps D r M σ i).adjoint ∘ₗ registerKrausOps D r M σ i = 1 := by
  classical
  by_cases hi : Function.Injective (r σ)
  · simpa only [registerKrausOps, dite_eq_left hi] using
      orderedLift_complete D ⟨r σ, hi⟩ (M σ) (hc σ hi)
  · simp only [registerKrausOps, dite_eq_right hi]
    rw [Finset.sum_eq_single (Classical.choice (inferInstance : Nonempty ι))]
    · simp [Module.End.one_eq_id]
    · intro j _ hj
      simp [hj]
    · simp

/-- A source Kraus combination retains distinctness and each child operand's domain. -/
def SourceEffect.registerKraus [Fintype ι] [Nonempty ι]
    (hc : ∀ σ, Function.Injective (r σ) → ∑ i, (M σ i).adjoint ∘ₗ M σ i = 1)
    (A : ι → SourceEffect S (tensorMemory D)) : SourceEffect S (tensorMemory D) :=
  (kraus (registerKrausOps D r M) (fun σ => (registerKrausOps_complete D r M hc σ).le) A).onDomain
    (fun σ => Function.Injective (r σ))

/-- Even a child with zero Kraus operator contributes its domain. -/
theorem SourceEffect.registerKraus_defined [Fintype ι] [Nonempty ι]
    (hc : ∀ σ, Function.Injective (r σ) → ∑ i, (M σ i).adjoint ∘ₗ M σ i = 1)
    (A : ι → SourceEffect S (tensorMemory D)) (σ : S) :
    (registerKraus D r M hc A).defined σ ↔ Function.Injective (r σ) ∧ ∀ i, (A i).defined σ :=
  and_comm

/-- The raw tuple's total Kraus extension commutes with all actions on disjoint sites.
Distinctness is required only at stores where the source operand is interpreted. -/
theorem commute_registerKrausOps [Nonempty ι] (p : Fin l ↪ Fin n) (σ : S) (i : ι)
    (hd : Function.Injective (r σ) → ∀ j t, p j ≠ r σ t) (X : Operator (tensorMemory (D ∘ p))) :
    Commute (orderedLift D p X) (registerKrausOps D r M σ i) := by
  classical
  by_cases hi : Function.Injective (r σ)
  · simpa only [registerKrausOps, dite_eq_left hi] using
      commute_orderedLift D p ⟨r σ, hi⟩ (hd hi) X (M σ i)
  · simp only [registerKrausOps, dite_eq_right hi]
    split <;> simp

variable (J : (σ : S) → Operator (tensorMemory (D ∘ r σ)))

/-- A program avoiding the raw tuple and preserving its parameters frames every Kraus branch,
including at stores where the tuple contains repeated sites. -/
theorem Command.krausFrame_register {Store : Type*} [Nonempty ι]
    {p : Command Store (Fin n) (tensorMemory D)} (e : Store → S)
    (hq : p.AvoidsRegister D (fun σ => Set.range (r (e σ)))) (hp : p.PreservesParameters e)
    (i : ι) : p.KrausFrame (fun σ => registerKrausOps D r M (e σ) i) := by
  apply krausFrame_of_parameters D e (fun a => Set.range (r a))
    (fun a => registerKrausOps D r M a i) _ hq hp
  intro a k q hd X
  exact commute_registerKrausOps D r M q a i (fun _ j t he => hd j ⟨t, he.symm⟩) X

/-- The singleton modifier uses the identity as its total extension on repeated operands. -/
def registerSingletonOp (σ : S) : Operator (tensorMemory D) := by
  classical
  exact if hi : Function.Injective (r σ) then orderedLift D ⟨r σ, hi⟩ (J σ) else 1

/-- Ordered lifting and the identity fallback both preserve the singleton contraction bound. -/
theorem registerSingletonOp_contraction
    (hc : ∀ σ, Function.Injective (r σ) → (J σ).adjoint ∘ₗ J σ ≤ 1) (σ : S) :
    (registerSingletonOp D r J σ).adjoint ∘ₗ registerSingletonOp D r J σ ≤ 1 := by
  classical
  by_cases hi : Function.Injective (r σ)
  · let F := orderedLift D ⟨r σ, hi⟩
    have he : registerSingletonOp D r J σ = F (J σ) := dite_eq_left hi
    rw [he]
    change star (F (J σ)) * F (J σ) ≤ 1
    have h : star (J σ) * J σ ≤ 1 := hc σ hi
    simpa only [map_mul, map_star, map_one] using (OrderHomClass.mono F h)
  · simp [registerSingletonOp, hi, Module.End.one_eq_id]

/-- Attach the distinct-register domain to a source singleton modifier. -/
def SourceEffect.registerKrausOne
    (hc : ∀ σ, Function.Injective (r σ) → (J σ).adjoint ∘ₗ J σ ≤ 1)
    (B : SourceEffect S (tensorMemory D)) : SourceEffect S (tensorMemory D) :=
  (krausOne (registerSingletonOp D r J) (registerSingletonOp_contraction D r J hc) B).onDomain
    (fun σ => Function.Injective (r σ))

/-- The singleton is defined exactly at distinct tuples where its child is defined. -/
theorem SourceEffect.registerKrausOne_defined
    (hc : ∀ σ, Function.Injective (r σ) → (J σ).adjoint ∘ₗ J σ ≤ 1)
    (B : SourceEffect S (tensorMemory D)) (σ : S) :
    (registerKrausOne D r J hc B).defined σ ↔ Function.Injective (r σ) ∧ B.defined σ :=
  and_comm

end

end QuantumProgram
