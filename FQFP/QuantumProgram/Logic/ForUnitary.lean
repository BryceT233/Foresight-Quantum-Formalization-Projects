/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the rule for applying local gates at distinct sites.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/ForRule.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.For
public import FQFP.QuantumProgram.Logic.SourceUnitary
public import FQFP.QuantumProgram.TensorRegister

/-!
# Finite iteration of disjoint one-site unitaries

Each site may have a different state space and a different gate. On a product input,
a duplicate-free list of gates transforms each listed factor once and fixes the others.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit

namespace QuantumProgram

variable {Store : Type*} {n : ℕ} {D : Fin n → Qudit}

/-- Apply a unitary to a single site of a heterogeneous tensor register. -/
noncomputable def Command.unitaryAt (i : Fin n) (U : D i ⟶ D i) [IsUnitary U] :
    Command Store (Fin n) (tensorMemory D) :=
  .unitary (fun _ (_ : Fin 1) => i) (fun _ _ => .gateHom (Register.site D i) U)

/-- A gate at one site maps the corresponding factor of a product-state assertion. -/
theorem DerivTot.unitaryAt_productState (i : Fin n) (U : D i ⟶ D i) [IsUnitary U]
    (v : (j : Fin n) → UnitState (D j)) :
    DerivTot (Store := Store) (Assertion.pure (registerProductState D v)) (.unitaryAt i U)
      (Assertion.pure (registerProductState D (Function.update v i (UnitState.map U (v i))))) := by
  have h := SourceDerivTot.unitary_pure (fun (_ : Store) (_ : Fin 1) => i)
    (fun _ _ => UnitaryProgram.gateHom (Register.site D i) U)
    (φ := fun _ => True) (fun _ => registerProductState D v)
    (fun _ => registerProductState D (Function.update v i (UnitState.map U (v i))))
    (fun _ _ => Function.injective_of_subsingleton _)
    (fun _ _ => Register.liftHom_site_productState D i U v)
  simpa only [CQAssertion.toAssn_ofEffect_true, Command.unitaryAt] using h.toDerivTot

variable (U : (i : Fin n) → D i ⟶ D i) [∀ i, IsUnitary (U i)]

/-- Map the local factors at the listed sites, retaining the input factors off the list. -/
noncomputable def applyAtSites (l : List (Fin n)) (v : (i : Fin n) → UnitState (D i))
    (i : Fin n) : UnitState (D i) :=
  if i ∈ l then UnitState.map (U i) (v i) else v i

/-- No local factor changes when the list is empty. -/
theorem applyAtSites_nil (v : (i : Fin n) → UnitState (D i)) : applyAtSites U [] v = v :=
  funext fun i => ite_eq_right (List.not_mem_nil (a := i))

/-- Updating a fresh head and then applying the tail gives the transformation on the cons list. -/
theorem applyAtSites_cons {a : Fin n} {l : List (Fin n)} (ha : a ∉ l)
    (v : (i : Fin n) → UnitState (D i)) :
    applyAtSites U l (Function.update v a (UnitState.map (U a) (v a))) =
      applyAtSites U (a :: l) v := by
  funext i
  by_cases hi : i = a
  · subst i
    simp [applyAtSites, ha]
  · simp [applyAtSites, hi]

/-- Full coverage applies the specified unitary at every site. -/
theorem applyAtSites_finRange (v : (i : Fin n) → UnitState (D i)) :
    applyAtSites U (List.finRange n) v = fun i => UnitState.map (U i) (v i) := by
  funext i
  simp [applyAtSites]

/-- The list program on distinct sites maps each listed factor exactly once. -/
theorem DerivTot.forList_unitaryAt (l : List (Fin n)) (hl : l.Nodup)
    (v : (i : Fin n) → UnitState (D i)) :
    DerivTot (Store := Store) (Assertion.pure (registerProductState D v))
      (.forList l fun i => .unitaryAt i (U i))
      (Assertion.pure (registerProductState D (applyAtSites U l v))) := by
  induction l generalizing v with
  | nil =>
    rw [applyAtSites_nil]
    exact .skip _
  | cons a l ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hl
    rw [← applyAtSites_cons U ha v]
    exact .seq (DerivTot.unitaryAt_productState a (U a) v) (ih ht _)

end QuantumProgram
