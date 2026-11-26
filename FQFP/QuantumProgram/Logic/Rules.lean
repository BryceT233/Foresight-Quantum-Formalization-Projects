/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the partial and total derivation systems.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Rules.lean
Qhl/Logic/Source/Rules.lean (evaluated Kraus accumulation for total derivations)

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Logic.PrimitiveRules
public import FQFP.QuantumProgram.Logic.Assertion.Kraus

/-!
# QHL⁺ derivations of partial and total correctness

The rules follow the two systems in `Qhl/Logic/Rules.lean` for evaluated whole-memory commands.
-/

@[expose] public section

open Qudit
open scoped NNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Select the assertion at a store using the conditional's classical guard. -/
def Assertion.guard (b : Store → Bool) (A₁ A₀ : Assertion Store H) : Assertion Store H :=
  fun σ => if b σ then A₁ σ else A₀ σ

/-- Partial-correctness derivations for the classical–quantum command language. -/
inductive DerivPar : Assertion Store H → Command Store Cell H → Assertion Store H → Prop
  /-- Skip preserves the assertion. -/
  | skip (A : Assertion Store H) : DerivPar A .skip A
  /-- Substitute the store update into the postcondition. -/
  | assign (f : Store → Store) (A : Assertion Store H) : DerivPar (A ∘ f) (.assign f) A
  /-- Pull back through an evaluated channel, including initialization channels. -/
  | channel (f : Store → QuantumChannel H H) (A : Assertion Store H) :
      DerivPar (A.channelPre f) (.channel f) A
  /-- Pull back through the unitary on a valid register. -/
  | unitary {k : ℕ} (r : Store → Fin k → Cell)
      (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (A : Assertion Store H) :
      DerivPar (A.unitaryPre r U) (.unitary r U) A
  /-- Sum the pulled-back effects after the measurement's write-back. -/
  | measure {k m : ℕ} (r : Store → Fin k → Cell)
      (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
      (A : Assertion Store H) : DerivPar (A.measurePre r I upd) (.measure r I upd) A
  /-- Compose two derivations at an intermediate assertion. -/
  | seq {A B C : Assertion Store H} {p q : Command Store Cell H} :
      DerivPar A p B → DerivPar B q C → DerivPar A (p.seq q) C
  /-- Choose the precondition of the branch selected by the guard. -/
  | cond {b : Store → Bool} {A₁ A₀ B : Assertion Store H} {p q : Command Store Cell H} :
      DerivPar A₁ p B → DerivPar A₀ q B → DerivPar (Assertion.guard b A₁ A₀) (.ite b p q) B
  /-- A guarded invariant establishes partial correctness on exit. -/
  | whileLoop {b : Store → Bool} {J : Assertion Store H} {p : Command Store Cell H} :
      DerivPar (J.mand b) p J → DerivPar J (.whileDo b p) (J.mandNot b)
  /-- Strengthen the precondition and weaken the postcondition in pointwise effect order. -/
  | conseq {A A' B' B : Assertion Store H} {p : Command Store Cell H} :
      A ≤ A' → DerivPar A' p B' → B' ≤ B → DerivPar A p B

/-- Total-correctness derivations for the classical–quantum command language. -/
inductive DerivTot : Assertion Store H → Command Store Cell H → Assertion Store H → Prop
  /-- Skip preserves the assertion. -/
  | skip (A : Assertion Store H) : DerivTot A .skip A
  /-- Substitute the store update into the postcondition. -/
  | assign (f : Store → Store) (A : Assertion Store H) : DerivTot (A ∘ f) (.assign f) A
  /-- Pull back through an evaluated channel, including initialization channels. -/
  | channel (f : Store → QuantumChannel H H) (A : Assertion Store H) :
      DerivTot (A.channelPre f) (.channel f) A
  /-- Pull back through the unitary on a valid register. -/
  | unitary {k : ℕ} (r : Store → Fin k → Cell)
      (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (A : Assertion Store H) :
      DerivTot (A.unitaryPre r U) (.unitary r U) A
  /-- Sum the pulled-back effects after the measurement's write-back. -/
  | measure {k m : ℕ} (r : Store → Fin k → Cell)
      (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
      (A : Assertion Store H) : DerivTot (A.measurePre r I upd) (.measure r I upd) A
  /-- Compose two derivations at an intermediate assertion. -/
  | seq {A B C : Assertion Store H} {p q : Command Store Cell H} :
      DerivTot A p B → DerivTot B q C → DerivTot A (p.seq q) C
  /-- Choose the precondition of the branch selected by the guard. -/
  | cond {b : Store → Bool} {A₁ A₀ B : Assertion Store H} {p q : Command Store Cell H} :
      DerivTot A₁ p B → DerivTot A₀ q B → DerivTot (Assertion.guard b A₁ A₀) (.ite b p q) B
  /-- Combined body premise with a strictly decreasing natural rank. -/
  | whileLoop {b : Store → Bool} {J : Assertion Store H} {p : Command Store Cell H}
      (t : Store → ℕ) :
      (∀ n, DerivTot ((J.mand b).mask fun σ => t σ = n) p (J.mask fun σ => t σ < n)) →
      DerivTot J (.whileDo b p) (J.mandNot b)
  /-- Integer-rank source rule with independent invariant and identity-effect decrease premises. -/
  | whileLoopSource {b : Store → Bool} {A : Assertion Store H} {φ : Store → Prop}
      {p : Command Store Cell H} (t : Store → ℤ) (hbound : ∀ σ, φ σ → 0 ≤ t σ) :
      DerivTot ((A.mask φ).mand b) p (A.mask φ) →
      (∀ z : ℤ, DerivTot (Assertion.identity.mask fun σ => φ σ ∧ b σ = true ∧ t σ = z)
        p (Assertion.identity.mask fun σ => t σ < z)) →
      DerivTot (A.mask φ) (.whileDo b p) ((A.mask φ).mandNot b)
  /-- Apply a common finite subprobability combination to both sides of the child derivations. -/
  | convex {ι : Type} [Fintype ι] (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1)
      {A B : ι → Assertion Store H} {p : Command Store Cell H} :
      (∀ i, DerivTot (A i) p (B i)) → DerivTot (Assertion.convex w hw A) p (Assertion.convex w hw B)
  /-- Pull the branches of a framed subnormalized Kraus family through a total derivation. -/
  | kraus {ι : Type} [Fintype ι] (K : Store → ι → Operator H)
      (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i ≤ 1) {p : Command Store Cell H}
      (hp : ∀ i, p.KrausFrame (fun σ => K σ i)) {A B : ι → Assertion Store H} :
      (∀ i, DerivTot (A i) p (B i)) → DerivTot (Assertion.kraus K hK A) p (Assertion.kraus K hK B)
  /-- Strengthen the precondition and weaken the postcondition in pointwise effect order. -/
  | conseq {A A' B' B : Assertion Store H} {p : Command Store Cell H} :
      A ≤ A' → DerivTot A' p B' → B' ≤ B → DerivTot A p B

/-- The zero precondition is derivable for every command in the total calculus. -/
theorem DerivTot.zeroPre (p : Command Store Cell H) (B : Assertion Store H) :
    DerivTot Assertion.zero p B := by
  have h := DerivTot.convex (p := p) (fun i : Fin 0 => i.elim0) (by simp)
    (A := fun i : Fin 0 => i.elim0) (B := fun i : Fin 0 => i.elim0) (fun i => i.elim0)
  simp only [Assertion.convex_empty (ι := Fin 0)] at h
  exact .conseq le_rfl h B.zero_le

end QuantumProgram
