/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Logic.Source.Rules

/-!
# Hoare rules for decidable classical predicates

The command evaluates `decide (P σ)`. Its Hoare rules restrict the input assertion to
`P σ` in the true branch or loop body and to `¬ P σ` in the false branch or on loop exit.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Restrict the classical support of a source assertion while retaining its quantum effect. -/
def CQAssertion.restrict (A : CQAssertion Store H) (P : Store → Prop) : CQAssertion Store H :=
  { A with cls := fun σ => A.cls σ ∧ P σ }

variable (P : Store → Prop) [DecidablePred P] {p q : Command Store Cell H}

private theorem guard_decide_mask (A : Assertion Store H) :
    Assertion.guard (fun σ => decide (P σ)) (A.mask P) (A.mask fun σ => ¬ P σ) = A := by
  funext σ
  by_cases h : P σ <;> simp [Assertion.guard, Assertion.mask, h]

/-- Prove partial correctness on the two complementary restrictions of the precondition. -/
theorem DerivPar.cond_decide {A B : Assertion Store H}
    (hy : DerivPar (A.mask P) p B) (hn : DerivPar (A.mask fun σ => ¬ P σ) q B) :
    DerivPar A (.ite (fun σ => decide (P σ)) p q) B := by
  simpa only [guard_decide_mask] using DerivPar.cond (b := fun σ => decide (P σ)) hy hn

/-- Prove total correctness on the two complementary restrictions of the precondition. -/
theorem DerivTot.cond_decide {A B : Assertion Store H}
    (hy : DerivTot (A.mask P) p B) (hn : DerivTot (A.mask fun σ => ¬ P σ) q B) :
    DerivTot A (.ite (fun σ => decide (P σ)) p q) B := by
  simpa only [guard_decide_mask] using DerivTot.cond (b := fun σ => decide (P σ)) hy hn

/-- A guarded invariant holds on exit wherever the predicate is false. -/
theorem DerivPar.whileLoop_decide {J : Assertion Store H} (h : DerivPar (J.mask P) p J) :
    DerivPar J (.whileDo (fun σ => decide (P σ)) p) (J.mask fun σ => ¬ P σ) := by
  have rule := DerivPar.whileLoop (b := fun σ => decide (P σ)) (J := J) (p := p)
  simp only [Assertion.mand, Assertion.mandNot, decide_eq_true_eq, decide_eq_false_iff_not] at rule
  exact rule h

/-- A predicate-guarded loop terminates when every iteration strictly decreases its natural rank. -/
theorem DerivTot.whileLoop_decide {J : Assertion Store H} (t : Store → ℕ)
    (h : ∀ n, DerivTot ((J.mask P).mask fun σ => t σ = n) p (J.mask fun σ => t σ < n)) :
    DerivTot J (.whileDo (fun σ => decide (P σ)) p) (J.mask fun σ => ¬ P σ) := by
  have rule := DerivTot.whileLoop (b := fun σ => decide (P σ)) (J := J) (p := p) t
  simp only [Assertion.mand, Assertion.mandNot, decide_eq_true_eq, decide_eq_false_iff_not] at rule
  exact rule h

/-- Split the classical part of a partial source triple on a decidable predicate. -/
theorem SourceDerivPar.cond_decide {A B : CQAssertion Store H}
    (hy : SourceDerivPar (A.restrict P) p B) (hn : SourceDerivPar (A.restrict fun σ => ¬ P σ) q B) :
    SourceDerivPar A (.ite (fun σ => decide (P σ)) p q) B := by
  apply SourceDerivPar.cond
  · simpa only [CQAssertion.onBranch, decide_eq_true_eq, CQAssertion.restrict] using hy
  · simpa only [CQAssertion.onBranch, decide_eq_false_iff_not, CQAssertion.restrict] using hn

/-- Split the classical part of a total source triple on a decidable predicate. -/
theorem SourceDerivTot.cond_decide {A B : CQAssertion Store H}
    (hy : SourceDerivTot (A.restrict P) p B) (hn : SourceDerivTot (A.restrict fun σ => ¬ P σ) q B) :
    SourceDerivTot A (.ite (fun σ => decide (P σ)) p q) B := by
  apply SourceDerivTot.cond
  · simpa only [CQAssertion.onBranch, decide_eq_true_eq, CQAssertion.restrict] using hy
  · simpa only [CQAssertion.onBranch, decide_eq_false_iff_not, CQAssertion.restrict] using hn

/-- Preserve the source invariant on states satisfying the loop predicate. -/
theorem SourceDerivPar.whileLoop_decide {A : Assertion Store H} {φ : Store → Prop}
    (h : SourceDerivPar (.ofEffect A fun σ => φ σ ∧ P σ) p (.ofEffect A φ)) :
    SourceDerivPar (.ofEffect A φ) (.whileDo (fun σ => decide (P σ)) p)
      (.ofEffect A fun σ => φ σ ∧ ¬ P σ) := by
  have rule := SourceDerivPar.whileLoop (b := fun σ => decide (P σ)) (A := A) (φ := φ) (p := p)
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at rule
  exact rule h

/-- Preserve the source invariant and decrease a nonnegative integer rank on guarded inputs. -/
theorem SourceDerivTot.whileLoop_decide {A : Assertion Store H} {φ : Store → Prop}
    (t : Store → ℤ) (hb : ∀ σ, φ σ → 0 ≤ t σ)
    (hInv : SourceDerivTot (.ofEffect A fun σ => φ σ ∧ P σ) p (.ofEffect A φ))
    (hRank : ∀ z, SourceDerivTot (.ofEffect Assertion.identity fun σ => φ σ ∧ P σ ∧ t σ = z)
      p (.ofEffect Assertion.identity fun σ => t σ < z)) :
    SourceDerivTot (.ofEffect A φ) (.whileDo (fun σ => decide (P σ)) p)
      (.ofEffect A fun σ => φ σ ∧ ¬ P σ) := by
  have rule := SourceDerivTot.whileLoop (b := fun σ => decide (P σ)) (A := A) (p := p) t hb
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at rule
  exact rule hInv hRank

end QuantumProgram
