/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/ClassicalInfo/Channel.lean: discrete memoryless channels and the product
distribution on fixed-length words and lists.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Discrete memoryless channels

A row of the channel gives the output probabilities for one input symbol. Conditional on
the input word, the output symbols are independent. A word of length zero has one possible
output, the empty word.
-/

@[expose] public noncomputable section

open Convexity

namespace Qudit

/-- A discrete memoryless channel with finite output alphabet. -/
structure MemorylessChannel (I O : Type*) [Fintype O] where
  /-- Distribution of the output symbol conditional on one input symbol. -/
  row : I → StdSimplex ℝ O

namespace MemorylessChannel

variable {I O : Type*} [Fintype O]

/-- Transmit a word through independent uses of the channel. -/
def onWord (C : MemorylessChannel I O) {n : ℕ} (x : Fin n → I) :
    StdSimplex ℝ (Fin n → O) where
  weights := Finsupp.equivFunOnFinite.symm (fun y => ∏ k, (C.row (x k)).weights (y k))
  nonneg y := by
    change 0 ≤ ∏ k, (C.row (x k)).weights (y k)
    exact Finset.prod_nonneg fun k _ => (C.row (x k)).weights_nonneg (y k)
  total := by
    classical
    simpa [Finsupp.sum_fintype] using
      Finset.sum_prod_piFinset Finset.univ (fun k o => (C.row (x k)).weights o)

/-- The conditional probability of an output word factors over its positions. -/
@[simp]
lemma weights_onWord (C : MemorylessChannel I O) {n : ℕ} (x : Fin n → I) (y : Fin n → O) :
    (C.onWord x).weights y = ∏ k, (C.row (x k)).weights (y k) := rfl

/-- Transmit a list, retaining its length in the type of the output word. -/
def onList (C : MemorylessChannel I O) (xs : List I) : StdSimplex ℝ (Fin xs.length → O) :=
  C.onWord xs.get

/-- A deterministic channel puts all its probability on the specified output symbol. -/
def ofFunction (f : I → O) : MemorylessChannel I O := ⟨fun i => .single (f i)⟩

/-- Deterministic symbol transmission applies the function at every position. -/
@[simp]
lemma onWord_ofFunction (f : I → O) {n : ℕ} (x : Fin n → I) :
    (ofFunction f).onWord x = .single (f ∘ x) := by
  classical
  ext y
  simp [ofFunction, StdSimplex.weights_single, Finsupp.single_apply,
    Fintype.prod_ite_zero, funext_iff, Function.comp_def]

end MemorylessChannel

end Qudit
