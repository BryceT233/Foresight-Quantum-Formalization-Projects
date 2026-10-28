/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.IteratedCommutator

/-!
# The eight four-fold commutators used in BCH estimates

The Childs family is indexed by `Fin 8`. Its definition and eight evaluation
lemmas require only a ring with its associative Lie bracket. The weighted norm
sums are developed separately in `Analysis.Normed.Algebra.BCH.CommutatorWeights`.
-/

@[expose] public section

namespace FQFP.BCH

attribute [local instance] LieRing.ofAssociativeRing

section Algebra

variable {𝔸 : Type*} [Ring 𝔸]

/-! ### The eight commutators -/

/-- The eight Childs four-fold commutators, as a `Fin 8`-indexed family. Branch `i` is the
concrete bracket expression `[X₁,[X₂,[X₃,[B,A]]]]`; see `childsComm_zero` … `childsComm_seven`
for the eight forms. -/
def childsComm (A B : 𝔸) : Fin 8 → 𝔸
  | 0 => ⁅A, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 1 => ⁅A, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 2 => ⁅A, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 3 => ⁅A, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 4 => ⁅B, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 5 => ⁅B, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 6 => ⁅B, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆
  | _ => ⁅B, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆

/-- `childsComm` is a pattern match on `Fin 8`, so `unfold childsComm` leaves a stuck `match` on
a literal index rather than reducing to the bracket expression. These lemmas discharge it. They
are marked `@[simp]` so that a downstream goal mentioning `‖childsComm A B i‖` can be normalized
to the bracket form; the match is stuck for a symbolic `i`, so the rules cannot loop. -/
@[simp] lemma childsComm_zero (A B : 𝔸) : childsComm A B 0 = ⁅A, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_one (A B : 𝔸) : childsComm A B 1 = ⁅A, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_two (A B : 𝔸) : childsComm A B 2 = ⁅A, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_three (A B : 𝔸) : childsComm A B 3 = ⁅A, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_four (A B : 𝔸) : childsComm A B 4 = ⁅B, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_five (A B : 𝔸) : childsComm A B 5 = ⁅B, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_six (A B : 𝔸) : childsComm A B 6 = ⁅B, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_seven (A B : 𝔸) : childsComm A B 7 = ⁅B, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl

end Algebra

end FQFP.BCH
