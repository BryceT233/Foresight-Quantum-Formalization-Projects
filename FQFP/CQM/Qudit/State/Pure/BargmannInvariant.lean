/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/

/-
Physlib reference for the three-state Bargmann invariant and phase.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Pure/BargmannInvariant.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Density
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Three-state Bargmann invariant

The cyclic product of three transition amplitudes is the trace of the ordered product
of the three pure density operators. It depends only on their rays. Its principal argument
is the Bargmann phase, with `Complex.arg 0 = 0` when two adjacent states are orthogonal.
This gives the invariant and phase of physlib's `QuantumInfo.States.Pure.BargmannInvariant`
on qudit unit states.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.DaggerCategory

namespace Qudit.UnitState

variable {H K : Qudit}

/-- The cyclic product of the transition amplitudes around three unit states. -/
def bargmannInvariantThree (u v w : UnitState H) : ℂ :=
  inner ℂ u.val v.val * inner ℂ v.val w.val * inner ℂ w.val u.val

/-- The principal argument of the three-state Bargmann invariant. -/
def bargmannPhaseThree (u v w : UnitState H) : ℝ :=
  (bargmannInvariantThree u v w).arg

/-- The ordered product of the three pure projectors has trace equal to the invariant. -/
theorem bargmannInvariantThree_eq_trace (u v w : UnitState H) :
    bargmannInvariantThree u v w =
      ((Density.pure u).op * (Density.pure v).op * (Density.pure w).op).trace := by
  rw [Density.op_pure w, Operator.trace_mul_outer, mul_apply_eq_comp, Density.pure_apply,
    Density.pure_apply, inner_smul_right, inner_smul_right]
  unfold bargmannInvariantThree
  ac_rfl

/-- Independent changes of phase at the vertices preserve the invariant. -/
theorem bargmannInvariantThree_phase (u v w : UnitState H) (a b c : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    bargmannInvariantThree (u.phase a ha) (v.phase b hb) (w.phase c hc) =
      bargmannInvariantThree u v w := by
  simp only [bargmannInvariantThree_eq_trace, Density.pure_phase]

/-- Simultaneous isometric evolution preserves the invariant, including under embeddings. -/
theorem bargmannInvariantThree_map (f : H ⟶ K) [IsIsometry f] (u v w : UnitState H) :
    bargmannInvariantThree (u.map f) (v.map f) (w.map f) = bargmannInvariantThree u v w := by
  simp only [bargmannInvariantThree, coe_map, inner_map_map_of_isIsometry]

/-- A single ray represented by the same unit vector at each vertex gives invariant one. -/
lemma bargmannInvariantThree_self (u : UnitState H) : bargmannInvariantThree u u u = 1 := by
  simp only [bargmannInvariantThree, u.inner_self, one_mul]

/-- Traversing the same vertex three times gives phase zero. -/
lemma bargmannPhaseThree_self (u : UnitState H) : bargmannPhaseThree u u u = 0 := by
  rw [bargmannPhaseThree, bargmannInvariantThree_self, Complex.arg_one]

/-- Choosing the next vertex as the starting point preserves the invariant. -/
lemma bargmannInvariantThree_cyclic (u v w : UnitState H) :
    bargmannInvariantThree v w u = bargmannInvariantThree u v w := by
  unfold bargmannInvariantThree
  ac_rfl

/-- The principal phase is invariant under cyclic permutation. -/
lemma bargmannPhaseThree_cyclic (u v w : UnitState H) :
    bargmannPhaseThree v w u = bargmannPhaseThree u v w :=
  congrArg Complex.arg (bargmannInvariantThree_cyclic u v w)

/-- Reversing orientation conjugates the invariant. -/
lemma bargmannInvariantThree_reverse (u v w : UnitState H) :
    bargmannInvariantThree w v u = starRingEnd ℂ (bargmannInvariantThree u v w) := by
  simp only [bargmannInvariantThree, map_mul, inner_conj_symm]
  ac_rfl

/-- Reversing orientation negates the phase modulo two pi. -/
lemma bargmannPhaseThree_reverse (u v w : UnitState H) :
    (bargmannPhaseThree w v u : Real.Angle) = -(bargmannPhaseThree u v w : Real.Angle) := by
  rw [bargmannPhaseThree, bargmannInvariantThree_reverse]
  exact Complex.arg_conj_coe_angle _

/-- The modulus of the invariant is bounded by one. -/
lemma norm_bargmannInvariantThree_le_one (u v w : UnitState H) :
    ‖bargmannInvariantThree u v w‖ ≤ 1 := by
  have h (x y : UnitState H) : ‖inner ℂ x.val y.val‖ ≤ 1 := by
    simpa only [x.norm_eq_one, y.norm_eq_one, one_mul] using norm_inner_le_norm (𝕜 := ℂ) x.val y.val
  rw [bargmannInvariantThree, norm_mul, norm_mul]
  exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (h w u)).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (h v w)).trans (h u v))

end Qudit.UnitState
