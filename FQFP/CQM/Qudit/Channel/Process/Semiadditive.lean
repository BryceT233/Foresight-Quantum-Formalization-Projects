/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Process.Category
public import FQFP.CategoryTheory.Semiadditive.Basic

/-!
# Addition of completely positive processes

The hom-sets of `CPQudit` admit the finite sums used to forget measurement outcomes.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

namespace Qudit

noncomputable section

namespace CPMap

variable {H K : Qudit}

instance : Zero (CPMap H K) where
  zero := ⟨0, by
    rw [Superoperator.isCompletelyPositive_iff_choi_positive (stdOrthonormalBasis ℂ H.state),
      map_zero]
    exact LinearMap.isPositive_zero⟩

instance : Add (CPMap H K) where
  add f g := ⟨f.toSuperoperator + g.toSuperoperator, by
    let b := stdOrthonormalBasis ℂ H.state
    rw [Superoperator.isCompletelyPositive_iff_choi_positive b, map_add]
    exact (f.completelyPositive.choi_positive b).add (g.completelyPositive.choi_positive b)⟩

instance : SMul ℕ (CPMap H K) where
  smul n f := ⟨n • f.toSuperoperator, by
    simpa using Superoperator.IsCompletelyPositive.sum (Finset.univ : Finset (Fin n))
      (fun _ => f.toSuperoperator) (fun _ _ => f.completelyPositive)⟩

instance : AddCommMonoid (CPMap H K) :=
  Function.Injective.addCommMonoid toSuperoperator (fun _ _ => CPMap.ext) rfl
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Forgetting complete positivity preserves addition. -/
def toSuperoperatorHom : CPMap H K →+ Superoperator H K where
  toFun := toSuperoperator
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Forgetting complete positivity commutes with finite sums. -/
lemma toSuperoperator_sum {ι : Type*} (s : Finset ι) (f : ι → CPMap H K) :
    (∑ i ∈ s, f i).toSuperoperator = ∑ i ∈ s, (f i).toSuperoperator :=
  map_sum toSuperoperatorHom f s

end CPMap

instance : Semiadditive CPQudit where
  homMonoid _ _ := inferInstanceAs (AddCommMonoid (CPMap _ _))
  add_comp _ _ _ _ _ _ := CPMap.ext (LinearMap.comp_add _ _ _)
  comp_add _ _ _ _ _ _ := CPMap.ext (LinearMap.add_comp _ _ _)
  zero_comp _ _ _ _ := CPMap.ext (LinearMap.comp_zero _)
  comp_zero _ _ _ _ := CPMap.ext (LinearMap.zero_comp _)

end

end Qudit
