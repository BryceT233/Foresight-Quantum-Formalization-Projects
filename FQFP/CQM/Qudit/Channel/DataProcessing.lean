/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Category.DataProcessing
public import FQFP.CQM.Qudit.Channel.Process.Causal

/-!
# Data processing by dilation

The state functor sends a deterministic channel to its action on densities. By
Stinespring dilation it suffices to check a data-processing inequality on isometries
and on discarding an environment.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.CausalQudit

/-- The action of deterministic processes on density states. -/
noncomputable def densityFunctor : CausalQudit ⥤ Type where
  obj X := Density X.toQudit
  map f := ↾f.map
  map_id _ := ConcreteCategory.hom_ext _ _ QuantumChannel.map_id
  map_comp f g := ConcreteCategory.hom_ext _ _ (QuantumChannel.map_comp g f)

/-- Isometric evolution and right partial trace suffice for data processing. -/
theorem satisfiesDataProcessing_of_dilation {R : Type*} [Preorder R]
    (q : ∀ {H : Qudit}, Density H → Density H → R)
    (hi : ∀ {H K : Qudit} (V : H ⟶ K) [IsIsometry V] (ρ σ : Density H),
      q (ρ.map V) (σ.map V) ≤ q ρ σ)
    (ht : ∀ {H E : Qudit} (ρ σ : Density (H ⊗ E)),
      q ρ.partialTraceRight σ.partialTraceRight ≤ q ρ σ) :
    CQM.SatisfiesDataProcessing densityFunctor (fun _ ρ σ => q ρ σ) := by
  intro X Y f ρ σ
  obtain ⟨n, V, hV, hf⟩ := f.exists_dilation_map
  change q (f.map ρ) (f.map σ) ≤ q ρ σ
  rw [hf ρ, hf σ]
  exact (ht _ _).trans (hi V ρ σ)

end Qudit.CausalQudit
