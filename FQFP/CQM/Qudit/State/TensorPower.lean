/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/FreeState.lean: tensor powers of states and their product law.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.TensorPower

/-!
# Independent states on tensor powers

The register index counts the sites following the first. The append map concatenates two
consecutive nonempty blocks, preserving their order.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit

/-- Reassociate two consecutive blocks into a single right-associated register. -/
def tensorPowerAppend (H : Qudit) : (a b : ℕ) →
    tensorPower H a ⊗ tensorPower H b ⟶ tensorPower H (b + a + 1)
  | 0, b => 𝟙 (H ⊗ tensorPower H b)
  | a + 1, b => (α_ H (tensorPower H a) (tensorPower H b)).hom ≫
      (𝟙 H ⊗ₘ tensorPowerAppend H a b)

instance (H : Qudit) (a b : ℕ) : IsUnitary (tensorPowerAppend H a b) := by
  induction a with
  | zero =>
    change IsUnitary (𝟙 (H ⊗ tensorPower H b))
    infer_instance
  | succ a ih =>
    have : IsUnitary (tensorPowerAppend H a b) := ih
    change IsUnitary ((α_ H (tensorPower H a) (tensorPower H b)).hom ≫
      (𝟙 H ⊗ₘ tensorPowerAppend H a b))
    infer_instance

namespace Density

variable {H K L M : Qudit}

/-- Isometric evolution of a product state acts independently on its two factors. -/
lemma map_tensor (ρ : Density H) (σ : Density K) (f : H ⟶ L) (g : K ⟶ M)
    [IsIsometry f] [IsIsometry g] :
    (ρ.tensor σ).map (f ⊗ₘ g) = (ρ.map f).tensor (σ.map g) := by
  apply Density.ext
  change Superoperator.conjugate (f ⊗ₘ g).hom (Operator.tensor ρ.op σ.op) = _
  rw [hom_tensorHom, Superoperator.conjugate_tensor, Superoperator.tensor_apply]
  rfl

/-- Reassociation preserves the factors of a product state. -/
lemma map_associator_tensor (ρ : Density H) (σ : Density K) (τ : Density L) :
    ((ρ.tensor σ).tensor τ).map (α_ H K L).hom = ρ.tensor (σ.tensor τ) := by
  apply Density.ext
  change Superoperator.conjugate (α_ H K L).hom.hom (Operator.tensor
    (Operator.tensor ρ.op σ.op) τ.op) = _
  rw [hom_hom_associator, ← TensorProduct.toLinearEquiv_assocIsometry]
  exact (DFunLike.congr_fun (Superoperator.relabel_eq_conjugate _).symm _).trans
    (Superoperator.relabel_assoc_tensor _ _ _)

/-- The independent input on a block of `n + 1` sites. -/
def tensorPower (ρ : Density H) : (n : ℕ) → Density (Qudit.tensorPower H n)
  | 0 => ρ
  | n + 1 => ρ.tensor (ρ.tensorPower n)

private lemma map_identity (ρ : Density H) : ρ.map (𝟙 H) = ρ := by
  apply Density.ext
  simp [hom_id]

private lemma map_composition (f : H ⟶ K) (g : K ⟶ L) [IsIsometry f] [IsIsometry g]
    (ρ : Density H) : ρ.map (f ≫ g) = (ρ.map f).map g := by
  apply Density.ext
  exact DFunLike.congr_fun (Superoperator.conjugate_comp f.hom g.hom) ρ.op

/-- Appending adjacent blocks of an independent state gives the larger independent state. -/
lemma tensorPower_append (ρ : Density H) (a b : ℕ) :
    ((ρ.tensorPower a).tensor (ρ.tensorPower b)).map (tensorPowerAppend H a b) =
      ρ.tensorPower (b + a + 1) := by
  induction a with
  | zero => exact map_identity (ρ.tensor (ρ.tensorPower b))
  | succ a ih =>
    change (((ρ.tensor (ρ.tensorPower a)).tensor (ρ.tensorPower b)).map
      ((α_ H (Qudit.tensorPower H a) (Qudit.tensorPower H b)).hom ≫
        (𝟙 H ⊗ₘ tensorPowerAppend H a b))) = ρ.tensor (ρ.tensorPower (b + a + 1))
    rw [map_composition, map_associator_tensor, map_tensor, map_identity, ih]

end Density

end Qudit
