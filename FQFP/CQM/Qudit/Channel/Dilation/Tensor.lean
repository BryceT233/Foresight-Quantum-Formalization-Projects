/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Dilation.Complementary
public import FQFP.CQM.Qudit.Channel.Capacity

/-!
# Parallel Stinespring dilations

Grouping receiver factors and environment factors separately gives an explicit dilation of a
block channel. Its complementary channel acts independently on the copies.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DaggerCategory SemiCartesianMonoidalCategory

namespace Qudit.QuantumChannel.Dilation

variable {A B E A' B' E' : Qudit} {Φ : QuantumChannel A B} {Ψ : QuantumChannel A' B'}

instance (B E B' E' : Qudit) : IsIsometry (tensorμ B E B' E') := by
  simp only [tensorμ, ← id_tensorHom, ← tensorHom_id]
  infer_instance

private lemma asHom_ofIsometry_tensorμ (B E B' E' : Qudit) :
    (ofIsometry (tensorμ B E B' E')).asHom =
      tensorμ (⟨B⟩ : CausalQudit) ⟨E⟩ ⟨B'⟩ ⟨E'⟩ := by
  simp only [tensorμ, ← id_tensorHom, ← tensorHom_id, ofIsometry_comp, ofIsometry_tensor,
    ofIsometry_id]
  have hi (X Y Z : Qudit) :
      ofIsometry (α_ X Y Z).inv = ofIsometry (α_ X Y Z).hom† := by
    apply QuantumChannel.ext
    exact congrArg (fun f => Superoperator.conjugate (Qudit.Hom.hom f))
      (IsUnitary.dagger_hom_eq_inv (α_ X Y Z)).symm
  rw [hi, hi]
  rfl

private lemma tensor_marginals {C : Type*} [Category* C] [SemiCartesianMonoidalCategory C]
    [BraidedCategory C] {A B E A' B' E' : C} {j : A ⟶ B ⊗ E} {j' : A' ⟶ B' ⊗ E'}
    {f : A ⟶ B} {g : A ⟶ E} {f' : A' ⟶ B'} {g' : A' ⟶ E'}
    (h : CQM.HasMarginals j f g) (h' : CQM.HasMarginals j' f' g') :
    CQM.HasMarginals ((j ⊗ₘ j') ≫ tensorμ B E B' E') (f ⊗ₘ f') (g ⊗ₘ g') := by
  constructor
  · rw [Category.assoc, tensorμ_fst, tensorHom_comp_tensorHom, h.1, h'.1]
  · rw [Category.assoc, tensorμ_snd, tensorHom_comp_tensorHom, h.2, h'.2]

/-- Regrouping two Stinespring isometries realizes both product marginals. -/
lemma hasMarginals_tensor (d : Φ.Dilation E) (e : Ψ.Dilation E') :
    CQM.HasMarginals (ofIsometry ((d.toHom ⊗ₘ e.toHom) ≫ tensorμ B E B' E')).asHom
      (Φ.tensor Ψ).asHom (d.complementary.tensor e.complementary).asHom := by
  rw [ofIsometry_comp, ofIsometry_tensor]
  change CQM.HasMarginals
    (((ofIsometry d.toHom).asHom ⊗ₘ (ofIsometry e.toHom).asHom) ≫
      (ofIsometry (tensorμ B E B' E')).asHom) (_ ⊗ₘ _) (_ ⊗ₘ _)
  rw [asHom_ofIsometry_tensorμ]
  exact tensor_marginals d.hasMarginals e.hasMarginals

/-- Realize parallel channels with the tensor product of their given environments. -/
def tensor (d : Φ.Dilation E) (e : Ψ.Dilation E') : (Φ.tensor Ψ).Dilation (E ⊗ E') where
  toHom := (d.toHom ⊗ₘ e.toHom) ≫ tensorμ B E B' E'
  isIsometry := inferInstance
  channel_eq := congrArg QuantumChannel.toSuperoperator
    (hasMarginals_iff.mp (hasMarginals_tensor d e)).1.symm

/-- The environment of a product dilation receives the product complementary channel. -/
lemma complementary_tensor (d : Φ.Dilation E) (e : Ψ.Dilation E') :
    (d.tensor e).complementary = d.complementary.tensor e.complementary :=
  (hasMarginals_iff.mp (hasMarginals_tensor d e)).2

/-- Independent dilations of all `n + 1` uses of a memoryless channel. -/
def tensorPower (d : Φ.Dilation E) : (n : ℕ) → (Φ.tensorPower n).Dilation (Qudit.tensorPower E n)
  | 0 => d
  | n + 1 => d.tensor (d.tensorPower n)

/-- A product dilation has the exact block complementary channel on all joint inputs. -/
lemma complementary_tensorPower (d : Φ.Dilation E) (n : ℕ) :
    (d.tensorPower n).complementary = d.complementary.tensorPower n := by
  induction n with
  | zero => rfl
  | succ n ih => exact (d.complementary_tensor (d.tensorPower n)).trans (congrArg _ ih)

end Qudit.QuantumChannel.Dilation
