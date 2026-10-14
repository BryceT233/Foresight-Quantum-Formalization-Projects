/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Derivation extension for the symmetric algebra

A lift into a trivial square-zero extension constructs the derivation without
choosing a basis of the generating module.
-/

@[expose] public section
noncomputable section
namespace SymmetricAlgebra
variable {R V M : Type*} [CommSemiring R]
  [AddCommMonoid V] [Module R V]
  [AddCommMonoid M] [Module R M] [Module (SymmetricAlgebra R V) M]
  [IsScalarTower R (SymmetricAlgebra R V) M]

lemma existsUnique_derivation (f : V →ₗ[R] M) :
    ∃! D : Derivation R (SymmetricAlgebra R V) M, ∀ v, D (ι R V v) = f v := by
  let A := SymmetricAlgebra R V
  let : Module Aᵐᵒᵖ M := Module.compHom M
    ((RingHom.id A).fromOpposite (fun a b => mul_comm a b))
  let : IsCentralScalar A M := ⟨fun _ _ => rfl⟩
  let g : V →ₗ[R] TrivSqZeroExt A M :=
    (TrivSqZeroExt.inlAlgHom R A M).toLinearMap.comp (ι R V) +
      ((TrivSqZeroExt.inrHom A M).restrictScalars R).comp f
  let h := SymmetricAlgebra.lift g
  have hfst (a : A) : (h a).fst = a := by
    have heq : (TrivSqZeroExt.fstHom R A M).comp h = AlgHom.id R A := by
      apply SymmetricAlgebra.algHom_ext
      ext v
      simp [h, g]
      rfl
    exact AlgHom.congr_fun heq a
  let D : Derivation R A M :=
    { toLinearMap := ((TrivSqZeroExt.sndHom A M).restrictScalars R).comp h.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' := by
        intro a b
        simp [TrivSqZeroExt.snd_mul, hfst, add_comm] }
  have hD (v : V) : D (ι R V v) = f v := by
    change (h (ι R V v)).snd = f v
    simp [h, g]
  refine ⟨D, hD, ?_⟩
  intro D' hD'
  apply Derivation.ext
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι v => rw [hD', hD]
  | mul a b ha hb => rw [D'.leibniz, D.leibniz, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

example (x : V) : SymmetricAlgebra R (Module.Dual R V) →ₐ[R] R :=
  SymmetricAlgebra.lift (Module.Dual.eval R V x)

end SymmetricAlgebra
