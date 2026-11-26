/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for product states and the action of a gate on one site.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/HSpace/LocalGate.lean
Qhl/Logic/ForRule.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.CQM.Qudit.State.Composite.Basic
public import FQFP.QuantumProgram.Circuit

/-!
# Finite registers of heterogeneous qudits

Each position in a finite family determines a static register path in its tensor product.
Lifting a gate along the path changes just that factor of a product state. The empty family
has the tensor unit as its memory and scalar one as its product vector.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped TensorProduct

namespace QuantumProgram

noncomputable section

/-- Tensor the sites in order, with the monoidal unit for the empty register. -/
def tensorMemory : {n : ℕ} → (Fin n → Qudit) → Qudit
  | 0, _ => 𝟙_ Qudit
  | _ + 1, D => D 0 ⊗ tensorMemory (Fin.tail D)

/-- The path to the indicated site of a finite tensor register. -/
def Register.site : {n : ℕ} → (D : Fin n → Qudit) → (i : Fin n) → Register (tensorMemory D) (D i)
  | 0, _, i => i.elim0
  | _ + 1, D, i => Fin.cases (.left .whole) (fun j => .right (site (Fin.tail D) j)) i

/-- Assemble a family of normalized local vectors in the same order as the register. -/
def registerProductState : {n : ℕ} → (D : Fin n → Qudit) →
    ((i : Fin n) → UnitState (D i)) → UnitState (tensorMemory D)
  | 0, _, _ => ⟨(1 : ℂ), by change inner ℂ (1 : ℂ) 1 = 1; simp⟩
  | _ + 1, D, v => (v 0).tensor (registerProductState (Fin.tail D) (Fin.tail v))

/-- A one-site isometry transports precisely its local factor of a product state. -/
theorem Register.liftHom_site_productState {n : ℕ} (D : Fin n → Qudit) (i : Fin n)
    (U : D i ⟶ D i) [IsIsometry U] (v : (j : Fin n) → UnitState (D j)) :
    ((site D i).liftHom U) (registerProductState D v).val =
      (registerProductState D (Function.update v i (UnitState.map U (v i)))).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      change (TensorProduct.map U.hom LinearMap.id) (_ ⊗ₜ[ℂ] _) =
        ((Function.update v 0 _ 0).val ⊗ₜ[ℂ]
          (registerProductState (Fin.tail D) (Fin.tail (Function.update v 0 _))).val)
      rw [TensorProduct.map_tmul, LinearMap.id_apply, Function.update_self, Fin.tail_update_zero]
      rfl
    | succ j =>
      change (TensorProduct.map LinearMap.id ((site (Fin.tail D) j).liftHom U).hom)
        (_ ⊗ₜ[ℂ] _) = ((Function.update v j.succ _ 0).val ⊗ₜ[ℂ]
          (registerProductState (Fin.tail D) (Fin.tail (Function.update v j.succ _))).val)
      rw [TensorProduct.map_tmul, LinearMap.id_apply,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)), Fin.tail_update_succ]
      exact congrArg (fun x => (v 0).val ⊗ₜ[ℂ] x) (ih (fun l => D l.succ) j U (Fin.tail v))

/-- A lifted isometric endomorphism acts on the selected factor of a product state. -/
theorem Register.liftEnd_site_productState {n : ℕ} (D : Fin n → Qudit) (i : Fin n)
    (A : End (D i)) [IsIsometry A.asHom] (v : (j : Fin n) → UnitState (D j)) :
    ((site D i).liftEnd A).asHom (registerProductState D v).val =
      (registerProductState D (Function.update v i (UnitState.map A.asHom (v i)))).val :=
  liftHom_site_productState D i A.asHom v

/-- A local eigenvalue is also the eigenvalue on a product with arbitrary spectator factors. -/
theorem Register.liftHom_site_productState_eigen {n : ℕ} (D : Fin n → Qudit) (i : Fin n)
    (U : D i ⟶ D i) (v : (j : Fin n) → UnitState (D j)) {z : ℂ}
    (hv : U (v i).val = z • (v i).val) :
    ((site D i).liftHom U) (registerProductState D v).val = z • (registerProductState D v).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      change (TensorProduct.map U.hom LinearMap.id) (_ ⊗ₜ[ℂ] _) = _
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
      change U (v 0).val ⊗ₜ[ℂ] _ = _
      rw [hv]
      exact TensorProduct.smul_tmul' ..
    | succ j =>
      change (TensorProduct.map LinearMap.id ((site (Fin.tail D) j).liftHom U).hom)
        (_ ⊗ₜ[ℂ] _) = _
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
      exact (congrArg (fun w => (v 0).val ⊗ₜ[ℂ] w)
        (ih (Fin.tail D) j U (Fin.tail v) hv)).trans (TensorProduct.tmul_smul ..)

/-- Extending a local operator preserves its eigenvalue on a product with spectator factors. -/
theorem Register.liftEnd_site_productState_eigen {n : ℕ} (D : Fin n → Qudit) (i : Fin n)
    (A : End (D i)) (v : (j : Fin n) → UnitState (D j)) {z : ℂ}
    (hv : A.asHom (v i).val = z • (v i).val) :
    ((site D i).liftEnd A).asHom (registerProductState D v).val =
      z • (registerProductState D v).val :=
  liftHom_site_productState_eigen D i A.asHom v hv

end

end QuantumProgram
