/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.TensorRegister
public import FQFP.QuantumProgram.Unitary

/-!
# Permutations of a tensor register

A permutation sends the local state at site `i` to site `e i`. Its unitary on the
whole tensor product is specified on the product basis, including on entangled inputs
by linear extension.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped TensorProduct

namespace QuantumProgram

noncomputable section

variable {H : Qudit} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state)

/-- Product basis indexed by words in the local basis labels, in register order. -/
def registerBasis (b : OrthonormalBasis ι ℂ H.state) : (n : ℕ) → OrthonormalBasis (Fin n → ι) ℂ
    (tensorMemory (fun _ : Fin n => H)).state
  | 0 => (OrthonormalBasis.singleton Unit ℂ).reindex (Equiv.ofUnique Unit (Fin 0 → ι))
  | n + 1 => (b.tensorProduct (registerBasis b n)).reindex
      (Fin.consEquiv (fun _ : Fin (n + 1) => ι))

/-- A basis word is the tensor product of the local basis vectors carrying its labels. -/
theorem registerBasis_apply {n : ℕ} (x : Fin n → ι) :
    registerBasis b n x = (registerProductState (fun _ => H)
      (fun i => UnitState.ofBasis b (x i))).val := by
  induction n with
  | zero =>
    change ((OrthonormalBasis.singleton Unit ℂ).reindex (Equiv.ofUnique Unit (Fin 0 → ι))) x = 1
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.singleton_apply]
  | succ n ih =>
    change ((b.tensorProduct (registerBasis b n)).reindex
      (Fin.consEquiv (fun _ : Fin (n + 1) => ι))) x =
      b (x 0) ⊗ₜ[ℂ] (registerProductState (fun _ => H)
        (fun i => UnitState.ofBasis b (x i.succ))).val
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.tensorProduct_apply]
    exact congrArg (fun w => b (x 0) ⊗ₜ[ℂ] w) (ih (Fin.tail x))

/-- The coordinate of a product state is the product of its local coordinates. -/
theorem inner_registerBasis_productState {n : ℕ} (x : Fin n → ι) (v : Fin n → UnitState H) :
    inner ℂ (registerBasis b n x) (registerProductState (fun _ => H) v).val =
      ∏ i, inner ℂ (b (x i)) (v i).val := by
  induction n with
  | zero =>
    change inner ℂ (((OrthonormalBasis.singleton Unit ℂ).reindex
      (Equiv.ofUnique Unit (Fin 0 → ι))) x) (1 : ℂ) = _
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.singleton_apply]
    simp
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change inner ℂ (((b.tensorProduct (registerBasis b n)).reindex
      (Fin.consEquiv (fun _ : Fin (n + 1) => ι))) x)
      ((v 0).val ⊗ₜ[ℂ] (registerProductState (fun _ => H) (Fin.tail v)).val) = _
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.tensorProduct_apply,
      TensorProduct.inner_tmul]
    exact congrArg (_ * ·) (ih (Fin.tail x) (Fin.tail v))

/-- Move each tensor factor to its image under a permutation of the sites. -/
def UnitaryProgram.permuteSites (b : OrthonormalBasis ι ℂ H.state) {n : ℕ}
    (e : Equiv.Perm (Fin n)) :
    UnitaryProgram (tensorMemory (fun _ : Fin n => H)) :=
  let B := registerBasis b n
  let U := B.equiv B (e.arrowCongr (Equiv.refl ι))
  haveI := isUnitary_isoMk_coe_LIEquiv (H₁ := tensorMemory (fun _ : Fin n => H))
    (H₂ := tensorMemory (fun _ : Fin n => H)) U
  .gateHom .whole (isoMk U.toLinearEquiv).hom

/-- Permuting a product moves its full local vectors, including their phases. -/
theorem UnitaryProgram.permuteSites_productState {n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin n → UnitState H) :
    (permuteSites b e).toOperator (registerProductState (fun _ => H) v).val =
      (registerProductState (fun _ => H) (v ∘ e.symm)).val := by
  let B := registerBasis b n
  let p := e.arrowCongr (Equiv.refl ι)
  let U := B.equiv B p
  apply InnerProductSpace.ext_inner_left_basis B.toBasis
  intro y
  obtain ⟨x, rfl⟩ := p.surjective y
  change inner ℂ (B (p x)) (U _) = inner ℂ (B (p x)) _
  rw [← B.equiv_apply_basis B p x, U.inner_map_map, B.equiv_apply_basis]
  rw [inner_registerBasis_productState, inner_registerBasis_productState]
  exact (Equiv.prod_comp e.symm (fun i => inner ℂ (b (x i)) (v i).val)).symm

end

end QuantumProgram
