/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Spectral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Spectral functions of density operators

Finite-dimensional spectral calculus does not require continuity of the scalar function.
The action on every eigenvector characterizes the result independently of the chosen basis.
`logOp` uses the natural logarithm on positive eigenvalues and zero on the kernel.
Relative entropy must separately enforce the support condition before using this logarithm.

## Main definitions and results

* `Qudit.Density.spectralMap`: spectral calculus for arbitrary real scalar functions.
* `Qudit.Density.logOp`: the natural logarithm on the support, extended by zero on the kernel.
* `Qudit.Density.spectralMap_eq_sum_of_eigenbasis`: evaluation in any orthonormal eigenbasis.
* `Qudit.Density.spectralMap_map_unitary`: spectral calculus commutes with unitary transport.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory DaggerCategory

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

/-- Apply a real scalar function to the spectrum of a density operator. -/
def spectralMap (ρ : Density H) (f : ℝ → ℝ) : Operator H :=
  ∑ i, (f (ρ.eigenvalue i) : ℂ) • Operator.outer (ρ.eigenbasis i) (ρ.eigenbasis i)

/-- Spectral calculus acts diagonally in the spectral basis. -/
lemma spectralMap_apply_eigenbasis (ρ : Density H) (f : ℝ → ℝ)
    (i : Fin (Module.finrank ℂ H.state)) :
    ρ.spectralMap f (ρ.eigenbasis i) = (f (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i := by
  classical
  simp [spectralMap, Operator.outer_apply, ρ.eigenbasis.inner_eq_ite]

/-- Spectral calculus acts by `f a` on every eigenvector of eigenvalue `a`. -/
lemma spectralMap_apply_of_eigenvector (ρ : Density H) (f : ℝ → ℝ)
    {v : H.state} {a : ℝ} (hv : ρ.op v = (a : ℂ) • v) :
    ρ.spectralMap f v = (f a : ℂ) • v := by
  have hc (i) : (ρ.eigenvalue i : ℂ) * ρ.eigenbasis.repr v i =
      (a : ℂ) * ρ.eigenbasis.repr v i := by
    have he := ρ.positive.isSymmetric.eigenvectorBasis_apply_self_apply rfl v i
    change ρ.eigenbasis.repr (ρ.op v) i = _ at he
    rw [hv, map_smul] at he
    exact he.symm
  calc
    _ = ρ.spectralMap f (∑ i, ρ.eigenbasis.repr v i • ρ.eigenbasis i) :=
      congrArg (ρ.spectralMap f) (ρ.eigenbasis.sum_repr v).symm
    _ = (f a : ℂ) • (∑ i, ρ.eigenbasis.repr v i • ρ.eigenbasis i) := by
      rw [map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, spectralMap_apply_eigenbasis, smul_smul, smul_smul]
      by_cases hi : ρ.eigenbasis.repr v i = 0
      · simp [hi]
      · have ha : ρ.eigenvalue i = a :=
          Complex.ofReal_injective (mul_right_cancel₀ hi (hc i))
        simp [ha, mul_comm]
    _ = _ := by rw [ρ.eigenbasis.sum_repr v]

/-- Evaluate a spectral function in any orthonormal eigenbasis. -/
lemma spectralMap_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι] (ρ : Density H)
    (f : ℝ → ℝ) (b : OrthonormalBasis ι ℂ H.state) (w : ι → ℝ)
    (hw : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    ρ.spectralMap f = ∑ i, (f (w i) : ℂ) • Operator.outer (b i) (b i) := by
  rw [← Operator.sum_outer_basis b (ρ.spectralMap f)]
  simp only [ρ.spectralMap_apply_of_eigenvector f (hw _), Operator.outer_smul_left]

/-- Real spectral functions of a density operator are self-adjoint. -/
lemma adjoint_spectralMap (ρ : Density H) (f : ℝ → ℝ) :
    (ρ.spectralMap f).adjoint = ρ.spectralMap f := by
  simp only [spectralMap, map_sum, map_smulₛₗ, Complex.conj_ofReal, Operator.adjoint_outer]

/-- An operator commuting with a density preserves its eigenspaces and hence commutes
with every spectral function of that density. -/
lemma commute_spectralMap (ρ : Density H) {A : Operator H} (h : Commute A ρ.op) (f : ℝ → ℝ) :
    Commute A (ρ.spectralMap f) := by
  apply ρ.eigenbasis.toBasis.ext
  intro i
  have hi := DFunLike.congr_fun h.eq.symm (ρ.eigenbasis i)
  simp only [Module.End.mul_apply, ρ.apply_eigenbasis, map_smul] at hi
  change A (ρ.spectralMap f (ρ.eigenbasis i)) = ρ.spectralMap f (A (ρ.eigenbasis i))
  rw [spectralMap_apply_eigenbasis, map_smul, ρ.spectralMap_apply_of_eigenvector f hi]

/-- The identity scalar function recovers the density operator. -/
@[simp]
lemma spectralMap_id (ρ : Density H) : ρ.spectralMap id = ρ.op :=
  ρ.op_eq_sum_eigenvalue_smul_outer.symm

/-- A constant scalar function gives a scalar multiple of the identity operator. -/
lemma spectralMap_const (ρ : Density H) (c : ℝ) :
    ρ.spectralMap (fun _ => c) = (c : ℂ) • (1 : Operator H) := by
  rw [spectralMap, ← Finset.smul_sum]
  congr 1
  simpa using Operator.sum_outer_basis ρ.eigenbasis (1 : Operator H)

/-- The expectation of a spectral function in its own state is a scalar spectral sum. -/
lemma expectation_spectralMap_self (ρ : Density H) (f : ℝ → ℝ) :
    ρ.expectation (ρ.spectralMap f) = ∑ i, ρ.eigenvalue i * f (ρ.eigenvalue i) := by
  rw [expectation, expectationComplex, ρ.op_eq_sum_eigenvalue_smul_outer]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    Operator.trace_mul_outer, spectralMap_apply_eigenbasis, inner_smul_right,
    OrthonormalBasis.inner_eq_one, mul_one, smul_eq_mul, Complex.re_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Natural logarithm on the support, extended by zero on the kernel. -/
def logOp (ρ : Density H) : Operator H := ρ.spectralMap Real.log

/-- Diagonal observables are evaluated against the state's diagonal probabilities. -/
lemma expectation_eq_sum_of_diagonal {ι : Type*} [Fintype ι] (ρ : Density H)
    (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) (a : ι → ℝ)
    (hA : ∀ i, A (b i) = (a i : ℂ) • b i) :
    ρ.expectation A = ∑ i, a i * (inner ℂ (b i) (ρ.op (b i))).re := by
  rw [expectation, expectationComplex, Operator.trace, LinearMap.trace_mul_comm,
    LinearMap.trace_eq_sum_inner _ b]
  simp only [Module.End.mul_apply, hA, map_smul, inner_smul_right, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Expectations of spectral functions in another state are overlap-weighted spectral sums. -/
lemma expectation_spectralMap (ρ σ : Density H) (f : ℝ → ℝ) :
    ρ.expectation (σ.spectralMap f) =
      ∑ i, ∑ j, ρ.eigenvalue i * f (σ.eigenvalue j) *
        ‖inner ℂ (σ.eigenbasis j) (ρ.eigenbasis i)‖ ^ 2 := by
  rw [expectation, expectationComplex, ρ.op_eq_sum_eigenvalue_smul_outer]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    Operator.trace_mul_outer, smul_eq_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [spectralMap]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Operator.outer_apply,
    inner_sum, inner_smul_right, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc,
    ← inner_conj_symm (ρ.eigenbasis i) (σ.eigenbasis j), Complex.mul_conj']
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The logarithm acts by the scalar logarithm on any eigenvector, including the kernel. -/
lemma logOp_apply_of_eigenvector (ρ : Density H) {v : H.state} {a : ℝ}
    (hv : ρ.op v = (a : ℂ) • v) : ρ.logOp v = (Real.log a : ℂ) • v :=
  ρ.spectralMap_apply_of_eigenvector Real.log hv

/-- Spectral calculus intertwines an isometry on its image for every scalar function. -/
lemma spectralMap_comp_isometry {K : Qudit} (ρ : Density H) (f : ℝ → ℝ)
    (V : H ⟶ K) [IsIsometry V] :
    (ρ.map V).spectralMap f ∘ₗ V.hom = V.hom ∘ₗ ρ.spectralMap f := by
  apply ρ.eigenbasis.toBasis.ext
  intro i
  change (ρ.map V).spectralMap f (V.hom (ρ.eigenbasis i)) = V.hom (ρ.spectralMap f (ρ.eigenbasis i))
  rw [spectralMap_apply_eigenbasis, map_smul]
  apply spectralMap_apply_of_eigenvector
  rw [op_map_apply, apply_eigenbasis, map_smul]

/-- A spectral function vanishing at zero commutes with isometric embedding, including
on the orthogonal complement of the image. -/
lemma spectralMap_map_isometry {K : Qudit} (ρ : Density H) (f : ℝ → ℝ) (hf : f 0 = 0)
    (V : H ⟶ K) [IsIsometry V] :
    (ρ.map V).spectralMap f = V.hom ∘ₗ ρ.spectralMap f ∘ₗ V.hom.adjoint := by
  ext x
  let y := V.hom (V.hom.adjoint x)
  have hk : (ρ.map V).op (x - y) = (0 : ℂ) • (x - y) := by
    simp [op_map, y, hom_adjoint_apply_of_isIsometry]
  have hz := (ρ.map V).spectralMap_apply_of_eigenvector f (a := 0) hk
  rw [map_sub, hf, Complex.ofReal_zero, zero_smul, sub_eq_zero] at hz
  exact hz.trans (LinearMap.congr_fun (ρ.spectralMap_comp_isometry f V) (V.hom.adjoint x))

/-- Spectral functions commute with unitary transport between Hilbert spaces. -/
lemma spectralMap_map_unitary {K : Qudit} (ρ : Density H) (f : ℝ → ℝ)
    (U : H ⟶ K) [IsUnitary U] :
    (ρ.map U).spectralMap f = U.hom ∘ₗ ρ.spectralMap f ∘ₗ U.hom.adjoint := by
  apply (ρ.eigenbasis.map (LIEquivOfIsUnitary U)).toBasis.ext
  intro i
  change (ρ.map U).spectralMap f (U.hom (ρ.eigenbasis i)) =
    U.hom (ρ.spectralMap f (U.hom.adjoint (U.hom (ρ.eigenbasis i))))
  rw [hom_adjoint_apply_of_isIsometry]
  exact LinearMap.congr_fun (ρ.spectralMap_comp_isometry f U) (ρ.eigenbasis i)

/-- Transporting both the state and an observable isometrically preserves its expectation. -/
lemma expectation_map_conj {K : Qudit} (ρ : Density H) (A : Operator H)
    (U : H ⟶ K) [IsIsometry U] :
    (ρ.map U).expectation (U.hom ∘ₗ A ∘ₗ U.hom.adjoint) = ρ.expectation A := by
  unfold expectation expectationComplex
  congr 1
  change (LinearMap.trace ℂ K.state)
    ((U.hom ∘ₗ A ∘ₗ U.hom.adjoint) ∘ₗ (U.hom ∘ₗ ρ.op ∘ₗ U.hom.adjoint)) = _
  simp only [LinearMap.comp_assoc]
  have hc : U.hom.adjoint ∘ₗ (U.hom ∘ₗ (ρ.op ∘ₗ U.hom.adjoint)) =
      ρ.op ∘ₗ U.hom.adjoint := by
    rw [← LinearMap.comp_assoc, hom_adjoint_comp_of_isIsometry, LinearMap.id_comp]
  rw [hc]
  calc
    _ = (LinearMap.trace ℂ H.state) ((A ∘ₗ (ρ.op ∘ₗ U.hom.adjoint)) ∘ₗ U.hom) :=
      LinearMap.trace_comp_comm' _ _
    _ = _ := by
      simp only [LinearMap.comp_assoc, hom_adjoint_comp_of_isIsometry, LinearMap.comp_id]
      rfl

/-- The supported logarithm commutes with isometric embedding, including added zero modes. -/
lemma logOp_map_isometry {K : Qudit} (ρ : Density H) (V : H ⟶ K) [IsIsometry V] :
    (ρ.map V).logOp = V.hom ∘ₗ ρ.logOp ∘ₗ V.hom.adjoint :=
  ρ.spectralMap_map_isometry Real.log Real.log_zero V

/-- The supported logarithm commutes with unitary transport. -/
lemma logOp_map_unitary {K : Qudit} (ρ : Density H) (U : H ⟶ K) [IsUnitary U] :
    (ρ.map U).logOp = U.hom ∘ₗ ρ.logOp ∘ₗ U.hom.adjoint :=
  ρ.spectralMap_map_unitary Real.log U

end

end Qudit.Density
