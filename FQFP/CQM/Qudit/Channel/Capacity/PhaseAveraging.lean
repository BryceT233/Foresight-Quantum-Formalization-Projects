/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Error.Fidelity
public import FQFP.Analysis.InnerProductSpace.TraceNormBounds
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# A finite phase ensemble for decoupling

Multiplying each amplitude by an independent cube root of unity makes distinct off-diagonal
ordered pairs orthogonal under averaging. For a family of bipartite amplitudes represented as
maps from receiver to environment this bounds the mean squared Hilbert–Schmidt deviation of
the environment operator by the purity of the receiver Gram operator.
-/

public noncomputable section

open RCLike
open scoped BigOperators ComplexConjugate

namespace Qudit.Superoperator

variable {ι : Type*}

private def phaseDifference (i j : ι) : AddChar (ι → ZMod 3) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom
    { toFun := fun z => z i - z j
      map_zero' := sub_self _
      map_add' := fun _ _ => by simp only [Pi.add_apply]; abel }

private lemma phaseDifference_injective :
    Function.Injective (fun p : {p : ι × ι // p.1 ≠ p.2} => phaseDifference p.1.1 p.1.2) := by
  classical
  rintro ⟨⟨i,j⟩, hij⟩ ⟨⟨k,l⟩, hkl⟩ h
  have eval (z : ι → ZMod 3) : z i - z j = z k - z l :=
    ZMod.injective_stdAddChar (congrArg (fun χ : AddChar _ ℂ => χ z) h)
  change i ≠ j at hij
  change k ≠ l at hkl
  have hik : i = k := by
    by_contra hn
    have he := eval (fun a => if i = a then 1 else 0)
    by_cases hl : i = l
    · subst l
      simp only [ite_true, ite_eq_right hij, ite_eq_right hn, sub_zero, zero_sub] at he
      exact (by decide : (1 : ZMod 3) ≠ -1) he
    · simp only [ite_true, ite_eq_right hij, ite_eq_right hn, ite_eq_right hl, sub_zero,
        one_ne_zero] at he
  subst k
  have he := eval (fun a => if j = a then 1 else 0)
  by_contra hn
  have hjl : j ≠ l := by rintro rfl; exact hn rfl
  simp [Ne.symm hij, hjl] at he

variable [Fintype ι]

private lemma expect_norm_sq_character_sum {G V : Type*} [Fintype G] [AddCommGroup G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (χ : ι → AddChar G ℂ)
    (hχ : Function.Injective χ) (v : ι → V) :
    (𝔼 z, ‖∑ i, χ i z • v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  classical
  have horth (i j : ι) : (𝔼 z, χ j z * conj (χ i z)) = if i = j then 1 else 0 := by
    simpa only [wInner_cWeight_eq_expect, RCLike.inner_apply, hχ.eq_iff] using
      (AddChar.wInner_cWeight_eq_boole (ψ₁ := χ i) (ψ₂ := χ j))
  have h : (𝔼 z, inner ℂ (∑ i, χ i z • v i) (∑ j, χ j z • v j)) = ∑ i, inner ℂ (v i) (v i) := by
    simp only [sum_inner, inner_sum]
    simp only [inner_smul_left, inner_smul_right, ← mul_assoc,
      Finset.expect_sum_comm, ← Finset.expect_mul, horth, ite_mul, one_mul, zero_mul]
    simp
  simp only [inner_self_eq_norm_sq_to_K, Fintype.expect_eq_sum_div_card] at h
  rw [Fintype.expect_eq_sum_div_card]
  apply Complex.ofReal_injective
  push_cast
  exact h

/-- Independent phase labels are orthogonal in mean, so the mean squared norm of a
superposition is its incoherent sum of squared norms. -/
theorem expect_norm_sq_phase_sum [DecidableEq ι] {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (v : ι → V) :
    (𝔼 z : ι → ZMod 3, ‖∑ i, ZMod.stdAddChar (z i) • v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  classical
  let χ (i : ι) : AddChar (ι → ZMod 3) ℂ :=
    ZMod.stdAddChar.compAddMonoidHom (Pi.evalAddMonoidHom (fun _ : ι => ZMod 3) i)
  have hinj : Function.Injective χ := by
    intro i j hij
    by_contra h
    let z (a : ι) : ZMod 3 := if i = a then 1 else 0
    have hh : z i = z j := ZMod.injective_stdAddChar (congrArg (fun f : AddChar _ ℂ => f z) hij)
    simp [z, h] at hh
  exact expect_norm_sq_character_sum χ hinj v

/-- Parseval's identity for the off-diagonal interference terms of an independent
finite random phase superposition. -/
theorem expect_norm_sq_phase_interference [DecidableEq ι] {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (v : ι → ι → V) :
    (𝔼 z : ι → ZMod 3, ‖∑ p : {p : ι × ι // p.1 ≠ p.2},
      ZMod.stdAddChar (z p.1.1 - z p.1.2) • v p.1.1 p.1.2‖ ^ 2) =
        ∑ p : {p : ι × ι // p.1 ≠ p.2}, ‖v p.1.1 p.1.2‖ ^ 2 := by
  change (𝔼 z, ‖∑ p : {p : ι × ι // p.1 ≠ p.2},
    phaseDifference p.1.1 p.1.2 z • v p.1.1 p.1.2‖ ^ 2) = _
  exact expect_norm_sq_character_sum
    (fun p : {p : ι × ι // p.1 ≠ p.2} => phaseDifference p.1.1 p.1.2)
    phaseDifference_injective (fun p => v p.1.1 p.1.2)

variable {B E : Qudit}

/-- Coherent superposition of bipartite amplitudes with independent finite phases. -/
@[expose] def phaseAmplitude (f : ι → B.state →ₗ[ℂ] E.state) (z : ι → ZMod 3) :
    B.state →ₗ[ℂ] E.state :=
  ∑ i, ZMod.stdAddChar (z i) • f i

private lemma phaseAmplitude_gram_sub [DecidableEq ι] (f : ι → B.state →ₗ[ℂ] E.state)
    (z : ι → ZMod 3) :
    phaseAmplitude f z ∘ₗ (phaseAmplitude f z).adjoint - ∑ i, f i ∘ₗ (f i).adjoint =
      ∑ p : {p : ι × ι // p.1 ≠ p.2}, ZMod.stdAddChar (z p.1.1 - z p.1.2) •
        (f p.1.1 ∘ₗ (f p.1.2).adjoint) := by
  classical
  let term (p : ι × ι) := ZMod.stdAddChar (z p.1 - z p.2) • (f p.1 ∘ₗ (f p.2).adjoint)
  have hgram : phaseAmplitude f z ∘ₗ (phaseAmplitude f z).adjoint = ∑ p, term p := by
    ext x
    simp only [phaseAmplitude, map_sum, map_smulₛₗ, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_smul, term, Fintype.sum_prod_type, Finset.smul_sum,
      AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]
    simp only [RingHom.id_apply, mul_comm (conj _)]
    exact Finset.sum_comm
  rw [hgram, sub_eq_iff_eq_add]
  have split := Fintype.sum_subtype_add_sum_subtype (fun p : ι × ι => p.1 ≠ p.2) term
  rw [← split]
  congr 1
  let diag : ι ≃ {p : ι × ι // ¬ p.1 ≠ p.2} :=
    ⟨fun i => ⟨(i, i), by simp⟩, fun p => p.val.1, fun _ => rfl, by
      rintro ⟨⟨i,j⟩, hp⟩
      exact Subtype.ext (Prod.ext rfl (not_not.mp hp))⟩
  rw [← diag.sum_comp]
  simp [diag, term]

private lemma sum_sq_cross_gram (f : ι → B.state →ₗ[ℂ] E.state)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ E.state)) ℂ E.state) :
    ∑ p : ι × ι, ‖vectorize b (f p.1 ∘ₗ (f p.2).adjoint)‖ ^ 2 =
      (LinearMap.trace ℂ B.state ((∑ i, (f i).adjoint ∘ₗ f i) ^ 2)).re := by
  have hpair i j : ‖vectorize b (f i ∘ₗ (f j).adjoint)‖ ^ 2 =
      (LinearMap.trace ℂ B.state (((f i).adjoint ∘ₗ f i) * ((f j).adjoint ∘ₗ f j))).re := by
    rw [norm_vectorize_sq, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
      LinearMap.comp_assoc, ← LinearMap.trace_comp_comm' (f j)]
    simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
  simp only [sq, Finset.sum_mul, Finset.mul_sum, map_sum, Complex.re_sum, Fintype.sum_prod_type,
    hpair]
  exact Finset.sum_comm

/-- The mean squared Hilbert–Schmidt fluctuation of the environment Gram operator is bounded
by the receiver Gram purity. No normalization or orthogonality of the amplitudes is needed. -/
theorem expect_sq_environment_gram_sub_le [DecidableEq ι] (f : ι → B.state →ₗ[ℂ] E.state) :
    let b := stdOrthonormalBasis ℂ E.state
    (𝔼 z : ι → ZMod 3, ‖vectorize b
      (phaseAmplitude f z ∘ₗ (phaseAmplitude f z).adjoint - ∑ i, f i ∘ₗ (f i).adjoint)‖ ^ 2) ≤
      (LinearMap.trace ℂ B.state ((∑ i, (f i).adjoint ∘ₗ f i) ^ 2)).re := by
  intro b
  simp only [phaseAmplitude_gram_sub, map_sum, map_smul]
  let v i j := vectorize b (f i ∘ₗ (f j).adjoint)
  rw [expect_norm_sq_phase_interference v, ← sum_sq_cross_gram f b]
  have he := Fintype.sum_subtype_add_sum_subtype (fun p : ι × ι => p.1 ≠ p.2)
    (fun p => ‖v p.1 p.2‖ ^ 2)
  exact he ▸ le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The squared trace norm of a self-adjoint error operator costs at most the register dimension
times its squared Hilbert–Schmidt norm. -/
private lemma traceNorm_sq_le_dim_mul {X : Operator E} (hX : X.IsSymmetric)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ E.state)) ℂ E.state) :
    LinearMap.traceNorm X ^ 2 ≤ Module.finrank ℂ E.state * ‖vectorize b X‖ ^ 2 := by
  rw [norm_vectorize_sq, hX.adjoint_eq]
  exact hX.traceNorm_sq_le_finrank_mul_re_trace_mul_self

/-- The mean squared trace-norm error costs at most environment dimension times receiver
purity. The expectation can be combined with truncation errors before selecting a phase.
-/
theorem expect_phase_traceNorm_sq_le [DecidableEq ι] (f : ι → B.state →ₗ[ℂ] E.state) :
    (𝔼 z, LinearMap.traceNorm (phaseAmplitude f z ∘ₗ (phaseAmplitude f z).adjoint -
        ∑ i, f i ∘ₗ (f i).adjoint) ^ 2) ≤
      Module.finrank ℂ E.state *
        (LinearMap.trace ℂ B.state ((∑ i, (f i).adjoint ∘ₗ f i) ^ 2)).re := by
  apply le_trans _ (mul_le_mul_of_nonneg_left (expect_sq_environment_gram_sub_le f)
    (Nat.cast_nonneg _))
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro z _
  apply traceNorm_sq_le_dim_mul
  apply (LinearMap.eq_adjoint_iff _ _).mp
  simp only [map_sub, map_sum, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]

end Qudit.Superoperator
