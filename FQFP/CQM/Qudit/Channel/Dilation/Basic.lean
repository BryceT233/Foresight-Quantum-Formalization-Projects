/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Choi

/-!
# Finite-dimensional isometric dilations of quantum channels

For a Kraus family `f` and an environment basis `b`, the dilation sends `x` to
`∑ i, f i x ⊗ b i`. The retained output is on the left, the discarded environment
on the right. Completeness makes this map isometric, and taking the right partial
trace recovers the channel on all operators. No nonzero-dimension assumption or
chosen normalized environment input is required.

## Main definitions and results

* `Qudit.Superoperator.krausDilation`: a coherent dilation from a Kraus family and environment
  basis.
* `Qudit.Superoperator.partialTraceRight_conjugate_krausDilation`: discarding recovers the Kraus
  map.
* `Qudit.QuantumChannel.exists_dilation_finrank`: an isometric dilation with a standard environment.
* `Qudit.QuantumChannel.exists_dilation_map`: the induced density-state dilation identity.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit

noncomputable section

namespace Superoperator

variable {H K E : Qudit} {ι : Type*} [Fintype ι]

/-- Coherently retain a Kraus label in a chosen orthonormal environment basis. -/
def krausDilation (b : OrthonormalBasis ι ℂ E.state)
    (f : ι → H.state →ₗ[ℂ] K.state) : H.state →ₗ[ℂ] (K ⊗ E).state :=
  ∑ i, (TensorProduct.mk ℂ K.state E.state).flip (b i) ∘ₗ f i

/-- The dilation appends the environment label before summing coherently. -/
lemma krausDilation_apply (b : OrthonormalBasis ι ℂ E.state)
    (f : ι → H.state →ₗ[ℂ] K.state) (x : H.state) :
    krausDilation b f x = ∑ i, f i x ⊗ₜ[ℂ] b i := by
  simp only [krausDilation, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

/-- Contracting the environment label recovers the corresponding Kraus operator. -/
lemma contract_krausDilation (b : OrthonormalBasis ι ℂ E.state)
    (f : ι → H.state →ₗ[ℂ] K.state) (i : ι) :
    ((TensorProduct.mk ℂ K.state E.state).flip (b i)).adjoint ∘ₗ krausDilation b f = f i := by
  classical
  ext x
  rw [LinearMap.comp_apply, krausDilation_apply b f x, map_sum]
  simp only [adjoint_tensorInsertion_apply (H := K), b.inner_eq_ite]
  simp

/-- The square of the dilation is the sum of the Kraus adjoint squares. -/
lemma adjoint_krausDilation_comp_self (b : OrthonormalBasis ι ℂ E.state)
    (f : ι → H.state →ₗ[ℂ] K.state) :
    (krausDilation b f).adjoint ∘ₗ krausDilation b f = ∑ i, (f i).adjoint ∘ₗ f i := by
  classical
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  change inner ℂ (krausDilation b f y : K.state ⊗[ℂ] E.state) (krausDilation b f x) = _
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.adjoint_inner_right,
    krausDilation_apply, sum_inner, inner_sum]
  change (∑ j, ∑ i, inner ℂ (f i y) (f j x) * inner ℂ (b i) (b j)) = _
  simp [b.inner_eq_ite]

/-- A normalized Kraus family gives an isometric pure process. -/
lemma isIsometry_krausDilation (b : OrthonormalBasis ι ℂ E.state)
    (f : ι → H.state →ₗ[ℂ] K.state) (hf : ∑ i, (f i).adjoint ∘ₗ f i = 1) :
    IsIsometry (ofHom (krausDilation b f) : H ⟶ K ⊗ E) := by
  constructor
  apply hom_ext
  change (krausDilation b f).adjoint ∘ₗ krausDilation b f = LinearMap.id
  rw [adjoint_krausDilation_comp_self, hf]
  rfl

/-- Discarding the environment after the coherent dilation recovers the Kraus map. -/
lemma partialTraceRight_conjugate_krausDilation (b : OrthonormalBasis ι ℂ E.state)
    (f : ι → H.state →ₗ[ℂ] K.state) :
    (Operator.partialTraceRight : Superoperator (K ⊗ E) K) ∘ₗ
      conjugate (krausDilation b f) = kraus f := by
  rw [partialTraceRight_eq_kraus b]
  apply LinearMap.ext
  intro A
  simp only [kraus, LinearMap.comp_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (conjugate (((TensorProduct.mk ℂ K.state E.state).flip (b i)).adjoint) ∘ₗ
    conjugate (krausDilation b f)) A = conjugate (f i) A
  rw [← conjugate_comp, contract_krausDilation]

end Superoperator

namespace QuantumChannel

variable {H K E : Qudit} {ι : Type*} [Fintype ι]

/-- The explicit dilation of a normalized Kraus family realizes its bundled channel. -/
lemma ofKraus_eq_dilation (b : OrthonormalBasis ι ℂ E.state)
    (f : ι → H.state →ₗ[ℂ] K.state) (hf : ∑ i, (f i).adjoint ∘ₗ f i = 1) :
    letI := Superoperator.isIsometry_krausDilation b f hf
    ofKraus f hf = (partialTraceRight K E).comp
      (ofIsometry (ofHom (Superoperator.krausDilation b f) : H ⟶ K ⊗ E)) := by
  let := Superoperator.isIsometry_krausDilation b f hf
  apply QuantumChannel.ext
  exact (Superoperator.partialTraceRight_conjugate_krausDilation b f).symm

/-- The standard environment of dimension `dim(output) * dim(input)` always suffices.
This is an upper bound, not a minimality claim. -/
lemma exists_dilation_finrank (Φ : QuantumChannel H K) :
    ∃ V : H ⟶ K ⊗ std (Module.finrank ℂ K.state * Module.finrank ℂ H.state),
      IsIsometry V ∧ Φ.toSuperoperator =
        (Operator.partialTraceRight :
          Superoperator (K ⊗ std (Module.finrank ℂ K.state * Module.finrank ℂ H.state)) K) ∘ₗ
            Superoperator.conjugate V.hom := by
  obtain ⟨f, hΦ, hf⟩ := Φ.exists_kraus_finrank
  let n := Module.finrank ℂ K.state * Module.finrank ℂ H.state
  refine ⟨ofHom (Superoperator.krausDilation (ZBasis n) f),
    Superoperator.isIsometry_krausDilation (ZBasis n) f hf, ?_⟩
  exact hΦ.trans (Superoperator.partialTraceRight_conjugate_krausDilation (ZBasis n) f).symm

/-- Every channel is an isometry into an output and a finite standard environment,
followed by discarding that environment. The identity holds on all operators. -/
lemma exists_dilation (Φ : QuantumChannel H K) :
    ∃ (n : ℕ) (V : H ⟶ K ⊗ std n),
      IsIsometry V ∧ Φ.toSuperoperator =
        (Operator.partialTraceRight : Superoperator (K ⊗ std n) K) ∘ₗ
          Superoperator.conjugate V.hom := by
  obtain ⟨V, hV, hΦ⟩ := Φ.exists_dilation_finrank
  exact ⟨Module.finrank ℂ K.state * Module.finrank ℂ H.state, V, hV, hΦ⟩

/-- Dilation realizes the original channel on mixed states, with the environment on the right. -/
lemma exists_dilation_map (Φ : QuantumChannel H K) :
    ∃ (n : ℕ) (V : H ⟶ K ⊗ std n) (_hV : IsIsometry V),
      ∀ ρ : Density H, Φ.map ρ = (ρ.map V).partialTraceRight := by
  obtain ⟨n, V, hV, hΦ⟩ := Φ.exists_dilation
  refine ⟨n, V, hV, fun ρ => ?_⟩
  apply Density.ext
  change Φ.toSuperoperator ρ.op = Operator.partialTraceRight
    (V.hom ∘ₗ ρ.op ∘ₗ V.hom.adjoint)
  rw [hΦ]
  rfl

end QuantumChannel

end

end Qudit
