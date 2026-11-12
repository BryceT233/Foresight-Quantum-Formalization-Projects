/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.QuditCat.CompletelyPositive

/-!
# Quantum channels on qudits

`QuantumChannel H K` bundles a completely positive, trace-preserving superoperator.
It acts on density operators and supports composition, tensor products, normalized
finite Kraus families, isometric (in particular unitary) processes, and partial traces.
It does not change the category or dagger instances of `QuditCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.DaggerCategory

namespace QuditCat

/-- A completely positive and trace-preserving linear map between operator spaces. -/
@[ext]
structure QuantumChannel (H K : QuditCat) where
  /-- The underlying map on all operators. -/
  toSuperoperator : Superoperator H K
  /-- Positivity holds with every finite-dimensional auxiliary system. -/
  completelyPositive : toSuperoperator.IsCompletelyPositive
  /-- The complex trace of every operator is preserved. -/
  tracePreserving : toSuperoperator.IsTracePreserving

namespace QuantumChannel

noncomputable section

variable {H K L M : QuditCat}

/-- Apply a quantum channel to a density state. -/
def map (Φ : QuantumChannel H K) (ρ : Density H) : Density K where
  op := Φ.toSuperoperator ρ.op
  positive := Φ.completelyPositive.isPositive ρ.op ρ.positive
  trace_one := (Φ.tracePreserving ρ.op).trans ρ.trace_one

/-- The underlying operator of the channel output. -/
lemma op_map (Φ : QuantumChannel H K) (ρ : Density H) :
    (Φ.map ρ).op = Φ.toSuperoperator ρ.op := rfl

/-- The identity quantum channel. -/
def id (H : QuditCat) : QuantumChannel H H where
  toSuperoperator := LinearMap.id
  completelyPositive := Superoperator.isCompletelyPositive_id H
  tracePreserving := Superoperator.isTracePreserving_id H

/-- Sequential composition: first `Φ`, then `Ψ`. -/
def comp (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K) : QuantumChannel H L where
  toSuperoperator := Ψ.toSuperoperator ∘ₗ Φ.toSuperoperator
  completelyPositive := Ψ.completelyPositive.comp Φ.completelyPositive
  tracePreserving := Ψ.tracePreserving.comp Φ.tracePreserving

/-- Independent parallel composition of quantum channels. -/
def tensor (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M) :
    QuantumChannel (H ⊗ L) (K ⊗ M) where
  toSuperoperator := Superoperator.tensor Φ.toSuperoperator Ψ.toSuperoperator
  completelyPositive := Φ.completelyPositive.tensor Ψ.completelyPositive
  tracePreserving := Φ.tracePreserving.tensor Ψ.tracePreserving

/-- A normalized finite Kraus family determines a quantum channel. -/
def ofKraus {ι : Type*} [Fintype ι] (f : ι → H.state →ₗ[ℂ] K.state)
    (hf : ∑ i, (f i).adjoint ∘ₗ f i = 1) : QuantumChannel H K where
  toSuperoperator := Superoperator.kraus f
  completelyPositive := Superoperator.isCompletelyPositive_kraus f
  tracePreserving := Superoperator.isTracePreserving_kraus f hf

/-- An isometric pure process, including any unitary, induces a quantum channel. -/
def ofIsometry (f : H ⟶ K) [IsIsometry f] : QuantumChannel H K where
  toSuperoperator := Superoperator.conjugate f.hom
  completelyPositive := Superoperator.isCompletelyPositive_conjugate f.hom
  tracePreserving := Superoperator.isTracePreserving_conjugate f.hom
    (congrArg Hom.hom (IsIsometry.comp_dagger_eq_id f))

/-- The channel discarding the right subsystem. -/
def partialTraceRight (H K : QuditCat) : QuantumChannel (H ⊗ K) H where
  toSuperoperator := Operator.partialTraceRight
  completelyPositive := Superoperator.isCompletelyPositive_partialTraceRight H K
  tracePreserving := LinearMap.trace_partialTraceRight

/-- The channel discarding the left subsystem. -/
def partialTraceLeft (H K : QuditCat) : QuantumChannel (H ⊗ K) K where
  toSuperoperator := Operator.partialTraceLeft
  completelyPositive := Superoperator.isCompletelyPositive_partialTraceLeft H K
  tracePreserving := LinearMap.trace_partialTraceLeft

/-- The identity channel fixes density states. -/
lemma map_id (ρ : Density H) : (id H).map ρ = ρ := by
  apply Density.ext
  rfl

/-- Channel composition agrees with sequential action on density states. -/
lemma map_comp (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K) (ρ : Density H) :
    (Ψ.comp Φ).map ρ = Ψ.map (Φ.map ρ) := by
  apply Density.ext
  rfl

/-- Product channels act separately on product density states. -/
lemma map_tensor (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M)
    (ρ : Density H) (σ : Density L) :
    (Φ.tensor Ψ).map (ρ.tensor σ) = (Φ.map ρ).tensor (Ψ.map σ) := by
  apply Density.ext
  exact Superoperator.tensor_apply Φ.toSuperoperator Ψ.toSuperoperator ρ.op σ.op

/-- Isometric channel evolution agrees with the existing density-state map. -/
lemma map_ofIsometry (f : H ⟶ K) [IsIsometry f] (ρ : Density H) :
    (ofIsometry f).map ρ = ρ.map f := by
  apply Density.ext
  rfl

/-- The right partial-trace channel computes the existing right reduction. -/
lemma map_partialTraceRight (ρ : Density (H ⊗ K)) :
    (partialTraceRight H K).map ρ = ρ.partialTraceRight := by
  apply Density.ext
  rfl

/-- The left partial-trace channel computes the existing left reduction. -/
lemma map_partialTraceLeft (ρ : Density (H ⊗ K)) :
    (partialTraceLeft H K).map ρ = ρ.partialTraceLeft := by
  apply Density.ext
  rfl

/-- Composition with the identity channel on the output changes nothing. -/
lemma id_comp (Φ : QuantumChannel H K) : (id K).comp Φ = Φ := by
  apply QuantumChannel.ext
  exact LinearMap.id_comp _

/-- Composition with the identity channel on the input changes nothing. -/
lemma comp_id (Φ : QuantumChannel H K) : Φ.comp (id H) = Φ := by
  apply QuantumChannel.ext
  exact LinearMap.comp_id _

/-- Quantum-channel composition is associative. -/
lemma comp_assoc (Χ : QuantumChannel L M) (Ψ : QuantumChannel K L)
    (Φ : QuantumChannel H K) : (Χ.comp Ψ).comp Φ = Χ.comp (Ψ.comp Φ) := by
  apply QuantumChannel.ext
  exact LinearMap.comp_assoc _ _ _

/-- Channels commute with probabilistic mixing of their inputs. -/
lemma map_mix (Φ : QuantumChannel H K) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ σ : Density H) :
    Φ.map (Density.mix p hp₀ hp₁ ρ σ) = Density.mix p hp₀ hp₁ (Φ.map ρ) (Φ.map σ) := by
  apply Density.ext
  exact map_add Φ.toSuperoperator _ _ |>.trans (congrArg₂ (· + ·)
    (map_smul Φ.toSuperoperator _ _) (map_smul Φ.toSuperoperator _ _))

end

end QuantumChannel

end QuditCat
