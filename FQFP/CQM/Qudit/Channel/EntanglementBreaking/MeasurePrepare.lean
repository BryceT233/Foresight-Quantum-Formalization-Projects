/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the proposed maximally entangled input criterion.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/CPTP.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.EntanglementBreaking.Antidegradable
public import FQFP.CQM.Qudit.Channel.Process.Classical

/-!
# The measure-and-prepare characterization of entanglement-breaking channels

In output-first Choi coordinates, a product decomposition gives a measurement by
transposing each weighted reference operator in the input basis. The output factors
are the prepared states. An empty outcome set represents every channel with zero input.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct ComplexOrder

namespace Qudit.QuantumChannel

noncomputable section

variable {H K : Qudit} {ι : Type*} [Fintype ι]

/-- Exactly the channels with zero-dimensional input have an empty-outcome representation.
The empty preparation family exists even when the output has no density states. -/
theorem exists_empty_measurePrepare_iff (Φ : QuantumChannel H K) :
    (∃ M : POVM H (Fin 0), Φ = M.measurePrepare (fun i => i.elim0)) ↔
      Module.finrank ℂ H.state = 0 := by
  constructor
  · rintro ⟨M, _⟩
    by_contra hn
    simpa using M.sum_probability (Density.maximallyMixed H hn)
  · intro hH
    have : Subsingleton H.state := Module.finrank_zero_iff.mp hH
    let M : POVM H (Fin 0) := ⟨Fin.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩
    exact ⟨M, QuantumChannel.ext (Subsingleton.elim _ _)⟩

/-- A channel breaks entanglement exactly when it has a finite measure-and-prepare
representation. Empty outcome sets are allowed, so no dimension assumptions are needed. -/
theorem isEntanglementBreaking_iff_exists_measurePrepare (Φ : QuantumChannel H K) :
    Φ.IsEntanglementBreaking ↔
      ∃ (α : Type) (_ : Fintype α) (M : POVM H α) (σ : α → Density K), Φ = M.measurePrepare σ := by
  constructor
  · intro hΦ
    by_cases hH : 0 < Module.finrank ℂ H.state
    · let b := stdOrthonormalBasis ℂ H.state
      exact exists_measurePrepare_of_isSeparable_choiState b hH (hΦ.isSeparable_choiState b hH)
    · obtain ⟨M, he⟩ := (exists_empty_measurePrepare_iff Φ).mpr (by lia)
      exact ⟨Fin 0, inferInstance, M, _, he⟩
  · rintro ⟨α, _, M, σ, rfl⟩
    exact M.isEntanglementBreaking_measurePrepare σ

/-- A channel breaks entanglement exactly when a finite classical measurement register
can simulate it by deterministic postprocessing. An empty register covers zero input. -/
theorem isEntanglementBreaking_iff_exists_outcomeChannel (Φ : QuantumChannel H K) :
    Φ.IsEntanglementBreaking ↔ ∃ (ι : Type) (_ : Fintype ι) (R : Qudit)
      (b : OrthonormalBasis ι ℂ R.state) (M : POVM H ι),
      CQM.IsDegradableTo (M.outcomeChannel b).asHom Φ.asHom := by
  rw [isEntanglementBreaking_iff_exists_measurePrepare]
  constructor
  · rintro ⟨ι, _, M, σ, h⟩
    let b := (ZBasis (Fintype.card ι)).reindex (Fintype.equivFin ι).symm
    exact ⟨ι, inferInstance, _, b, M, (M.isDegradableTo_iff_exists_measurePrepare b Φ).mpr ⟨σ, h⟩⟩
  · rintro ⟨ι, _, R, b, M, h⟩
    obtain ⟨σ, hσ⟩ := (M.isDegradableTo_iff_exists_measurePrepare b Φ).mp h
    exact ⟨ι, inferInstance, M, σ, hσ⟩

/-- On a positive-dimensional input, testing the normalized Choi state in a single
orthonormal basis characterizes entanglement breaking. -/
theorem isEntanglementBreaking_iff_isSeparable_choiState (Φ : QuantumChannel H K)
    (b : OrthonormalBasis ι ℂ H.state) (hH : 0 < Module.finrank ℂ H.state) :
    Φ.IsEntanglementBreaking ↔ (Φ.choiState b hH).IsSeparable :=
  ⟨fun h => h.isSeparable_choiState b hH, fun h =>
    (isEntanglementBreaking_iff_exists_measurePrepare Φ).mpr
      (exists_measurePrepare_of_isSeparable_choiState b hH h)⟩

end

end Qudit.QuantumChannel
