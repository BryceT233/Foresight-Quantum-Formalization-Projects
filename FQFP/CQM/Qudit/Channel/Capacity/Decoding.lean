/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.Subspace
public import FQFP.CQM.Qudit.Error.FidelityTraceDistance

/-!
# Recovery from an environment fidelity test

Uhlmann's theorem and trace-preserving recovery of an isometric embedding turn a comparison
of retained marginals into a physical channel on their purifying systems.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.QuantumChannel

variable {A B C R E : Qudit}

private lemma map_pure_tensor_isometry (v : UnitState (A ⊗ B)) (J : B ⟶ C) [IsIsometry J] :
    ((id A).tensor (ofIsometry J)).map (Density.pure v) = Density.pure (v.map (𝟙 A ⊗ₘ J)) := by
  rw [← ofIsometry_id, ← ofIsometry_tensor, map_ofIsometry, Density.map_pure]

/-- Local transition between purifications, allowing purifying registers of either size.
The channel on the second system attains at least the fidelity of the first marginals. -/
theorem exists_channel_fidelity_of_purifications (u : UnitState (A ⊗ B)) (v : UnitState (A ⊗ C)) :
    ∃ D : QuantumChannel B C,
      (Density.pure u).partialTraceRight.fidelity (Density.pure v).partialTraceRight ≤
        (((id A).tensor D).map (Density.pure u)).fidelity (Density.pure v) := by
  let ρ := (Density.pure u).partialTraceRight
  let σ := (Density.pure v).partialTraceRight
  rcases le_total (Module.finrank ℂ B.state) (Module.finrank ℂ C.state) with h | h
  · obtain ⟨w, hw, hf⟩ := σ.exists_purification_norm_inner_eq_fidelity ρ v rfl
      ((ρ.finrank_range_le_of_purification u rfl).trans h)
    obtain ⟨J, hJ, rfl⟩ := u.exists_isometry_of_partialTraceRight_eq w h hw.symm
    refine ⟨ofIsometry J, ?_⟩
    rw [map_pure_tensor_isometry, Density.fidelity_pure_pure, norm_inner_symm, hf,
      Density.fidelity_comm]
  · obtain ⟨w, hw, hf⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ u rfl
      ((σ.finrank_range_le_of_purification v rfl).trans h)
    obtain ⟨J, hJ, rfl⟩ := v.exists_isometry_of_partialTraceRight_eq w h hw.symm
    obtain ⟨D, hD⟩ := exists_leftInverse_ofIsometry J
      (replacement B (Density.pure v).partialTraceLeft)
    refine ⟨D, ?_⟩
    have hrec : ((id A).tensor D).map (Density.pure (v.map (𝟙 A ⊗ₘ J))) = Density.pure v := by
      rw [← map_pure_tensor_isometry, ← map_comp, ← tensor_comp, id_comp, hD, tensor_id_id, map_id]
    have hb := ((id A).tensor D).fidelity_le_map (Density.pure u) (Density.pure (v.map (𝟙 A ⊗ₘ J)))
    rwa [hrec, Density.fidelity_pure_pure, hf] at hb

/-- A pure shared input can approximate any extension of the target marginal by a channel
on the purifying register alone, with no loss in root fidelity. -/
theorem exists_channel_fidelity_of_extension (u : UnitState (A ⊗ B)) (τ : Density (A ⊗ C)) :
    ∃ D : QuantumChannel B C, (Density.pure u).partialTraceRight.fidelity τ.partialTraceRight ≤
      (((id A).tensor D).map (Density.pure u)).fidelity τ := by
  let U := (α_ A C (A ⊗ C)).hom
  let v := τ.purify.map U
  have hinv : (Density.pure v).map (α_ A C (A ⊗ C)).inv = Density.pure τ.purify := by
    rw [Density.map_pure]
    apply congrArg Density.pure
    exact Subtype.ext (congrArg (fun f => (Hom.hom f) τ.purify.val) (α_ A C (A ⊗ C)).hom_inv_id)
  have hpur := partialTraceRight_map_associator_inv (Density.pure v)
  rw [hinv, τ.partialTraceRight_pure_purify] at hpur
  have hm := congrArg Density.partialTraceRight hpur
  rw [partialTraceRight_map_tensor, map_id] at hm
  obtain ⟨D, hD⟩ := exists_channel_fidelity_of_purifications u v
  refine ⟨(partialTraceRight C (A ⊗ C)).comp D, ?_⟩
  rw [← hm] at hD
  have hc := ((id A).tensor (partialTraceRight C (A ⊗ C))).fidelity_le_map
    (((id A).tensor D).map (Density.pure u)) (Density.pure v)
  rw [← hpur, ← map_comp, ← tensor_comp, id_comp] at hc
  exact hD.trans hc

/-- Decoupling an environment from a reference yields a decoder on the receiver alone.
The decoder attains the environment-reference root fidelity for any requested target
joint state of the reference and the decoded system. -/
theorem exists_decoder_of_decoupling (u : UnitState ((E ⊗ R) ⊗ B))
    (σ : Density E) (τ : Density (R ⊗ C)) :
    ∃ D : QuantumChannel B C,
      (Density.pure u).partialTraceRight.fidelity (σ.tensor τ.partialTraceRight) ≤
        (((id R).tensor D).map
          (((partialTraceLeft E R).tensor (id B)).map (Density.pure u))).fidelity τ := by
  let a := α_ E R C
  let target := (σ.tensor τ).map a.inv
  have hm : target.partialTraceRight = σ.tensor τ.partialTraceRight := by
    rw [partialTraceRight_map_associator_inv, map_tensor, map_id, map_partialTraceRight]
  have hinv : (ofIsometry a.hom).map target = σ.tensor τ := by
    rw [show target = (ofIsometry a.inv).map (σ.tensor τ) from rfl, ← map_comp, ← ofIsometry_comp]
    simp only [a.inv_hom_id, ofIsometry_id, map_id]
  have hout : (((partialTraceLeft E R).tensor (id C)).map target) = τ := by
    rw [← partialTraceLeft_comp_associator, map_comp, hinv, map_partialTraceLeft,
      Density.partialTraceLeft_tensor]
  obtain ⟨D, hD⟩ := exists_channel_fidelity_of_extension u target
  have hf := (((partialTraceLeft E R).tensor (id C))).fidelity_le_map
    (((id _).tensor D).map (Density.pure u)) target
  rw [hout, ← map_comp, ← tensor_comp, comp_id, id_comp] at hf
  refine ⟨D, ?_⟩
  rw [← map_comp, ← tensor_comp, comp_id, id_comp, ← hm]
  exact hD.trans hf

private lemma drop_middle (X Y Z : CausalQudit) :
    (α_ X Y Z).hom ≫ X ◁ SemiCartesianMonoidalCategory.snd Y Z =
      SemiCartesianMonoidalCategory.fst X Y ▷ Z := by
  rw [SemiCartesianMonoidalCategory.snd_def, SemiCartesianMonoidalCategory.fst_def,
    whiskerLeft_comp, comp_whiskerRight, ← associator_naturality_middle_assoc, triangle]

private lemma Dilation.retain_receiver_reference {Φ : QuantumChannel A B} (d : Φ.Dilation E)
    (v : UnitState (A ⊗ R)) :
    (((id B).tensor (partialTraceLeft E R)).map (Density.pure (v.map (d.lift R)))) =
      (Φ.tensor (id R)).map (Density.pure v) := by
  have hd : ((id B).tensor (partialTraceLeft E R)).comp (ofIsometry (α_ B E R).hom) =
      (partialTraceRight B E).tensor (id R) := by
    simpa only [CausalQudit.fst_eq_partialTraceRight, CausalQudit.snd_eq_partialTraceLeft] using!
      drop_middle ⟨B⟩ ⟨E⟩ ⟨R⟩
  rw [← Density.map_pure, ← map_ofIsometry, ← map_comp]
  change (((id B).tensor (partialTraceLeft E R)).comp
    (ofIsometry ((d.toHom ⊗ₘ 𝟙 R) ≫ (α_ B E R).hom))).map (Density.pure v) = _
  rw [ofIsometry_comp, ← comp_assoc, hd, ofIsometry_tensor, ofIsometry_id, ← tensor_comp, id_comp,
    ← d.channel_eq_comp]

private lemma map_swap_tensor (F : QuantumChannel A B) (G : QuantumChannel E C)
    (τ : Density (A ⊗ E)) :
    (G.tensor F).map ((ofIsometry (β_ A E).hom).map τ) =
      (ofIsometry (β_ B C).hom).map ((F.tensor G).map τ) := by
  rw [← map_comp, ← map_comp]
  exact congrArg (fun f : QuantumChannel _ _ => f.map τ)
    (BraidedCategory.braiding_naturality F.asHom G.asHom).symm

private lemma pure_swap (u : UnitState (A ⊗ R)) :
    Density.pure u.swap = (ofIsometry (β_ A R).hom).map (Density.pure u) := by
  rw [map_ofIsometry, Density.map_pure]
  rfl

private lemma map_swap_swap (τ : Density (A ⊗ R)) :
    (ofIsometry (β_ R A).hom).map ((ofIsometry (β_ A R).hom).map τ) = τ := by
  rw [← map_comp, ← ofIsometry_comp]
  simp only [SymmetricCategory.symmetry, ofIsometry_id, map_id]

/-- One-shot decoding for any encoded channel. If its complementary output is close to a
fixed environment state times the untouched reference, a physical receiver decoder transmits
the requested shared target state with at least that root fidelity. -/
theorem Dilation.exists_decoder_of_decoupling {Φ : QuantumChannel A B} (d : Φ.Dilation E)
    (v : UnitState (A ⊗ R)) (t : UnitState (C ⊗ R)) (σ : Density E) :
    ∃ D : QuantumChannel B C,
      ((d.complementary.tensor (id R)).map (Density.pure v)).fidelity
          (σ.tensor (Density.pure t).partialTraceLeft) ≤
        (((D.comp Φ).tensor (id R)).map (Density.pure v)).fidelity (Density.pure t) := by
  let w := v.map (d.lift R)
  obtain ⟨D, h⟩ := QuantumChannel.exists_decoder_of_decoupling w.swap σ (Density.pure t.swap)
  refine ⟨D, ?_⟩
  rw [Density.partialTraceRight_pure_swap, Density.partialTraceRight_pure_swap,
    d.partialTraceLeft_pure_lift] at h
  rw [pure_swap w, map_swap_tensor, d.retain_receiver_reference, map_swap_tensor] at h
  rw [← map_comp (D.tensor (id R)), ← tensor_comp, id_comp, pure_swap t] at h
  apply h.trans
  exact (ofIsometry (β_ R C).hom).fidelity_le_map _ _
    |>.trans_eq (by rw [map_swap_swap, map_swap_swap])

private lemma exists_encoder (t : UnitState (C ⊗ R)) (v : UnitState (A ⊗ R)) :
    ∃ J : QuantumChannel C A,
      (Density.pure t).partialTraceLeft.fidelity (Density.pure v).partialTraceLeft ≤
        ((J.tensor (id R)).map (Density.pure t)).fidelity (Density.pure v) := by
  obtain ⟨J, h⟩ := exists_channel_fidelity_of_purifications t.swap v.swap
  rw [Density.partialTraceRight_pure_swap, Density.partialTraceRight_pure_swap,
    pure_swap, pure_swap, map_swap_tensor] at h
  refine ⟨J, h.trans ?_⟩
  exact (ofIsometry (β_ R A).hom).fidelity_le_map _ _
    |>.trans_eq (by rw [map_swap_swap, map_swap_swap])

private lemma dist_le_half_of_fidelity {X : Qudit} (ρ σ : Density X) {ε : ℝ} (hε : 0 ≤ ε)
    (h : 1 - ε ^ 2 / 8 ≤ ρ.fidelity σ) : ρ.traceDistance σ ≤ ε / 2 := by
  apply (sq_le_sq₀ (Density.traceDistance_nonneg ..) (by positivity)).mp
  nlinarith only [h, ρ.traceDistance_sq_add_fidelity_sq_le_one σ, sq_nonneg (1 - ρ.fidelity σ)]

/-- A single decoupled vector on the physical input and reference suffices to construct both
encoding and decoding channels. Its reference marginal may differ from that of the target.
The comparison uses root fidelity throughout. -/
theorem Dilation.exists_code_of_decoupled_vector {Φ : QuantumChannel A B} (d : Φ.Dilation E)
    (v : UnitState (A ⊗ R)) (t : UnitState (C ⊗ R)) (σ : Density E) {ε : ℝ} (hε : 0 ≤ ε)
    (h : 1 - ε ^ 2 / 8 ≤ ((d.complementary.tensor (id R)).map (Density.pure v)).fidelity
      (σ.tensor (Density.pure t).partialTraceLeft)) :
    ∃ Ψ : QuantumChannel C C, Φ.Emulates Ψ ∧
      1 - ε ≤ ((Ψ.tensor (id R)).map (Density.pure t)).fidelity (Density.pure t) := by
  obtain ⟨D, hD⟩ := d.exists_decoder_of_decoupling v t σ
  obtain ⟨J, hJ⟩ := exists_encoder t v
  have href := h.trans (Density.fidelity_le_partialTraceLeft _ _)
  rw [partialTraceLeft_map_tensor, map_id, Density.partialTraceLeft_tensor,
    Density.fidelity_comm] at href
  let F := (D.comp Φ).tensor (id R)
  let η := (J.tensor (id R)).map (Density.pure t)
  have h₁ : η.traceDistance (Density.pure v) ≤ ε / 2 :=
    dist_le_half_of_fidelity _ _ hε (href.trans hJ)
  have h₂ : (F.map (Density.pure v)).traceDistance (Density.pure t) ≤ ε / 2 :=
    dist_le_half_of_fidelity _ _ hε (h.trans hD)
  have hdist := (Density.traceDistance_triangle (F.map η) (F.map (Density.pure v))
    (Density.pure t)).trans (add_le_add ((F.traceDistance_map_le _ _).trans h₁) h₂)
  refine ⟨D.comp (Φ.comp J), ⟨J, D, rfl⟩, ?_⟩
  have hf : 1 - ε ≤ (F.map η).fidelity (Density.pure t) := by
    linarith only [hdist, (F.map η).one_sub_fidelity_le_traceDistance (Density.pure t)]
  simpa only [F, η, ← map_comp, ← tensor_comp, id_comp, comp_assoc] using hf

/-- Arbitrarily long blocks admit a pure physical input and reference with decoupled
environment at this rate. The environment may come from any dilation of the block. -/
def AdmitsDecoupledInputs (Φ : QuantumChannel A B) (R : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ (n k : ℕ) (E : Qudit) (d : (Φ.tensorPower n).Dilation E)
    (v : UnitState (Qudit.tensorPower A n ⊗ std (k + 1))) (σ : Density E),
      N ≤ n ∧ R * (n + 1 : ℝ) ≤ Real.logb 2 (k + 1 : ℝ) ∧
        1 - η ≤ ((d.complementary.tensor (id _)).map (Density.pure v)).fidelity
          (σ.tensor (Density.pure (UnitState.maximallyEntangled (ZBasis (k + 1)))).partialTraceLeft)

/-- Decoupled physical inputs produce actual encoders and decoders at the same entanglement rate. -/
theorem AdmitsDecoupledInputs.achievesEntanglementRate {Φ : QuantumChannel A B} {R : ℝ}
    (h : Φ.AdmitsDecoupledInputs R) : Φ.AchievesEntanglementRate R := by
  intro ε hε N
  obtain ⟨n, k, E, d, v, σ, hn, hR, hf⟩ := h (ε ^ 2 / 8) (by positivity) N
  obtain ⟨Ψ, he, hΨ⟩ := d.exists_code_of_decoupled_vector v
    (UnitState.maximallyEntangled (ZBasis (k + 1))) σ hε.le hf
  exact ⟨n, k, Ψ, hn, he, hR, hΨ⟩

/-- To establish the general regularized achievability inequality it suffices to construct
decoupled vectors for positive rates below each block's coherent information in qubits. -/
theorem regularizedCoherentInfo_le_quantumCapacity_of_decoupled_inputs (Φ : QuantumChannel A B)
    (h : ∀ n (ρ : Density (Qudit.tensorPower A n)) (R : ℝ), 0 < R →
      R < (Φ.tensorPower n).coherentInfo ρ / Real.log 2 →
        (Φ.tensorPower n).AdmitsDecoupledInputs R) :
    Φ.regularizedCoherentInfo ≤ Φ.quantumCapacity :=
  Φ.regularizedCoherentInfo_le_quantumCapacity_of_entanglement_codes fun n ρ R hp hR =>
    (h n ρ R hp hR).achievesEntanglementRate

end Qudit.QuantumChannel
