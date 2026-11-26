/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.VonNeumann.Channel
public import FQFP.CQM.Qudit.Entropy.VonNeumann.Subadditivity
public import FQFP.CQM.Qudit.Channel.Dilation.Complementary

/-!
# Entropy exchange and complementary coherent information

Entropy exchange is the joint output-reference entropy when a channel acts on a purification.
It equals the environment entropy for every Stinespring dilation, including nonminimal ones.
This proves independence of the chosen purification and of the dilation at the level of entropy.
Coherent information is output entropy minus environment entropy; complementary channels have
opposite coherent information. Subadditivity then bounds its absolute value by the input entropy.
All entropies use natural logarithms. No full-rank or positive-dimension hypotheses are added.

## Main definitions and results

* `Qudit.QuantumChannel.entropyExchange`: joint output-reference entropy in nats.
* `Qudit.QuantumChannel.Dilation.entropyExchange_eq`: any dilation computes entropy exchange.
* `Qudit.QuantumChannel.entropyExchange_eq_of_purification`: independence of the purification.
* `Qudit.QuantumChannel.abs_coherentInfo_le`: coherent information is bounded by input entropy.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K E R : Qudit}

/-- Entropy of the environment equals joint output-reference entropy for any pure input. -/
lemma Dilation.entropy_complementary_eq_joint {Φ : QuantumChannel H K}
    (d : Φ.Dilation E) (ψ : UnitState (H ⊗ R)) :
    (d.complementary.map (Density.pure ψ).partialTraceRight).vonNeumannEntropy =
      ((Φ.tensor (id R)).map (Density.pure ψ)).vonNeumannEntropy := by
  have h := Density.vonNeumannEntropy_partialTraceRight_eq_partialTraceLeft
    (ψ.map (d.symm.lift R))
  rwa [d.symm.partialTraceRight_pure_lift, d.symm.partialTraceLeft_pure_lift,
    d.complementary_symm] at h

/-- Entropy exchange in nats, defined using the existing spectral purification. -/
def entropyExchange (Φ : QuantumChannel H K) (ρ : Density H) : ℝ :=
  ((Φ.tensor (id H)).map (Density.pure ρ.purify)).vonNeumannEntropy

/-- Any Stinespring environment computes the same entropy exchange. -/
lemma Dilation.entropyExchange_eq {Φ : QuantumChannel H K}
    (d : Φ.Dilation E) (ρ : Density H) :
    Φ.entropyExchange ρ = (d.complementary.map ρ).vonNeumannEntropy := by
  have h := d.entropy_complementary_eq_joint ρ.purify
  rw [Density.partialTraceRight_pure_purify] at h
  exact h.symm

/-- A finite Kraus representation bounds entropy exchange by the log of the family size:
one orthonormal environment label suffices for each Kraus operator. -/
lemma entropyExchange_le_log_card_of_kraus {ι : Type*} [Fintype ι] (Φ : QuantumChannel H K)
    (f : ι → H.state →ₗ[ℂ] K.state) (hf : Φ.toSuperoperator = Superoperator.kraus f)
    (ρ : Density H) : Φ.entropyExchange ρ ≤ Real.log (Fintype.card ι) := by
  let E := std (Fintype.card ι)
  let b : OrthonormalBasis ι ℂ E.state := (ZBasis _).reindex (Fintype.equivFin ι).symm
  have htp := (Superoperator.isTracePreserving_kraus_iff f).mp (hf ▸ Φ.tracePreserving)
  let d : Φ.Dilation E :=
    ⟨ofHom (Superoperator.krausDilation b f), Superoperator.isIsometry_krausDilation b f htp,
      hf.trans (Superoperator.partialTraceRight_conjugate_krausDilation b f).symm⟩
  rw [d.entropyExchange_eq]
  simpa only [E, finrank_std] using (d.complementary.map ρ).vonNeumannEntropy_le_log_finrank

/-- The chosen complementary channel computes entropy exchange. -/
lemma entropyExchange_eq_complementary (Φ : QuantumChannel H K) (ρ : Density H) :
    Φ.entropyExchange ρ = (Φ.complementary.map ρ).vonNeumannEntropy :=
  Φ.dilation.entropyExchange_eq ρ

/-- Joint output-reference entropy is independent of the purification and reference dimension. -/
lemma entropyExchange_eq_of_purification (Φ : QuantumChannel H K) (ρ : Density H)
    (ψ : UnitState (H ⊗ R)) (hψ : (Density.pure ψ).partialTraceRight = ρ) :
    Φ.entropyExchange ρ = ((Φ.tensor (id R)).map (Density.pure ψ)).vonNeumannEntropy := by
  rw [entropyExchange_eq_complementary]
  have h := Φ.dilation.entropy_complementary_eq_joint ψ
  rwa [hψ] at h

/-- Environment entropies agree even for dilations with different environment dimensions. -/
lemma Dilation.entropy_complementary_eq {Φ : QuantumChannel H K} {E' : Qudit}
    (d : Φ.Dilation E) (d' : Φ.Dilation E') (ρ : Density H) :
    (d.complementary.map ρ).vonNeumannEntropy =
      (d'.complementary.map ρ).vonNeumannEntropy :=
  (d.entropyExchange_eq ρ).symm.trans (d'.entropyExchange_eq ρ)

/-- Entropy exchange is nonnegative. -/
lemma entropyExchange_nonneg (Φ : QuantumChannel H K) (ρ : Density H) :
    0 ≤ Φ.entropyExchange ρ := Density.vonNeumannEntropy_nonneg _

/-- Coherent information subtracts entropy exchange from the output entropy. -/
lemma coherentInfo_eq_sub_entropyExchange (Φ : QuantumChannel H K) (ρ : Density H) :
    Φ.coherentInfo ρ = (Φ.map ρ).vonNeumannEntropy - Φ.entropyExchange ρ := rfl

/-- Coherent information can be computed with any dilation's environment output. -/
lemma Dilation.coherentInfo_eq {Φ : QuantumChannel H K} (d : Φ.Dilation E) (ρ : Density H) :
    Φ.coherentInfo ρ = (Φ.map ρ).vonNeumannEntropy -
      (d.complementary.map ρ).vonNeumannEntropy := by
  rw [coherentInfo_eq_sub_entropyExchange, d.entropyExchange_eq]

/-- Complementary channels have opposite coherent information. -/
lemma Dilation.coherentInfo_complementary {Φ : QuantumChannel H K}
    (d : Φ.Dilation E) (ρ : Density H) :
    d.complementary.coherentInfo ρ = -Φ.coherentInfo ρ := by
  rw [d.symm.coherentInfo_eq, d.complementary_symm, d.coherentInfo_eq]
  ring

/-- The chosen complementary channel has the opposite coherent information. -/
lemma coherentInfo_complementary (Φ : QuantumChannel H K) (ρ : Density H) :
    Φ.complementary.coherentInfo ρ = -Φ.coherentInfo ρ :=
  Φ.dilation.coherentInfo_complementary ρ

/-- The unchanged reference has the input entropy after the channel acts. -/
lemma entropy_reference_output (Φ : QuantumChannel H K) (ρ : Density H) :
    ((Φ.tensor (id H)).map (Density.pure ρ.purify)).partialTraceLeft.vonNeumannEntropy =
      ρ.vonNeumannEntropy := by
  rw [partialTraceLeft_map_tensor, map_id,
    ← Density.vonNeumannEntropy_partialTraceRight_eq_partialTraceLeft,
    Density.partialTraceRight_pure_purify]

/-- Entropy exchange is at most the sum of the input and output entropies. -/
lemma entropyExchange_le_add (Φ : QuantumChannel H K) (ρ : Density H) :
    Φ.entropyExchange ρ ≤ (Φ.map ρ).vonNeumannEntropy + ρ.vonNeumannEntropy := by
  have h := ((Φ.tensor (id H)).map (Density.pure ρ.purify)).vonNeumannEntropy_le_add_marginals
  rwa [entropy_reference_output, partialTraceRight_map_tensor,
    Density.partialTraceRight_pure_purify] at h

/-- Coherent information is bounded below by minus the input entropy. -/
lemma neg_entropy_le_coherentInfo (Φ : QuantumChannel H K) (ρ : Density H) :
    -ρ.vonNeumannEntropy ≤ Φ.coherentInfo ρ := by
  rw [coherentInfo_eq_sub_entropyExchange]
  linarith [Φ.entropyExchange_le_add ρ]

/-- Coherent information is bounded above by the input entropy. -/
lemma coherentInfo_le_input_entropy (Φ : QuantumChannel H K) (ρ : Density H) :
    Φ.coherentInfo ρ ≤ ρ.vonNeumannEntropy := by
  have h := Φ.complementary.neg_entropy_le_coherentInfo ρ
  rw [coherentInfo_complementary] at h
  linarith

/-- The magnitude of coherent information cannot exceed the input entropy. -/
lemma abs_coherentInfo_le (Φ : QuantumChannel H K) (ρ : Density H) :
    |Φ.coherentInfo ρ| ≤ ρ.vonNeumannEntropy :=
  abs_le.mpr ⟨Φ.neg_entropy_le_coherentInfo ρ, Φ.coherentInfo_le_input_entropy ρ⟩

/-- A pure input has entropy exchange equal to its output entropy. -/
lemma entropyExchange_pure (Φ : QuantumChannel H K) (ψ : UnitState H) :
    Φ.entropyExchange (Density.pure ψ) = (Φ.map (Density.pure ψ)).vonNeumannEntropy := by
  have h := Φ.coherentInfo_pure ψ
  rw [coherentInfo_eq_sub_entropyExchange, sub_eq_zero] at h
  exact h.symm

/-- The identity channel has zero entropy exchange. -/
lemma entropyExchange_id (ρ : Density H) : (id H).entropyExchange ρ = 0 := by
  rw [entropyExchange, tensor_id_id, map_id, Density.vonNeumannEntropy_pure]

end

end Qudit.QuantumChannel
