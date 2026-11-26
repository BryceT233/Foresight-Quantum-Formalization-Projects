/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Degradation.BroadcastExtension
public import FQFP.CQM.Qudit.Channel.Process.Tomography

/-!
# No broadcasting of a full quantum system

An isometric channel has a dilation with a one-dimensional environment. On a
positive-dimensional input, every compatible channel therefore prepares a fixed state.
This gives the full matrix algebra case of no broadcasting in §7.3.2 of
*Categorical Quantum Mechanics*: a single channel can broadcast the identity precisely
in dimensions zero and one.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory SemiCartesianMonoidalCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K L : Qudit}

/-- An isometry is its own dilation after adjoining the tensor unit as environment. -/
def isometryDilation (f : H ⟶ K) [IsIsometry f] : (ofIsometry f).Dilation (𝟙_ Qudit) where
  toHom := f ≫ (ρ_ K).hom†
  isIsometry := inferInstance
  channel_eq := by
    have h : (partialTraceRight K (𝟙_ Qudit)).comp (ofIsometry (f ≫ (ρ_ K).hom†)) =
        ofIsometry f := by
      rw [ofIsometry_comp]
      have e : ((ofIsometry f).asHom ≫ (ρ_ (⟨K⟩ : CausalQudit)).inv) ≫ fst _ _ =
          (ofIsometry f).asHom := by simp [fst_def]
      rw [CausalQudit.fst_eq_partialTraceRight] at e
      exact e
    exact congrArg toSuperoperator h.symm

/-- If one output carries an isometric image of the input, a jointly available output
is independent of the input. Positive input dimension ensures that it admits a state. -/
theorem compatible_ofIsometry_iff (f : H ⟶ K) [IsIsometry f] (Γ : QuantumChannel H L)
    (hH : 0 < Module.finrank ℂ H.state) :
    CQM.Compatible (ofIsometry f).asHom Γ.asHom ↔ ∃ σ, Γ = replacement H σ := by
  constructor
  · intro h
    have hd := ((isometryDilation f).mutuallyDegradable_complementary (ofIsometry f).dilation hH).1
    obtain ⟨D, hD⟩ := hd.trans ((compatible_iff_complementary_isDegradableTo _ _).mp h)
    obtain ⟨σ, rfl⟩ := (Density.causalStateEquiv L).surjective D
    refine ⟨σ, hD.symm.trans ?_⟩
    change (isometryDilation f).complementary.asHom ≫ σ.toState = _
    rw [CausalQudit.eq_discard (isometryDilation f).complementary.asHom]
    rfl
  · rintro ⟨σ, rfl⟩
    exact CQM.compatible_toUnit_comp (ofIsometry f).asHom σ.toState

/-- A trace-one replacement acts as the identity on every operator precisely in dimension one. -/
lemma id_eq_replacement_iff (σ : Density H) :
    id H = replacement H σ ↔ Module.finrank ℂ H.state = 1 := by
  let tr := LinearMap.trace ℂ H.state
  have hs : Function.Surjective tr := fun z => ⟨z • σ.op, by
    simp [tr, show LinearMap.trace ℂ H.state σ.op = 1 from σ.trace_one]⟩
  constructor
  · intro h
    have hi : Function.Injective tr := by
      intro A B hab
      have he (T : Operator H) : T = T.trace • σ.op :=
        (congrArg (fun Γ => Γ.toSuperoperator T) h).trans (replacement_apply σ T)
      exact (he A).trans ((congrArg (· • σ.op) hab).trans (he B).symm)
    have hd := (LinearEquiv.ofBijective tr ⟨hi, hs⟩).finrank_eq
    rw [Module.finrank_linearMap, Module.finrank_self] at hd
    exact Nat.eq_one_of_mul_eq_one_left hd
  · intro h
    have hi : Function.Injective tr :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [Module.finrank_linearMap, Module.finrank_self, h, one_mul])).mpr hs
    apply QuantumChannel.ext
    apply LinearMap.ext
    intro A
    exact hi (((id H).tracePreserving A).trans ((replacement H σ).tracePreserving A).symm)

/-- A full finite-dimensional quantum system admits a universal broadcasting channel
exactly in dimensions zero and one. -/
theorem isBroadcastable_iff_finrank_le_one (H : Qudit) :
    CQM.IsBroadcastable (⟨H⟩ : CausalQudit) ↔ Module.finrank ℂ H.state ≤ 1 := by
  rw [CQM.isBroadcastable_iff_compatible_id]
  change CQM.Compatible (id H).asHom (id H).asHom ↔ _
  by_cases hH : 0 < Module.finrank ℂ H.state
  · have h := compatible_ofIsometry_iff (𝟙 H) (id H) hH
    rw [ofIsometry_id] at h
    rw [h]
    exact ⟨fun ⟨σ, hσ⟩ => ((id_eq_replacement_iff σ).mp hσ).le,
      fun hd => ⟨Density.maximallyMixed H hH.ne', (id_eq_replacement_iff _).mpr (by lia)⟩⟩
  · have hz : Module.finrank ℂ H.state = 0 := by lia
    exact iff_of_true ((compatible_self_iff_isAntidegradable _).mpr
      (isAntidegradable_of_finrank_eq_zero _ hz)) (by lia)

/-- A channel broadcasts the entire system exactly when both output marginals return
each input density state. -/
lemma broadcasts_id_iff_forall_density (d : QuantumChannel H (H ⊗ H)) :
    CQM.Broadcasts d.asHom (𝟙 (⟨H⟩ : CausalQudit)) ↔ ∀ ρ : Density H,
      (d.map ρ).partialTraceRight = ρ ∧ (d.map ρ).partialTraceLeft = ρ := by
  rw [CQM.broadcasts_id_iff_forall_state CausalQudit.isSeparator_tensorUnit]
  rw [← (Density.causalStateEquiv H).forall_congr_right]
  change (∀ ρ : Density H, CQM.Broadcasts d.asHom ρ.toState) ↔ _
  simp only [CQM.Broadcasts, ← Category.assoc, CausalQudit.fst_eq_partialTraceRight,
    CausalQudit.snd_eq_partialTraceLeft, Density.toState_comp, Density.toState_injective.eq_iff,
    map_partialTraceRight, map_partialTraceLeft]

/-- The finite-dimensional no-broadcasting theorem for arbitrary input density matrices. -/
theorem exists_broadcasting_channel_iff (H : Qudit) :
    (∃ d : QuantumChannel H (H ⊗ H), ∀ ρ : Density H,
      (d.map ρ).partialTraceRight = ρ ∧ (d.map ρ).partialTraceLeft = ρ) ↔
      Module.finrank ℂ H.state ≤ 1 := by
  rw [← isBroadcastable_iff_finrank_le_one, CQM.IsBroadcastable]
  exact exists_congr fun d => (broadcasts_id_iff_forall_density d).symm

end

end Qudit.QuantumChannel
