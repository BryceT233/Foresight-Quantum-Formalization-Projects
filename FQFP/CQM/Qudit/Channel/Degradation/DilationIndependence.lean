/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Degradation.IsometryRecovery
public import FQFP.CQM.Qudit.Channel.Dilation.StinespringUniqueness

/-!
# Degradability is independent of the Stinespring dilation

For a channel with positive-dimensional input, all Stinespring complements are equivalent
under CPTP postprocessing. Both degradability and antidegradability can consequently be tested
using any dilation. The general directional theorem also covers zero-dimensional systems:
a simulation exists precisely when there exists a channel between the environments.
-/

@[expose] public section

open CategoryTheory DaggerCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K E F : Qudit} {Φ : QuantumChannel H K}

/-- A channel with a positive-dimensional input has a positive-dimensional output. -/
lemma finrank_pos_of_input (Γ : QuantumChannel E F) (h : 0 < Module.finrank ℂ E.state) :
    0 < Module.finrank ℂ F.state := by
  by_contra! hz
  have : Subsingleton F.state := Module.finrank_zero_iff.mp (Nat.eq_zero_of_le_zero hz)
  exact isEmptyElim (Γ.map (Density.maximallyMixed E h.ne'))

/-- A channel exists exactly when a positive-dimensional input has a positive-dimensional
output. From a zero-dimensional input the unique linear map is isometric. -/
lemma nonempty_iff_finrank_pos (E F : Qudit) :
    Nonempty (QuantumChannel E F) ↔
      (0 < Module.finrank ℂ E.state → 0 < Module.finrank ℂ F.state) := by
  refine ⟨fun ⟨Γ⟩ => Γ.finrank_pos_of_input, fun h => ?_⟩
  by_cases hE : 0 < Module.finrank ℂ E.state
  · exact ⟨replacement E (Density.maximallyMixed F (h hE).ne')⟩
  · have hd : Module.finrank ℂ E.state ≤ Module.finrank ℂ F.state := by lia
    exact ⟨ofIsometry (ofLinearIsometry (LinearIsometry.ofFinrankLE hd))⟩

namespace Dilation

/-- One Stinespring complement degrades to another exactly when a channel from the first
environment to the second exists. This includes the case of a zero-dimensional input. -/
theorem isDegradableTo_complementary_iff (d : Φ.Dilation E) (d' : Φ.Dilation F) :
    d.complementary.IsDegradableTo d'.complementary ↔ Nonempty (QuantumChannel E F) := by
  refine ⟨fun ⟨D, _⟩ => ⟨D⟩, fun ⟨Γ⟩ => ?_⟩
  rcases le_total (Module.finrank ℂ E.state) (Module.finrank ℂ F.state) with h | h
  · obtain ⟨J, hJ, he⟩ := d.exists_isometry d' h
    exact ⟨ofIsometry J, (d.complementary_eq_comp_of_intertwines d' J he).symm⟩
  · obtain ⟨J, hJ, he⟩ := d'.exists_isometry d h
    obtain ⟨D, hD⟩ := exists_leftInverse_ofIsometry J Γ
    refine ⟨D, ?_⟩
    rw [d'.complementary_eq_comp_of_intertwines d J he, ← comp_assoc, hD, id_comp]

/-- Two Stinespring complements are mutually degradable exactly when their environments
are both positive-dimensional or both zero-dimensional. -/
theorem mutuallyDegradable_complementary_iff (d : Φ.Dilation E) (d' : Φ.Dilation F) :
    (d.complementary.IsDegradableTo d'.complementary ∧
      d'.complementary.IsDegradableTo d.complementary) ↔
      (0 < Module.finrank ℂ E.state ↔ 0 < Module.finrank ℂ F.state) := by
  rw [d.isDegradableTo_complementary_iff, d'.isDegradableTo_complementary_iff,
    nonempty_iff_finrank_pos, nonempty_iff_finrank_pos]
  exact ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- Replacing the dilation preserves both postprocessing tests whenever the two environments
agree on whether they have positive dimension. This also applies to zero-dimensional inputs. -/
theorem degradation_iffs (d : Φ.Dilation E) (d' : Φ.Dilation F)
    (hdim : 0 < Module.finrank ℂ E.state ↔ 0 < Module.finrank ℂ F.state) :
    (Φ.IsDegradableTo d.complementary ↔ Φ.IsDegradableTo d'.complementary) ∧
      (d.complementary.IsDegradableTo Φ ↔ d'.complementary.IsDegradableTo Φ) := by
  obtain ⟨h, h'⟩ := (d.mutuallyDegradable_complementary_iff d').mpr hdim
  exact ⟨⟨fun hΦ => hΦ.trans h, fun hΦ => hΦ.trans h'⟩,
    ⟨fun hΦ => h'.trans hΦ, fun hΦ => h.trans hΦ⟩⟩

/-- Any two dilations of a channel with nontrivial input have mutually degradable complements. -/
theorem mutuallyDegradable_complementary (d : Φ.Dilation E) (d' : Φ.Dilation F)
    (h : 0 < Module.finrank ℂ H.state) :
    d.complementary.IsDegradableTo d'.complementary ∧
      d'.complementary.IsDegradableTo d.complementary := by
  apply (d.mutuallyDegradable_complementary_iff d').mpr
  exact ⟨fun _ => d'.complementary.finrank_pos_of_input h,
    fun _ => d.complementary.finrank_pos_of_input h⟩

/-- Degradability can be checked against the complement of any explicit dilation. -/
theorem isDegradable_iff (d : Φ.Dilation E) (hH : 0 < Module.finrank ℂ H.state) :
    Φ.IsDegradable ↔ Φ.IsDegradableTo d.complementary := by
  obtain ⟨h, h'⟩ := Φ.dilation.mutuallyDegradable_complementary d hH
  exact ⟨fun hΦ => hΦ.trans h, fun hΦ => hΦ.trans h'⟩

/-- Antidegradability can be checked against the complement of any explicit dilation. -/
theorem isAntidegradable_iff (d : Φ.Dilation E) (hH : 0 < Module.finrank ℂ H.state) :
    Φ.IsAntidegradable ↔ d.complementary.IsDegradableTo Φ := by
  obtain ⟨h, h'⟩ := Φ.dilation.mutuallyDegradable_complementary d hH
  exact ⟨fun hΦ => h'.trans hΦ, fun hΦ => h.trans hΦ⟩

end Dilation

end

end Qudit.QuantumChannel
