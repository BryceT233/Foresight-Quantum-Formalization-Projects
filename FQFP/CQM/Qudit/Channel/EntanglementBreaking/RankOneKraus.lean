/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.EntanglementBreaking.MeasurePrepare

/-!
# Rank-one Kraus representations of entanglement-breaking channels

Refining both positive factors in each measure-and-prepare branch gives Kraus operators
`ket u ∘ₗ bra v`. Discarding the zero operators leaves a finite family of exact rank one.
Conversely, the image line of each rank-one operator supplies the pure prepared state.
This is the rank-one criterion of Horodecki, Shor and Ruskai, Theorem 4 (D).
-/

@[expose] public section

open scoped ComplexOrder

namespace Qudit

noncomputable section

variable {H K : Qudit} {ι : Type*} [Fintype ι]

/-- Removing zero Kraus operators preserves their sum of conjugations. -/
lemma Superoperator.kraus_subtype_ne_zero (f : ι → H.state →ₗ[ℂ] K.state)
    [DecidablePred (fun i => f i ≠ 0)] :
    kraus (fun i : {i // f i ≠ 0} => f i.val) = kraus f := by
  classical
  unfold kraus
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => f i ≠ 0) (fun i => conjugate (f i))
  have hz (i : {i // ¬ f i ≠ 0}) : conjugate (f i.val) = 0 := by
    rw [not_not.mp i.property]
    ext A x
    simp [conjugate_apply]
  simpa only [hz, Finset.sum_const_zero, add_zero] using h

/-- Refining the effects and the prepared densities into outer squares gives a finite
Kraus family in which every operator has one-dimensional range. -/
theorem POVM.exists_rankOne_kraus_measurePrepare (M : POVM H ι) (σ : ι → Density K) :
    ∃ (n : ℕ) (f : Fin n → H.state →ₗ[ℂ] K.state),
      (M.measurePrepare σ).toSuperoperator = Superoperator.kraus f ∧
        ∀ i, Module.finrank ℂ (LinearMap.range (f i)) = 1 := by
  classical
  choose v hv using fun a => Operator.exists_sum_outer_of_isPositive (M.op a) (M.positive a)
  choose u hu using fun a => Operator.exists_sum_outer_of_isPositive (σ a).op (σ a).positive
  let β := ι × Fin (Module.finrank ℂ H.state) × Fin (Module.finrank ℂ K.state)
  let g (t : β) := ket (u t.1 t.2.2) ∘ₗ bra (v t.1 t.2.1)
  have hsum : (M.measurePrepare σ).toSuperoperator = Superoperator.kraus g := by
    ext A : 1
    rw [M.measurePrepare_apply]
    change _ = (∑ t : β, Superoperator.conjugate (g t)) A
    simp only [β, LinearMap.sum_apply, Fintype.sum_prod_type, g,
      Superoperator.conjugate_ket_comp_bra, hv, hu, Finset.sum_mul, Operator.trace, map_sum,
      Finset.sum_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  let e := (Fintype.equivFin {t // g t ≠ 0}).symm
  refine ⟨_, fun i => g (e i).val, hsum.trans ?_, fun i => ?_⟩
  · rw [← Superoperator.kraus_subtype_ne_zero g]
    exact (e.sum_comp (fun t => Superoperator.conjugate (g t.val))).symm
  · let t := (e i).val
    have hle := Submodule.finrank_mono (LinearMap.range_comp_le_range
      (bra (v t.1 t.2.1)) (ket (u t.1 t.2.2)))
    have hket := (ket (u t.1 t.2.2)).finrank_range_le
    rw [Module.finrank_self] at hket
    have hn : Module.finrank ℂ (LinearMap.range (g t)) ≠ 0 := fun h =>
      (e i).property (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h))
    change Module.finrank ℂ (LinearMap.range (g t)) = 1
    exact Nat.le_antisymm (hle.trans hket) (Nat.pos_of_ne_zero hn)

/-- A rank-one map factors through the unit ket spanning its range. -/
lemma exists_unitState_ket_comp_bra_of_finrank_range_eq_one (f : H.state →ₗ[ℂ] K.state)
    (hf : Module.finrank ℂ (LinearMap.range f) = 1) :
    ∃ u : UnitState K, f = ket u.val ∘ₗ bra (f.adjoint u.val) := by
  let b := stdOrthonormalBasis ℂ (LinearMap.range f)
  let j : Fin (Module.finrank ℂ (LinearMap.range f)) := ⟨0, by lia⟩
  let u : UnitState K := ⟨(b j).val, inner_self_eq_one_of_norm_eq_one (b.norm_eq_one j)⟩
  refine ⟨u, LinearMap.ext fun x => ?_⟩
  have hmem := LinearMap.mem_range_self f x
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hf (b j).property u.ne_zero] at hmem
  obtain ⟨c, hc : c • u.val = f x⟩ := Submodule.mem_span_singleton.mp hmem
  simp only [LinearMap.comp_apply, bra_apply, hom_ket_apply, LinearMap.adjoint_inner_left,
    ← hc, inner_smul_right, u.inner_self, mul_one]

namespace QuantumChannel

/-- Each Kraus operator of rank one supplies a POVM outcome and a pure prepared state,
with the same index as the given Kraus family. -/
theorem exists_measurePrepare_of_rankOne_kraus (Φ : QuantumChannel H K)
    (f : ι → H.state →ₗ[ℂ] K.state) (he : Φ.toSuperoperator = Superoperator.kraus f)
    (hr : ∀ i, Module.finrank ℂ (LinearMap.range (f i)) = 1) :
    ∃ (M : POVM H ι) (u : ι → UnitState K),
      (∀ i, M.op i = (f i).adjoint ∘ₗ f i) ∧
        Φ = M.measurePrepare (fun i => Density.pure (u i)) := by
  choose u hu using fun i => exists_unitState_ket_comp_bra_of_finrank_range_eq_one (f i) (hr i)
  let v (i : ι) := (f i).adjoint (u i).val
  have hs (i : ι) : (f i).adjoint ∘ₗ f i = Operator.outer (v i) (v i) := by
    ext x
    change (f i).adjoint (f i x) = _
    rw [congrArg (fun k : H.state →ₗ[ℂ] K.state => k x) (hu i)]
    simp only [LinearMap.comp_apply, hom_ket_apply, bra_apply, map_smul, Operator.outer_apply, v]
  let M : POVM H ι :=
    ⟨fun i => (f i).adjoint ∘ₗ f i, fun i => LinearMap.isPositive_adjoint_comp_self _,
      (Superoperator.isTracePreserving_kraus_iff f).mp (he ▸ Φ.tracePreserving)⟩
  refine ⟨M, u, fun _ => rfl, QuantumChannel.ext (LinearMap.ext fun A => ?_)⟩
  rw [he, M.measurePrepare_apply]
  change (∑ i, Superoperator.conjugate (f i)) A = _
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change Superoperator.conjugate (f i) A = Operator.trace (((f i).adjoint ∘ₗ f i) * A) • _
  rw [hs, hu i, Superoperator.conjugate_ket_comp_bra, Density.op_pure]

/-- A channel breaks entanglement exactly when it admits a finite Kraus representation
by operators of rank one. The empty family is allowed. -/
theorem isEntanglementBreaking_iff_exists_rankOne_kraus (Φ : QuantumChannel H K) :
    Φ.IsEntanglementBreaking ↔ ∃ (n : ℕ) (f : Fin n → H.state →ₗ[ℂ] K.state),
      Φ.toSuperoperator = Superoperator.kraus f ∧
        ∀ i, Module.finrank ℂ (LinearMap.range (f i)) = 1 := by
  constructor
  · intro h
    obtain ⟨α, _, M, σ, rfl⟩ := (isEntanglementBreaking_iff_exists_measurePrepare Φ).mp h
    exact M.exists_rankOne_kraus_measurePrepare σ
  · rintro ⟨n, f, he, hr⟩
    obtain ⟨M, u, _, rfl⟩ := Φ.exists_measurePrepare_of_rankOne_kraus f he hr
    exact M.isEntanglementBreaking_measurePrepare _

/-- A channel is represented by an empty Kraus family exactly in input dimension zero. -/
theorem eq_empty_kraus_iff [IsEmpty ι] (Φ : QuantumChannel H K)
    (f : ι → H.state →ₗ[ℂ] K.state) :
    Φ.toSuperoperator = Superoperator.kraus f ↔ Module.finrank ℂ H.state = 0 := by
  constructor
  · intro he
    have h := Φ.tracePreserving (1 : Operator H)
    simpa [he, Superoperator.kraus, Operator.trace, eq_comm] using h
  · intro hz
    have : Subsingleton H.state := Module.finrank_zero_iff.mp hz
    exact Subsingleton.elim _ _

/-- In an exact rank-one representation the index type is forced to be empty for zero
input, and trace preservation forces an index to exist for positive-dimensional input. -/
theorem isEmpty_iff_finrank_eq_zero_of_rankOne_kraus (Φ : QuantumChannel H K)
    (f : ι → H.state →ₗ[ℂ] K.state) (he : Φ.toSuperoperator = Superoperator.kraus f)
    (hr : ∀ i, Module.finrank ℂ (LinearMap.range (f i)) = 1) :
    IsEmpty ι ↔ Module.finrank ℂ H.state = 0 := by
  refine ⟨fun _ => (Φ.eq_empty_kraus_iff f).mp he, fun hz => ⟨fun i => ?_⟩⟩
  have h := (f i).finrank_range_le
  simp [hr i, hz] at h

end QuantumChannel

end

end Qudit
