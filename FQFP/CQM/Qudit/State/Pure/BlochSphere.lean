/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/

/-
Physlib reference for angular coordinates and oriented solid angle.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Pure/BlochSphere.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.UnitState
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Bloch sphere of a pure qubit

The angular coordinates and oriented solid angle follow physlib's
`QuantumInfo.States.Pure.BlochSphere`. A normalized qubit determines a point
on this sphere in the computational basis. The dot product of two such points
determines the squared modulus of the transition amplitude.
-/

@[expose] public noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Qudit

/-- The unit sphere in three-dimensional real Euclidean space. -/
abbrev BlochSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

namespace BlochSphere

/-- Cartesian coordinates at polar angle `α` and azimuth `θ`. -/
def blochVecRaw (α θ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin α * Real.cos θ, Real.sin α * Real.sin θ, Real.cos α]

/-- The Cartesian vector in spherical coordinates has length one. -/
lemma blochVecRaw_norm (α θ : ℝ) :
    Real.sqrt ((blochVecRaw α θ 0) ^ 2 + (blochVecRaw α θ 1) ^ 2 +
      (blochVecRaw α θ 2) ^ 2) = 1 := by
  simp [blochVecRaw, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, Real.sin_sq_add_cos_sq]

/-- The point with polar angle `α` and azimuth `θ`. -/
def blochPoint (α θ : ℝ) : BlochSphere :=
  ⟨(WithLp.equiv 2 _).symm (blochVecRaw α θ), by
    simpa [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_three] using
      blochVecRaw_norm α θ⟩

/-- The underlying Euclidean vector of an angularly parameterized point. -/
lemma blochPoint_val (α θ : ℝ) :
    (blochPoint α θ).val = (WithLp.equiv 2 _).symm (blochVecRaw α θ) := rfl

/-- The oriented solid angle given by twice the principal argument of the
dot- and triple-product expression. This uses `Complex.arg 0 = 0` at singular triples. -/
def solidAngle (p q r : BlochSphere) : ℝ :=
  let den := 1 + p.val ⬝ᵥ q.val + q.val ⬝ᵥ r.val + r.val ⬝ᵥ p.val
  let num := p.val ⬝ᵥ q.val ⨯₃ r.val
  2 * Complex.arg ⟨den, num⟩

/-- Dot product in terms of polar angles and the difference of azimuths. -/
lemma dot_blochPoint (α₁ θ₁ α₂ θ₂ : ℝ) :
    (blochPoint α₁ θ₁).val ⬝ᵥ (blochPoint α₂ θ₂).val =
      Real.sin α₁ * Real.sin α₂ * Real.cos (θ₂ - θ₁) + Real.cos α₁ * Real.cos α₂ := by
  simp [blochPoint_val, dotProduct, blochVecRaw, Fin.sum_univ_three, Real.cos_sub]
  ring

end BlochSphere

namespace UnitState

/-- The three Cartesian Bloch coordinates of a vector of qubit amplitudes. -/
def blochCoords (v : EuclideanSpace ℂ (Fin 2)) : Fin 3 → ℝ :=
  let z := conj (v 0) * v 1
  ![2 * z.re, 2 * z.im, Complex.normSq (v 0) - Complex.normSq (v 1)]

private lemma dot_blochCoords (u v : EuclideanSpace ℂ (Fin 2)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    blochCoords u ⬝ᵥ blochCoords v = 2 * ‖inner ℂ u v‖ ^ 2 - 1 := by
  have normalized (w : EuclideanSpace ℂ (Fin 2)) (hw : ‖w‖ = 1) :
      Complex.normSq (w 0) + Complex.normSq (w 1) = 1 := by
    simpa only [Fin.sum_univ_two, Complex.sq_norm, hw, one_pow] using
      (EuclideanSpace.norm_sq_eq w).symm
  have h := congrArg₂ (· * ·) (normalized u hu) (normalized v hv)
  rw [one_mul] at h
  rw [← h, PiLp.inner_apply]
  simp [blochCoords, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, RCLike.inner_apply,
    Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

private lemma dot_blochCoords_unitState (u v : UnitState Qubit) :
    blochCoords u.val ⬝ᵥ blochCoords v.val = 2 * ‖inner ℂ u.val v.val‖ ^ 2 - 1 :=
  dot_blochCoords u.val v.val u.norm_eq_one v.norm_eq_one

/-- The Bloch point of a normalized qubit in the computational basis. -/
def blochVector (v : UnitState Qubit) : BlochSphere :=
  ⟨(WithLp.equiv 2 _).symm (blochCoords v.val), by
    rw [Metric.mem_sphere, dist_zero_right, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
      EuclideanSpace.real_norm_sq_eq, one_pow]
    simpa [dotProduct, sq, v.inner_self, show (2 : ℝ) - 1 = 1 by norm_num] using
      dot_blochCoords_unitState v v⟩

/-- The squared transition amplitude is one half of one plus the Bloch dot product. -/
theorem norm_inner_sq_eq_bloch (u v : UnitState Qubit) :
    ‖inner ℂ u.val v.val‖ ^ 2 = (1 + u.blochVector.val ⬝ᵥ v.blochVector.val) / 2 := by
  change _ = (1 + blochCoords u.val ⬝ᵥ blochCoords v.val) / 2
  rw [dot_blochCoords_unitState]
  ring

/-- Two unit qubits have the same Bloch point exactly when their transition probability is one. -/
theorem blochVector_eq_iff (u v : UnitState Qubit) :
    u.blochVector = v.blochVector ↔ ‖inner ℂ u.val v.val‖ ^ 2 = 1 := by
  have norm_one (p : BlochSphere) : ‖p.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  rw [Subtype.ext_iff, ← inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ)
    (norm_one u.blochVector) (norm_one v.blochVector), norm_inner_sq_eq_bloch]
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, dotProduct]
  constructor <;> intro h <;> linarith

/-- Multiplying a qubit by a global phase preserves its Bloch point. -/
theorem blochVector_phase (v : UnitState Qubit) (c : ℂ) (hc : ‖c‖ = 1) :
    (v.phase c hc).blochVector = v.blochVector := by
  rw [blochVector_eq_iff]
  simp [inner_smul_left, hc]

end UnitState

end Qudit
