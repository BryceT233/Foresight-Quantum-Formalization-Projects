/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity
public import FQFP.CQM.Qudit.Entropy.VonNeumann.Composite
public import FQFP.CQM.Qudit.Entropy.VonNeumann.Exchange
public import FQFP.CQM.Qudit.State.Spectral.Tensor

/-!
# Spectral typicality for memoryless channel coding

The variance of spectral surprisal is additive under independent tensor products.
Chebyshev's inequality then controls the weight outside the typical subspace of a block.
All logarithms and the typicality width are in nats. The block index counts the sites
following the first.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace Qudit

variable {H K : Qudit}

namespace Density

/-- The independent input on a block of `n + 1` sites. -/
def tensorPower (ρ : Density H) : (n : ℕ) → Density (Qudit.tensorPower H n)
  | 0 => ρ
  | n + 1 => ρ.tensor (ρ.tensorPower n)

/-- Spectral entropy variance in squared nats. Terms at zero eigenvalues have zero weight. -/
def entropyVariance (ρ : Density H) : ℝ :=
  ∑ i, ρ.eigenvalue i * (-Real.log (ρ.eigenvalue i) - ρ.vonNeumannEntropy) ^ 2

private lemma sum_centered_surprisal (ρ : Density H) :
    ∑ i, ρ.eigenvalue i * (-Real.log (ρ.eigenvalue i) - ρ.vonNeumannEntropy) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_eigenvalue, one_mul,
    vonNeumannEntropy_eq_sum, Real.negMulLog, mul_neg, neg_mul, sub_self]

/-- Independent systems have additive entropy variance, including for singular states. -/
theorem entropyVariance_tensor (ρ : Density H) (σ : Density K) :
    (ρ.tensor σ).entropyVariance = ρ.entropyVariance + σ.entropyVariance := by
  let a i := -Real.log (ρ.eigenvalue i) - ρ.vonNeumannEntropy
  let b j := -Real.log (σ.eigenvalue j) - σ.vonNeumannEntropy
  obtain ⟨e, he⟩ := ρ.exists_equiv_eigenvalue_tensor σ
  unfold entropyVariance
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [he, vonNeumannEntropy_tensor]
  have split i j :
      ρ.eigenvalue i * σ.eigenvalue j *
        (-Real.log (ρ.eigenvalue i * σ.eigenvalue j) -
          (ρ.vonNeumannEntropy + σ.vonNeumannEntropy)) ^ 2 =
      (ρ.eigenvalue i * a i ^ 2) * σ.eigenvalue j +
        (2 * ρ.eigenvalue i * a i) * (σ.eigenvalue j * b j) +
        ρ.eigenvalue i * (σ.eigenvalue j * b j ^ 2) := by
    by_cases hp : ρ.eigenvalue i = 0
    · simp [hp]
    by_cases hq : σ.eigenvalue j = 0
    · simp [hq]
    rw [Real.log_mul hp hq]
    dsimp [a, b]
    ring
  simp only [split, Finset.sum_add_distrib, ← Finset.mul_sum, σ.sum_eigenvalue, mul_one,
    show ∑ j, σ.eigenvalue j * b j = 0 from σ.sum_centered_surprisal, mul_zero, add_zero,
    ← Finset.sum_mul, ρ.sum_eigenvalue, one_mul]
  rfl

/-- Independent copies have extensive entropy. -/
theorem vonNeumannEntropy_tensorPower (ρ : Density H) (n : ℕ) :
    (ρ.tensorPower n).vonNeumannEntropy = (n + 1 : ℝ) * ρ.vonNeumannEntropy := by
  induction n with
  | zero => change ρ.vonNeumannEntropy = _; norm_num
  | succ n ih =>
    change (ρ.tensor (ρ.tensorPower n)).vonNeumannEntropy = _
    rw [vonNeumannEntropy_tensor, ih, Nat.cast_succ]
    ring

/-- The variance of the total surprisal grows linearly in the number of copies. -/
theorem entropyVariance_tensorPower (ρ : Density H) (n : ℕ) :
    (ρ.tensorPower n).entropyVariance = (n + 1 : ℝ) * ρ.entropyVariance := by
  induction n with
  | zero => change ρ.entropyVariance = _; norm_num
  | succ n ih =>
    change (ρ.tensor (ρ.tensorPower n)).entropyVariance = _
    rw [entropyVariance_tensor, ih, Nat.cast_succ]
    ring

/-- Eigenvectors of positive weight whose total surprisal lies within the specified width
of the state's entropy. The index retains multiplicities of repeated eigenvalues. -/
def typicalIndices (ρ : Density H) (width : ℝ) : Finset (Fin (Module.finrank ℂ H.state)) :=
  Finset.univ.filter fun i => 0 < ρ.eigenvalue i ∧
    |-Real.log (ρ.eigenvalue i) - ρ.vonNeumannEntropy| ≤ width

/-- Spectral Chebyshev inequality, expressed as the probability of the atypical subspace. -/
theorem one_sub_typical_weight_le (ρ : Density H) {w : ℝ} (hw : 0 < w) :
    1 - ∑ i ∈ ρ.typicalIndices w, ρ.eigenvalue i ≤ ρ.entropyVariance / w ^ 2 := by
  classical
  let t := ρ.typicalIndices w
  have he i (hi : i ∈ tᶜ) : ρ.eigenvalue i * w ^ 2 ≤
      ρ.eigenvalue i * (-Real.log (ρ.eigenvalue i) - ρ.vonNeumannEntropy) ^ 2 := by
    rcases (ρ.eigenvalue_nonneg i).eq_or_lt with hz | hp
    · simp [← hz]
    have hbad := Finset.mem_compl.mp hi
    simp only [t, typicalIndices, Finset.mem_filter, Finset.mem_univ, true_and, hp, not_le] at hbad
    exact mul_le_mul_of_nonneg_left ((sq_le_sq).mpr (by rw [abs_of_pos hw]; exact hbad.le))
      hp.le
  have hm := Finset.sum_add_sum_compl t ρ.eigenvalue
  rw [ρ.sum_eigenvalue] at hm
  apply (le_div_iff₀ (sq_pos_of_pos hw)).mpr
  change (1 - ∑ i ∈ t, ρ.eigenvalue i) * w ^ 2 ≤ _
  rw [show 1 - ∑ i ∈ t, ρ.eigenvalue i = ∑ i ∈ tᶜ, ρ.eigenvalue i by linarith,
    Finset.sum_mul]
  exact (Finset.sum_le_sum he).trans (Finset.sum_le_univ_sum_of_nonneg fun i =>
    mul_nonneg (ρ.eigenvalue_nonneg i) (sq_nonneg _))

/-- On a block of `n + 1` copies the probability outside the typical subspace is at most
`V / ((n + 1) δ²)`, for any fixed positive per-site width `δ`. -/
theorem one_sub_typical_weight_tensorPower_le (ρ : Density H) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    1 - ∑ i ∈ (ρ.tensorPower n).typicalIndices ((n + 1 : ℝ) * δ), (ρ.tensorPower n).eigenvalue i ≤
      ρ.entropyVariance / ((n + 1 : ℝ) * δ ^ 2) := by
  apply ((ρ.tensorPower n).one_sub_typical_weight_le (mul_pos (by positivity) hδ)).trans_eq
  rw [entropyVariance_tensorPower]
  field_simp

/-- The dimension of a typical subspace is bounded by the exponential of entropy plus width. -/
theorem card_typicalIndices_le (ρ : Density H) (w : ℝ) :
    ((ρ.typicalIndices w).card : ℝ) ≤ Real.exp (ρ.vonNeumannEntropy + w) := by
  have hlo i (hi : i ∈ ρ.typicalIndices w) :
      Real.exp (-(ρ.vonNeumannEntropy + w)) ≤ ρ.eigenvalue i := by
    obtain ⟨hp, ha⟩ := (Finset.mem_filter.mp hi).2
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp ha).2])
  have hb := (Finset.sum_le_sum hlo).trans (Finset.sum_le_univ_sum_of_nonneg ρ.eigenvalue_nonneg)
  rw [ρ.sum_eigenvalue, Finset.sum_const, nsmul_eq_mul, Real.exp_neg, ← div_eq_mul_inv] at hb
  simpa using (div_le_iff₀ (Real.exp_pos _)).mp hb

/-- A typical eigenvalue is at most the exponential of minus entropy plus width. -/
theorem eigenvalue_le_of_mem_typicalIndices (ρ : Density H) {w : ℝ} {i}
    (hi : i ∈ ρ.typicalIndices w) : ρ.eigenvalue i ≤ Real.exp (-ρ.vonNeumannEntropy + w) := by
  obtain ⟨hp, ha⟩ := (Finset.mem_filter.mp hi).2
  rw [← Real.exp_log hp]
  exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp ha).1])

/-- The typical spectral projector keeps exactly the selected eigenvectors. -/
def typicalProjection (ρ : Density H) (w : ℝ) : Operator H :=
  ρ.spectralMap fun p => if 0 < p ∧ |-Real.log p - ρ.vonNeumannEntropy| ≤ w then 1 else 0

/-- The typical test acts diagonally on the spectral basis, including the kernel. -/
lemma typicalProjection_apply_eigenbasis (ρ : Density H) (w : ℝ) (i) :
    ρ.typicalProjection w (ρ.eigenbasis i) =
      if i ∈ ρ.typicalIndices w then ρ.eigenbasis i else 0 := by
  rw [typicalProjection, spectralMap_apply_eigenbasis]
  by_cases h : 0 < ρ.eigenvalue i ∧ |-Real.log (ρ.eigenvalue i) - ρ.vonNeumannEntropy| ≤ w <;>
    simp [typicalIndices, h]

/-- The typical test is a projective measurement. -/
theorem isStarProjection_typicalProjection (ρ : Density H) (w : ℝ) :
    IsStarProjection (ρ.typicalProjection w) := by
  refine ⟨?_, ρ.adjoint_spectralMap _⟩
  apply ρ.eigenbasis.toBasis.ext
  intro i
  change ρ.typicalProjection w (ρ.typicalProjection w (ρ.eigenbasis i)) =
    ρ.typicalProjection w (ρ.eigenbasis i)
  by_cases hi : i ∈ ρ.typicalIndices w <;> simp [typicalProjection_apply_eigenbasis, hi]

/-- The dimension of the physical typical register is bounded by its spectral count. -/
lemma finrank_range_typicalProjection_le (ρ : Density H) (w : ℝ) :
    Module.finrank ℂ (LinearMap.range (ρ.typicalProjection w)) ≤ (ρ.typicalIndices w).card := by
  classical
  let s := (ρ.typicalIndices w).image ρ.eigenbasis
  have hr : LinearMap.range (ρ.typicalProjection w) ≤ Submodule.span ℂ (s : Set H.state) := by
    rintro _ ⟨v, rfl⟩
    rw [← ρ.eigenbasis.sum_repr' v, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, ρ.typicalProjection_apply_eigenbasis]
    apply Submodule.smul_mem
    split_ifs with hi
    · exact Submodule.subset_span (Finset.mem_image_of_mem _ hi)
    · exact Submodule.zero_mem _
  exact (Submodule.finrank_mono hr).trans
    ((finrank_span_finset_le_card (R := ℂ) s).trans Finset.card_image_le)

/-- The trace of the squared compressed output uses only retained eigenvalues. -/
lemma re_trace_sq_conjugate_typicalProjection (ρ : Density H) (w : ℝ) :
    ((Superoperator.conjugate (ρ.typicalProjection w) ρ.op) ^ 2).trace.re =
      ∑ i ∈ ρ.typicalIndices w, ρ.eigenvalue i ^ 2 := by
  have hP : (ρ.typicalProjection w).adjoint = ρ.typicalProjection w :=
    (ρ.isStarProjection_typicalProjection w).isSelfAdjoint
  rw [Operator.trace, LinearMap.trace_eq_sum_inner _ ρ.eigenbasis, Complex.re_sum]
  have hs : ρ.typicalIndices w = Finset.univ.filter (· ∈ ρ.typicalIndices w) := by ext; simp
  conv_rhs => rw [hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Superoperator.conjugate_apply, hP, sq, mul_apply_eq_comp, LinearMap.coe_comp,
    Function.comp_apply, ρ.typicalProjection_apply_eigenbasis]
  by_cases hi : i ∈ ρ.typicalIndices w
  · simp only [hi, ↓reduceIte, ρ.apply_eigenbasis, map_smul, ρ.typicalProjection_apply_eigenbasis,
      inner_smul_right, ρ.eigenbasis.inner_eq_one, mul_one, ← Complex.ofReal_mul, Complex.ofReal_re]
  · simp only [hi, ↓reduceIte, map_zero, inner_zero_right, Complex.zero_re]

/-- The probability of the typical outcome is its total spectral weight. -/
lemma expectation_typicalProjection (ρ : Density H) (w : ℝ) :
    ρ.expectation (ρ.typicalProjection w) = ∑ i ∈ ρ.typicalIndices w, ρ.eigenvalue i := by
  simp [typicalProjection, expectation_spectralMap_self, typicalIndices, Finset.sum_filter,
    mul_ite]

/-- The squared spectral weights retained by the typical projection have exponentially
small sum when the entropy exceeds the width. -/
theorem sum_sq_typical_eigenvalues_le (ρ : Density H) (w : ℝ) :
    ∑ i ∈ ρ.typicalIndices w, ρ.eigenvalue i ^ 2 ≤ Real.exp (-ρ.vonNeumannEntropy + w) := by
  calc
    _ ≤ ∑ i ∈ ρ.typicalIndices w, ρ.eigenvalue i * Real.exp (-ρ.vonNeumannEntropy + w) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [sq]
      exact mul_le_mul_of_nonneg_left (ρ.eigenvalue_le_of_mem_typicalIndices hi)
        (ρ.eigenvalue_nonneg i)
    _ ≤ 1 * Real.exp (-ρ.vonNeumannEntropy + w) := by
      rw [← Finset.sum_mul, ← ρ.sum_eigenvalue]
      exact mul_le_mul_of_nonneg_right (Finset.sum_le_univ_sum_of_nonneg ρ.eigenvalue_nonneg)
        (Real.exp_pos _).le
    _ = _ := one_mul _

end Density

/-- Parallel copies of a channel on an independent input produce independent outputs. -/
theorem QuantumChannel.map_tensorPower (Φ : QuantumChannel H K) (ρ : Density H) (n : ℕ) :
    (Φ.tensorPower n).map (ρ.tensorPower n) = (Φ.map ρ).tensorPower n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Φ.tensor (Φ.tensorPower n)).map (ρ.tensor (ρ.tensorPower n)) = _
    rw [QuantumChannel.map_tensor, ih]
    rfl

/-- For a candidate code of dimension at most `2^(m R)`, the typical environment dimension
times the retained output purity gives the coherent-information exponent. Here `m = n + 1`. -/
theorem QuantumChannel.typical_rank_mul_purity_bound (Φ : QuantumChannel H K) (ρ : Density H)
    (n k : ℕ) (R δ : ℝ) (hk : (k : ℝ) ≤ Real.exp ((n + 1 : ℝ) * (R * Real.log 2))) :
    let m : ℝ := n + 1
    let B := (Φ.map ρ).tensorPower n
    let E := (Φ.complementary.map ρ).tensorPower n
    (k : ℝ) * (E.typicalIndices (m * δ)).card * (∑ i ∈ B.typicalIndices (m * δ), B.eigenvalue i ^ 2)
      ≤ Real.exp (m * (R * Real.log 2 - Φ.coherentInfo ρ + 2 * δ)) := by
  intro m B E
  calc
    _ ≤ Real.exp (m * (R * Real.log 2)) * Real.exp (E.vonNeumannEntropy + m * δ) *
        Real.exp (-B.vonNeumannEntropy + m * δ) := by
      apply mul_le_mul _ (B.sum_sq_typical_eigenvalues_le _) (by positivity) (by positivity)
      exact mul_le_mul hk (E.card_typicalIndices_le _) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, coherentInfo_eq_sub_entropyExchange,
        entropyExchange_eq_complementary]
      simp only [E, B, Density.vonNeumannEntropy_tensorPower, m]
      congr 1
      ring

/-- Below the coherent-information rate the product of code dimension, typical environment
dimension, and typical output purity tends to zero for a positive typicality width. -/
theorem QuantumChannel.tendsto_typical_rank_mul_purity_zero (Φ : QuantumChannel H K)
    (ρ : Density H) {R : ℝ} (hR : R < Φ.coherentInfo ρ / Real.log 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ → ℕ,
      (∀ n, (k n : ℝ) ≤ Real.exp ((n + 1 : ℝ) * (R * Real.log 2))) →
      Filter.Tendsto (fun n : ℕ =>
        let m : ℝ := n + 1
        let B := (Φ.map ρ).tensorPower n
        let E := (Φ.complementary.map ρ).tensorPower n
        (k n : ℝ) * (E.typicalIndices (m * δ)).card *
          (∑ i ∈ B.typicalIndices (m * δ), B.eigenvalue i ^ 2)) Filter.atTop (nhds 0) := by
  let δ := (Φ.coherentInfo ρ - R * Real.log 2) / 4
  have hgap := (lt_div_iff₀ (by positivity : 0 < Real.log 2)).mp hR
  refine ⟨δ, by dsimp [δ]; linarith, fun k hk => ?_⟩
  apply squeeze_zero (fun n => by positivity)
    (fun n => Φ.typical_rank_mul_purity_bound ρ n (k n) R δ (hk n))
  apply Real.tendsto_exp_atBot.comp
  apply (Filter.tendsto_mul_const_atBot_of_neg (show R * Real.log 2 - Φ.coherentInfo ρ + 2 * δ < 0
    by dsimp [δ]; linarith)).mpr
  exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

end Qudit
