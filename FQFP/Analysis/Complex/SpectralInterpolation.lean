/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Three-lines interpolation for finite spectral sums

We use the complex power `r^(z/2)` on positive eigenvalues and the identically zero
holomorphic function on zero eigenvalues. Squared Euclidean norms therefore interpolate
without taking a logarithm of a zero eigenvalue.
-/

@[expose] public section

namespace Complex.HadamardThreeLines

noncomputable section

/-- The half power used in strip interpolation, extended by zero on the kernel. -/
def spectralFactor (r : ℝ) (z : ℂ) : ℂ :=
  if r = 0 then 0 else Complex.exp ((Real.log r : ℂ) * z / 2)

lemma norm_sq_spectralFactor {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖spectralFactor r z‖ ^ 2 = if r = 0 then 0 else r ^ z.re := by
  split_ifs with h
  · simp [spectralFactor, h]
  rw [spectralFactor, ite_eq_right h, Complex.norm_exp, ← Real.exp_nat_mul,
    Real.rpow_def_of_pos (hr.lt_of_ne' h)]
  congr 1
  simp [Complex.mul_re, Complex.div_ofNat_re]
  ring

lemma norm_sq_spectralFactor_of_re_ne_zero {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : z.re ≠ 0) :
    ‖spectralFactor r z‖ ^ 2 = r ^ z.re := by
  rw [norm_sq_spectralFactor hr]
  split_ifs with h
  · simp [h, Real.zero_rpow hz]
  · rfl

lemma norm_sq_spectralFactor_le_one {r : ℝ} (hr : 0 ≤ r) {z : ℂ} (hz : z.re = 0) :
    ‖spectralFactor r z‖ ^ 2 ≤ 1 := by
  rw [norm_sq_spectralFactor hr, hz, Real.rpow_zero]
  split_ifs <;> norm_num

lemma spectralFactor_ofReal {r t : ℝ} (hr : 0 ≤ r) (ht : t ≠ 0) :
    spectralFactor r (t : ℂ) = (↑(r ^ (t / 2)) : ℂ) := by
  by_cases h : r = 0
  · simp [spectralFactor, h, Real.zero_rpow (by simpa using ht : t / 2 ≠ 0)]
  rw [spectralFactor, ite_eq_right h, Real.rpow_def_of_pos (hr.lt_of_ne' h), Complex.ofReal_exp]
  push_cast
  ring_nf

/-- An entire scalar function bounded on the closed unit strip. -/
def StripBoundedEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ M : ℝ, ∀ z ∈ verticalClosedStrip 0 1, ‖f z‖ ≤ M

namespace StripBoundedEntire

lemma const (c : ℂ) : StripBoundedEntire (fun _ => c) :=
  ⟨differentiable_const _, ‖c‖, fun _ _ => le_rfl⟩

lemma mul {f g : ℂ → ℂ} (hf : StripBoundedEntire f) (hg : StripBoundedEntire g) :
    StripBoundedEntire (fun z => f z * g z) := by
  obtain ⟨hd, M, hM⟩ := hf
  obtain ⟨he, N, hN⟩ := hg
  refine ⟨hd.mul he, M * N, fun z hz => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hM z hz) (hN z hz) (norm_nonneg _) ((norm_nonneg _).trans (hM z hz))

lemma sum {ι : Type*} [Fintype ι] {f : ι → ℂ → ℂ} (hf : ∀ i, StripBoundedEntire (f i)) :
    StripBoundedEntire (fun z => ∑ i, f i z) := by
  choose M hM using fun i => (hf i).2
  exact ⟨Differentiable.fun_sum fun i _ => (hf i).1, ∑ i, M i,
    fun z hz => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hM i z hz)⟩

lemma spectralFactor_affine (r a d : ℝ) :
    StripBoundedEntire (fun z => spectralFactor r (a + d * z)) := by
  by_cases h : r = 0
  · simpa [spectralFactor, h] using const 0
  simp only [spectralFactor, ite_eq_right h]
  constructor
  · fun_prop
  · refine ⟨Real.exp (|Real.log r| * (|a| + |d|) / 2), fun z hz => ?_⟩
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.ofReal_re, Complex.add_re]
    have ht : |z.re| ≤ 1 := (abs_of_nonneg hz.1).le.trans hz.2
    have hb : |a + d * z.re| ≤ |a| + |d| := by
      refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left ht (abs_nonneg d)
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left hb (abs_nonneg _)))) (by norm_num)

end StripBoundedEntire

/-- Squared norm form of Hadamard's three-lines theorem for a finite family of entries. -/
lemma sum_norm_sq_interpolate {ι : Type*} [Fintype ι] {f : ι → ℂ → ℂ}
    (hf : ∀ i, StripBoundedEntire (f i)) {A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h₀ : ∀ z : ℂ, z.re = 0 → ∑ i, ‖f i z‖ ^ 2 ≤ A)
    (h₁ : ∀ z : ℂ, z.re = 1 → ∑ i, ‖f i z‖ ^ 2 ≤ B) (ht : t ∈ Set.Icc 0 1) :
    ∑ i, ‖f i t‖ ^ 2 ≤ A ^ (1 - t) * B ^ t := by
  let F (z : ℂ) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => f i z)
  have hn (z : ℂ) : ‖F z‖ ^ 2 = ∑ i, ‖f i z‖ ^ 2 := EuclideanSpace.norm_sq_eq _
  have hd : Differentiable ℂ F := differentiable_euclidean.mpr (fun i => (hf i).1)
  choose M hM using fun i => (hf i).2
  have hb : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
    refine ⟨Real.sqrt (∑ i, M i ^ 2), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    apply Real.le_sqrt_of_sq_le
    rw [Function.comp_apply, hn]
    exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hM i z hz) 2
  have h := norm_le_interp_of_mem_verticalClosedStrip₀₁' F (z := (t : ℂ)) ht
    hd.diffContOnCl hb (a := Real.sqrt A) (b := Real.sqrt B)
    (fun z hz => Real.le_sqrt_of_sq_le ((hn z).le.trans (h₀ z hz)))
    (fun z hz => Real.le_sqrt_of_sq_le ((hn z).le.trans (h₁ z hz)))
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [hn, mul_pow] at hs
  have hp (x y : ℝ) (hx : 0 ≤ x) : (Real.sqrt x ^ y) ^ 2 = x ^ y := by
    rw [← Real.rpow_mul_natCast (Real.sqrt_nonneg _), mul_comm y,
      Real.rpow_natCast_mul (Real.sqrt_nonneg _), Real.sq_sqrt hx]
  simpa only [Complex.ofReal_re, hp A _ hA, hp B _ hB] using hs

private lemma rotate_sums {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (v : I → J → K → ℝ) :
    ∑ j, ∑ k, ∑ i, v i j k = ∑ i, ∑ j, ∑ k, v i j k := by
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset K)) (t := (Finset.univ : Finset I))]
  rw [Finset.sum_comm]

/-- Interpolating a transfer matrix between two weighted spectral sums.
At the interior point the output weights are obtained by pushing the input weights forward. -/
lemma sum_rpow_le_of_strip_transfer {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    {α : ℝ} (hα : 1 < α) (x : I → ℝ) (y : J → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j)
    (T : I → J → K → ℂ → ℂ) (hT : ∀ i j k, StripBoundedEntire (T i j k))
    (h₀ : ∀ z : ℂ, z.re = 0 → ∀ i, ∑ j, ∑ k, ‖T i j k z‖ ^ 2 ≤ 1)
    (h₁ : ∀ z : ℂ, z.re = 1 → ∀ j, ∑ k, ∑ i, ‖T i j k z‖ ^ 2 ≤ 1)
    (hm : ∀ j, ∑ k, ∑ i, x i * ‖T i j k ((1 - α⁻¹ : ℝ) : ℂ)‖ ^ 2 = y j) :
    ∑ j, y j ^ α ≤ ∑ i, x i ^ α := by
  let s := 1 - α⁻¹
  have ha := zero_lt_one.trans hα
  have hs : 0 < s := sub_pos.mpr (inv_lt_one_of_one_lt₀ hα)
  have ht : s < 1 := sub_lt_self _ (inv_pos.mpr ha)
  let X (i : I) (z : ℂ) := spectralFactor (x i) (α + (-α : ℝ) * z)
  let Y (j : J) (z : ℂ) := spectralFactor (y j) ((0 : ℝ) + (α : ℂ) * z)
  let f (a : J × K × I) (z : ℂ) := Y a.1 z * (X a.2.2 z * T a.2.2 a.1 a.2.1 z)
  have hf (a) : StripBoundedEntire (f a) :=
    (StripBoundedEntire.spectralFactor_affine _ 0 α).mul
      ((StripBoundedEntire.spectralFactor_affine _ α (-α)).mul (hT _ _ _))
  have hX (i z) : ‖X i z‖ ^ 2 =
      if x i = 0 then 0 else x i ^ (α - α * z.re) := by
    simp [X, norm_sq_spectralFactor (hx i), Complex.mul_re, sub_eq_add_neg]
  have hY (j z) : ‖Y j z‖ ^ 2 = if y j = 0 then 0 else y j ^ (α * z.re) := by
    simp [Y, norm_sq_spectralFactor (hy j), Complex.mul_re]
  have hpow (r : ℝ) {a : ℝ} (h : a ≠ 0) : (if r = 0 then 0 else r ^ a) = r ^ a := by
    split_ifs with h' <;> simp_all [Real.zero_rpow h]
  have hunit (r : ℝ) : (if r = 0 then (0 : ℝ) else 1) ≤ 1 := by split_ifs <;> norm_num
  let A := ∑ i, x i ^ α
  let B := ∑ j, y j ^ α
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hx i) _
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hy j) _
  have left (z : ℂ) (hz : z.re = 0) : ∑ a, ‖f a z‖ ^ 2 ≤ A := by
    simp only [f, Fintype.sum_prod_type, norm_mul, mul_pow, hX, hY, hz, mul_zero,
      sub_zero, Real.rpow_zero, hpow _ ha.ne']
    rw [rotate_sums (fun i j k => _ * (x i ^ α * ‖T i j k z‖ ^ 2))]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ ∑ j, ∑ k, x i ^ α * ‖T i j k z‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
          mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg (hx i) _) (sq_nonneg _)) (hunit _)
      _ ≤ x i ^ α := by
        simp_rw [← Finset.mul_sum]
        exact mul_le_of_le_one_right (Real.rpow_nonneg (hx i) _) (h₀ z hz i)
  have right (z : ℂ) (hz : z.re = 1) : ∑ a, ‖f a z‖ ^ 2 ≤ B := by
    simp only [f, Fintype.sum_prod_type, norm_mul, mul_pow, hX, hY, hz, mul_one,
      sub_self, Real.rpow_zero, hpow _ ha.ne']
    apply Finset.sum_le_sum
    intro j _
    simp_rw [← Finset.mul_sum]
    apply mul_le_of_le_one_right (Real.rpow_nonneg (hy j) _)
    refine le_trans (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => ?_) (h₁ z hz j)
    exact mul_le_of_le_one_left (sq_nonneg _) (hunit _)
  have hz' (r : ℝ) : (if r = 0 then 0 else r) = r := by split_ifs <;> simp_all
  have mid : ∑ a, ‖f a s‖ ^ 2 = B := by
    have he : α * s = α - 1 := by simp [s, mul_sub, ha.ne']
    simp only [f, Fintype.sum_prod_type, norm_mul, mul_pow, hX, hY, Complex.ofReal_re, he,
      sub_sub_cancel, Real.rpow_one, hz', hpow _ (sub_pos.mpr hα).ne']
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [← Finset.mul_sum]
    rw [hm j, ← Real.rpow_add_one' (hy j) (by linarith : α - 1 + 1 ≠ 0), sub_add_cancel]
  have hi := sum_norm_sq_interpolate hf hA hB left right ⟨hs.le, ht.le⟩
  rw [mid] at hi
  by_cases hb : B = 0
  · exact hb.le.trans hA
  have hp := hB.lt_of_ne' hb
  have he : B = B ^ (1 - s) * B ^ s := by rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_one]
  have hi' := he.ge.trans hi
  exact (Real.rpow_le_rpow_iff hB hA (sub_pos.mpr ht)).mp
    (le_of_mul_le_mul_right hi' (Real.rpow_pos_of_pos hp s))

end

end Complex.HadamardThreeLines
