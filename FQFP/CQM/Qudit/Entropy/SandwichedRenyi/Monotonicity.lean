/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi.LimitAtOne

/-!
# Order monotonicity of the sandwiched Rényi relative entropy

Factor the sandwich as `T T†` and evaluate the same spectral sum on `T† T`.
In any fixed basis, the diagonal entries of the latter are moments of the reference
eigenvalues with nonnegative weights. Two applications of Hölder's inequality compare
these moments at different orders. The right limit at one gives the Umegaki lower bound.
-/

@[expose] public section

open Filter
open scoped BigOperators

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

private lemma sum_geometric_le {ι : Type*} [Fintype ι] (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    ∑ i, x i ^ (1 - t) * y i ^ t ≤ (∑ i, x i) ^ (1 - t) * (∑ i, y i) ^ t := by
  have hu := sub_pos.mpr ht'
  have hpq : (1 - t)⁻¹.HolderConjugate t⁻¹ := by
    apply Real.holderConjugate_iff.mpr
    exact ⟨(one_lt_inv₀ hu).mpr (sub_lt_self _ ht), by simp⟩
  simpa only [Real.rpow_rpow_inv (hx _) hu.ne', Real.rpow_rpow_inv (hy _) ht.ne',
    one_div, inv_inv] using Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
      (f := fun i => x i ^ (1 - t)) (g := fun i => y i ^ t) hpq
      (fun i _ => Real.rpow_nonneg (hx i) _) (fun i _ => Real.rpow_nonneg (hy i) _)

private lemma moment_le {ι : Type*} [Fintype ι] (w r : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hr : ∀ i, 0 ≤ r i) (s : ℝ) {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    ∑ i, w i * r i ^ (s * t) ≤ (∑ i, w i) ^ (1 - t) * (∑ i, w i * r i ^ s) ^ t := by
  have he (i) : w i ^ (1 - t) * (w i * r i ^ s) ^ t = w i * r i ^ (s * t) := by
    rw [Real.mul_rpow (hw i) (Real.rpow_nonneg (hr i) _), ← mul_assoc,
      ← Real.rpow_add_of_nonneg (hw i) (sub_nonneg.mpr ht'.le) ht.le, sub_add_cancel,
      Real.rpow_one, ← Real.rpow_mul (hr i)]
  simpa only [he] using sum_geometric_le w (fun i => w i * r i ^ s) hw
    (fun i => mul_nonneg (hw i) (Real.rpow_nonneg (hr i) _)) ht ht'

private def factor (ρ σ : Density H) (a : ℝ) : Operator H :=
  σ.spectralMap (fun x => x ^ (-(1 - a⁻¹) / 2)) ∘ₗ ρ.op.sqrt

private lemma sandwich_eq_factor (ρ σ : Density H) (a : ℝ) :
    ρ.renyiSandwich σ (1 - a⁻¹) = factor ρ σ a ∘ₗ (factor ρ σ a).adjoint := by
  have hs : ρ.op.sqrt ∘ₗ ρ.op.sqrt = ρ.op := ρ.op.sqrt_mul_sqrt ρ.positive
  simp only [renyiSandwich, factor, LinearMap.adjoint_comp, Operator.adjoint_sqrt,
    LinearMap.comp_assoc]
  conv_lhs => rw [← hs, LinearMap.comp_assoc]

private lemma traceFunctional_eq_sum_gram (ρ σ : Density H) (a : ℝ) :
    ρ.sandwichedTraceFunctional σ a =
      ∑ i, ((factor ρ σ a).isPositive_adjoint_comp_self.isSymmetric.eigenvalues rfl i) ^ a := by
  let T := factor ρ σ a
  let b := (stdOrthonormalBasis ℂ H.state).toBasis
  have hc : (ρ.renyiSandwich σ (1 - a⁻¹)).charpoly = (T.adjoint ∘ₗ T).charpoly := by
    rw [sandwich_eq_factor]
    change (T ∘ₗ T.adjoint).charpoly = _
    rw [← LinearMap.charpoly_toMatrix _ b, ← LinearMap.charpoly_toMatrix (T.adjoint ∘ₗ T) b,
      LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, Matrix.charpoly_mul_comm]
  have he := congrArg (fun p : Polynomial ℂ => (p.roots.map (fun z => z.re ^ a)).sum) hc
  simpa only [(ρ.renyiSandwich_positive σ _).isSymmetric.roots_charpoly_eq_eigenvalues rfl,
    T.isPositive_adjoint_comp_self.isSymmetric.roots_charpoly_eq_eigenvalues rfl, Multiset.map_map,
    Finset.sum, Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re,
    sandwichedTraceFunctional, T] using he

private def overlap (ρ σ : Density H) (v : H.state) (i : Fin (Module.finrank ℂ H.state)) : ℝ :=
  ‖inner ℂ (σ.eigenbasis i) (ρ.op.sqrt v)‖ ^ 2

private lemma gram_diagonal (ρ σ : Density H) (a : ℝ) (v : H.state) :
    (inner ℂ v (((factor ρ σ a).adjoint ∘ₗ factor ρ σ a) v)).re =
      ∑ i, overlap ρ σ v i * σ.eigenvalue i ^ (a⁻¹ - 1) := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← σ.eigenbasis.sum_sq_norm_inner_right]
  apply Finset.sum_congr rfl
  intro i _
  simp only [factor, LinearMap.comp_apply, ← LinearMap.adjoint_inner_left (σ.spectralMap _),
    adjoint_spectralMap, spectralMap_apply_eigenbasis, inner_smul_left, Complex.conj_ofReal,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
      (σ.eigenvalue_nonneg i) _), mul_pow, overlap]
  rw [← Real.rpow_mul_natCast (σ.eigenvalue_nonneg i), mul_comm]
  ring_nf

/-- The trace functional at the smaller order is bounded by a fractional power of the
one at the larger order. The estimate holds on the entire state space. -/
theorem sandwichedTraceFunctional_le_rpow (ρ σ : Density H) {a b : ℝ}
    (ha : 1 < a) (hab : a < b) : ρ.sandwichedTraceFunctional σ a ≤
      (ρ.sandwichedTraceFunctional σ b) ^ ((a - 1) / (b - 1)) := by
  let k := (a - 1) / (b - 1)
  let t := b * k / a
  have hb := ha.trans hab
  have ha₀ := zero_lt_one.trans ha
  have hb₀ := zero_lt_one.trans hb
  have hk : 0 < k := div_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
  have hk' : k < 1 := (div_lt_one (sub_pos.mpr hb)).mpr (sub_lt_sub_right hab 1)
  have ht : 0 < t := div_pos (mul_pos hb₀ hk) ha₀
  have hta : t * a = b * k := div_mul_cancel₀ _ ha₀.ne'
  have hkb : k * (b - 1) = a - 1 := div_mul_cancel₀ _ (sub_pos.mpr hb).ne'
  have hta' : (1 - t) * a = 1 - k := by linarith only [hta, hkb]
  have ht' : t < 1 := by
    apply lt_of_mul_lt_mul_right (a := a) _ ha₀.le
    linarith only [hta', hk']
  have hexp : a⁻¹ - 1 = (b⁻¹ - 1) * t := by
    dsimp [t, k]
    field_simp
    ring
  let P := (factor ρ σ a).isPositive_adjoint_comp_self
  let c := P.isSymmetric.eigenvectorBasis rfl
  let w j := overlap ρ σ (c j)
  let m (p : ℝ) j := ∑ i, w j i * σ.eigenvalue i ^ (p⁻¹ - 1)
  have hw (j i) : 0 ≤ w j i := sq_nonneg _
  have hm (p j) : 0 ≤ m p j :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw j i) (Real.rpow_nonneg (σ.eigenvalue_nonneg i) _)
  have hmass : ∑ j, ∑ i, w j i = 1 := by
    simp only [w, overlap, σ.eigenbasis.sum_sq_norm_inner_right,
      ← ρ.op.re_inner_apply_eq_norm_sqrt_sq ρ.positive, ← Complex.re_sum,
      ← LinearMap.trace_eq_sum_inner, ρ.trace_one, Complex.one_re]
  have hsmall : ρ.sandwichedTraceFunctional σ a = ∑ j, m a j ^ a := by
    rw [traceFunctional_eq_sum_gram]
    apply Finset.sum_congr rfl
    intro j _
    have he := gram_diagonal ρ σ a (c j)
    rw [P.isSymmetric.apply_eigenvectorBasis rfl, inner_smul_right, c.inner_eq_one,
      mul_one] at he
    exact congrArg (fun u : ℝ => u ^ a) he
  have hlarge : ∑ j, m b j ^ b ≤ ρ.sandwichedTraceFunctional σ b := by
    rw [traceFunctional_eq_sum_gram]
    have he := (Operator.isGreatest_sum_rpow_diagonal
      (factor ρ σ b).isPositive_adjoint_comp_self hb.le).2 ⟨c, c.orthonormal, rfl⟩
    simpa only [gram_diagonal, w, m] using he
  rw [hsmall]
  calc
    _ ≤ ∑ j, (∑ i, w j i) ^ (1 - k) * (m b j ^ b) ^ k := by
      apply Finset.sum_le_sum
      intro j _
      have h := moment_le (w j) σ.eigenvalue (hw j) σ.eigenvalue_nonneg (b⁻¹ - 1) ht ht'
      rw [← hexp] at h
      have hmass' := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hw j i)
      change m a j ≤ (∑ i, w j i) ^ (1 - t) * m b j ^ t at h
      simpa only [Real.mul_rpow (Real.rpow_nonneg hmass' _) (Real.rpow_nonneg (hm b j) _),
        ← Real.rpow_mul hmass', ← Real.rpow_mul (hm b j), hta, hta'] using
        Real.rpow_le_rpow (hm a j) h ha₀.le
    _ ≤ _ := by
      have h := sum_geometric_le (fun j => ∑ i, w j i) (fun j => m b j ^ b)
        (fun j => Finset.sum_nonneg fun i _ => hw j i) (fun j => Real.rpow_nonneg (hm b j) _) hk hk'
      rw [hmass, Real.one_rpow, one_mul] at h
      exact h.trans (Real.rpow_le_rpow (Finset.sum_nonneg fun j _ =>
        Real.rpow_nonneg (hm b j) _) hlarge hk.le)

/-- Sandwiched Rényi relative entropy is nondecreasing in its real order above one. -/
theorem monotone_sandwichedRenyiRelativeEntropy (ρ σ : Density H) :
    Monotone (ρ.sandwichedRenyiRelativeEntropy σ) := by
  intro a b hab
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  by_cases h : ρ.AbsolutelyContinuous σ
  · simp only [sandwichedRenyiRelativeEntropy, h, reduceIte]
    apply ENNReal.ofReal_le_ofReal
    have hpa := zero_lt_one.trans_le (ρ.one_le_sandwichedTraceFunctional σ a.property h)
    have hpb := zero_lt_one.trans_le (ρ.one_le_sandwichedTraceFunctional σ b.property h)
    have hl := Real.log_le_log hpa (ρ.sandwichedTraceFunctional_le_rpow σ a.property hab)
    rw [Real.log_rpow hpb] at hl
    apply (div_le_iff₀ (sub_pos.mpr a.property)).mpr
    convert hl using 1
    ring
  · simp [sandwichedRenyiRelativeEntropy, h]

/-- Umegaki relative entropy is a lower bound at every order above one, including
when support inclusion fails and both sides are infinite. -/
theorem relativeEntropy_le_sandwichedRenyiRelativeEntropy (ρ σ : Density H) (a : Set.Ioi (1 : ℝ)) :
    ρ.relativeEntropy σ ≤ ρ.sandwichedRenyiRelativeEntropy σ a :=
  le_of_tendsto (ρ.tendsto_sandwichedRenyiRelativeEntropy_one σ)
    ((eventually_le_atBot a).mono fun _ h => ρ.monotone_sandwichedRenyiRelativeEntropy σ h)

end

end Qudit.Density
