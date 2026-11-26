/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for continuity of the sandwiched divergence in its order.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/Relative.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.DataProcessing
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Topology.Order.Compact

/-!
# Continuity of sandwiched Rényi relative entropy in its order

For a positive operator and an exponent above one, the sum of powers of its eigenvalues
is the maximum of the corresponding sums of diagonal entries over orthonormal bases.
This compact maximum lets the sandwich and the exponent vary together, including at
degenerate eigenvalues. On the kernel of the reference, its negative powers stay zero.
-/

@[expose] public section

open scoped BigOperators

namespace Qudit

noncomputable section

variable {H : Qudit}

/-- Orthonormal families form a closed subset of a product of compact unit spheres. -/
lemma isCompact_orthonormal (H : Qudit) (ι : Type*) :
    IsCompact {v : ι → H.state | Orthonormal ℂ v} := by
  classical
  let _ := FiniteDimensional.proper ℂ H.state
  apply (isCompact_pi_infinite fun _ : ι => isCompact_sphere (0 : H.state) 1).of_isClosed_subset
  · simp only [orthonormal_iff_ite, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
  · intro v hv i
    simpa only [Metric.mem_sphere, dist_zero_right] using hv.1 i

/-- For exponents at least one, the eigenbasis maximizes the sum of powers of the
diagonal entries of a positive operator over orthonormal bases. -/
lemma Operator.isGreatest_sum_rpow_diagonal {A : Operator H} (hA : A.IsPositive)
    {p : ℝ} (hp : 1 ≤ p) :
    IsGreatest ((fun v : Fin (Module.finrank ℂ H.state) → H.state =>
      ∑ j, (inner ℂ (v j) (A (v j))).re ^ p) '' {v | Orthonormal ℂ v})
      (∑ i, (hA.isSymmetric.eigenvalues rfl i) ^ p) := by
  let b := hA.isSymmetric.eigenvectorBasis rfl
  let x := hA.isSymmetric.eigenvalues rfl
  have hx (i) : A (b i) = (x i : ℂ) • b i := hA.isSymmetric.apply_eigenvectorBasis rfl i
  refine ⟨⟨b, b.orthonormal, ?_⟩, ?_⟩
  · simp only [hx, inner_smul_right, b.inner_eq_one, mul_one, Complex.ofReal_re, x]
  · rintro _ ⟨v, hv, rfl⟩
    let w i j := ‖inner ℂ (b i) (v j)‖ ^ 2
    have hrow (j) : ∑ i, w i j = 1 := by
      rw [show ∑ i, w i j = ‖v j‖ ^ 2 from b.sum_sq_norm_inner_right _, hv.1 j, one_pow]
    have hcol (i) : ∑ j, w i j ≤ 1 := by
      simpa only [w, norm_inner_symm (b i), b.norm_eq_one, one_pow] using
        hv.sum_inner_products_le (s := Finset.univ) (b i)
    calc
      _ ≤ ∑ j, ∑ i, w i j * x i ^ p := by
        apply Finset.sum_le_sum
        intro j _
        rw [Operator.re_inner_apply_eq_sum_of_eigenbasis b A x hx]
        simpa only [w, mul_comm] using Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
          (fun i => w i j) x (fun i _ => sq_nonneg _) (hrow j)
          (fun i _ => hA.nonneg_eigenvalues rfl i) hp
      _ = ∑ i, (∑ j, w i j) * x i ^ p := by rw [Finset.sum_comm]; simp only [Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_of_le_one_left
        (Real.rpow_nonneg (hA.nonneg_eigenvalues rfl i) p) (hcol i)

namespace Density

private lemma continuous_sandwich_power_apply (σ : Density H) :
    Continuous (fun z : Set.Ioi (1 : ℝ) × H.state =>
      σ.spectralMap (fun x => x ^ (-(1 - z.1.val⁻¹) / 2)) z.2) := by
  have he : Continuous (fun a : Set.Ioi (1 : ℝ) => -(1 - a.val⁻¹) / 2) := by
    fun_prop (disch := exact fun a => (zero_lt_one.trans a.property).ne')
  simp only [spectralMap, LinearMap.sum_apply, LinearMap.smul_apply, Operator.outer_apply]
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (fun a : Set.Ioi (1 : ℝ) => σ.eigenvalue i ^ (-(1 - a.val⁻¹) / 2)) := by
    by_cases h : σ.eigenvalue i = 0
    · have hz (a : Set.Ioi (1 : ℝ)) : (0 : ℝ) ^ (-(1 - a.val⁻¹) / 2) = 0 :=
        Real.zero_rpow (div_ne_zero (neg_ne_zero.mpr (sub_pos.mpr
          (inv_lt_one_of_one_lt₀ a.property)).ne') (by norm_num))
      simp only [h, hz]
      exact continuous_const
    · exact (Real.continuous_const_rpow h).comp he
  exact (Complex.continuous_ofReal.comp (hc.comp continuous_fst)).smul
    ((continuous_const.inner continuous_snd).smul continuous_const)

/-- The sandwiched trace functional is continuous in the order on the interval above one,
including when the reference has a kernel. -/
theorem continuousOn_sandwichedTraceFunctional (ρ σ : Density H) :
    ContinuousOn (ρ.sandwichedTraceFunctional σ) (Set.Ioi 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let A (a : Set.Ioi (1 : ℝ)) := ρ.renyiSandwich σ (1 - a.val⁻¹)
  have hA : Continuous (fun z : Set.Ioi (1 : ℝ) × H.state => A z.1 z.2) := by
    simp only [A, renyiSandwich, adjoint_spectralMap, LinearMap.comp_apply]
    exact (continuous_sandwich_power_apply σ).comp (continuous_fst.prodMk
      (ρ.op.continuous_of_finiteDimensional.comp (continuous_sandwich_power_apply σ)))
  let f (a : Set.Ioi (1 : ℝ)) (v : Fin (Module.finrank ℂ H.state) → H.state) :=
    ∑ j, (inner ℂ (v j) (A a (v j))).re ^ a.val
  have hf : Continuous ↿f := by
    change Continuous (fun z : Set.Ioi (1 : ℝ) × (Fin (Module.finrank ℂ H.state) → H.state) =>
      ∑ j, (inner ℂ (z.2 j) (A z.1 (z.2 j))).re ^ z.1.val)
    apply continuous_finsetSum
    intro j _
    have hv := (continuous_apply j).comp
      (continuous_snd (X := Set.Ioi (1 : ℝ)) (Y := Fin (Module.finrank ℂ H.state) → H.state))
    exact (Complex.continuous_re.comp (hv.inner (hA.comp (continuous_fst.prodMk hv)))).rpow
      (continuous_subtype_val.comp continuous_fst) (fun z => .inr (zero_lt_one.trans z.1.property))
  exact ((isCompact_orthonormal H _).continuous_sSup hf).congr fun a =>
    (Operator.isGreatest_sum_rpow_diagonal (ρ.renyiSandwich_positive σ _) a.property.le).csSup_eq

/-- For every fixed pair of states, the extended divergence is continuous in its order
above one. If support inclusion fails, its value is constantly infinite. -/
theorem continuous_sandwichedRenyiRelativeEntropy (ρ σ : Density H) :
    Continuous (ρ.sandwichedRenyiRelativeEntropy σ) := by
  classical
  change Continuous (fun a => ρ.sandwichedRenyiRelativeEntropy σ a)
  by_cases h : ρ.AbsolutelyContinuous σ
  · simp only [sandwichedRenyiRelativeEntropy, h, reduceIte]
    apply ENNReal.continuous_ofReal.comp
    apply Continuous.div
    · exact ((continuousOn_iff_continuous_domRestrict.mp
        (ρ.continuousOn_sandwichedTraceFunctional σ)).log fun a =>
          (zero_lt_one.trans_le (ρ.one_le_sandwichedTraceFunctional σ a.property h)).ne')
    · exact continuous_subtype_val.sub continuous_const
    · exact fun a => (sub_pos.mpr a.property).ne'
  · simpa only [sandwichedRenyiRelativeEntropy, h, reduceIte] using
      (continuous_const : Continuous (fun _ : Set.Ioi (1 : ℝ) => (⊤ : ENNReal)))

end Density

end

end Qudit
