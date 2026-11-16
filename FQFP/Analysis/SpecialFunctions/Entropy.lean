/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen

/-!
# Shannon entropy of finite probability distributions

The existing standard simplex supplies the probabilities. Entropy uses the natural
logarithm, so its unit is the nat. Zero probabilities contribute zero.

## Main definitions and results

* `Convexity.StdSimplex.shannonEntropy` defines Shannon entropy in nats on a finite simplex.
* `Convexity.StdSimplex.shannonEntropy_le_log_card` bounds entropy by the logarithm of the number of
  outcomes.
* `Convexity.StdSimplex.mul_shannonEntropy_add_le` gives concavity under binary mixtures.
-/

@[expose] public section

open scoped BigOperators

namespace Convexity.StdSimplex

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Shannon entropy in nats, including distributions with zero probabilities. -/
def shannonEntropy (p : StdSimplex ℝ ι) : ℝ := ∑ i, Real.negMulLog (p.weights i)

/-- Shannon entropy is the expected negative logarithm of the outcome probability. -/
lemma shannonEntropy_eq_sum_mul_neg_log (p : StdSimplex ℝ ι) :
    p.shannonEntropy = ∑ i, p.weights i * (-Real.log (p.weights i)) := by
  simp only [shannonEntropy, Real.negMulLog, neg_mul, mul_neg]

/-- Shannon entropy is nonnegative. -/
lemma shannonEntropy_nonneg (p : StdSimplex ℝ ι) : 0 ≤ p.shannonEntropy :=
  Finset.sum_nonneg fun i _ ↦
    Real.negMulLog_nonneg (p.weights_nonneg i) (p.weights_apply_le_one i)

/-- Shannon entropy is at most the logarithm of the number of outcomes. -/
lemma shannonEntropy_le_log_card (p : StdSimplex ℝ ι) :
    p.shannonEntropy ≤ Real.log (Fintype.card ι) := by
  have := p.nonempty
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹)
    (p := fun i ↦ p.weights i) (fun _ _ ↦ (inv_pos.mpr hn).le)
    (by simp [ne_of_gt hn]) (fun i _ ↦ p.weights_nonneg i)
  simp only [smul_eq_mul, ← Finset.mul_sum, p.total_of_fintype, mul_one,
    Real.negMulLog, Real.log_inv, neg_mul_neg] at hj
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr hn)).mp hj

/-- A deterministic distribution has zero entropy. -/
@[simp]
lemma shannonEntropy_single (i : ι) : (single i : StdSimplex ℝ ι).shannonEntropy = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : i = j <;> simp [weights_single, h]

/-- A constant probability distribution has entropy equal to the logarithm of its size. -/
lemma shannonEntropy_eq_log_card_of_uniform (p : StdSimplex ℝ ι)
    (hp : ∀ i, p.weights i = (Fintype.card ι : ℝ)⁻¹) :
    p.shannonEntropy = Real.log (Fintype.card ι) := by
  have := p.nonempty
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [shannonEntropy, hp, Real.negMulLog, Real.log_inv, hn]

/-- Shannon entropy is continuous even at distributions with zero probabilities. -/
@[fun_prop]
lemma continuous_shannonEntropy : Continuous (shannonEntropy (ι := ι)) := by
  unfold shannonEntropy
  fun_prop

/-- Shannon entropy is concave under arbitrary binary probability mixtures. -/
lemma mul_shannonEntropy_add_le (p q : StdSimplex ℝ ι)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * p.shannonEntropy + b * q.shannonEntropy ≤
      (convexCombPair a b ha hb hab p q).shannonEntropy := by
  simp only [shannonEntropy, weights_convexCombPair, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦
    Real.concaveOn_negMulLog.2 (p.weights_nonneg i) (q.weights_nonneg i) ha hb hab

end

end Convexity.StdSimplex
