/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.SpecialFunctions.Entropy
public import Mathlib.Basic.ENNReal.Real

/-!
# Finite classical relative entropy

Natural logarithms give relative entropy in nats. It is infinite precisely when some
outcome has positive source probability and zero reference probability. Otherwise it
equals the real-valued logarithmic sum.

## Main definitions and results

* `Convexity.StdSimplex.relativeEntropy` defines extended nonnegative relative entropy in nats.
* `Convexity.StdSimplex.relativeEntropy_ne_top_iff` characterizes finiteness by absolute continuity.
* `Convexity.StdSimplex.relativeEntropyReal_nonneg` proves Gibbs' inequality for the logarithmic sum
  under absolute continuity.
-/

@[expose] public section

open scoped BigOperators

namespace Real

/-- The strict scalar logarithmic inequality for unequal arguments, including a zero source. -/
lemma sub_lt_mul_log_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≠ b) :
    a - b < a * (log a - log b) := by
  rcases ha.eq_or_lt with h | ha
  · simp [← h, hb]
  · have hr : a / b ≠ 1 := fun e => hab ((div_eq_one_iff_eq hb.ne').mp e)
    have h := mul_lt_mul_of_pos_right (self_sub_one_lt_mul_log (div_nonneg ha.le hb.le) hr) hb
    rwa [sub_mul, one_mul, div_mul_cancel₀ _ hb.ne', mul_right_comm _ (log _) b,
      div_mul_cancel₀ _ hb.ne', log_div ha.ne' hb.ne'] at h

/-- The scalar logarithmic inequality underlying Gibbs and Klein inequalities. -/
lemma sub_le_mul_log_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * (log a - log b) := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  · exact (sub_lt_mul_log_sub ha hb hab).le

/-- The scalar inequality remains valid at zero when the support condition is imposed. -/
lemma sub_le_mul_log_sub_of_support {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : b = 0 → a = 0) : a - b ≤ a * (log a - log b) := by
  rcases eq_or_lt_of_le hb with hb | hb
  · simp [← hb, h hb.symm]
  · exact sub_le_mul_log_sub ha hb

end Real

namespace Convexity.StdSimplex

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Absolute continuity of finite distributions, allowing zeros in either distribution. -/
def AbsolutelyContinuous (p q : StdSimplex ℝ ι) : Prop :=
  ∀ i, q.weights i = 0 → p.weights i = 0

/-- The real logarithmic sum; it represents relative entropy only under absolute continuity. -/
def relativeEntropyReal (p q : StdSimplex ℝ ι) : ℝ :=
  ∑ i, p.weights i * (Real.log (p.weights i) - Real.log (q.weights i))

/-- **Gibbs' inequality** for the finite logarithmic sum under absolute continuity. -/
lemma relativeEntropyReal_nonneg (p q : StdSimplex ℝ ι) (h : p.AbsolutelyContinuous q) :
    0 ≤ p.relativeEntropyReal q := by
  have he := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    Real.sub_le_mul_log_sub_of_support (p.weights_nonneg i) (q.weights_nonneg i) (h i)
  simpa only [relativeEntropyReal, Finset.sum_sub_distrib,
    p.total_of_fintype, q.total_of_fintype, sub_self]
    using he

open Classical in
/-- Classical relative entropy in nats, infinite when absolute continuity fails. -/
def relativeEntropy (p q : StdSimplex ℝ ι) : ENNReal :=
  if p.AbsolutelyContinuous q then ENNReal.ofReal (p.relativeEntropyReal q) else ⊤

/-- Relative entropy is finite exactly under absolute continuity. -/
lemma relativeEntropy_ne_top_iff (p q : StdSimplex ℝ ι) :
    p.relativeEntropy q ≠ ⊤ ↔ p.AbsolutelyContinuous q := by
  classical
  simp only [relativeEntropy]
  split_ifs <;> simp_all

/-- Failure of absolute continuity is exactly the infinite case. -/
lemma relativeEntropy_eq_top_iff (p q : StdSimplex ℝ ι) :
    p.relativeEntropy q = ⊤ ↔ ¬p.AbsolutelyContinuous q := by
  simpa using not_congr (p.relativeEntropy_ne_top_iff q)

/-- Under absolute continuity, converting relative entropy to `ℝ` recovers the logarithmic sum. -/
lemma toReal_relativeEntropy (p q : StdSimplex ℝ ι) (h : p.AbsolutelyContinuous q) :
    (p.relativeEntropy q).toReal = p.relativeEntropyReal q := by
  simp [relativeEntropy, h, ENNReal.toReal_ofReal (p.relativeEntropyReal_nonneg q h)]

/-- A distribution has zero relative entropy with respect to itself. -/
@[simp]
lemma relativeEntropy_self (p : StdSimplex ℝ ι) : p.relativeEntropy p = 0 := by
  simp [relativeEntropy, AbsolutelyContinuous, relativeEntropyReal]

end

end Convexity.StdSimplex
