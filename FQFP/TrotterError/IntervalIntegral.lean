/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Interval-integral identities and bounds

Ordinary oriented interval integrals used in Dyson-series and commutator estimates.
These lemmas do not depend on time-ordered evolution.
-/

@[expose] public section

namespace TrotterError

open NormedSpace
open scoped Topology BigOperators Interval

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ### The fundamental-theorem identity behind the norm bound -/

/-- For continuous `f`, the iterated-integral identity
`∫ τ in a..b, f τ * (∫ u in a..τ, f u)^n / n! = (∫ u in a..b, f u)^(n+1) / (n+1)!`
(valid for all `a b`, with the interval integral carrying the orientation).
This is the FTC applied to `t ↦ (∫_a^t f)^(n+1)/(n+1)!` and is the key step in bounding the
Dyson terms by `(∫ ‖H‖)^n/n!`. -/
lemma integral_mul_integral_pow_div_factorial (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (n : ℕ) :
    (∫ τ in a..b, f τ * (∫ u in a..τ, f u) ^ n / Nat.factorial n) =
      (∫ u in a..b, f u) ^ (n + 1) / Nat.factorial (n + 1) := by
  let F : ℝ → ℝ := fun t => ∫ u in a..t, f u
  let G : ℝ → ℝ := fun t => F t ^ (n + 1) / Nat.factorial (n + 1)
  have hFderiv : ∀ t : ℝ, HasDerivAt F (f t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hGderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt G (f t * F t ^ n / Nat.factorial n) t := by
    intro t _
    have hdiff : DifferentiableAt ℝ G t := ((hFderiv t).differentiableAt.pow (n + 1)).div_const
      (Nat.factorial (n + 1) : ℝ)
    have hderiv : deriv G t = f t * F t ^ n / Nat.factorial n := by
      dsimp [G]
      rw [deriv_div_const]
      change deriv (F ^ (n + 1)) t / (Nat.factorial (n + 1) : ℝ) = _
      rw [deriv_pow (hFderiv t).differentiableAt (n + 1), (hFderiv t).deriv, Nat.add_one_sub_one,
        Nat.factorial_succ, Nat.cast_mul]
      field_simp
    simpa [hderiv] using hdiff.hasDerivAt
  have hFcont : Continuous F :=
    (intervalIntegral.differentiable_integral_of_continuous hf).continuous
  have hint : IntervalIntegrable (fun τ => f τ * F τ ^ n / Nat.factorial n)
      MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun τ => f τ * F τ ^ n / Nat.factorial n).intervalIntegrable a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G)
    (f' := fun τ => f τ * F τ ^ n / Nat.factorial n) hGderiv hint
  calc
    (∫ τ in a..b, f τ * (∫ u in a..τ, f u) ^ n / Nat.factorial n)
        = ∫ τ in a..b, f τ * F τ ^ n / Nat.factorial n := rfl
    _ = G b - G a := hFTC
    _ = (∫ u in a..b, f u) ^ (n + 1) / Nat.factorial (n + 1) := by simp [G, F]

/-- For continuous nonnegative `g`, the two-sided FTC identity
`|∫ τ in a..b, g τ * |∫ u in a..τ, g u|^n / n!| = |∫ u in a..b, g u|^(n+1) / (n+1)!`.
This is the "backward" companion of `integral_mul_integral_pow_div_factorial`. -/
lemma abs_integral_mul_abs_integral_pow_div_factorial (g : ℝ → ℝ) (hg : Continuous g)
    (hgnn : ∀ τ, 0 ≤ g τ) (a b : ℝ) (n : ℕ) :
    |∫ τ in a..b, g τ * |∫ u in a..τ, g u| ^ n / Nat.factorial n| =
      |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
  let F : ℝ → ℝ := fun τ => ∫ u in a..τ, g u
  by_cases hab : a ≤ b
  · -- forward: `F τ ≥ 0` on `[a, b]`, so `|F τ| = F τ` and the integral is nonnegative.
    have hFnn_interval : ∀ τ ∈ Set.Icc a b, 0 ≤ F τ := by
      intro τ hτ
      exact intervalIntegral.integral_nonneg hτ.1 (fun u _ => hgnn u)
    have hFnn_uIoo : ∀ τ ∈ Set.uIoo a b, 0 ≤ F τ := by
      intro τ hτ
      have hmin : min a b < τ := hτ.1
      have haτ : a ≤ τ := by simpa [min_eq_left hab] using le_of_lt hmin
      exact intervalIntegral.integral_nonneg haτ (fun u _ => hgnn u)
    have heq : (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n) =
        ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
      apply intervalIntegral.integral_congr_uIoo
      intro τ hτ
      simp [abs_of_nonneg (hFnn_uIoo τ hτ)]
    have hnonneg : 0 ≤ ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n :=
      intervalIntegral.integral_nonneg hab (fun τ hτ =>
        div_nonneg (mul_nonneg (hgnn τ) (pow_nonneg (hFnn_interval τ hτ) n)) (by positivity))
    calc
      |∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n|
          = ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by rw [heq, abs_of_nonneg hnonneg]
      _ = F b ^ (n + 1) / Nat.factorial (n + 1) :=
          integral_mul_integral_pow_div_factorial g hg a b n
      _ = |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
          rw [show F b = ∫ u in a..b, g u by rfl,
            abs_of_nonneg (intervalIntegral.integral_nonneg hab (fun u _ => hgnn u))]
  · -- backward: `b ≤ a`, so `F τ ≤ 0` on `[b, a]`, `|F τ| = -F τ`.
    have hba : b ≤ a := le_of_not_ge hab
    have hFnonpos_uIoo : ∀ τ ∈ Set.uIoo a b, F τ ≤ 0 := by
      intro τ hτ
      have hmax : τ < max a b := hτ.2
      have hτa : τ ≤ a := by simpa [max_eq_left hba] using le_of_lt hmax
      calc
        F τ = ∫ u in a..τ, g u := rfl
        _ ≤ 0 := by
          have hnonneg : 0 ≤ ∫ u in τ..a, g u :=
            intervalIntegral.integral_nonneg hτa (fun u _ => hgnn u)
          rw [intervalIntegral.integral_symm]
          linarith
    have heq : (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n) =
        (-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
      calc
        (∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n)
            = ∫ τ in a..b, (-1 : ℝ) ^ n * (g τ * F τ ^ n / Nat.factorial n) := by
                apply intervalIntegral.integral_congr_uIoo
                intro τ hτ; simp only
                rw [abs_of_nonpos (hFnonpos_uIoo τ hτ), neg_pow]
                ring
        _ = (-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n := by
                rw [intervalIntegral.integral_const_mul]
    calc
      |∫ τ in a..b, g τ * |F τ| ^ n / Nat.factorial n|
          = |(-1 : ℝ) ^ n * ∫ τ in a..b, g τ * F τ ^ n / Nat.factorial n| := by rw [heq]
      _ = |(-1 : ℝ) ^ n * (F b ^ (n + 1) / Nat.factorial (n + 1))| := by
          rw [integral_mul_integral_pow_div_factorial g hg a b n]
      _ = |∫ u in a..b, g u| ^ (n + 1) / Nat.factorial (n + 1) := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (Nat.factorial (n + 1) : ℝ))]

/-- For continuous nonnegative `g`, the "distance travelled" `|∫_t₁^x g|` is bounded on any
interval `[a, b]` by the sum of its endpoint values: monotonicity of the oriented integral. -/
lemma abs_integral_le_abs_integral_of_mem_Icc {g : ℝ → ℝ} (hg : Continuous g)
    (hgnn : ∀ t, 0 ≤ g t) (t₁ a b x : ℝ) (hx : x ∈ Set.Icc a b) :
    |(∫ u in t₁..x, g u)| ≤ |(∫ u in t₁..a, g u)| + |(∫ u in t₁..b, g u)| := by
  have hmono : Monotone (fun t : ℝ => ∫ u in t₁..t, g u) := by
    intro s t hst
    have hnonneg : 0 ≤ ∫ u in s..t, g u :=
      intervalIntegral.integral_nonneg hst (fun u _ => hgnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := g)
      (μ := MeasureTheory.volume) (a := t₁) (b := s) (c := t) (hg.intervalIntegrable t₁ s)
      (hg.intervalIntegrable s t)
    linarith [hadd, hnonneg]
  have hlo : (∫ u in t₁..a, g u) ≤ ∫ u in t₁..x, g u := hmono hx.1
  have hhi : (∫ u in t₁..x, g u) ≤ ∫ u in t₁..b, g u := hmono hx.2
  have hneg_abs : -|∫ u in t₁..a, g u| ≤ ∫ u in t₁..a, g u := by
    simpa using (neg_le_neg (neg_le_abs (∫ u in t₁..a, g u)))
  exact abs_le.mpr ⟨
    le_trans (le_trans (neg_le_neg (le_add_of_nonneg_right (abs_nonneg (∫ u in t₁..b, g u))))
      hneg_abs) hlo,
    le_trans (le_trans hhi (le_abs_self (∫ u in t₁..b, g u)))
      (le_add_of_nonneg_left (abs_nonneg (∫ u in t₁..a, g u)))⟩

/-- `∫ τ in a..b, (τ - a)^n = (b - a)^(n+1) / (n+1)`. -/
lemma integral_sub_pow (a b : ℝ) (n : ℕ) :
    (∫ τ in a..b, (τ - a) ^ n) = (b - a) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  have hfun : (fun τ : ℝ => (τ - a) ^ n) = fun τ => (τ + (-a)) ^ n := by
    funext τ
    rw [sub_eq_add_neg]
  rw [hfun, intervalIntegral.integral_comp_add_right (f := fun σ : ℝ => σ ^ n) (d := -a),
    integral_pow]
  simp [sub_eq_add_neg]

/-- Left multiplication by a constant commutes with the interval integral (for a general normed
ℝ-algebra). -/
lemma integral_mul_left (c : 𝔸) (f : ℝ → 𝔸) (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, c * f x) = c * ∫ x in a..b, f x := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    (ContinuousLinearMap.mul ℝ 𝔸 c).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

/-! ### Distance bound: monotonicity "last mile" -/

/-- For nonnegative continuous `f, g` and `x` in the unordered interval between `a` and `b`, the
sum of the two partial oriented-absolute integrals `|∫_x^b f| + |∫_a^x g|` is at most
`|∫_a^b (f + g)|`. This is the monotonicity "last mile" for the distance bound: both partial
integrals carry the sign of the orientation, so their absolute values telescope into the single
oriented integral of `f + g`. -/
lemma abs_integral_add_le_abs_integral_of_mem_uIcc {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfnn : ∀ t, 0 ≤ f t) (hgnn : ∀ t, 0 ≤ g t) (a b x : ℝ)
    (hx : x ∈ Set.uIcc a b) :
    |∫ u in x..b, f u| + |∫ u in a..x, g u| ≤ |∫ u in a..b, f u + g u| := by
  by_cases hab : a ≤ b
  · -- forward: `a ≤ x ≤ b`, all partial integrals are nonnegative.
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    have hfx : 0 ≤ ∫ u in x..b, f u :=
      intervalIntegral.integral_nonneg hx'.2 (fun u _ => hfnn u)
    have hgx : 0 ≤ ∫ u in a..x, g u :=
      intervalIntegral.integral_nonneg hx'.1 (fun u _ => hgnn u)
    have hfg : 0 ≤ ∫ u in a..b, f u + g u :=
      intervalIntegral.integral_nonneg hab (fun u _ => add_nonneg (hfnn u) (hgnn u))
    rw [abs_of_nonneg hfx, abs_of_nonneg hgx, abs_of_nonneg hfg]
    have hfx_le : ∫ u in x..b, f u ≤ ∫ u in x..b, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := x) (b := b) hx'.2
        (hf.intervalIntegrable x b) ((hf.add hg).intervalIntegrable x b) ?_
      intro u _
      exact le_add_of_nonneg_right (hgnn u)
    have hgx_le : ∫ u in a..x, g u ≤ ∫ u in a..x, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := a) (b := x) hx'.1
        (hg.intervalIntegrable a x) ((hf.add hg).intervalIntegrable a x) ?_
      intro u _
      exact le_add_of_nonneg_left (hfnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := fun u => f u + g u)
      (μ := MeasureTheory.volume) (a := a) (b := x) (c := b)
      ((hf.add hg).intervalIntegrable a x) ((hf.add hg).intervalIntegrable x b)
    calc
      (∫ u in x..b, f u) + ∫ u in a..x, g u
          ≤ (∫ u in a..x, f u + g u) + ∫ u in x..b, f u + g u :=
              (add_le_add hfx_le hgx_le).trans_eq (add_comm _ _)
      _ = ∫ u in a..b, f u + g u := hadd
  · -- backward: `b ≤ x ≤ a`, the partial integrals are nonpositive, so their absolute values are
    -- the integrals over the reversed (nonnegative) subintervals.
    have hba : b ≤ a := le_of_not_ge hab
    have hx' : x ∈ Set.Icc b a := by
      simpa [Set.uIcc_of_ge hba] using hx
    have hfx : 0 ≤ ∫ u in b..x, f u :=
      intervalIntegral.integral_nonneg hx'.1 (fun u _ => hfnn u)
    have hgx : 0 ≤ ∫ u in x..a, g u :=
      intervalIntegral.integral_nonneg hx'.2 (fun u _ => hgnn u)
    have hfg : 0 ≤ ∫ u in b..a, f u + g u :=
      intervalIntegral.integral_nonneg hba (fun u _ => add_nonneg (hfnn u) (hgnn u))
    have hfx_le : ∫ u in b..x, f u ≤ ∫ u in b..x, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := b) (b := x) hx'.1
        (hf.intervalIntegrable b x) ((hf.add hg).intervalIntegrable b x) ?_
      intro u _
      exact le_add_of_nonneg_right (hgnn u)
    have hgx_le : ∫ u in x..a, g u ≤ ∫ u in x..a, f u + g u := by
      refine intervalIntegral.integral_mono_on (a := x) (b := a) hx'.2
        (hg.intervalIntegrable x a) ((hf.add hg).intervalIntegrable x a) ?_
      intro u _
      exact le_add_of_nonneg_left (hfnn u)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (f := fun u => f u + g u)
      (μ := MeasureTheory.volume) (a := b) (b := x) (c := a)
      ((hf.add hg).intervalIntegrable b x) ((hf.add hg).intervalIntegrable x a)
    have hsum : (∫ u in b..x, f u) + ∫ u in x..a, g u ≤ ∫ u in b..a, f u + g u := by
      calc
        (∫ u in b..x, f u) + ∫ u in x..a, g u
            ≤ (∫ u in b..x, f u + g u) + ∫ u in x..a, f u + g u := add_le_add hfx_le hgx_le
        _ = ∫ u in b..a, f u + g u := hadd
    have habs_f : |∫ u in x..b, f u| = ∫ u in b..x, f u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hfx]
    have habs_g : |∫ u in a..x, g u| = ∫ u in x..a, g u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hgx]
    have habs_fg : |∫ u in a..b, f u + g u| = ∫ u in b..a, f u + g u := by
      rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hfg]
    rwa [habs_f, habs_g, habs_fg]

end TrotterError
