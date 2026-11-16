/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiQuintic
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiSepticDataRelations
public import FQFP.Analysis.Normed.Algebra.WordTable

/-!
# Seventh-order Suzuki logarithm error

The expanded BCH word table gives a uniform bound for the seventh coefficient at
the standard real Suzuki parameter. Truncating the logarithm of the actual
exponential product after degree seven gives a local eighth-order remainder.
-/

@[expose] public noncomputable section

open FQFP.SuzukiSepticCertificate Finset NormedSpace TrotterError
open scoped RealScalar

namespace FQFP.BCH

/-- Rounding down both scaled powers of the Suzuki parameter with one unit of error
in each gives an integer upper bound for `10⁸ |a + p b + p² c|`. -/
private def scaledCoeffBound (c : Triple) : ℤ :=
  |100000000 * c.1 + 41449077 * c.2.1 + 17180259 * c.2.2| + |c.2.1| + |c.2.2|

private theorem abs_tripleValue_le (c : Triple) :
    |tripleValue suzukiP c| ≤ (scaledCoeffBound c : ℝ) / 100000000 := by
  obtain ⟨hl, hu⟩ := suzukiP_mem_tight_rational_interval
  have h₁ : |100000000 * suzukiP - 41449077| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [hl, hu]
  have h₂ : |100000000 * suzukiP ^ 2 - 17180259| ≤ 1 := by
    have hlo := pow_le_pow_left₀ (by norm_num) hl.le 2
    have hhi := pow_le_pow_left₀ (by linarith only [hl]) hu.le 2
    rw [abs_le]
    constructor <;> linarith only [hlo, hhi]
  have herr {x : ℝ} (hx : |x| ≤ 1) (z : ℝ) : |x * z| ≤ |z| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right hx (abs_nonneg z)
  have he : tripleValue suzukiP c * 100000000 =
      (100000000 * c.1 + 41449077 * c.2.1 + 17180259 * c.2.2 : ℝ) +
        (100000000 * suzukiP - 41449077) * c.2.1 +
        (100000000 * suzukiP ^ 2 - 17180259) * c.2.2 := by
    unfold tripleValue
    ring
  rw [le_div_iff₀ (by norm_num)]
  calc
    _ = |tripleValue suzukiP c * 100000000| := by simp [abs_mul]
    _ ≤ _ := by
      rw [he]
      unfold scaledCoeffBound
      push_cast
      exact (abs_add_le ..).trans (add_le_add
        ((abs_add_le ..).trans (add_le_add_right (herr h₁ _) _)) (herr h₂ _))

private theorem sum_abs_tripleValue_le :
    (expandedBchData.map fun r ↦ |tripleValue suzukiP r.2|).sum ≤ 0.01951 * denominator := by
  have hdata : (expandedBchData.map fun r ↦ scaledCoeffBound r.2).sum ≤
      1951 * (denominator : ℤ) * 1000 := by decide +kernel
  have hcast : (((expandedBchData.map fun r ↦ scaledCoeffBound r.2).sum : ℤ) : ℝ) ≤
      1951 * denominator * 1000 := by exact_mod_cast hdata
  calc
    _ ≤ (expandedBchData.map fun r ↦ (scaledCoeffBound r.2 : ℝ) / 100000000).sum :=
      List.sum_le_sum fun r _ ↦ abs_tripleValue_le r.2
    _ = (((expandedBchData.map fun r ↦ scaledCoeffBound r.2).sum : ℤ) : ℝ) / 100000000 := by
      simp only [div_eq_mul_inv, List.sum_map_mul_right, Int.cast_list_sum, List.map_map,
        Function.comp_def]
    _ ≤ _ := by
      rw [div_le_iff₀ (by norm_num)]
      calc
        _ ≤ _ := hcast
        _ = _ := by ring

section RationalAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The seventh logarithm coefficient at the standard Suzuki parameter has
absolute word-coefficient budget at most `0.01951`. -/
theorem norm_suzukiBchSepticTerm_suzukiP_le (a b : A) :
    ‖suzukiBchSepticTerm a b suzukiP‖ ≤ (0.01951 : ℝ) * max ‖a‖ ‖b‖ ^ 7 := by
  let M := max ‖a‖ ‖b‖
  have hletters (i : Fin 2) : ‖![a, b] i‖ ≤ M := by
    fin_cases i
    · exact le_max_left ..
    · exact le_max_right ..
  have hword (r) (hr : r ∈ expandedBchData) : ‖(r.1.map ![a, b]).prod‖ ≤ M ^ 7 := by
    have hw : r.1 ∈ expandedBchData.map Prod.fst := List.mem_map.mpr ⟨r, hr, rfl⟩
    rw [expandedBchData_positions] at hw
    have hlen := (CoeffWordTable.mem_fixedWords_iff_length 2 7 r.1).mp
      (binaryWords_perm_fixedWords.subset hw)
    rw [← hlen, ← List.ofFn_getElem_eq_map r.1 ![a, b]]
    exact norm_word_le_of_pos (by lia) _ fun _ ↦ hletters _
  have hnorm : ‖rowsValue ![a, b] suzukiP expandedBchData‖ ≤
      (expandedBchData.map fun r ↦ |tripleValue suzukiP r.2|).sum * M ^ 7 := by
    simpa only [rowsValue, one_mul, mul_one, Real.norm_eq_abs] using
      List.norm_sum_map_smul_le expandedBchData (fun r ↦ tripleValue suzukiP r.2)
        (fun r ↦ (r.1.map ![a, b]).prod) (fun _ ↦ 1) (fun r hr ↦ by simpa using hword r hr)
  have h := hnorm.trans (mul_le_mul_of_nonneg_right sum_abs_tripleValue_le
    (pow_nonneg ((norm_nonneg a).trans (le_max_left ..)) 7))
  rw [rowsValue_eq_expandedPolynomialValue, norm_smul, Real.norm_natCast] at h
  rw [suzukiBchSepticTerm_eq_expandedPolynomialValue a b suzukiP isSuzukiCubic_suzukiP]
  apply le_of_mul_le_mul_left _ (by norm_num [denominator] : 0 < (denominator : ℝ))
  simpa only [mul_left_comm, mul_assoc] using h

variable [NormOneClass A]

/-- After the two leading error coefficients, the logarithm of the five-stage product
has an explicit eighth-order remainder on the quarter-radius domain. -/
theorem norm_fiveStageStrangLog_sub_quintic_sub_septic_le (a b : A) (p t : ℝ)
    (hp : IsSuzukiCubic p) (ht : fiveStageStrangArgNormBound a b p t < 1 / 4) :
    ‖fiveStageStrangLog a b p t - t • (a + b) - t ^ 5 • suzukiQuinticTerm a b p -
      t ^ 7 • suzukiBchSepticTerm a b p‖ ≤ 1536 * fiveStageStrangArgNormBound a b p t ^ 8 := by
  let half := List.ofFn (fiveStageStrangHalfGenerator a b p)
  let args := (half ++ half.reverse).map (fun x ↦ t • x)
  have hsum : (args.map norm).sum = fiveStageStrangArgNormBound a b p t := by
    simp [args, half, fiveStageStrangHalfGenerator,
      fiveStageStrangArgNormBound, norm_smul, norm_div]
    ring
  have hjet : (∑ k ∈ range 8, expListLogCoeff args k) =
      t • (a + b) + t ^ 5 • suzukiQuinticTerm a b p + t ^ 7 • suzukiBchSepticTerm a b p := by
    simp only [args, expListLogCoeff_smul]
    trans ∑ k ∈ range 8, t ^ k • (if k = 1 then a + b else if k = 5 then
      suzukiQuinticTerm a b p else if k = 7 then suzukiBchSepticTerm a b p else 0)
    · apply sum_congr rfl
      intro k hk
      congr 1
      simpa [half, Fin.ext_iff] using expListLogCoeff_suzukiHalf_through_seven a b p hp
        ⟨k, mem_range.mp hk⟩
    · norm_num [sum_range_succ]
  have hprod : (args.map exp).prod = fiveStageStrangProduct a b p t := by
    rw [fiveStageStrangProduct_eq_symmetricExpProduct]
    simp only [args, half, symmetricExpProduct, expListProduct, List.map_map, List.map_append,
      List.prod_append, Function.comp_def]
  have h := norm_log_prod_exp_sub_sum_le args (hsum.trans_lt ht) 8
  rw [hjet, hprod, hsum] at h
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd, Nat.reducePow] at h
  simpa only [fiveStageStrangLog, sub_add_eq_sub_sub] using h

end RationalAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

/-- The local logarithm error at the standard parameter retains the individual quintic
commutator weights and the uniform seventh-order word bound, with an eighth-order tail. -/
theorem norm_fiveStageStrangLog_sub_smul_le_septic_at_suzukiP (a b : A) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < δ →
      ‖fiveStageStrangLog a b suzukiP t - t • (a + b)‖ ≤
        t ^ 5 * (∑ i : Fin 8, suzukiQuinticCoeffUpperBound i * ‖binaryQuinticCommutator a b i‖) +
        t ^ 7 * (0.01951 * max ‖a‖ ‖b‖ ^ 7) + K * t ^ 8 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hreal : normedAlgebraReal A = ‹NormedAlgebra ℝ A› := Subsingleton.elim _ _
  have hlocal := norm_fiveStageStrangLog_sub_quintic_sub_septic_le a b suzukiP
  have hseptic := norm_suzukiBchSepticTerm_suzukiP_le a b
  rw [hreal] at hlocal hseptic
  let C := fiveStageStrangArgNormBound a b suzukiP 1
  have hC : 0 ≤ C := fiveStageStrangArgNormBound_nonneg a b suzukiP 1
  refine ⟨1 / (4 * (C + 1)), by positivity, 1536 * C ^ 8, by positivity, ?_⟩
  intro t ht hδ
  have hscale : fiveStageStrangArgNormBound a b suzukiP t = t * C := by
    simp [fiveStageStrangArgNormBound, C, Real.norm_eq_abs, abs_of_nonneg ht]
  have hsmall : fiveStageStrangArgNormBound a b suzukiP t < 1 / 4 := by
    rw [hscale]
    have h : t * (4 * (C + 1)) < 1 := (lt_div_iff₀ (by positivity)).mp hδ
    linarith only [h, ht]
  let e := fiveStageStrangLog a b suzukiP t - t • (a + b)
  let q := t ^ 5 • suzukiQuinticTerm a b suzukiP
  let s := t ^ 7 • suzukiBchSepticTerm a b suzukiP
  have htail : ‖e - q - s‖ ≤ (1536 * C ^ 8) * t ^ 8 := by
    simpa only [e, q, s, hscale, mul_pow, mul_left_comm, mul_assoc, mul_comm] using
      hlocal t isSuzukiCubic_suzukiP hsmall
  calc
    ‖e‖ ≤ ‖e - q‖ + ‖q‖ := norm_le_norm_sub_add ..
    _ ≤ (‖e - q - s‖ + ‖s‖) + ‖q‖ := add_le_add_left (norm_le_norm_sub_add ..) _
    _ = ‖q‖ + ‖s‖ + ‖e - q - s‖ := by ring
    _ ≤ _ := by
      simp only [q, s, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht _)]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (norm_suzukiQuinticTerm_suzukiP_le a b) (pow_nonneg ht _))
        (mul_le_mul_of_nonneg_left hseptic (pow_nonneg ht _)))
        htail

end FQFP.BCH
