# Mapping: `D:\project\CQM1\FQFP\TrotterError\` → "A Theory of Trotter Error" (arXiv:1912.08854)

Source of the paper: `C:\Users\Windows11\Downloads\papers\TrotterError\`
(module files: `prelim.tex`, `type.tex`, `order.tex`, `rep.tex`, `theory.tex`, `prefactor.tex`, `pf2k.tex`, `TrotterErrorTheory.tex`).

All Lean declarations live in `namespace TrotterError`, except `ListLemmas.lean`
(`namespace TrotterError.List`) and `OrderCondition.lean`'s `P.IsOrderOf`
(`namespace TrotterError.ProductFormulaData`, nested inside `TrotterError`).
The full name of every declaration below is therefore `TrotterError.<name>`,
except the `ListLemmas.lean` ones (`TrotterError.List.<name>`) and
`TrotterError.ProductFormulaData.IsOrderOf`.

## 1. File inventory (16 files, 9 021 lines)

| # | File | Lines |
|---|------|-------|
| 1 | `ListLemmas.lean` | 289 |
| 2 | `TimeOrderedExp.lean` | 1103 |
| 3 | `CommutatorExpansion.lean` | 1524 |
| 4 | `CommutatorScaling.lean` | 274 |
| 5 | `ErrorTypes.lean` | 578 |
| 6 | `ExpSMulConj.lean` | 301 |
| 7 | `Integrals.lean` | 147 |
| 8 | `MainTheorem.lean` | 829 |
| 9 | `OrderCondition.lean` | 898 |
| 10 | `OrderingRemoval.lean` | 284 |
| 11 | `Prefactor.lean` | 693 |
| 12 | `Suzuki.lean` | 343 |
| 13 | `Calculus.lean` | 812 |
| 14 | `Commutator.lean` | 620 |
| 15 | `OneNormScaling.lean` | 680 |
| 16 | `ProductFormula.lean` | 802 |
| — | **Total** | **9 021** |

Private declarations: **6 total** — `ProductFormula.lean` lines 398, 405, 412, 419
(`concat_generator_castAdd`, `concat_generator_natAdd`, `concat_evalFactor_castAdd`,
`concat_evalFactor_natAdd`) and `Prefactor.lean` lines 398, 406
(`lie_smul_half_mul_coe`, `lie_mul_neg_half_coe`). No other file has `private`
declarations.

---

## 2. Declarations per file (name, line, full signature)

### 2.1 `ListLemmas.lean` (289 lines) — namespace `TrotterError.List`

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 49 | lemma | `prod_drop_eq_get_mul` | `{ι M : Type*} [Monoid M] (l : List ι) (f : ι → M) (k : Fin l.length) : ((l.drop (k : ℕ)).map f).prod = f (l.get k) * ((l.drop ((k : ℕ) + 1)).map f).prod` |
| 57 | lemma | `prod_map_eq_take_mul_get_mul_drop` | `{ι M : Type*} [BEq ι] [LawfulBEq ι] [Monoid M] (l : List ι) (f : ι → M) (i : ι) (hi : i ∈ l) : (l.map f).prod = ((l.take (l.idxOf i)).map f).prod * f i * ((l.drop (l.idxOf i + 1)).map f).prod` (has `@[to_additive]`) |
| 81 | lemma | `prod_mul_rev_eq_one_of_mul_eq_one` | `{ι M : Type*} [Monoid M] (l : List ι) (f g : ι → M) (hfg : ∀ i, f i * g i = 1) : (l.map f).prod * (l.reverse.map g).prod = 1` |
| 94 | lemma | `rev_mul_prod_eq_one_of_mul_eq_one` | `{ι M : Type*} [Monoid M] (l : List ι) (f g : ι → M) (hgf : ∀ i, g i * f i = 1) : (l.reverse.map g).prod * (l.map f).prod = 1` |
| 109 | lemma | `sum_get_eq_sum_idxOf` | `{ι A : Type*} [Fintype ι] [BEq ι] [LawfulBEq ι] [AddCommMonoid A] {l : List ι} (hnodup : l.Nodup) (hmem : ∀ i : ι, i ∈ l) (G : ι → ℕ → A) : (∑ k : Fin l.length, G (l.get k) (k : ℕ)) = ∑ i : ι, G i (l.idxOf i)` |
| 129 | lemma | `hasDerivAt_list_prod` | `{ι 𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (l : List ι) (f : ι → ℝ → 𝔸) (Df : ι → ℝ → 𝔸) (hf : ∀ i ∈ l, ∀ t : ℝ, HasDerivAt (f i) (Df i t) t) (t : ℝ) : HasDerivAt (fun s : ℝ => (l.map (fun i => f i s)).prod) (∑ k : Fin l.length, ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t * ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t` |
| 173 | lemma | `contDiff_list_prod` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (hf : ∀ i ∈ l, ContDiff ℝ ∞ (f i)) : ContDiff ℝ ∞ (fun t : ℝ => (l.map (fun i => f i t)).prod)` |
| 188 | lemma | `ofFn_castSucc_drop_reverse_prod` | `{s} {𝔸 : Type*} [Monoid 𝔸] (f : Fin (s + 1) → 𝔸) (k : ℕ) (hk : k ≤ s) : f (Fin.last s) * ((List.ofFn (fun i : Fin s => f i.castSucc)).drop k).reverse.prod = ((List.ofFn f).drop k).reverse.prod` |
| 200 | lemma | `ofFn_castSucc_drop_prod` | `{s} {𝔸 : Type*} [Monoid 𝔸] (f : Fin (s + 1) → 𝔸) (k : ℕ) (hk : k ≤ s) : ((List.ofFn (fun i : Fin s => f i.castSucc)).drop k).prod * f (Fin.last s) = ((List.ofFn f).drop k).prod` |
| 211 | lemma | `ofFn_get_comp` | `{α β : Type*} (l : List α) (f : α → β) : List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f` |
| 217 | lemma | `product_ofFn` | `{α β : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → β) : List.product (List.ofFn f) (List.ofFn g) = List.ofFn (fun k : Fin (m * n) => (f k.divNat, g k.modNat))` |
| 260 | lemma | `finRange_add` | `{n m : ℕ} : List.finRange (n + m) = (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n)` |
| 268 | lemma | `finRange_reverse_add` | `{n m : ℕ} : (List.finRange (n + m)).reverse = (List.finRange m).reverse.map (Fin.natAdd n) ++ (List.finRange n).reverse.map (Fin.castAdd m)` |
| 275 | lemma | `finRange_reverse_map_comp_revPerm` | `{n : ℕ} {α : Type*} (g : Fin n → α) : ((List.finRange n).reverse).map (g ∘ Fin.revPerm) = (List.finRange n).map g` |
| 284 | lemma | `sum_fin_cast` | `{s t : ℕ} (h : s = t) {A : Type*} [AddCommMonoid A] (f : Fin s → A) : (∑ i : Fin t, f (Fin.cast h.symm i)) = ∑ i : Fin s, f i` |

Private: 0. **Paper-referenced docstrings: none** (only the module header cites arXiv:1912.08854).

### 2.2 `TimeOrderedExp.lean` (1103 lines) — namespace `TrotterError`

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 61 | noncomputable def | `dysonTerm` | `(H : ℝ → 𝔸) (t₁ : ℝ) : ℕ → ℝ → 𝔸` |
| 69 | noncomputable def | `timeOrderedExp` | `(H : ℝ → 𝔸) (t₁ t₂ : ℝ) : 𝔸` |
| 75 | lemma | `continuous_dysonTerm` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) (n : ℕ) : Continuous (dysonTerm H t₁ n)` |
| 91 | lemma | `integral_mul_integral_pow_div_factorial` | `(f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (n : ℕ) : (∫ τ in a..b, f τ * (∫ u in a..τ, f u) ^ n / Nat.factorial n) = (∫ u in a..b, f u) ^ (n + 1) / Nat.factorial (n + 1)` |
| 128 | lemma | `abs_integral_mul_abs_integral_pow_div_factorial` | `(g : ℝ → ℝ) (hg : Continuous g) (hgnn : ∀ τ, 0 ≤ g τ) (a b : ℝ) (n : ℕ) : \|∫ τ in a..b, g τ * \|∫ u in a..τ, g u\| ^ n / Nat.factorial n\| = \|∫ u in a..b, g u\| ^ (n + 1) / Nat.factorial (n + 1)` |
| 197 | lemma | `norm_dysonTerm_le_abs` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) (n : ℕ) (t : ℝ) : ‖dysonTerm H t₁ n t‖ ≤ ‖(1 : 𝔸)‖ * \|∫ u in t₁..t, ‖H u‖\| ^ n / Nat.factorial n` (has `omit [CompleteSpace 𝔸] in`) |
| 226 | lemma | `summable_dysonTerm_abs` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) : Summable (fun n : ℕ => dysonTerm H t₁ n t₂)` |
| 236 | lemma | `Real.hasSum_pow_div_factorial` | `(x : ℝ) : HasSum (fun n : ℕ => x ^ n / Nat.factorial n) (Real.exp x)` |
| 244 | lemma | `timeOrderedExp_norm_le` | `[NormOneClass 𝔸] (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) : ‖timeOrderedExp H t₁ t₂‖ ≤ Real.exp \|∫ τ in t₁..t₂, ‖H τ‖\|` (has `omit [CompleteSpace 𝔸] in`) |
| 259 | lemma | `timeOrderedExp_initial` | `(H : ℝ → 𝔸) (t₁ : ℝ) : timeOrderedExp H t₁ t₁ = 1` (has `omit [CompleteSpace 𝔸] in`) |
| 271 | lemma | `abs_integral_le_abs_integral_of_mem_Icc` | `{g : ℝ → ℝ} (hg : Continuous g) (hgnn : ∀ t, 0 ≤ g t) (t₁ a b x : ℝ) (hx : x ∈ Set.Icc a b) : \|(∫ u in t₁..x, g u)\| ≤ \|(∫ u in t₁..a, g u)\| + \|(∫ u in t₁..b, g u)\|` |
| 295 | lemma | `continuous_timeOrderedExp` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) : Continuous (fun t => timeOrderedExp H t₁ t)` |
| 326 | lemma | `timeOrderedExp_eq_integral` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) : timeOrderedExp H t₁ t₂ = 1 + ∫ τ in t₁..t₂, H τ * timeOrderedExp H t₁ τ` |
| 385 | lemma | `timeOrderedExp_hasDerivAt` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) : HasDerivAt (fun s => timeOrderedExp H t₁ s) (H t₂ * timeOrderedExp H t₁ t₂) t₂` |
| 406 | lemma | `ode_solution_unique` | `(H : ℝ → 𝔸) (hH : Continuous H) {f g : ℝ → 𝔸} (hf : ∀ t, HasDerivAt f (H t * f t) t) (hg : ∀ t, HasDerivAt g (H t * g t) t) (t₀ : ℝ) (heq : f t₀ = g t₀) : f = g` (has `omit [CompleteSpace 𝔸] in`) |
| 441 | lemma | `timeOrderedExp_mul` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ t₃ : ℝ) : timeOrderedExp H t₁ t₃ = timeOrderedExp H t₂ t₃ * timeOrderedExp H t₁ t₂` |
| 458 | lemma | `timeOrderedExp_mul_inv_self` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) : timeOrderedExp H t₁ t₂ * timeOrderedExp H t₂ t₁ = 1` |
| 465 | lemma | `timeOrderedExp_inv_mul_self` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) : timeOrderedExp H t₂ t₁ * timeOrderedExp H t₁ t₂ = 1` |
| 472 | lemma | `isUnit_timeOrderedExp` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) : IsUnit (timeOrderedExp H t₁ t₂)` |
| 479 | lemma | `integral_sub_pow` | `(a b : ℝ) (n : ℕ) : (∫ τ in a..b, (τ - a) ^ n) = (b - a) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)` |
| 489 | lemma | `dysonTerm_const` | `(H : 𝔸) (t₁ : ℝ) (n : ℕ) (t : ℝ) : dysonTerm (fun _ : ℝ => H) t₁ n t = (Nat.factorial n : ℝ)⁻¹ • ((t - t₁) • H) ^ n` |
| 517 | lemma | `timeOrderedExp_const` | `(H : 𝔸) (t₁ t₂ : ℝ) : timeOrderedExp (fun _ => H) t₁ t₂ = exp ((t₂ - t₁) • H)` |
| 532 | lemma | `timeOrderedExp_hasDerivAt_lower` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) : HasDerivAt (fun s => timeOrderedExp H s t₂) (-(timeOrderedExp H t₁ t₂ * H t₁)) t₁` |
| 555 | lemma | `continuous_timeOrderedExp_lower` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₂ : ℝ) : Continuous (fun t => timeOrderedExp H t t₂)` |
| 565 | lemma | `integral_mul_left` | `(c : 𝔸) (f : ℝ → 𝔸) (hf : Continuous f) (a b : ℝ) : (∫ x in a..b, c * f x) = c * ∫ x in a..b, f x` |
| 573 | lemma | `duhamelParticular_factor` | `(H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R) (t₀ t : ℝ) : (∫ τ in t₀..t, timeOrderedExp H τ t * R τ) = timeOrderedExp H t₀ t * ∫ τ in t₀..t, timeOrderedExp H τ t₀ * R τ` |
| 593 | lemma | `duhamelParticular_hasDerivAt` | `(H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R) (t₀ t : ℝ) : HasDerivAt (fun s => ∫ τ in t₀..s, timeOrderedExp H τ s * R τ) (R t + H t * ∫ τ in t₀..t, timeOrderedExp H τ t * R τ) t` |
| 621 | lemma | `timeOrderedExp_duhamel_hasDerivAt` | `(H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R) (U₀ : 𝔸) (t : ℝ) : HasDerivAt (fun s => timeOrderedExp H 0 s * U₀ + ∫ τ in 0..s, timeOrderedExp H τ s * R τ) (H t * (timeOrderedExp H 0 t * U₀ + ∫ τ in 0..t, timeOrderedExp H τ t * R τ) + R t) t` |
| 637 | lemma | `timeOrderedExp_duhamel_initial` | `(H R : ℝ → 𝔸) (U₀ : 𝔸) : timeOrderedExp H 0 0 * U₀ + ∫ τ in 0..0, timeOrderedExp H τ 0 * R τ = U₀` (has `omit [CompleteSpace 𝔸] in`) |
| 643 | lemma | `timeOrderedExp_duhamel` | `(H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R) {U : ℝ → 𝔸} (U₀ : 𝔸) (hU : ∀ t, HasDerivAt U (H t * U t + R t) t) (hU0 : U 0 = U₀) (t : ℝ) : U t = timeOrderedExp H 0 t * U₀ + ∫ τ in 0..t, timeOrderedExp H τ t * R τ` |
| 677 | lemma | `timeOrderedExp_interaction_picture` | `(A B : ℝ → 𝔸) (hA : Continuous A) (hB : Continuous B) (t : ℝ) : timeOrderedExp (fun τ => A τ + B τ) 0 t = timeOrderedExp A 0 t * timeOrderedExp (fun τ => timeOrderedExp A τ 0 * B τ * timeOrderedExp A 0 τ) 0 t` |
| 725 | lemma | `contDiff_timeOrderedExp` | `(H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) : ContDiff ℝ 1 (fun t => timeOrderedExp H t₁ t)` |
| 740 | lemma | `fundamentalTheorem_timeOrderedExp_of_isUnit` | `(U : ℝ → 𝔸) (hU : ContDiff ℝ 1 U) (hunit : ∀ t, IsUnit (U t)) : IsUnit (U 0) ∧ ∃ H : ℝ → 𝔸, Continuous H ∧ ∀ t, U t = timeOrderedExp H 0 t * U 0` |
| 768 | lemma | `fundamentalTheorem_timeOrderedExp_of_timeOrderedExp` | `(U : ℝ → 𝔸) (hU0 : IsUnit (U 0)) (H : ℝ → 𝔸) (hH : Continuous H) (hEq : ∀ t, U t = timeOrderedExp H 0 t * U 0) : ContDiff ℝ 1 U ∧ ∀ t, IsUnit (U t)` |
| 780 | lemma | `fundamentalTheorem_timeOrderedExp` | `(U : ℝ → 𝔸) : (ContDiff ℝ 1 U ∧ ∀ t, IsUnit (U t)) ↔ IsUnit (U 0) ∧ ∃ H : ℝ → 𝔸, Continuous H ∧ ∀ t, U t = timeOrderedExp H 0 t * U 0` |
| 791 | lemma | `fundamentalTheorem_timeOrderedExp_unique` | `(U : ℝ → 𝔸) (hU0 : IsUnit (U 0)) (H₁ H₂ : ℝ → 𝔸) (hH₁ : Continuous H₁) (hH₂ : Continuous H₂) (hEq₁ : ∀ t, U t = timeOrderedExp H₁ 0 t * U 0) (hEq₂ : ∀ t, U t = timeOrderedExp H₂ 0 t * U 0) : H₁ = H₂` |
| 831 | lemma | `timeOrderedExp_norm_eq_one_of_skewAdjoint` | `[StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : ℝ → 𝔸) (hH : Continuous H) (hskew : ∀ τ, star (H τ) = -H τ) (t₁ t₂ : ℝ) : ‖timeOrderedExp H t₁ t₂‖ = 1` |
| 874 | lemma | `abs_integral_add_le_abs_integral_of_mem_uIcc` | `{f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hfnn : ∀ t, 0 ≤ f t) (hgnn : ∀ t, 0 ≤ g t) (a b x : ℝ) (hx : x ∈ Set.uIcc a b) : \|∫ u in x..b, f u\| + \|∫ u in a..x, g u\| ≤ \|∫ u in a..b, f u + g u\|` |
| 953 | lemma | `timeOrderedExp_sub` | `(H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G) (t₁ t₂ : ℝ) : timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂ = ∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ` |
| 997 | lemma | `norm_timeOrderedExp_sub_integrand_le` | `[NormOneClass 𝔸] (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G) (t₁ t₂ τ : ℝ) (hτ : τ ∈ Set.uIcc t₁ t₂) : ‖timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖ ≤ Real.exp \|∫ u in t₁..t₂, ‖H u‖ + ‖G u‖\| * ‖H τ - G τ‖` (has `omit [CompleteSpace 𝔸] in`) |
| 1051 | lemma | `timeOrderedExp_dist_le` | `[NormOneClass 𝔸] (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G) (t₁ t₂ : ℝ) : ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖ ≤ \|∫ τ in t₁..t₂, ‖H τ - G τ‖\| * Real.exp (\|∫ τ in t₁..t₂, ‖H τ‖ + ‖G τ‖\|)` |
| 1077 | lemma | `timeOrderedExp_dist_le_of_skewAdjoint` | `[StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G) (Hskew : ∀ τ, star (H τ) = -H τ) (hGskew : ∀ τ, star (G τ) = -G τ) (t₁ t₂ : ℝ) : ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖ ≤ \|∫ τ in t₁..t₂, ‖H τ - G τ‖\|` |

Private: 0. **Paper-referenced docstrings: 12** (see §3.2).

### 2.3 `CommutatorExpansion.lean` (1524 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 53 | noncomputable def | `multiConj` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) : 𝔸` |
| 60 | noncomputable def | `commutatorRemainderTerm` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) : 𝔸` |
| 74 | noncomputable def | `commutatorRemainder` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : 𝔸` |
| 81 | noncomputable def | `conjCoeff` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (j : ℕ) : 𝔸` |
| 91 | lemma | `norm_integral_smul_conj_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C) (hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤ C * (\|τ - u\| ^ (q - 1) * \|τ\| ^ m / D)) : ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤ C * (\|τ\| ^ m / D) * (\|τ\| ^ q / (q : ℝ))` |
| 136 | lemma | `norm_conj_smul_integral_le_of_norm_conj_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C) (hconj : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖expSMulConj A X u‖ ≤ C) : ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤ C * \|τ\| ^ (q + m) / ((q : ℝ) * D)` |
| 169 | lemma | `norm_conj_smul_integral_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) : ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤ ‖X‖ * \|τ\| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * \|τ\| * ‖A‖)` |
| 197 | lemma | `norm_exp_mul_expSMulConj_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (τ u : ℝ) (hτ : 0 ≤ τ) (hu : u ∈ Set.uIcc (0 : ℝ) (-τ)) : ‖exp (τ • A) * expSMulConj A X u‖ ≤ ‖X‖ * Real.exp (τ * ‖A‖)` |
| 241 | lemma | `norm_absorbed_conj_smul_integral_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (hτ : 0 ≤ τ) : ‖∫ u in 0..(-τ), (((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) • (exp (τ • A) * expSMulConj A X u)‖ ≤ ‖X‖ * \|τ\| ^ (q + m) / ((q : ℝ) * D) * Real.exp (τ * ‖A‖)` |
| 310 | lemma | `ofFn_take_succ_prod` | `{s : ℕ} {𝔸 : Type*} [Monoid 𝔸] (f : Fin s → 𝔸) (j : Fin s) : ((List.ofFn f).take ((j : ℕ) + 1)).prod = ((List.ofFn f).take (j : ℕ)).prod * f j` |
| 319 | lemma | `prod_exp_mul_drop_reverse_telescope` | `{s : ℕ} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) : (List.ofFn (fun k : Fin s => exp (τ • A k))).prod * (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod` |
| 357 | lemma | `norm_prod_exp_smul_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {ι : Type*} (l : List ι) (A : ι → 𝔸) (t : ι → ℝ) : (l.map (fun i => ‖exp (t i • A i)‖)).prod ≤ Real.exp ((l.map (fun i => \|t i\| * ‖A i‖)).sum)` |
| 381 | lemma | `norm_prod_exp_smul_list_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {s : ℕ} (A : Fin s → 𝔸) (l : List (Fin s)) (τ : ℝ) : ‖(l.map (fun i => exp (τ • A i))).prod‖ ≤ Real.exp (\|τ\| * (l.map (fun i => ‖A i‖)).sum)` |
| 396 | lemma | `norm_ofFn_drop_reverse_prod_exp_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) : ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.prod‖ ≤ Real.exp (((List.ofFn (fun i : Fin s => \|τ\| * ‖A i‖)).drop k).sum)` |
| 422 | lemma | `sum_norm_take_add_point_add_drop` | `{s : ℕ} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) : ((List.ofFn (fun i : Fin s => ‖A i‖)).take (j : ℕ)).sum + ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop ((j : ℕ) + 1)).sum = ∑ i : Fin s, ‖A i‖` |
| 438 | lemma | `norm_point_add_drop_sum_le` | `{s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) : ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum ≤ ∑ i : Fin s, ‖A i‖` |
| 461 | noncomputable def | `layerSum` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) : ℝ` |
| 469 | lemma | `αCommConj_snoc_split` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) : αCommConj A B p = αCommConj (fun i : Fin s => A i.castSucc) B p + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0), (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖` |
| 506 | lemma | `layerSum_le_αCommConj` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) : layerSum A B p ≤ αCommConj A B p` |
| 525 | lemma | `coeff_eq_multinomial_div_factorial` | `{j p : ℕ} (q : Fin (j + 1) → ℕ) (τ : ℝ) (hsum : (∑ i : Fin (j + 1), q i) = p) (hlast : 1 ≤ q (Fin.last j)) : \|τ\| ^ p / ((q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) * ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) = (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * \|τ\| ^ p / (Nat.factorial p : ℝ)` |
| 557 | lemma | `norm_mul_commutatorRemainderTerm_le` | `{s : ℕ} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (L : 𝔸) (C : ℝ) (p : ℕ) (j : Fin s) (q : Fin (j + 1) → ℕ) (τ : ℝ) (hτ : 0 ≤ τ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) (hL : ‖L‖ ≤ Real.exp (\|τ\| * C)) : ‖L * (List.ofFn (fun k : Fin s => exp (τ • A k))).prod * commutatorRemainderTerm A B (-τ) j q‖ ≤ ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ * (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * \|τ\| ^ p / (Nat.factorial p : ℝ) * Real.exp (\|τ\| * (C + ∑ k : Fin s, ‖A k‖))` |
| 703 | lemma | `exp_bound_combine` | `{s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) : Real.exp (((List.ofFn (fun i : Fin s => \|τ\| * ‖A i‖)).drop (j + 1)).sum) * Real.exp (2 * \|τ\| * ‖A j‖) * Real.exp (((List.ofFn (fun i : Fin s => \|τ\| * ‖A i‖)).drop (j + 1)).sum) ≤ Real.exp (2 * \|τ\| * ∑ i : Fin s, ‖A i‖)` |
| 733 | lemma | `norm_ofFn_drop_prod_exp_le` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) : ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).prod‖ ≤ Real.exp (((List.ofFn (fun i : Fin s => \|τ\| * ‖A i‖)).drop k).sum)` |
| 756 | lemma | `norm_commutatorRemainderTerm_le` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) : ‖commutatorRemainderTerm A B τ j q‖ ≤ ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ * (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * \|τ\| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * \|τ\| * ∑ i : Fin s, ‖A i‖)` |
| 822 | lemma | `norm_commutatorRemainder_le_of_term_bound` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (F : ℝ) (hF : 0 ≤ F) (hterm : ∀ j : Fin s, ∀ q : Fin (j + 1) → ℕ, q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0) → ‖commutatorRemainderTerm A B τ j q‖ ≤ ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ * (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * \|τ\| ^ p / (Nat.factorial p : ℝ) * F) : ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * \|τ\| ^ p / (Nat.factorial p : ℝ) * F` |
| 870 | lemma | `norm_mul_commutatorRemainder_le_of_term_bound` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (M : 𝔸) (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (F : ℝ) (hF : 0 ≤ F) (hterm : ∀ j : Fin s, ∀ q : Fin (j + 1) → ℕ, q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0) → ‖M * commutatorRemainderTerm A B τ j q‖ ≤ ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ * (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * \|τ\| ^ p / (Nat.factorial p : ℝ) * F) : ‖M * commutatorRemainder A B p τ‖ ≤ αCommConj A B p * \|τ\| ^ p / (Nat.factorial p : ℝ) * F` |
| 916 | **theorem** | `norm_commutatorRemainder_le` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * \|τ\| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * \|τ\| * ∑ i : Fin s, ‖A i‖)` |
| 926 | lemma | `norm_ofFn_drop_prod_le_one_of_skewAdjoint` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (hskew : ∀ i, star (A i) = -A i) (k : ℕ) (τ : ℝ) : (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map (fun x : 𝔸 => ‖x‖)).prod ≤ 1` |
| 959 | lemma | `norm_conj_smul_integral_le_of_skew` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (hskew : star A = -A) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) : ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤ ‖X‖ * \|τ\| ^ (q + m) / ((q : ℝ) * D)` |
| 970 | lemma | `norm_commutatorRemainderTerm_le_of_skewAdjoint` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (hskew : ∀ i, star (A i) = -A i) (j : Fin s) (q : Fin (j + 1) → ℕ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) : ‖commutatorRemainderTerm A B τ j q‖ ≤ ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ * (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * \|τ\| ^ p / (Nat.factorial p : ℝ)` |
| 1035 | **theorem** | `norm_commutatorRemainder_le_of_skewAdjoint` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (hskew : ∀ i, star (A i) = -A i) : ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * \|τ\| ^ p / (Nat.factorial p : ℝ)` |
| 1049 | lemma | `multiConj_succ` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) : multiConj A B τ = expSMulConj (A (Fin.last s)) (multiConj (fun i : Fin s => A i.castSucc) B τ) τ` |
| 1068 | lemma | `conjCoeff_snoc_summand` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸) (B : 𝔸) (q : Fin s → ℕ) (j : ℕ) : (Nat.factorial j : ℝ)⁻¹ • adPow (A (Fin.last s)) j ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ • adSequence (fun i : Fin s => A i.castSucc) q B) = ((∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))⁻¹ : ℝ) • adSequence A (Fin.snoc q j) B` |
| 1080 | lemma | `conjCoeff_succ` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸) (B : 𝔸) (m : ℕ) : conjCoeff A B m = ∑ j ∈ range (m + 1), ((Nat.factorial j : ℝ)⁻¹ : ℝ) • adPow (A (Fin.last s)) j (conjCoeff (fun i : Fin s => A i.castSucc) B (m - j))` |
| 1109 | lemma | `expSMulConj_mul_cast` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A X : 𝔸) (r : ℝ) (τ : ℝ) : expSMulConj A (X * (r : 𝔸)) τ = expSMulConj A X τ * (r : 𝔸)` |
| 1118 | lemma | `expSMulConj_map_sum` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : 𝔸) (τ : ℝ) {ι : Type*} (s : Finset ι) (f : ι → 𝔸) : expSMulConj A (∑ x ∈ s, f x) τ = ∑ x ∈ s, expSMulConj A (f x) τ` |
| 1126 | lemma | `integral_mul_cast` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (F : ℝ → 𝔸) (c : ℝ) (τ : ℝ) : (∫ u in 0..τ, F u) * (c : 𝔸) = ∫ u in 0..τ, F u * (c : 𝔸)` |
| 1136 | lemma | `expSMulConj_taylor_remainder_smul` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A X : 𝔸) (k j : ℕ) (d : ℝ) (τ : ℝ) (hd : d ≠ 0) : (d⁻¹ • (∫ u in 0..τ, expSMulConj A X (τ - u) * ((u ^ k / (Nat.factorial k : ℝ)) : 𝔸))) * (τ ^ j : 𝔸) = ∫ u in 0..τ, ((τ - u) ^ k * τ ^ j / ((Nat.factorial k : ℝ) * d)) • expSMulConj A X u` |
| 1160 | lemma | `comp_castSucc_castLE` | `{s} {𝔸 : Type*} (A : Fin (s + 1) → 𝔸) (j : Fin s) : (fun i : Fin s => A i.castSucc) ∘ Fin.castLE (Nat.succ_le_of_lt j.2) = A ∘ Fin.castLE (Nat.succ_le_of_lt j.castSucc.2)` |
| 1168 | lemma | `expSMulConj_commutatorRemainderTerm` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) : expSMulConj (A (Fin.last s)) (commutatorRemainderTerm (fun i : Fin s => A i.castSucc) B τ j q) τ = commutatorRemainderTerm A B τ j.castSucc q` |
| 1218 | lemma | `commutatorRemainder_succ` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : commutatorRemainder A B p τ = expSMulConj (A (Fin.last s)) (commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0), commutatorRemainderTerm A B τ (Fin.last s) q` |
| 1239 | lemma | `conjCoeff_sum_of_taylor` | `{s} {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : (∑ j ∈ range p, (∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ • (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) * (τ ^ i : 𝔸)) * (τ ^ j : 𝔸)) = ∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸)` |
| 1285 | lemma | `commutatorRemainderTerm_last` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) (q : Fin s → ℕ) (m : ℕ) : commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q m) = ∫ u in 0..τ, (((τ - u) ^ (m - 1) * τ ^ (∑ i : Fin s, q i) / ((Nat.factorial (m - 1) : ℝ) * ∏ i : Fin s, (Nat.factorial (q i) : ℝ)))) • expSMulConj (A (Fin.last s)) (adPow (A (Fin.last s)) m (adSequence (fun i : Fin s => A i.castSucc) q B)) u` |
| 1306 | lemma | `expSMulConj_taylor_remainder_conjCoeff` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p j : ℕ) (τ : ℝ) : (∫ u in 0..τ, expSMulConj (A (Fin.last s)) (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) * ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸) = ∑ q ∈ finAntidiagonal s j, commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j))` |
| 1401 | lemma | `taylor_remainder_sum` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : (∑ j ∈ range p, (∫ u in 0..τ, expSMulConj (A (Fin.last s)) (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) * ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸)) = ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0), commutatorRemainderTerm A B τ (Fin.last s) q` |
| 1430 | lemma | `expSMulConj_taylor_poly` | `{s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : expSMulConj (A (Fin.last s)) (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ = (∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸)) + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0), commutatorRemainderTerm A B τ (Fin.last s) q` |
| 1471 | **theorem** | `commutatorExpansion_conj` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) : multiConj A B τ = (∑ j ∈ Finset.range p, conjCoeff A B j * (τ ^ j : 𝔸)) + commutatorRemainder A B p τ` |

Private: 0. **Paper-referenced docstrings: 7** (see §3.3).

### 2.4 `CommutatorScaling.lean` (274 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 42 | lemma | `multiConj_ofFn_get` | `[NormedAlgebra ℝ 𝔸] {ι : Type*} (l : List ι) (gen : ι → 𝔸) (B : 𝔸) (τ : ℝ) : multiConj (fun k : Fin l.length => gen (l.get k)) B τ = (l.reverse.map (fun j => exp (τ • gen j))).prod * B * (l.map (fun j => exp (-τ • gen j))).prod` |
| 53 | lemma | `additiveKernel_summand_eq_multiConj` | `[NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (τ : ℝ) : invStrictSuffixFactorProd P H i τ * P.generator H i * strictSuffixFactorProd P H i τ = multiConj (suffixGenerators P H i) (P.generator H i) (-τ)` |
| 64 | lemma | `additiveKernel_full_eq_multiConj` | `[NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (τ : ℝ) : factorProdOver P H (-τ) ((evalIndexList Υ Γ).reverse) * (∑ γ : Fin Γ, H γ) * factorProdOver P H τ (evalIndexList Υ Γ) = multiConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) (-τ)` |
| 75 | lemma | `additiveKernel_eq_sum_multiConj` | `[NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (τ : ℝ) : additiveKernel P H τ = (∑ i : Fin Υ × Fin Γ, multiConj (suffixGenerators P H i) (P.generator H i) (-τ)) - multiConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) (-τ)` |
| 92 | lemma | `commutatorRemainder_isBigO` | `{s} [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) : (fun τ : ℝ => ‖commutatorRemainder A B p τ‖) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p)` |
| 129 | lemma | `additiveKernel_eq_commutatorRemainder_sum` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (τ : ℝ) : additiveKernel P H τ = (∑ i : Fin Υ × Fin Γ, commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)) - commutatorRemainder (orderedGenerators P H) (∑ γ, H γ) p (-τ)` |

Private: 0. **Paper-referenced docstrings: 4** (lines 51, 62, 73, 127).

### 2.5 `ErrorTypes.lean` (578 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 56 | noncomputable def | `factorProdOver` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (s : ℝ) (l : List (Fin Υ × Fin Γ)) : 𝔸` |
| 61 | noncomputable def | `prefixFactorProd` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸` |
| 66 | noncomputable def | `strictSuffixFactorProd` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸` |
| 71 | noncomputable abbrev | `suffixFactorProd` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸` |
| 76 | noncomputable def | `invPrefixFactorProd` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸` |
| 81 | noncomputable def | `invStrictSuffixFactorProd` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸` |
| 86 | lemma | `factorProdOver_evalIndexList` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (τ : ℝ) : factorProdOver P H τ (evalIndexList Υ Γ) = P.eval H τ` |
| 90 | lemma | `evalIndexList_nodup` | `(evalIndexList Υ Γ).Nodup` |
| 95 | lemma | `evalIndexList_mem` | `(i : Fin Υ × Fin Γ) : i ∈ evalIndexList Υ Γ` |
| 103 | lemma | `continuous_evalFactor` | `(H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) : Continuous (fun t : ℝ => P.evalFactor H i t)` (has `@[fun_prop]`) |
| 109 | lemma | `continuous_factorProdOver` | `(H : Fin Γ → 𝔸) (l : List (Fin Υ × Fin Γ)) : Continuous (fun s : ℝ => factorProdOver P H s l)` (has `@[fun_prop]`) |
| 120 | lemma | `continuous_eval` | `(H : Fin Γ → 𝔸) : Continuous (fun t : ℝ => P.eval H t)` (has `@[fun_prop]`) |
| 124 | lemma | `contDiff_eval` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) : ContDiff ℝ ∞ (fun t : ℝ => P.eval H t)` |
| 134 | lemma | `List.prod_exp_mul_rev_neg` | `[NormedAlgebra ℚ 𝔸] {ι : Type*} (l : List ι) (A : ι → 𝔸) : (l.map (fun i => exp (A i))).prod * ((l.reverse).map (fun i => exp (-A i))).prod = 1` (has `omit [NormedAlgebra ℝ 𝔸] in`) |
| 141 | lemma | `List.prod_map_neg_exp_mul_prod` | `[NormedAlgebra ℚ 𝔸] {ι : Type*} (l : List ι) (A : ι → 𝔸) : (l.reverse.map (fun i => exp (-A i))).prod * (l.map (fun i => exp (A i))).prod = 1` (has `omit [NormedAlgebra ℝ 𝔸] in`) |
| 148 | lemma | `evalFactor_commute_coeffOp` | `(H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : P.evalFactor H i t * (P.generator H i) = (P.generator H i) * P.evalFactor H i t` (has `omit [CompleteSpace 𝔸] in`) |
| 155 | lemma | `evalFactor_hasDerivAt` | `(H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : HasDerivAt (fun s : ℝ => P.evalFactor H i s) ((P.generator H i) * P.evalFactor H i t) t` |
| 161 | noncomputable def | `posDerivSum` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸` |
| 170 | noncomputable def | `evalDeriv` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸` |
| 177 | lemma | `posDerivSum_eq_evalDeriv` | `(H : Fin Γ → 𝔸) (t : ℝ) : posDerivSum P H t = evalDeriv P H t` (has `omit [CompleteSpace 𝔸] in`) |
| 227 | **theorem** | `eval_hasDerivAt` | `(H : Fin Γ → 𝔸) (t : ℝ) : HasDerivAt (fun s : ℝ => P.eval H s) (evalDeriv P H t) t` |
| 242 | noncomputable def | `additiveResidual` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸` |
| 247 | **theorem** | `eval_hasDerivAt_additive` | `(H : Fin Γ → 𝔸) (t : ℝ) : HasDerivAt (fun s : ℝ => P.eval H s) ((∑ γ, H γ) * P.eval H t + additiveResidual P H t) t` |
| 254 | noncomputable def | `exponentiatedGenerator` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸` |
| 260 | lemma | `evalFactor_neg_eq_exp_neg` | `(H : Fin Γ → 𝔸) (j : Fin Υ × Fin Γ) (t : ℝ) : P.evalFactor H j (-t) = exp (-((t * P.coeff j) • H (P.perm j.1 j.2)))` (has `omit [CompleteSpace 𝔸] in`) |
| 265 | lemma | `invPrefix_mul_prefix` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : invPrefixFactorProd P H i t * prefixFactorProd P H i t = 1` |
| 276 | lemma | `strictSuffix_mul_invStrictSuffix` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (τ : ℝ) : strictSuffixFactorProd P H i τ * invStrictSuffixFactorProd P H i τ = 1` |
| 287 | lemma | `eval_mul_invStrictSuffix` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (τ : ℝ) : P.eval H τ * invStrictSuffixFactorProd P H i τ = prefixFactorProd P H i τ * P.evalFactor H i τ` |
| 299 | lemma | `invPrefix_mul_eval` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : invPrefixFactorProd P H i t * P.eval H t = suffixFactorProd P H i t` |
| 311 | lemma | `exponentiatedGenerator_mul_eval_eq_evalDeriv` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : exponentiatedGenerator P H t * P.eval H t = evalDeriv P H t` |
| 322 | lemma | `norm_factorProdOver_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (τ : ℝ) (l : List (Fin Υ × Fin Γ)) : ‖factorProdOver P H τ l‖ ≤ Real.exp (\|τ\| * (l.map (fun j => ‖H (P.perm j.1 j.2)‖)).sum)` |
| 347 | lemma | `norm_prefixFactorProd_mul_evalFactor_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (τ : ℝ) : ‖prefixFactorProd P H i τ * P.evalFactor H i τ‖ ≤ Real.exp (\|τ\| * ((((evalIndexList Υ Γ).take ((evalIndexList Υ Γ).idxOf i)).map (fun j => ‖H (P.perm j.1 j.2)‖)).sum + ‖H (P.perm i.1 i.2)‖))` |
| 372 | lemma | `prefix_point_suffix_norm_sum_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) : (((evalIndexList Υ Γ).take ((evalIndexList Υ Γ).idxOf i)).map (fun j => ‖H (P.perm j.1 j.2)‖)).sum + ‖H (P.perm i.1 i.2)‖ + (∑ k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length, ‖suffixGenerators P H i k‖) ≤ (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖` |
| 415 | **theorem** | `eval_hasDerivAt_exponentiated` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : HasDerivAt (fun s : ℝ => P.eval H s) (exponentiatedGenerator P H t * P.eval H t) t` |
| 424 | noncomputable def | `additiveKernel` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) : ℝ → 𝔸` |
| 432 | noncomputable def | `exponentiatedError` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) : ℝ → 𝔸` |
| 437 | noncomputable def | `interactionGenerator` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) : ℝ → 𝔸` |
| 442 | noncomputable def | `multiplicativeError` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸` |
| 447 | lemma | `eval_mul_invFull` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (τ : ℝ) : P.eval H τ * factorProdOver P H (-τ) ((evalIndexList Υ Γ).reverse) = 1` |
| 459 | lemma | `eval_mul_kernel_term` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (τ : ℝ) : P.eval H τ * (invStrictSuffixFactorProd P H i τ * (P.generator H i) * strictSuffixFactorProd P H i τ) = prefixFactorProd P H i τ * (P.generator H i) * suffixFactorProd P H i τ` |
| 490 | lemma | `additiveResidual_eq_eval_mul_kernel` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (τ : ℝ) : additiveResidual P H τ = P.eval H τ * additiveKernel P H τ` |
| 507 | lemma | `continuous_additiveKernel` | `(H : Fin Γ → 𝔸) : Continuous (additiveKernel P H)` (has `@[fun_prop]`) |
| 513 | lemma | `continuous_exponentiatedError` | `(H : Fin Γ → 𝔸) : Continuous (exponentiatedError P H)` (has `@[fun_prop]`) |
| 520 | **theorem** | `errorType_additive` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : P.eval H t = exp (t • (∑ γ, H γ)) + ∫ τ in 0..t, exp ((t - τ) • (∑ γ, H γ)) * P.eval H τ * additiveKernel P H τ` |
| 543 | **theorem** | `errorType_exponentiated` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : P.eval H t = timeOrderedExp (fun τ : ℝ => (∑ γ, H γ) + exponentiatedError P H τ) 0 t` |
| 561 | **theorem** | `errorType_multiplicative` | `[NormedAlgebra ℚ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : P.eval H t = exp (t • (∑ γ, H γ)) * (1 + multiplicativeError P H t)` |

Private: 0. **Paper-referenced docstrings: 16** (lines 60, 65, 70, 75, 80, 240, 246, 253, 286, 298, 309, 423, 431, 436, 441, 519, 542, 560).

### 2.6 `ExpSMulConj.lean` (301 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 46 | noncomputable def | `expSMulConj` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A X : 𝔸) (τ : ℝ) : 𝔸` |
| 52 | lemma | `exp_smul_comm` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : 𝔸) (t : ℝ) : Commute A (exp (t • A))` |
| 57 | lemma | `contDiff_expSMulConj` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A Y : 𝔸) : ContDiff ℝ ∞ (fun t : ℝ => expSMulConj A Y t)` |
| 66 | lemma | `continuous_expSMulConj` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A Y : 𝔸) : Continuous (fun t : ℝ => expSMulConj A Y t)` (has `@[fun_prop]`) |
| 74 | **theorem** | `expSMulConj_hasDerivAt` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (τ : ℝ) : HasDerivAt (fun s => expSMulConj A X s) (expSMulConj A ⁅A, X⁆ τ) τ` |
| 92 | **theorem** | `expSMulConj_sub_eq_integral` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (τ : ℝ) : expSMulConj A X τ - X = ∫ s in 0..τ, expSMulConj A ⁅A, X⁆ s` |
| 107 | lemma | `iteratedDeriv_expSMulConj` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (j : ℕ) : iteratedDeriv j (fun τ => expSMulConj A X τ) = fun τ => expSMulConj A (adPow A j X) τ` |
| 118 | **theorem** | `iteratedDeriv_expSMulConj_zero` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (j : ℕ) : iteratedDeriv j (fun τ => expSMulConj A X τ) 0 = adPow A j X` |
| 124 | lemma | `taylor_poly_zero` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A X : 𝔸) (p : ℕ) (hp : 1 ≤ p) : (∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X * (0 : 𝔸) ^ j)) = X` |
| 135 | **theorem** | `expSMulConj_taylor` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) : expSMulConj A X τ = (∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X) * (τ ^ j : 𝔸)) + ∫ s in 0..τ, expSMulConj A (adPow A p X) (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)` |
| 202 | **theorem** | `norm_expSMulConj_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A Y : 𝔸) (t : ℝ) : ‖expSMulConj A Y t‖ ≤ ‖Y‖ * Real.exp (2 * \|t\| * ‖A‖)` |
| 226 | lemma | `norm_expSMulConj_le_of_skewAdjoint` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (hskew : star A = -A) (u : ℝ) : ‖expSMulConj A X u‖ ≤ ‖X‖` |
| 243 | **theorem** | `norm_expSMulConj_remainder_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) : ‖∫ s in 0..τ, expSMulConj A (adPow A p X) (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖ ≤ ‖adPow A p X‖ * \|τ\| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * \|τ\| * ‖A‖)` |
| 295 | noncomputable def | `expSMulConjLin` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : 𝔸) (τ : ℝ) : 𝔸 →ₗ[ℝ] 𝔸` |

Private: 0. **Paper-referenced docstrings: 3** (lines 132, 240 and the module header).

### 2.7 `Integrals.lean` (147 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 37 | lemma | `integral_abs_sub_pow_uIoc` | `(q : ℕ) (τ : ℝ) (hq : 1 ≤ q) : (∫ u in Set.uIoc (0 : ℝ) τ, \|τ - u\| ^ (q - 1)) = \|τ\| ^ q / (q : ℝ)` |
| 54 | lemma | `integral_abs_pow_sub_div_factorial_uIoc` | `(p : ℕ) (τ : ℝ) (hp : 1 ≤ p) : (∫ s in Set.uIoc (0 : ℝ) τ, \|s\| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) = \|τ\| ^ p / (Nat.factorial p : ℝ)` |
| 77 | lemma | `abs_integral_abs_pow_div_factorial` | `(p : ℕ) (τ : ℝ) (hp : 1 ≤ p) : \|∫ s in 0..τ, \|s\| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)\| = \|τ\| ^ p / (Nat.factorial p : ℝ)` |
| 87 | lemma | `integral_smul_eq_integral_mul_sub` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (F : ℝ → 𝔸) (n : ℕ) (τ : ℝ) : (∫ s in 0..τ, ((τ - s) ^ n / (Nat.factorial n : ℝ)) • F s) = ∫ s in 0..τ, F (τ - s) * ((s ^ n / (Nat.factorial n : ℝ)) : 𝔸)` |
| 102 | lemma | `intervalIntegral_one_sub_pow` | `(p : ℕ) : (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p) = (1 : ℝ) / ((p + 1 : ℕ) : ℝ)` |
| 115 | lemma | `intervalIntegral_const_mul_abs_pow_div_factorial` | `(C : ℝ) (p : ℕ) (t : ℝ) (ht : 0 ≤ t) : ∫ τ in 0..t, C * \|τ\| ^ p / (Nat.factorial p : ℝ) = (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))` |
| 136 | lemma | `intervalIntegral_const_mul_abs_pow_div_factorial_mul` | `(C E : ℝ) (p : ℕ) (t : ℝ) (ht : 0 ≤ t) : ∫ τ in 0..t, C * \|τ\| ^ p / (Nat.factorial p : ℝ) * E = (C / (Nat.factorial p : ℝ)) * E * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))` |

Private: 0. **Paper-referenced docstrings: none** (module header cites arXiv:1912.08854 only).

### 2.8 `MainTheorem.lean` (829 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 49 | lemma | `norm_additiveKernel_le_of_rem_bound` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C) (hrem_i : ∀ i : Fin Υ × Fin Γ, ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤ αCommConj (suffixGenerators P H i) (P.generator H i) p * C) (hrem_all : ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖ ≤ αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C) (hcoeff : (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p) + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) : ‖additiveKernel P H τ‖ ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C` |
| 93 | **theorem** | `norm_additiveKernel_le_of_skewAdjoint` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) (τ : ℝ) : ‖additiveKernel P H τ‖ ≤ 2 * (Υ : ℝ) * (∑ γ, αCommConj (orderedSummandsEval P H) (H γ) p) * \|τ\| ^ p / (Nat.factorial p : ℝ)` |
| 130 | **theorem** | `norm_additiveKernel_le` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) (τ : ℝ) : ‖additiveKernel P H τ‖ ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * \|τ\| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * \|τ\| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)` |
| 198 | lemma | `norm_eval_mul_commutatorRemainderTerm_le` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (p : ℕ) (j : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length) (q : Fin (j + 1) → ℕ) (τ : ℝ) (hτ : 0 ≤ τ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) : ‖P.eval H τ * commutatorRemainderTerm (suffixGenerators P H i) (P.generator H i) (-τ) j q‖ ≤ ‖adSequence (suffixGenerators P H i ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q (P.generator H i)‖ * (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * \|τ\| ^ p / (Nat.factorial p : ℝ) * Real.exp (\|τ\| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)` |
| 275 | lemma | `norm_eval_mul_commutatorRemainderTerm_ordered_le` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (j : Fin (evalIndexList Υ Γ).length) (q : Fin (j + 1) → ℕ) (τ : ℝ) (hτ : 0 ≤ τ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) : ‖P.eval H τ * commutatorRemainderTerm (orderedGenerators P H) (∑ γ : Fin Γ, H γ) (-τ) j q‖ ≤ ‖adSequence (orderedGenerators P H ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q (∑ γ : Fin Γ, H γ)‖ * (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * \|τ\| ^ p / (Nat.factorial p : ℝ) * Real.exp (\|τ\| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)` |
| 329 | lemma | `norm_additiveResidual_le_of_rem_bound` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C) (hrem_i : ∀ i : Fin Υ × Fin Γ, ‖P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤ αCommConj (suffixGenerators P H i) (P.generator H i) p * C) (hrem_all : ‖P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖ ≤ αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C) (hcoeff : (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p) + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) : ‖additiveResidual P H τ‖ ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C` |
| 375 | **theorem** | `norm_additiveResidual_le` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) (τ : ℝ) (hτ : 0 ≤ τ) : ‖additiveResidual P H τ‖ ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * \|τ\| ^ p / (Nat.factorial p : ℝ) * Real.exp (\|τ\| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)` |
| 416 | lemma | `eval_sub_exp_eq_integral_residual` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : P.eval H t - exp (t • ∑ γ : Fin Γ, H γ) = ∫ τ in 0..t, exp ((t - τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ` |
| 431 | **theorem** | `trotter_error_bound_comm_scaling` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) : ∀ t : ℝ, 0 ≤ t → ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) * Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)` |
| 519 | **theorem** | `trotter_error_comm_scaling` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) : (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖) =O[Filter.atTop] (fun t : ℝ ↦ αComm p H * t ^ (p + 1) * Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖))` |
| 542 | **theorem** | `trotter_error_bound_comm_scaling_of_skewAdjoint` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) : ∀ t : ℝ, 0 ≤ t → ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1)` |
| 605 | **theorem** | `trotter_error_comm_scaling_of_skewAdjoint` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) : (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖) =O[Filter.atTop] (fun t : ℝ ↦ αComm p H * t ^ (p + 1))` |
| 628 | lemma | `multiplicativeError_eq_integral_residual` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : multiplicativeError P H t = ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ` |
| 665 | **theorem** | `multiplicative_error_bound_comm_scaling` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) : ∀ t : ℝ, 0 ≤ t → ‖multiplicativeError P H t‖ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) * Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)` |
| 755 | **theorem** | `multiplicative_error_comm_scaling` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) : (fun t : ℝ ↦ ‖multiplicativeError P H t‖) =O[Filter.atTop] (fun t : ℝ ↦ αComm p H * t ^ (p + 1) * Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖))` |
| 776 | lemma | `norm_multiplicativeError_le_norm_sub_of_skewAdjoint` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (t : ℝ) : ‖multiplicativeError P H t‖ ≤ ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖` |
| 797 | **theorem** | `multiplicative_error_bound_comm_scaling_of_skewAdjoint` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) : ∀ t : ℝ, 0 ≤ t → ‖multiplicativeError P H t‖ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1)` |
| 811 | **theorem** | `multiplicative_error_comm_scaling_of_skewAdjoint` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) : (fun t : ℝ ↦ ‖multiplicativeError P H t‖) =O[Filter.atTop] (fun t : ℝ ↦ αComm p H * t ^ (p + 1))` |

Private: 0. **Paper-referenced docstrings: 15** (lines 45, 91, 128, 196, 273, 327, 373, 429, 518, 540, 604, 625, 662, 753, 795).

### 2.9 `OrderCondition.lean` (898 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 63 | def | `ProductFormulaData.IsOrderOf` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (p : ℕ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) : Prop` (fully: `TrotterError.ProductFormulaData.IsOrderOf`) |
| 74 | lemma | `eventually_abs_le_one_nhds_zero` | `∀ᶠ τ in 𝓝 (0 : ℝ), \|τ\| ≤ 1` |
| 81 | lemma | `isBigO_abs_pow_abs_pow_of_le` | `{m n : ℕ} (hmn : m ≤ n) : (fun τ : ℝ => \|τ\| ^ n) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => \|τ\| ^ m)` |
| 91 | lemma | `isBigO_norm_iff_iteratedDeriv_lt_eq_zero` | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ ∞ F) : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔ ∀ j : ℕ, j < p → iteratedDeriv j F 0 = 0` |
| 118 | **theorem** | `orderCond_add` | `(F G : ℝ → 𝔸) (p q : ℕ) (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)) (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ q)) : (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ min p q)` |
| 144 | **theorem** | `orderCond_mul` | `(F G : ℝ → 𝔸) (p q : ℕ) (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)) (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ q)) : (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + q))` |
| 159 | **theorem** | `orderCond_deriv_iff` | `[NormedAlgebra ℝ 𝔸] (F : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + 1)) ↔ F 0 = 0 ∧ (fun τ => ‖deriv F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)` |
| 184 | lemma | `contDiff_integral_of_contDiff` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (F : ℝ → 𝔸) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fun t => ∫ τ in 0..t, F τ)` |
| 199 | **theorem** | `orderCond_integral_iff` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (F : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔ (fun t => ‖∫ τ in 0..t, F τ‖) =O[𝓝 (0 : ℝ)] (fun t => t ^ (p + 1))` |
| 233 | lemma | `contDiff_timeOrderedExp_of_contDiff` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : ℝ → 𝔸) (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (fun t => timeOrderedExp H 0 t)` |
| 259 | lemma | `iteratedDeriv_timeOrderedExp_succ` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : ℝ → 𝔸) (hH : ContDiff ℝ ∞ H) (j : ℕ) : iteratedDeriv (j + 1) (fun t => timeOrderedExp H 0 t) 0 = (∑ i ∈ Finset.range j, (j.choose i : 𝔸) * iteratedDeriv i H 0 * iteratedDeriv (j - i) (fun t => timeOrderedExp H 0 t) 0) + iteratedDeriv j H 0` |
| 292 | lemma | `timeOrderedExp_iteratedDeriv_eq_iff` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (F G : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) : (∀ j, j < p → iteratedDeriv j F 0 = iteratedDeriv j G 0) ↔ (∀ j, j ≤ p → iteratedDeriv j (fun t => timeOrderedExp F 0 t) 0 = iteratedDeriv j (fun t => timeOrderedExp G 0 t) 0)` |
| 373 | **theorem** | `orderCond_exp_iff` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (F G : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) : (fun τ => ‖F τ - G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔ (fun t => ‖timeOrderedExp F 0 t - timeOrderedExp G 0 t‖) =O[𝓝 (0 : ℝ)] (fun t => t ^ (p + 1))` |
| 420 | noncomputable def | `iteratedIntegralMonomial` | `(Γ : ℕ) (p : Fin Γ → ℕ) : ℝ → ℝ` |
| 427 | noncomputable def | `monomialConstant` | `(Γ : ℕ) (p : Fin Γ → ℕ) : ℝ` |
| 433 | lemma | `iteratedIntegralMonomial_eq` | `(Γ : ℕ) (p : Fin Γ → ℕ) (t : ℝ) : iteratedIntegralMonomial Γ p t = monomialConstant Γ p * t ^ ((∑ i : Fin Γ, p i) + Γ)` |
| 466 | **theorem** | `monomial_integral_order` | `(Γ : ℕ) (p : Fin Γ → ℕ) : (fun t : ℝ => iteratedIntegralMonomial Γ p t) =O[𝓝 (0 : ℝ)] (fun t => t ^ ((∑ i : Fin Γ, p i) + Γ))` |
| 483 | lemma | `isBigO_norm_one_of_continuous` | `{F : ℝ → 𝔸} (hF : Continuous F) : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ))` |
| 488 | lemma | `orderCond_mul_left` | `{F G : ℝ → 𝔸} (p : ℕ) (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ))) (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)) : (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)` |
| 495 | lemma | `orderCond_mul_right` | `{F G : ℝ → 𝔸} (p : ℕ) (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)) (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ))) : (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)` |
| 502 | lemma | `isUnit_eval` | `[NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (τ : ℝ) : IsUnit (P.eval H τ)` |
| 514 | lemma | `inverse_isBigO_one_of_continuous_unit` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {U : ℝ → 𝔸} (hU : Continuous U) (hU0 : IsUnit (U 0)) : (fun τ => ‖Ring.inverse (U τ)‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ))` |
| 522 | lemma | `contDiff_factorProdOver` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (l : List (Fin Υ × Fin Γ)) : ContDiff ℝ ∞ (fun s : ℝ => factorProdOver P H s l)` |
| 531 | lemma | `contDiff_additiveKernel` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) : ContDiff ℝ ∞ (additiveKernel P H)` |
| 559 | lemma | `contDiff_exponentiatedError` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) : ContDiff ℝ ∞ (exponentiatedError P H)` |
| 583 | lemma | `eval_sub_exp_eq_exp_mul_integral` | `[NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : P.eval H t - exp (t • ∑ γ, H γ) = exp (t • ∑ γ, H γ) * ∫ τ in 0..t, (exp ((-τ) • ∑ γ, H γ) * P.eval H τ) * additiveKernel P H τ` |
| 614 | lemma | `errorOrderCond_additive_iff` | `[NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (p : ℕ) (H : Fin Γ → 𝔸) : P.IsOrderOf p H ↔ (fun τ => ‖additiveKernel P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)` |
| 690 | lemma | `errorOrderCond_exponentiated_iff` | `[NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (p : ℕ) (H : Fin Γ → 𝔸) : P.IsOrderOf p H ↔ (fun τ => ‖exponentiatedError P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)` |
| 728 | lemma | `errorOrderCond_multiplicative_iff` | `[NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (p : ℕ) (H : Fin Γ → 𝔸) : P.IsOrderOf p H ↔ (fun t => ‖multiplicativeError P H t‖) =O[𝓝 (0 : ℝ)] (fun t => t ^ (p + 1))` |
| 764 | **theorem** | `errorOrderCond_iff` | `[NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (p : ℕ) (H : Fin Γ → 𝔸) : List.TFAE [P.IsOrderOf p H, (fun τ => ‖additiveKernel P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p), (fun τ => ‖exponentiatedError P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p), (fun t => ‖multiplicativeError P H t‖) =O[𝓝 (0 : ℝ)] (fun t => t ^ (p + 1))]` |
| 780 | lemma | `contDiff_algebraMap` | `[NormedAlgebra ℝ 𝔸] : ContDiff ℝ ∞ (fun τ : ℝ => (τ : 𝔸))` |
| 787 | lemma | `contDiff_algebraMap_pow` | `[NormedAlgebra ℝ 𝔸] (k : ℕ) : ContDiff ℝ ∞ (fun τ : ℝ => (τ ^ k : 𝔸))` |
| 791 | lemma | `contDiff_monomial` | `[NormedAlgebra ℝ 𝔸] (c : 𝔸) (k : ℕ) : ContDiff ℝ ∞ (fun τ : ℝ => c * (τ ^ k : 𝔸))` |
| 798 | lemma | `iteratedDeriv_algebraMap_pow` | `[NormedAlgebra ℝ 𝔸] (m n : ℕ) (x : ℝ) : iteratedDeriv n (fun τ : ℝ => (τ : 𝔸) ^ m) x = (m.descFactorial n : ℝ) • (x : 𝔸) ^ (m - n)` |
| 812 | lemma | `iteratedDeriv_polynomial_zero` | `[NormedAlgebra ℝ 𝔸] (p : ℕ) (T : ℕ → 𝔸) (j : ℕ) (hj : j < p) : iteratedDeriv j (fun τ : ℝ => ∑ k ∈ Finset.range p, T k * (τ ^ k : 𝔸)) 0 = (Nat.factorial j : ℝ) • T j` |
| 850 | **theorem** | `polynomial_isBigO_iff_coeffs_zero` | `[NormedAlgebra ℝ 𝔸] (p : ℕ) (T : ℕ → 𝔸) : (fun τ : ℝ => ‖∑ j ∈ Finset.range p, T j * (τ ^ j : 𝔸)‖) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) ↔ ∀ j : ℕ, j < p → T j = 0` |
| 885 | lemma | `neg_pow_isBigO` | `(p : ℕ) : (fun τ : ℝ => (-τ) ^ p) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p)` |
| 895 | lemma | `tendsto_neg_nhds_zero` | `Filter.Tendsto (fun a : ℝ => -a) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))` |

Private: 0. **Paper-referenced docstrings: 12** (lines 17–38 header, 61, 89, 117, 142, 158, 198, 415, 465, 761).

### 2.10 `OrderingRemoval.lean` (284 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 35 | **abbrev** | `Antidiag` | `(s p : ℕ) : Type` ( := `{q : Fin s → ℕ // q ∈ finAntidiagonal s p}`) |
| 38 | noncomputable def | `layerAt` | `{n : ℕ} (p : ℕ) (q : Antidiag n p) (j : Fin p) : Fin n` |
| 44 | noncomputable def | `stageOf` | `{Υ Γ : ℕ} (p : ℕ) (q : Antidiag (Υ * Γ) p) (j : Fin p) : Fin Υ` |
| 51 | noncomputable def | `orderedLayers` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (γ : Fin Γ) (p : ℕ) (q : Antidiag (Υ * Γ) p) : Fin (p + 1) → Fin Γ` |
| 57 | lemma | `orderedLayers_succ` | `(γ : Fin Γ) (p : ℕ) (q : Antidiag (Υ * Γ) p) (j : Fin p) : orderedLayers P γ p q j.succ = P.perm (stageOf p q j) ((layerAt p q j).modNat)` |
| 73 | lemma | `orderedLayers_zero` | `(γ : Fin Γ) (p : ℕ) (q : Antidiag (Υ * Γ) p) : orderedLayers P γ p q 0 = γ` |
| 86 | lemma | `adSequence_orderedSummands_eq_nestedComm` | `[Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (γ : Fin Γ) (p : ℕ) (q : Antidiag (Υ * Γ) p) : adSequence (orderedSummands P H) q.1 (H γ) = nestedComm (H ∘ orderedLayers P γ p q)` |
| 109 | lemma | `layerAt_eq_of_orderedLayers_stageOf` | `(γ : Fin Γ) (p : ℕ) (q : Antidiag (Υ * Γ) p) (j : Fin p) : layerAt p q j = finProdFinEquiv (stageOf p q j, (P.perm (stageOf p q j)).symm (orderedLayers P γ p q j.succ))` |
| 123 | lemma | `orderedLayers_stageOf_injective` | `(γ : Fin Γ) (p : ℕ) : Function.Injective (fun q : Antidiag (Υ * Γ) p => (orderedLayers P γ p q, stageOf p q))` |
| 151 | lemma | `fiber_card_le` | `(γ : Fin Γ) (p : ℕ) (γ' : Fin (p + 1) → Fin Γ) : (univ.filter (fun q : Antidiag (Υ * Γ) p => orderedLayers P γ p q = γ')).card ≤ (Υ : ℕ) ^ p` |
| 175 | lemma | `αCommConj_le_mul_sum` | `[Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) : αCommConj A B p ≤ (Nat.factorial p : ℝ) * ∑ q ∈ finAntidiagonal s p, ‖adSequence A q B‖` |
| 190 | lemma | `sum_adSequence_norm_le` | `[Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (γ : Fin Γ) (p : ℕ) : (∑ q ∈ finAntidiagonal (Υ * Γ) p, ‖adSequence (orderedSummands P H) q (H γ)‖) ≤ (Υ : ℝ) ^ p * (∑ γ' ∈ univ.filter (fun γ' : Fin (p + 1) → Fin Γ => γ' 0 = γ), ‖nestedComm (H ∘ γ')‖)` |
| 224 | **theorem** | `αCommConj_sum_le_αComm` | `[Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) : (∑ γ : Fin Γ, αCommConj (orderedSummands P H) (H γ) p) ≤ (Nat.factorial p : ℝ) * (Υ : ℝ) ^ p * αComm p H` |
| 266 | lemma | `sum_αCommConj_orderedSummandsEval_le` | `[Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) : (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) ≤ (Nat.factorial p : ℝ) * (Υ : ℝ) ^ p * αComm p H` |
| 275 | lemma | `two_mul_commScaling_div_factorial_le` | `[Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) : (2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) / (Nat.factorial p : ℝ) ≤ 2 * (Υ : ℝ) ^ (p + 1) * αComm p H` |

Private: 0. **Paper-referenced docstrings: 4** (lines 221, 262, 273, and the module header).

### 2.11 `Prefactor.lean` (693 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 50 | lemma | `exp_mul_exp_sub_exp_add_eq_integral` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) (t : ℝ) : exp (t • B) * exp (t • A) - exp (t • (A + B)) = ∫ τ in 0..t, exp ((t - τ) • (A + B)) * (expSMulConj B A τ - A) * exp (τ • B) * exp (τ • A)` |
| 114 | **theorem** | `firstOrder_twoTerm` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) : ∀ t : ℝ, 0 ≤ t → ‖exp (t • B) * exp (t • A) - exp (t • (A + B))‖ ≤ (t ^ 2 / 2) * ‖⁅B, A⁆‖` |
| 190 | **abbrev** | `upperSum` | `{𝔸 : Type*} [AddCommMonoid 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (j : Fin Γ) : 𝔸` |
| 194 | lemma | `upperSum_zero_eq` | `{𝔸 : Type*} [AddCommMonoid 𝔸] {n : ℕ} (K : Fin (n + 1) → 𝔸) : upperSum K 0 = ∑ i : Fin n, K i.succ` |
| 201 | lemma | `upperSum_succ` | `{𝔸 : Type*} [AddCommMonoid 𝔸] {n : ℕ} (K : Fin (n + 1) → 𝔸) (i : Fin n) : upperSum (fun j : Fin n => K j.succ) i = upperSum K i.succ` |
| 209 | lemma | `norm_lieTrotter_le_one_of_skew` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (h : ∀ γ, star (K γ) = -(K γ)) (t : ℝ) : ‖lieTrotter K t‖ ≤ 1` |
| 226 | **theorem** | `firstOrder_bound` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (Γ : ℕ) (K : Fin Γ → 𝔸) (h : ∀ γ, star (K γ) = -(K γ)) : ∀ t : ℝ, 0 ≤ t → ‖lieTrotter K t - exp (t • ∑ γ, K γ)‖ ≤ (t ^ 2 / 2) * ∑ γ₁ : Fin Γ, ‖⁅upperSum K γ₁, K γ₁⁆‖` |
| 290 | noncomputable def | `secondOrderKernel` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A B : 𝔸) (τ : ℝ) : 𝔸` |
| 296 | lemma | `secondOrder_sub_eq_integral` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) (t : ℝ) : exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B)) = ∫ τ in 0..t, exp ((t - τ) • (A + B)) * exp ((τ / 2) • A) * secondOrderKernel A B τ * exp (τ • B) * exp ((τ / 2) • A)` |
| 398 | private lemma | `lie_smul_half_mul_coe` | (private — omitted) |
| 406 | private lemma | `lie_mul_neg_half_coe` | (private — omitted) |
| 419 | lemma | `expSMulConj_taylor_two` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (τ : ℝ) : expSMulConj A X τ = X + ⁅A, X⁆ * (τ : 𝔸) + ∫ s in 0..τ, expSMulConj A (adPow A 2 X) (τ - s) * (s : 𝔸)` |
| 433 | lemma | `secondOrderKernel_eq_remainder` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A B : 𝔸) (τ : ℝ) : secondOrderKernel A B τ = (∫ s in 0..τ, expSMulConj B ((1 / 2 : ℝ) • adPow B 2 A) (τ - s) * (s : 𝔸)) - (∫ s in 0..-(τ / 2), expSMulConj A (adPow A 2 B) ((-(τ / 2)) - s) * (s : 𝔸))` |
| 447 | lemma | `norm_expSMulConj_taylor_remainder_le_of_skew` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (A Y : 𝔸) (hA : star A = -A) (τ : ℝ) : ‖∫ s in 0..τ, expSMulConj A Y (τ - s) * (s : 𝔸)‖ ≤ ‖Y‖ * (\|τ\| ^ 2 / 2)` |
| 482 | lemma | `norm_secondOrderKernel_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) (τ : ℝ) : ‖secondOrderKernel A B τ‖ ≤ (τ ^ 2 / 4) * ‖adPow B 2 A‖ + (τ ^ 2 / 8) * ‖adPow A 2 B‖` |
| 509 | **theorem** | `secondOrder_twoTerm` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (A B : 𝔸) (hA : star A = -A) (hB : star B = -B) : ∀ t : ℝ, 0 ≤ t → ‖exp ((t / 2) • A) * exp (t • B) * exp ((t / 2) • A) - exp (t • (A + B))‖ ≤ (t ^ 3 / 12) * ‖adPow B 2 A‖ + (t ^ 3 / 24) * ‖adPow A 2 B‖` |
| 598 | lemma | `norm_suzuki2_le_one_of_skew` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (h : ∀ γ, star (K γ) = -(K γ)) (t : ℝ) : ‖suzuki2 K t‖ ≤ 1` |
| 622 | **theorem** | `secondOrder_bound` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (Γ : ℕ) (K : Fin Γ → 𝔸) (h : ∀ γ, star (K γ) = -(K γ)) : ∀ t : ℝ, 0 ≤ t → ‖suzuki2 K t - exp (t • ∑ γ, K γ)‖ ≤ (t ^ 3 / 12) * ∑ γ₁ : Fin Γ, ‖adPow (upperSum K γ₁) 2 (K γ₁)‖ + (t ^ 3 / 24) * ∑ γ₁ : Fin Γ, ‖adPow (K γ₁) 2 (upperSum K γ₁)‖` |

Private: 2. **Paper-referenced docstrings: 13** (lines 47, 112, 224, 288, 295, 417, 431, 445, 480, 507, 620, and the module header).

### 2.12 `Suzuki.lean` (343 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 51 | noncomputable def | `lieTrotter` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (t : ℝ) : 𝔸` |
| 61 | noncomputable def | `suzuki2` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (t : ℝ) : 𝔸` |
| 69 | noncomputable def | `suzukiU` | `(k : ℕ) : ℝ` |
| 75 | noncomputable def | `suzuki` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] : ℕ → {Γ : ℕ} → (Fin Γ → 𝔸) → ℝ → 𝔸` |
| 86 | def | `lieTrotterData` | `(Γ : ℕ) : ProductFormulaData 1 Γ` (has `@[reducible]`) |
| 93 | noncomputable def | `suzuki2Data` | `(Γ : ℕ) : ProductFormulaData 2 Γ` (has `@[reducible]`) |
| 99 | lemma | `lieTrotterData_evalIndexList` | `ProductFormulaData.evalIndexList 1 Γ = ((List.finRange Γ).reverse).map (fun γ => ((0 : Fin 1), γ))` |
| 107 | lemma | `lieTrotterData_eval_eq` | `[NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : (lieTrotterData Γ).eval H t = (((List.finRange Γ).reverse).map (fun γ => exp (t • H γ))).prod` |
| 121 | lemma | `lieTrotter_eq_prod` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (K : Fin Γ → 𝔸) (t : ℝ) : lieTrotter K t = (((List.finRange Γ).reverse).map (fun γ => exp (t • K γ))).prod` |
| 136 | **theorem** | `lieTrotter_eq_eval` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (K : Fin Γ → 𝔸) (t : ℝ) : lieTrotter K t = (lieTrotterData Γ).eval K t` |
| 141 | lemma | `suzuki2Data_evalIndexList` | `ProductFormulaData.evalIndexList 2 Γ = ((List.finRange Γ).reverse).map (fun γ => ((1 : Fin 2), γ)) ++ ((List.finRange Γ).reverse).map (fun γ => ((0 : Fin 2), γ))` |
| 150 | lemma | `suzuki2Data_eval_eq` | `[NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : (suzuki2Data Γ).eval H t = (((List.finRange Γ).map (fun γ => exp ((t / 2) • H γ))).prod) * (((List.finRange Γ).reverse).map (fun γ => exp ((t / 2) • H γ))).prod` |
| 180 | lemma | `suzuki2_eq_prod` | `[NormedAlgebra ℝ 𝔸] (K : Fin Γ → 𝔸) (t : ℝ) : suzuki2 K t = (((List.finRange Γ).map (fun γ => exp ((t / 2) • K γ))).prod) * (((List.finRange Γ).reverse).map (fun γ => exp ((t / 2) • K γ))).prod` |
| 200 | **theorem** | `suzuki2_eq_eval` | `[NormedAlgebra ℝ 𝔸] (K : Fin Γ → 𝔸) (t : ℝ) : suzuki2 K t = (suzuki2Data Γ).eval K t` |
| 208 | lemma | `suzukiU_rpow_le_two` | `(k : ℕ) (hk : 2 ≤ k) : (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) ≤ 2` |
| 229 | lemma | `suzukiU_denom_pos` | `(k : ℕ) (hk : 2 ≤ k) : 0 < (4 : ℝ) - (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1))` |
| 235 | lemma | `suzukiU_pos` | `(k : ℕ) (hk : 2 ≤ k) : 0 < suzukiU k` |
| 240 | lemma | `suzukiU_le_one_half` | `(k : ℕ) (hk : 2 ≤ k) : suzukiU k ≤ 1 / 2` |
| 247 | lemma | `abs_suzukiU_le_one` | `(k : ℕ) (hk : 2 ≤ k) : \|suzukiU k\| ≤ 1` |
| 254 | lemma | `abs_one_sub_four_mul_suzukiU_le_one` | `(k : ℕ) (hk : 2 ≤ k) : \|1 - 4 * suzukiU k\| ≤ 1` |
| 265 | def | `suzukiStages` | `: ℕ → ℕ` |
| 271 | lemma | `suzukiStages_five` | `(k : ℕ) : ((((suzukiStages (k + 1) + suzukiStages (k + 1)) + suzukiStages (k + 1)) + suzukiStages (k + 1)) + suzukiStages (k + 1)) = suzukiStages (k + 2)` |
| 279 | noncomputable def | `suzukiData` | `: (k : ℕ) → (Γ : ℕ) → ProductFormulaData (suzukiStages k) Γ` |
| 295 | lemma | `suzukiData_succ_eval` | `(k : ℕ) [NormedSpace ℝ 𝔸] (K : Fin Γ → 𝔸) (t : ℝ) : (suzukiData (k + 2) Γ).eval K t = (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2 * (suzukiData (k + 1) Γ).eval K ((1 - 4 * suzukiU (k + 2)) * t) * (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2` |
| 321 | lemma | `suzuki_succ_eq_eval` | `[NormedAlgebra ℝ 𝔸] (K : Fin Γ → 𝔸) (k : ℕ) (t : ℝ) : suzuki (k + 1) K t = (suzukiData (k + 1) Γ).eval K t` |
| 337 | **theorem** | `suzuki_eq_eval` | `[NormedAlgebra ℝ 𝔸] (K : Fin Γ → 𝔸) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) : suzuki k K t = (suzukiData k Γ).eval K t` |

Private: 0. **Paper-referenced docstrings: 9** (lines 15–19 header, 48, 57, 67, 72, 84, 91, 277, 293).

### 2.13 `Calculus.lean` (812 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 44 | **theorem** | `iteratedDeriv_exp_smul_const` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (q : ℕ) : iteratedDeriv q (fun u : ℝ => exp (u • A)) = fun u : ℝ => A ^ q * exp (u • A)` |
| 59 | lemma | `contDiffAt_list_prod` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ) (t : ℝ) (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) : ContDiffAt ℝ n (fun t : ℝ => (l.map (fun i => f i t)).prod) t` |
| 71 | lemma | `natCast_mul_smul_eq` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (a b : ℕ) (x y : 𝔸) : (a : 𝔸) * x * ((b : ℝ) • y) = ((a * b : ℕ) : ℝ) • (x * y)` |
| 78 | lemma | `multinomial_image` | `{α β : Type*} [DecidableEq β] (s : Finset α) (e : α → β) (he : Set.InjOn e s) (f : β → ℕ) : Nat.multinomial (s.image e) f = Nat.multinomial s (f ∘ e)` |
| 84 | lemma | `multinomial_fin_succ` | `{m : ℕ} (k : ℕ) (q : Fin m → ℕ) : Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) = (k + ∑ i : Fin m, q i).choose k * Nat.multinomial (Finset.univ : Finset (Fin m)) q` |
| 107 | lemma | `sum_finAntidiagonal_succ` | `{𝔸 : Type*} [AddCommMonoid 𝔸] (m n : ℕ) (G : (Fin (m + 1) → ℕ) → 𝔸) : (∑ q' ∈ Finset.finAntidiagonal (m + 1) n, G q') = ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k), G (Fin.cons k q)` |
| 146 | lemma | `finAntidiagonal_eq_piAntidiag_univ` | `(m n : ℕ) : Finset.finAntidiagonal m n = Finset.piAntidiag (Finset.univ : Finset (Fin m)) n` |
| 152 | lemma | `finAntidiagonal_zero` | `(n : ℕ) : Finset.finAntidiagonal 0 n = if n = 0 then {0} else ∅` |
| 164 | **theorem** | `iteratedDeriv_ofFn_prod` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {m : ℕ} (f : Fin m → ℝ → 𝔸) (n : ℕ) (t : ℝ) (hf : ∀ i, ContDiffAt ℝ n (f i) t) : iteratedDeriv n (fun t : ℝ => (List.ofFn (fun i : Fin m => f i t)).prod) t = ∑ q ∈ Finset.finAntidiagonal m n, (Nat.multinomial (Finset.univ : Finset (Fin m)) q : ℝ) • (List.ofFn (fun i : Fin m => iteratedDeriv (q i) (f i) t)).prod` |
| 230 | **theorem** | `iteratedDeriv_list_prod_general` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ) (t : ℝ) (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) : iteratedDeriv n (fun t : ℝ => (l.map (fun i => f i t)).prod) t = ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin l.length)) n, (Nat.multinomial (Finset.univ : Finset (Fin l.length)) q : ℝ) • (List.ofFn (fun j : Fin l.length => iteratedDeriv (q j) (f (l.get j)) t)).prod` |
| 248 | lemma | `sum_piAntidiag_univ_equiv` | `{α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β) (n : ℕ) {𝕄 : Type*} [AddCommMonoid 𝕄] (G : (α → ℕ) → 𝕄) : (∑ q ∈ Finset.piAntidiag (Finset.univ : Finset α) n, G q) = ∑ q' ∈ Finset.piAntidiag (Finset.univ : Finset β) n, G (q' ∘ e)` |
| 277 | lemma | `multinomial_univ_equiv` | `{α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (q : β → ℕ) : Nat.multinomial (Finset.univ : Finset β) q = Nat.multinomial (Finset.univ : Finset α) (q ∘ e)` |
| 285 | lemma | `contDiffAt_exp_smul_const` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (m : ℕ) (t : ℝ) : ContDiffAt ℝ m (fun u : ℝ => exp (u • A)) t` |
| 292 | lemma | `contDiff_exp_smul_const` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) : ContDiff ℝ ∞ (fun t : ℝ => exp (t • A))` |
| 304 | lemma | `taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below` | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E) (n : ℕ) {x₀ x : ℝ} (h0 : ∀ k < n, iteratedDeriv k F x₀ = 0) : taylorWithinEval F n Set.univ x₀ x = (x - x₀) ^ n • ((Nat.factorial n : ℝ)⁻¹ • iteratedDeriv n F x₀)` |
| 323 | **theorem** | `isBigO_norm_iff_iteratedDeriv_eq_zero` | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ ∞ F) : (fun t : ℝ => ‖F t‖) =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1)) ↔ ∀ j : ℕ, j ≤ p → iteratedDeriv j F 0 = 0` |
| 419 | lemma | `taylorWithinEval_eq_zero_of_iteratedDeriv_eq_zero` | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {p : ℕ} {t : ℝ} (hf : ContDiff ℝ (p + 1) f) (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) (ht : t ≠ 0) : taylorWithinEval f p (Set.uIcc 0 t) 0 t = 0` |
| 438 | lemma | `taylor_paper_scalar_eq` | `(p : ℕ) (t u : ℝ) : t * ((t - u * t) ^ p / (Nat.factorial p : ℝ)) = (p + 1 : ℝ) * ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ)))` |
| 449 | **theorem** | `taylor_integral_remainder_iteratedDeriv_zero` | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {p : ℕ} {t : ℝ} (hf : ContDiff ℝ (p + 1) f) (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) : f t = ∫ s in (0 : ℝ)..t, ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s` |
| 475 | **theorem** | `taylor_integral_remainder_iteratedDeriv_zero_paper` | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {p : ℕ} {t : ℝ} (hf : ContDiff ℝ (p + 1) f) (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) : f t = (p + 1 : ℝ) • ∫ u in (0 : ℝ)..(1 : ℝ), ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) • iteratedDeriv (p + 1) f (u * t)` |
| 508 | lemma | `norm_exp_term_le` | `[NormOneClass 𝔸] (a : 𝔸) (n : ℕ) : ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ ≤ ‖a‖ ^ n / Nat.factorial n` |
| 516 | lemma | `norm_exp_le` | `[NormOneClass 𝔸] (a : 𝔸) : ‖exp a‖ ≤ Real.exp ‖a‖` |
| 531 | lemma | `norm_exp_smul_of_skewAdjoint` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] {a : 𝔸} (ha : star a = -a) (t : ℝ) : ‖exp (t • a)‖ = 1` |
| 543 | **theorem** | `norm_pow_mul_exp_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸] (H : 𝔸) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) : ‖H ^ k * exp (s • H)‖ ≤ ‖H‖ ^ k * Real.exp (s * ‖H‖)` |
| 558 | lemma | `sum_finAntidiagonal_snoc` | `{𝔸 : Type*} [AddCommMonoid 𝔸] (m n : ℕ) (G : (Fin (m + 1) → ℕ) → 𝔸) : (∑ q' ∈ finAntidiagonal (m + 1) n, G q') = ∑ k ∈ range (n + 1), ∑ q ∈ finAntidiagonal m (n - k), G (Fin.snoc q k)` |
| 593 | lemma | `multinomial_snoc_zero` | `{m : ℕ} (q : Fin m → ℕ) : Nat.multinomial (univ : Finset (Fin (m + 1))) (Fin.snoc q 0) = Nat.multinomial (univ : Finset (Fin m)) q` |
| 601 | lemma | `sum_range_filter_ne_zero` | `{𝔸 : Type*} [AddCommMonoid 𝔸] (n : ℕ) (f : ℕ → 𝔸) : (∑ k ∈ (range (n + 1)).filter (fun k => k ≠ 0), f k) = ∑ k ∈ range n, f (k + 1)` |
| 619 | lemma | `sum_finAntidiagonal_filter_last_ne_zero` | `{𝔸 : Type*} [AddCommMonoid 𝔸] (s p : ℕ) (G : (Fin (s + 1) → ℕ) → 𝔸) : (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0), G q) = ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)), G (Fin.snoc q (k + 1))` |
| 636 | lemma | `factorial_prod_snoc` | `{s : ℕ} (q : Fin s → ℕ) (j : ℕ) : (∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ)) = (∏ i : Fin s, (Nat.factorial (q i) : ℝ)) * (Nat.factorial j : ℝ)` |
| 644 | lemma | `factorial_inv_snoc` | `{s : ℕ} (q : Fin s → ℕ) (j : ℕ) : (Nat.factorial j : ℝ)⁻¹ * (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ = (∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))⁻¹` |
| 652 | lemma | `sum_range_add_antidiagonal` | `{𝔸 : Type*} [AddCommMonoid 𝔸] (p : ℕ) (f : ℕ → ℕ → 𝔸) : (∑ j ∈ range p, ∑ i ∈ range (p - j), f i j) = ∑ m ∈ range p, ∑ i ∈ range (m + 1), f i (m - i)` |
| 703 | lemma | `sum_range_finAntidiagonal_reflect` | `{s p : ℕ} {𝔸 : Type*} [AddCommMonoid 𝔸] (G : (Fin (s + 1) → ℕ) → 𝔸) : (∑ j ∈ range p, ∑ q ∈ finAntidiagonal s j, G (Fin.snoc q (p - j))) = ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)), G (Fin.snoc q (k + 1))` |
| 724 | lemma | `exp_neg_mul_self` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸) : exp (-x) * exp x = 1` |
| 729 | lemma | `exp_mul_neg_self` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸) : exp x * exp (-x) = 1` |
| 734 | lemma | `continuous_exp_smul_const` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) : Continuous (fun t : ℝ => exp (t • A))` |
| 743 | lemma | `smul_eq_mul_right` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (r : ℝ) (a : 𝔸) : r • a = a * (r : 𝔸)` |
| 749 | lemma | `pow_smul_eq_smul_mul` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (j : ℕ) (x : 𝔸) (τ : ℝ) : ((Nat.factorial j : ℝ)⁻¹ * τ ^ j) • x = (Nat.factorial j : ℝ)⁻¹ • x * (τ : 𝔸) ^ j` |
| 755 | lemma | `smul_mul_cast` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (r c : ℝ) (a : 𝔸) : (r • a) * (c : 𝔸) = (r * c) • a` |
| 760 | lemma | `scalar_combine` | `(k j : ℕ) (d τ u : ℝ) (hd : d ≠ 0) : (d⁻¹ * ((τ - u) ^ k / (Nat.factorial k : ℝ))) * τ ^ j = (τ - u) ^ k * τ ^ j / ((Nat.factorial k : ℝ) * d)` |
| 767 | lemma | `norm_smul_le_of_abs_le_one` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (c : ℝ) (A : 𝔸) (hc : \|c\| ≤ 1) : ‖c • A‖ ≤ ‖A‖` |
| 776 | lemma | `norm_smul_exp_arg_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (c : ℝ) (A : 𝔸) (hc : \|c\| ≤ 1) (u t : ℝ) (ht : 0 ≤ t) (hu1 : u ≤ 1) : (u * t) * ‖c • A‖ ≤ t * ‖A‖` |
| 793 | lemma | `commute_smul_self` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : 𝔸) (s : ℝ) : Commute (s • A) A` |
| 798 | lemma | `star_smul_of_skew` | `{𝔸 : Type*} [Star 𝔸] [AddGroup 𝔸] [DistribSMul ℝ 𝔸] [StarModule ℝ 𝔸] {A : 𝔸} {c : ℝ} (hA : star A = -A) : star (c • A) = -(c • A)` |
| 804 | lemma | `sum_skewAdjoint` | `{𝔸 : Type*} [AddCommGroup 𝔸] [StarAddMonoid 𝔸] {ι : Type*} [Fintype ι] (H : ι → 𝔸) (h : ∀ i, star (H i) = -(H i)) : star (∑ i : ι, H i) = -(∑ i : ι, H i)` |

Private: 0. **Paper-referenced docstrings: 3** (lines 300, 321, 541).

### 2.14 `Commutator.lean` (620 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 62 | lemma | `ad_pow_succ` | `{R 𝔸 : Type*} [CommRing R] [Ring 𝔸] [LieAlgebra R 𝔸] (A : 𝔸) (q : ℕ) (B : 𝔸) : ((ad R 𝔸 A) ^ (q + 1)) B = ⁅A, ((ad R 𝔸 A) ^ q) B⁆` (has `@[simp]`) |
| 66 | **abbrev** | `adPow` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (q : ℕ) : Module.End ℝ 𝔸` |
| 72 | def | `adSequence` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) : 𝔸` |
| 82 | def | `nestedComm` | `{𝔸 : Type*} [Ring 𝔸] {p : ℕ} (H : Fin (p + 1) → 𝔸) : 𝔸` |
| 90 | noncomputable def | `αComm` | `{𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ) (H : Fin Γ → 𝔸) : ℝ` |
| 96 | noncomputable def | `αCommConj` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) : ℝ` |
| 104 | **theorem** | `norm_commutator_le` | `{𝔸 : Type*} [NormedRing 𝔸] (A B : 𝔸) : ‖⁅A, B⁆‖ ≤ 2 * ‖A‖ * ‖B‖` |
| 113 | **theorem** | `norm_adPow_le` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (k : ℕ) (B : 𝔸) : ‖adPow A k B‖ ≤ (2 * ‖A‖) ^ k * ‖B‖` |
| 126 | **theorem** | `norm_adSequence_le` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) : ‖adSequence A q B‖ ≤ (∏ i : Fin s, (2 * ‖A i‖) ^ (q i)) * ‖B‖` |
| 154 | **theorem** | `αComm_nonneg` | `{𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ) (H : Fin Γ → 𝔸) : 0 ≤ αComm p H` |
| 160 | lemma | `adSequence_snoc_zero` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸) (q : Fin m → ℕ) (B : 𝔸) : adSequence A (Fin.snoc q 0) B = adSequence (fun i : Fin m => A i.castSucc) q B` |
| 168 | lemma | `adSequence_snoc` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸) (q : Fin m → ℕ) (k : ℕ) (B : 𝔸) : adSequence A (Fin.snoc q k) B = adPow (A (Fin.last m)) k (adSequence (fun i : Fin m => A i.castSucc) q B)` |
| 176 | lemma | `adSequence_smul` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ) (r : ℝ) (X : 𝔸) : adSequence A q (r • X) = r • adSequence A q X` |
| 189 | lemma | `nestedComm_cast` | `{𝔸 : Type*} [Ring 𝔸] {n m : ℕ} (h : n = m) (H : Fin (m + 1) → 𝔸) : nestedComm (H ∘ Fin.cast (congrArg (· + 1) h)) = nestedComm H` |
| 196 | def | `nestedCommOfList` | `{𝔸 : Type*} [Ring 𝔸] (b : 𝔸) : List 𝔸 → 𝔸` |
| 199 | lemma | `nestedCommOfList_nil` | `{𝔸 : Type*} [Ring 𝔸] (b : 𝔸) : nestedCommOfList b [] = b` (has `@[simp]`) |
| 202 | lemma | `nestedCommOfList_append` | `{𝔸 : Type*} [Ring 𝔸] (b X : 𝔸) (L : List 𝔸) : nestedCommOfList b (L ++ [X]) = ⁅X, nestedCommOfList b L⁆` (has `@[simp]`) |
| 209 | lemma | `nestedCommOfList_append_replicate` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (b X : 𝔸) (L : List 𝔸) (k : ℕ) : nestedCommOfList b (L ++ List.replicate k X) = adPow X k (nestedCommOfList b L)` |
| 218 | def | `listIndexed` | `{ι 𝔸 : Type*} (b : 𝔸) (L : List ι) (f : ι → 𝔸) : Fin (L.length + 1) → 𝔸` |
| 222 | lemma | `nestedComm_cons_succ` | `{𝔸 : Type*} [Ring 𝔸] {n : ℕ} (b : 𝔸) (tail : Fin (n + 1) → 𝔸) : nestedComm (Fin.cons b tail) = ⁅tail (Fin.last n), nestedComm (Fin.cons b (fun i : Fin n => tail i.castSucc))⁆` |
| 238 | lemma | `nestedComm_ofFn_cons` | `{𝔸 : Type*} [Ring 𝔸] {n : ℕ} (b : 𝔸) (tail : Fin n → 𝔸) : nestedComm (Fin.cons b tail) = nestedCommOfList b (List.ofFn tail)` |
| 247 | lemma | `nestedComm_listIndexed` | `{𝔸 : Type*} [Ring 𝔸] {ι : Type*} (b : 𝔸) (L : List ι) (f : ι → 𝔸) : nestedComm (listIndexed b L f) = nestedCommOfList b (L.map f)` |
| 264 | lemma | `multinomial_le_factorial` | `{α : Type*} (s : Finset α) (f : α → ℕ) : Nat.multinomial s f ≤ Nat.factorial (∑ i ∈ s, f i)` |
| 278 | def | `layersOf` | `{α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) : List α` |
| 282 | lemma | `layersOf_length` | `{α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) : (layersOf f q).length = ∑ i : Fin s, q i` |
| 294 | lemma | `layersOf_map` | `{α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) : layersOf (g ∘ f) q = (layersOf f q).map g` |
| 302 | def | `layerIndices` | `{s : ℕ} (q : Fin s → ℕ) : List (Fin s)` |
| 305 | lemma | `layersOf_count` | `{s : ℕ} (q : Fin s → ℕ) (i : Fin s) : (layersOf (fun i : Fin s => i) q).count i = q i` |
| 344 | def | `expandTuple` | `{α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) : Fin (∑ i : Fin s, q i + 1) → α` |
| 350 | lemma | `expandTuple_zero` | `{α : Type*} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) : expandTuple f q b 0 = b` |
| 356 | lemma | `expandTuple_succ` | `{α : Type*} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) (t : ℕ) (ht : t < ∑ i : Fin s, q i) : expandTuple f q b ⟨t + 1, Nat.succ_lt_succ ht⟩ = f ((layersOf (fun i : Fin s => i) q)[t]'(by simpa [layersOf_length] using ht))` |
| 368 | lemma | `expandTuple_nat` | `{α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) (b : α) : expandTuple (g ∘ f) q (g b) = g ∘ expandTuple f q b` |
| 380 | lemma | `adSequence_eq_nestedCommOfList` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) : adSequence A q B = nestedCommOfList B (layersOf A q)` |
| 394 | lemma | `adSequence_eq_nestedComm_expandTuple` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) : adSequence A q B = nestedComm (expandTuple A q B)` |
| 418 | lemma | `adPow_smul_left` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (c : ℝ) (A : 𝔸) (k : ℕ) (X : 𝔸) : adPow (c • A) k X = c ^ k • adPow A k X` |
| 426 | lemma | `adSequence_smul_fun` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (c : Fin s → ℝ) (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) : adSequence (fun i => c i • A i) q B = (∏ i : Fin s, (c i) ^ q i) • adSequence A q B` |
| 437 | lemma | `αCommConj_smul_fun_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ} (c : Fin s → ℝ) (A : Fin s → 𝔸) (hc : ∀ i, \|c i\| ≤ 1) (B : 𝔸) (p : ℕ) : αCommConj (fun i => c i • A i) B p ≤ αCommConj A B p` |
| 453 | lemma | `αCommConj_smul_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (c : ℝ) (hc : \|c\| ≤ 1) (B : 𝔸) (p : ℕ) : αCommConj A (c • B) p ≤ αCommConj A B p` |
| 464 | lemma | `αCommConj_cast` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s t : ℕ} (h : s = t) (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) : αCommConj (fun i : Fin t => A (Fin.cast h.symm i)) B p = αCommConj A B p` |
| 473 | lemma | `adSequence_sum` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ) {ι : Type*} [Fintype ι] (H : ι → 𝔸) : adSequence A q (∑ γ : ι, H γ) = ∑ γ : ι, adSequence A q (H γ)` |
| 490 | lemma | `αCommConj_sum_le` | `{𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) {ι : Type*} [Fintype ι] (H : ι → 𝔸) (p : ℕ) : αCommConj A (∑ γ : ι, H γ) p ≤ ∑ γ : ι, αCommConj A (H γ) p` |
| 521 | lemma | `layersOf_cons_zero` | `{α : Type*} {s : ℕ} (f : Fin (s + 1) → α) (q : Fin s → ℕ) : layersOf f (Fin.cons 0 q) = layersOf (fun i : Fin s => f i.succ) q` |
| 532 | lemma | `adSequence_cons_zero` | `{𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸) (q : Fin s → ℕ) (B : 𝔸) : adSequence A (Fin.cons 0 q) B = adSequence (fun i : Fin s => A i.succ) q B` |
| 541 | lemma | `multinomial_cons_zero` | `{s : ℕ} (q : Fin s → ℕ) : Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.cons 0 q) = Nat.multinomial (univ : Finset (Fin s)) q` |
| 549 | lemma | `αCommConj_succ_le` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) : αCommConj (fun i : Fin s => A i.succ) B p ≤ αCommConj A B p` |
| 586 | lemma | `αCommConj_natAdd_le` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {m n : ℕ} (A : Fin (m + n) → 𝔸) (B : 𝔸) (p : ℕ) : αCommConj (A ∘ Fin.natAdd m) B p ≤ αCommConj A B p` |
| 616 | lemma | `αCommConj_nonneg` | `{𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) : 0 ≤ αCommConj A B p` |

Private: 0. **Paper-referenced docstrings: none** (module header cites arXiv:1912.08854 only).

### 2.15 `OneNormScaling.lean` (680 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 39 | lemma | `contDiff_exp_sum` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] {ι : Type*} [Fintype ι] (H : ι → 𝔸) : ContDiff ℝ ∞ (fun t : ℝ => exp (t • ∑ i : ι, H i))` |
| 47 | lemma | `norm_iteratedDeriv_exp_sum_le` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] {ι : Type*} [Fintype ι] (H : ι → 𝔸) (p : ℕ) (s : ℝ) : ‖iteratedDeriv (p + 1) (fun r : ℝ => exp (r • ∑ i : ι, H i)) s‖ ≤ (∑ i : ι, ‖H i‖) ^ (p + 1) * Real.exp (\|s\| * ∑ i : ι, ‖H i‖)` |
| 68 | lemma | `norm_iteratedDeriv_exp_sum_le_of_nonneg` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] {ι : Type*} [Fintype ι] (H : ι → 𝔸) (p : ℕ) (u t : ℝ) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖iteratedDeriv (p + 1) (fun r : ℝ => exp (r • ∑ i : ι, H i)) (u * t)‖ ≤ (∑ i : ι, ‖H i‖) ^ (p + 1) * Real.exp (t * ∑ i : ι, ‖H i‖)` |
| 86 | lemma | `norm_iteratedDeriv_F_le` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (u t : ℝ) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s - exp (s • ∑ γ : Fin Γ, H γ)) (u * t)‖ ≤ ((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) + (∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * ∑ γ : Fin Γ, ‖H γ‖)` |
| 114 | lemma | `norm_taylor_le_of_deriv_bound` | `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ (p + 1) F) (h0 : ∀ k ≤ p, iteratedDeriv k F 0 = 0) (t : ℝ) (ht : 0 ≤ t) {D : ℝ} (hD : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖iteratedDeriv (p + 1) F (u * t)‖ ≤ D) : ‖F t‖ ≤ t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * D` |
| 168 | lemma | `isBigO_pow_le_target_left` | `{a S : ℝ} (p : ℕ) (hS : 0 < S) (ha : 0 ≤ a) : (fun t : ℝ => t ^ (p + 1)) =O[𝓝[≤] (0 : ℝ)] (fun t : ℝ => (S * t) ^ (p + 1) * Real.exp (t * a))` |
| 193 | lemma | `paper_bound_le_target` | `(Υ : ℕ) (S : ℝ) (p : ℕ) (t : ℝ) (hS : 0 ≤ S) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * (((Υ : ℝ) * S) ^ (p + 1) * Real.exp (t * (Υ : ℝ) * S) + S ^ (p + 1) * Real.exp (t * S)) ≤ (S * t) ^ (p + 1) * (((Υ : ℝ) ^ (p + 1) * Real.exp ((Υ : ℝ) * S) + Real.exp S) / (Nat.factorial (p + 1) : ℝ)) * Real.exp (t * (Υ : ℝ) * S)` |
| 240 | **theorem** | `trotter_error_bound_one_norm_scaling` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (h_order : P.IsOrderOf p H) : ∀ t : ℝ, 0 ≤ t → ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖ ≤ t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * (((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) + (∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * ∑ γ : Fin Γ, ‖H γ‖))` |
| 261 | **theorem** | `trotter_error_one_norm_scaling` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (h_order : P.IsOrderOf p H) : (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖) =O[𝓝 (0 : ℝ)] (fun t : ℝ ↦ ((∑ γ : Fin Γ, ‖H γ‖) * t) ^ (p + 1) * exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖))` |
| 326 | lemma | `norm_factor_le_skew` | `[NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ : Fin Γ, star (H γ) = -(H γ)) (i : Fin Υ × Fin Γ) (q : ℕ) (u t : ℝ) : ‖(P.generator H i) ^ q * exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))‖ ≤ ‖H (P.perm i.1 i.2)‖ ^ q` |
| 358 | lemma | `norm_derivProd_le_skew` | `[NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ : Fin Γ, star (H γ) = -(H γ)) (q : Fin Υ × Fin Γ → ℕ) (u t : ℝ) : ‖P.derivProd H q (u * t)‖ ≤ ∏ i : Fin Υ × Fin Γ, ‖H (P.perm i.1 i.2)‖ ^ q i` |
| 382 | lemma | `eval_iteratedDeriv_norm_le_skew` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ : Fin Γ, star (H γ) = -(H γ)) (p : ℕ) (u t : ℝ) : ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t)‖ ≤ ((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1)` |
| 419 | lemma | `norm_iteratedDeriv_exp_sum_le_skew` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] {ι : Type*} [Fintype ι] (H : ι → 𝔸) (p : ℕ) (h_skew_sum : star (∑ i : ι, H i) = -(∑ i : ι, H i)) (s : ℝ) : ‖iteratedDeriv (p + 1) (fun r : ℝ => exp (r • ∑ i : ι, H i)) s‖ ≤ (∑ i : ι, ‖H i‖) ^ (p + 1)` |
| 438 | lemma | `norm_iteratedDeriv_F_le_skew` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ : Fin Γ, star (H γ) = -(H γ)) (p : ℕ) (u t : ℝ) : ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s - exp (s • ∑ γ : Fin Γ, H γ)) (u * t)‖ ≤ ((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) + (∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1)` |
| 466 | **theorem** | `trotter_error_bound_one_norm_scaling_of_skew_adjoint` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (h_skew : ∀ γ : Fin Γ, star (H γ) = -(H γ)) (h_order : P.IsOrderOf p H) : ∀ t : ℝ, 0 ≤ t → ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖ ≤ t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) * (((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) + (∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1))` |
| 488 | **theorem** | `trotter_error_one_norm_scaling_of_skew_adjoint` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (h_skew : ∀ γ : Fin Γ, star (H γ) = -(H γ)) (h_order : P.IsOrderOf p H) : (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖) =O[𝓝 (0 : ℝ)] (fun t : ℝ ↦ ((∑ γ : Fin Γ, ‖H γ‖) * t) ^ (p + 1))` |
| 550 | lemma | `norm_pow_sub_pow_le_of_norm_le_one` | `[NormOneClass 𝔸] (A B : 𝔸) (r : ℕ) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A ^ r - B ^ r‖ ≤ (r : ℝ) * ‖A - B‖` |
| 577 | lemma | `exp_smul_eq_pow_of_div` | `[NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormedSpace ℝ 𝔸] (x : 𝔸) (t : ℝ) {r : ℕ} (hr : 0 < r) : exp (t • x) = exp ((t / (r : ℝ)) • x) ^ r` |
| 588 | lemma | `norm_eval_le_one_of_skew` | `[NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ : Fin Γ, star (H γ) = -(H γ)) (s : ℝ) : ‖P.eval H s‖ ≤ 1` |
| 613 | lemma | `natCast_mul_pow_div_pow_succ` | `(a : ℝ) (r p : ℕ) (hr : (r : ℝ) ≠ 0) : (r : ℝ) * (a / (r : ℝ)) ^ (p + 1) = a ^ (p + 1) * ((r : ℝ) ^ p)⁻¹` |
| 622 | **theorem** | `trotter_number_one_norm_scaling` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (h_skew : ∀ γ : Fin Γ, star (H γ) = -(H γ)) (h_order : P.IsOrderOf p H) (t : ℝ) (ht : 0 ≤ t) : (fun r : ℕ => ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ : Fin Γ, H γ)‖) =O[Filter.atTop] (fun r : ℕ => ((r : ℝ) ^ p)⁻¹)` |

Private: 0. **Paper-referenced docstrings: 11** (lines 15–18 header, 84, 111, 167, 191, 238, 259, 380, 436, 464, 486, 619).

### 2.16 `ProductFormula.lean` (802 lines)

| Line | Kind | Name | Signature |
|------|------|------|-----------|
| 63 | **structure** | `ProductFormulaData` | `(Υ Γ : ℕ)` with fields `coeff : Fin Υ × Fin Γ → ℝ`, `perm : Fin Υ → Equiv.Perm (Fin Γ)`, `coeff_abs_le_one : ∀ i : Fin Υ × Fin Γ, \|coeff i\| ≤ 1` |
| 77 | def | `evalIndexList` | `(Υ Γ : ℕ) : List (Fin Υ × Fin Γ)` |
| 81 | noncomputable def | `generator` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) : 𝔸` |
| 88 | lemma | `norm_generator_le` | `[NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) : ‖P.generator H i‖ ≤ ‖H (P.perm i.1 i.2)‖` |
| 95 | noncomputable def | `evalFactor` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸` |
| 102 | lemma | `norm_evalFactor_le` | `[NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (s : ℝ) : ‖P.evalFactor H i s‖ ≤ Real.exp (\|s\| * ‖H (P.perm i.1 i.2)‖)` |
| 114 | noncomputable def | `eval` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸` |
| 121 | **theorem** | `eval_zero` | `[NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) : P.eval H 0 = 1` (has `@[simp]`) |
| 124 | lemma | `evalIndexList_map_prod` | `{M : Type*} [Monoid M] (g : Fin Υ × Fin Γ → M) : ((evalIndexList Υ Γ).map g).prod = (((List.finRange Υ).reverse).map (fun υ => (((List.finRange Γ).reverse).map (fun γ => g (υ, γ))).prod)).prod` |
| 135 | lemma | `evalFactor_iteratedDeriv` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (k : ℕ) (t : ℝ) : iteratedDeriv k (fun t : ℝ => P.evalFactor H i t) t = P.generator H i ^ k * P.evalFactor H i t` |
| 144 | **theorem** | `eval_iteratedDeriv_succ` | `[NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (t : ℝ) : iteratedDeriv (p + 1) (fun t : ℝ => P.eval H t) t = ∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1), (Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) • (((List.finRange Υ).reverse).map (fun υ : Fin Υ => (((List.finRange Γ).reverse).map (fun γ : Fin Γ => ((P.generator H (υ, γ)) ^ (q (υ, γ))) * exp ((t * P.coeff (υ, γ)) • H (P.perm υ γ)))).prod)).prod` |
| 205 | lemma | `norm_factor_le` | `[NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (q : ℕ) (u t : ℝ) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖(P.generator H i) ^ q * exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))‖ ≤ ‖H (P.perm i.1 i.2)‖ ^ q * Real.exp (t * ‖H (P.perm i.1 i.2)‖)` |
| 228 | noncomputable def | `derivProd` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (q : Fin Υ × Fin Γ → ℕ) (t : ℝ) : 𝔸` |
| 239 | lemma | `nested_prod_eq_finset_prod` | `{M : Type*} [CommMonoid M] (f : Fin Υ × Fin Γ → M) : (((List.finRange Υ).reverse).map (fun υ : Fin Υ => (((List.finRange Γ).reverse).map (fun γ : Fin Γ => f (υ, γ))).prod)).prod = ∏ i : Fin Υ × Fin Γ, f i` |
| 249 | lemma | `norm_derivProd_le` | `[NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (q : Fin Υ × Fin Γ → ℕ) (u t : ℝ) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖P.derivProd H q (u * t)‖ ≤ ∏ i : Fin Υ × Fin Γ, ‖H (P.perm i.1 i.2)‖ ^ q i * Real.exp (t * ‖H (P.perm i.1 i.2)‖)` |
| 272 | lemma | `sum_norm_prod` | `(H : Fin Γ → 𝔸) : (∑ i : Fin Υ × Fin Γ, ‖H (P.perm i.1 i.2)‖) = (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖` |
| 287 | **theorem** | `eval_iteratedDeriv_norm_le` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (u t : ℝ) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t)‖ ≤ ((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) * Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)` |
| 348 | def | `scale` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (c : ℝ) (hc : \|c\| ≤ 1) : ProductFormulaData Υ Γ` (has `@[reducible]`) |
| 357 | lemma | `scale_eval` | `(c : ℝ) (hc : \|c\| ≤ 1) [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : (scale P c hc).eval H t = P.eval H (c * t)` |
| 368 | def | `concat` | `{Υ₁ Υ₂ Γ : ℕ} (P : ProductFormulaData Υ₁ Γ) (Q : ProductFormulaData Υ₂ Γ) : ProductFormulaData (Υ₂ + Υ₁) Γ` (has `@[reducible]`) |
| 398 | private lemma | `concat_generator_castAdd` | (private — omitted) |
| 405 | private lemma | `concat_generator_natAdd` | (private — omitted) |
| 412 | private lemma | `concat_evalFactor_castAdd` | (private — omitted) |
| 419 | private lemma | `concat_evalFactor_natAdd` | (private — omitted) |
| 426 | lemma | `concat_eval` | `{Υ₁ Υ₂ : ℕ} (P : ProductFormulaData Υ₁ Γ) (Q : ProductFormulaData Υ₂ Γ) [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : (concat P Q).eval H t = P.eval H t * Q.eval H t` |
| 455 | def | `castStages` | `{n m Γ : ℕ} (h : n = m) (P : ProductFormulaData n Γ) : ProductFormulaData m Γ` (has `@[reducible]`) |
| 462 | lemma | `castStages_eval` | `{n m : ℕ} (h : n = m) (P : ProductFormulaData n Γ) [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : (castStages h P).eval H t = P.eval H t` (has `@[simp]`) |
| 480 | noncomputable def | `orderedSummands` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} (H : Fin Γ → 𝔸) : Fin (Υ * Γ) → 𝔸` |
| 487 | noncomputable def | `orderedGenerators` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) : Fin (evalIndexList Υ Γ).length → 𝔸` |
| 493 | noncomputable def | `suffixGenerators` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length → 𝔸` |
| 500 | lemma | `evalIndexList_eq_ofFn` | `evalIndexList Υ Γ = List.ofFn (fun k : Fin (Υ * Γ) => (Fin.revPerm k.divNat, Fin.revPerm k.modNat))` |
| 510 | def | `reverseStages` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) : ProductFormulaData Υ Γ` |
| 516 | noncomputable def | `orderedSummandsEval` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} (H : Fin Γ → 𝔸) : Fin (Υ * Γ) → 𝔸` |
| 522 | lemma | `orderedSummands_reverseStages` | `{𝔸 : Type*} (H : Fin Γ → 𝔸) : orderedSummands (reverseStages P) H = orderedSummandsEval P H` |
| 527 | noncomputable def | `fullGenerators` | `{Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} (H : Fin Γ → 𝔸) : Fin (evalIndexList Υ Γ).length → 𝔸` |
| 533 | lemma | `evalIndexList_length` | `(evalIndexList Υ Γ).length = Υ * Γ` |
| 538 | lemma | `fullGenerators_eq_orderedSummandsEval` | `{𝔸 : Type*} (H : Fin Γ → 𝔸) : (fun i : Fin (Υ * Γ) => fullGenerators P H (Fin.cast (evalIndexList_length).symm i)) = orderedSummandsEval P H` |
| 547 | lemma | `sum_norm_fullGenerators_eq` | `(H : Fin Γ → 𝔸) : (∑ k : Fin (evalIndexList Υ Γ).length, ‖fullGenerators P H k‖) = (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖` |
| 572 | lemma | `sum_norm_orderedGenerators_le` | `[NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) : (∑ k : Fin (evalIndexList Υ Γ).length, ‖orderedGenerators P H k‖) ≤ (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖` |
| 589 | lemma | `sum_norm_suffixGenerators_le` | `[NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) : (∑ k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length, ‖suffixGenerators P H i k‖) ≤ (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖` |
| 620 | lemma | `norm_eval_le` | `[NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (H : Fin Γ → 𝔸) (s : ℝ) : ‖P.eval H s‖ ≤ Real.exp (\|s\| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)` |
| 650 | lemma | `sum_αCommConj_perm` | `[Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) : (∑ i : Fin Υ × Fin Γ, αCommConj (orderedSummandsEval P H) (H (P.perm i.1 i.2)) p) = (Υ : ℝ) * ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p` |
| 659 | lemma | `star_generator_of_skew` | `[NormedSpace ℝ 𝔸] [Star 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (j : Fin Υ × Fin Γ) : star (P.generator H j) = -(P.generator H j)` |
| 666 | lemma | `αCommConj_fullGenerators_eq` | `[Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (B : 𝔸) (p : ℕ) : αCommConj (fullGenerators P H) B p = αCommConj (orderedSummandsEval P H) B p` |
| 678 | lemma | `αCommConj_orderedGenerators_le` | `[NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (B : 𝔸) (p : ℕ) : αCommConj (orderedGenerators P H) B p ≤ αCommConj (fullGenerators P H) B p` |
| 693 | lemma | `αCommConj_suffixGenerators_le` | `[NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (p : ℕ) : αCommConj (suffixGenerators P H i) (P.generator H i) p ≤ αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p` |
| 764 | lemma | `sum_αCommConj_suffix_add_ordered_le` | `[NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) (hΥ : 0 < Υ) : (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p) + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p)` |

Private: 4. **Paper-referenced docstrings: 5** (lines 16–25 header, 59, 142, 285, 476).

---

## 3. Docstrings that mention a paper reference (verbatim)

Rendering convention: `/-! … -/` module headers are indented by two spaces as in the source; `/-- … -/` docstrings are quoted verbatim including line breaks.

### 3.1 Module headers

**`ListLemmas.lean:11-38`** (declaration: file header)

```
/-!
# General list lemmas

General results about `List` (ordered `List.prod` products, `List.finRange`/`List.ofFn`
reindexing, `Fin`-indexed sums) at the `Monoid` / `AddCommMonoid` / `NormedAlgebra` level,
used by the Trotter error theory (arXiv:1912.08854). This is the shared home for list- and
`Fin`-level facts that the product-formula lemmas in `ErrorTypes.lean` (`factorProdOver`,
`prefixFactorProd`, `strictSuffixFactorProd`, …) and the commutator-expansion lemmas specialize.

## Main results

* `prod_drop_eq_get_mul`: `((l.drop k).map f).prod = f (l.get k) * ((l.drop (k + 1)).map f).prod`.
* `prod_map_eq_take_mul_get_mul_drop`: splitting `(l.map f).prod` at an element `i ∈ l` into
  prefix `· f i ·` suffix.
* `sum_get_eq_sum_idxOf`: reindexing a sum over positions `Fin l.length` to a sum over the
  (nodup) elements of `l`.
* `hasDerivAt_list_prod`: the product rule for the ordered product `t ↦ (l.map (f · t)).prod`.
* `contDiff_list_prod`: smoothness of the ordered product `t ↦ (l.map (f · t)).prod`.
* `prod_mul_rev_eq_one_of_mul_eq_one`, `rev_mul_prod_eq_one_of_mul_eq_one`: telescoping
  product-of-units identities.
* `ofFn_castSucc_drop_prod`, `ofFn_castSucc_drop_reverse_prod`: peeling the outermost entry
  off a dropped `List.ofFn` suffix.
* `finRange_add`, `finRange_reverse_add`: splitting `List.finRange (n + m)` into its parts.
* `finRange_reverse_map_comp_revPerm`: `Fin.revPerm` reindexing of the reversed `finRange`.
* `sum_fin_cast`: reindexing a `Fin`-indexed sum along `Fin.cast`.

**Assisted by Deepseek Harness**
-/
```

**`TimeOrderedExp.lean:10-45`** (declaration: file header)

```
/-!
# Time-ordered exponential

The time-ordered exponential `exp_T(∫ H dτ)` of arXiv:1912.08854 §2.2, defined via the Dyson
(Neumann/Picard) series `∑' n, D_n` with `D₀ = 1` and `D_{n+1}(t) = ∫ τ in t₁..t, H τ * D_n τ`.
The interval integral carries the orientation, so the definition is automatically two-sided.

## Main results

* `timeOrderedExp_initial`: `exp_T H t₁ t₁ = 1`.
* `timeOrderedExp_hasDerivAt`, `timeOrderedExp_hasDerivAt_lower`: the two differentiation rules
  `∂/∂t₂ exp_T = H·exp_T` and `∂/∂t₁ exp_T = -exp_T·H` (`prelim.tex:44-49`).
* `timeOrderedExp_mul`: the multiplicative property
  `exp_T H t₁ t₃ = exp_T H t₂ t₃ · exp_T H t₁ t₂` (`prelim.tex:52`).
* `timeOrderedExp_mul_inv_self`, `timeOrderedExp_inv_mul_self`, `isUnit_timeOrderedExp`:
  every `exp_T H t₁ t₂` is a unit with inverse `exp_T H t₂ t₁`.
* `timeOrderedExp_eq_integral`: the integral equation `U = 1 + ∫ H·U` (`eq:int_eq`).
* `timeOrderedExp_duhamel`: the variation-of-parameters formula (`lem:td_Duhamel`).
* `timeOrderedExp_interaction_picture`: time-ordered evolution in the interaction picture
  (`lem:interaction_picture`).
* `fundamentalTheorem_timeOrderedExp`, `fundamentalTheorem_timeOrderedExp_unique`: the
  fundamental theorem of time-ordered evolution and the uniqueness of its generator (`lem:fte`).
* `timeOrderedExp_const`: `exp_T (fun _ => H) t₁ t₂ = exp ((t₂ - t₁) • H)` (`prelim.tex:41`).
* `timeOrderedExp_norm_le`, `timeOrderedExp_norm_eq_one_of_skewAdjoint`:
  `‖exp_T H t₁ t₂‖ ≤ Real.exp |∫ τ in t₁..t₂, ‖H τ‖|`, and `= 1` when `H` is skew-adjoint
  (`lem:time_ordered_norm_bound`).
* `timeOrderedExp_dist_le`, `timeOrderedExp_dist_le_of_skewAdjoint`: distance bounds between
  two evolutions (`cor:time_ordered_distance_bound`).
* `ode_solution_unique`: uniqueness of solutions to `U' = H·U`.
* `continuous_timeOrderedExp`, `continuous_timeOrderedExp_lower`, `contDiff_timeOrderedExp`:
  continuity/smoothness of the solution in its upper and lower limits.
* `timeOrderedExp_sub`: the difference identity between two evolutions
  (`cor:time_ordered_distance_bound`).

**Assisted by Deepseek Harness**
-/
```

**`CommutatorExpansion.lean:14-38`**

```
/-!
# Multi-layer conjugation: commutator expansion and remainder norm bounds

The multi-layer conjugation results for the Trotter error theory (arXiv:1912.08854): the
commutator expansion of `e^{τA_s} ⋯ e^{τA_1} B e^{-τA_1} ⋯ e^{-τA_s}` and the norm bounds
of its remainder (theory.tex:184-249).

## Main definitions

* `multiConj`: the multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA_0} B e^{-τA_0}⋯e^{-τA_{s-1}}`.
* `commutatorRemainderTerm`, `commutatorRemainder`: the operator-valued remainder `𝒞(τ)`.
* `conjCoeff`: the multinomial-weighted `τ^j` coefficient of the multi-layer expansion.

## Main results

* `commutatorExpansion_conj`: the commutator expansion of a multi-layer conjugation
  `multiConj A B τ = Σ_{j < p} conjCoeff A B j · τ^j + commutatorRemainder A B p τ`
  (`thm:comm_exp_conj`, theory.tex:222-236).
* `norm_commutatorRemainder_le`: the spectral-norm bound of the commutator remainder for
  general operators (theory.tex:238-241).
* `norm_commutatorRemainder_le_of_skewAdjoint`: the bound for anti-Hermitian operators
  (theory.tex:242-244).

**Assisted by Deepseek Harness**
-/
```

**`CommutatorScaling.lean:13-23`**

```
/-!
# Commutator scaling bridge

The bridge from the additive kernel `𝒯(τ)` to the commutator expansion:
`additiveKernel = Σ multiConj − multiConj` (`papers/rep.tex` lines 5-12) and the
order-condition cancellation `𝒯 = Σ commutatorRemainder − commutatorRemainder`
(`papers/theory.tex` lines 251-266). These are shared by the anti-Hermitian and
general-operator branches of `thm:trotter_error_comm_scaling`.

**Assisted by Deepseek Harness**
-/
```

**`ErrorTypes.lean:13-37`**

```
/-!
# Three types of Trotter error

This file formalizes `thm:error_type` of arXiv:1912.08854 (Appendix A): the three equivalent
representations of the product formula `𝒮(t) = P.eval H t` relative to the ideal evolution
`e^{tH}`, `H = ∑ γ H γ`:

* *additive*: `𝒮(t) = e^{tH} + ∫₀ᵗ e^{(t−τ)H} 𝒮(τ) 𝒯(τ) dτ` (`errorType_additive`);
* *exponentiated*: `𝒮(t) = exp_T(∫₀ᵗ (H + ℰ(τ)) dτ)` (`errorType_exponentiated`);
* *multiplicative*: `𝒮(t) = e^{tH} (1 + ℳ(t))` (`errorType_multiplicative`).

The lexicographic order `(υ,γ) ≻ (υ',γ')` of the paper (`papers/type.tex`) is exactly the
left-to-right order of `evalIndexList`, so the prefix / suffix products
`∏_{j ≻ i}`, `∏_{j ≤ i}` are implemented with `List.take` / `List.drop` at `List.idxOf i`.

## Main results

* `eval_hasDerivAt`: the product-rule derivative of `𝒮(t)`.
* `eval_hasDerivAt_additive`, `eval_hasDerivAt_exponentiated`: the two rearranged ODEs.
* `additiveResidual`, `additiveKernel`, `exponentiatedGenerator`, `exponentiatedError`,
  `multiplicativeError`: the residual `ℛ` and the three error operators `𝒯`, `ℰ`, `ℳ` of the paper.
* `errorType_additive`, `errorType_exponentiated`, `errorType_multiplicative`: `thm:error_type`.

**Assisted by Deepseek Harness**
-/
```

**`ExpSMulConj.lean:12-36`**

```
/-!
# Single-layer conjugation

Single-layer conjugation results for the Trotter error theory (arXiv:1912.08854): the Taylor
expansion and norm bounds of the single conjugation `exp (τ • A) * X * exp (-τ • A)`
(theory.tex:137-155), before the multi-layer induction.

## Main definitions

* `expSMulConj`: the single conjugation `e^{τA} X e^{-τA} = exp (τ • A) * X * exp ((-τ) • A)`.

## Main results

* `expSMulConj_hasDerivAt`: `d/dτ expSMulConj A X τ = expSMulConj A ⁅A, X⁆ τ`.
* `expSMulConj_sub_eq_integral`: the fundamental-theorem identity
  `expSMulConj A X τ - X = ∫₀^τ expSMulConj A ⁅A, X⁆ s ds`.
* `iteratedDeriv_expSMulConj_zero`: `iteratedDeriv j (expSMulConj A X) 0 = adPow A j X`.
* `expSMulConj_taylor`: the single-layer Taylor expansion with integral remainder.
* `norm_expSMulConj_le`, `norm_expSMulConj_remainder_le`: norm bounds for the conjugation
  and its remainder (theory.tex:151-155).
* `norm_expSMulConj_le_of_skewAdjoint`: the conjugation has norm at most `‖X‖` when the
  generator is anti-Hermitian (the exponential factors are unitary).

**Assisted by Deepseek Harness**
-/
```

**`Integrals.lean:11-27`**

```
/-!
# Interval integrals used in the Trotter error bounds

Generic interval-integral identities over `ℝ` used across the Trotter error theory
(arXiv:1912.08854): beta-type integrals, the substituted Taylor remainder integral, and the
FTC identity `∫₀¹ (1-u)^p = 1/(p+1)`.

## Main results

* `integral_abs_sub_pow_uIoc`: `∫ u in uIoc 0 τ, |τ - u|^(q-1) = |τ|^q / q`.
* `integral_abs_pow_sub_div_factorial_uIoc`, `abs_integral_abs_pow_div_factorial`:
  `|∫₀^τ |s|^(p-1)/(p-1)!| = |τ|^p/p!`.
* `integral_smul_eq_integral_mul_sub`: the substituted Taylor remainder integral identity.
* `intervalIntegral_one_sub_pow`: `∫₀¹ (1-u)^p = 1/(p+1)`.

**Assisted by Deepseek Harness**
-/
```

**`MainTheorem.lean:14-28`**

```
/-!
# Main theorem: commutator scaling of Trotter error

The main theorems of *A Theory of Trotter Error* (arXiv:1912.08854): the norm bound for the
additive kernel `𝒯(τ)` and the commuting-scaling bounds for the Trotter error
`thm:trotter_error_comm_scaling`.

Supporting steps live in dedicated files:
* `OrderingRemoval.lean` — `αCommConj_sum_le_αComm` (`papers/rep.tex` lines 129–139).
* `CommutatorScaling.lean` — the `additiveKernel = Σ multiConj − multiConj` bridge and the
  order-condition cancellation `additiveKernel_eq_commutatorRemainder_sum`
  (`papers/theory.tex` lines 251–266).

**Assisted by Deepseek Harness**
-/
```

**`OrderCondition.lean:14-40`**

```
/-!
# Order conditions for Trotter error

The order-condition calculus of arXiv:1912.08854, `prop:order_cond_rule` (order.tex:76-86).
An operator-valued function `F` satisfies `F = O(τ^p)` (the italic `O`, limit `τ → 0`) when
`(fun τ => ‖F τ‖) =O[𝓝 (0:ℝ)] (fun τ => τ^p)`; the `IsBigO` relation norm-wraps its right-hand
side, so `τ^p` acts as `|τ|^p`.

## Main results

* `IsOrderOf`: the `p`-th order condition `𝒮(t) = e^{tH} + O(t^{p+1})` (`prelim.tex:150`).
* `orderCond_add`, `orderCond_mul`: the addition and multiplication rules.
* `orderCond_deriv_iff`: `F = O(τ^{p+1})` iff `F 0 = 0` and `F' = O(τ^p)`.
* `orderCond_integral_iff`: `F = O(τ^p)` iff `∫₀ᵗ F = O(t^{p+1})`.
* `orderCond_exp_iff`: `F = G + O(τ^p)` iff `exp_T(∫₀ᵗ F) = exp_T(∫₀ᵗ G) + O(t^{p+1})`.
* `monomial_integral_order`: the canonical nested integral of a monomial is `O(t^{Σp + Γ})`
  (`lem:monomial`).
* `errorOrderCond_iff`: the additive / exponentiated / multiplicative order conditions are
  all equivalent to the `p`-th order condition (`thm:error_order_cond`, order.tex:124).
* `polynomial_isBigO_iff_coeffs_zero`: a polynomial of degree `< p` is `O(τ^p)` at `0` iff
  its coefficients vanish (the order-condition cancellation step).

All rules are stated for smooth generators (the paper's standing hypothesis "infinitely
differentiable", order.tex:78).

**Assisted by Deepseek Harness**
-/
```

**`OrderingRemoval.lean:11-19`**

```
/-!
# Ordering removal (`α_comm ≲ p!·Υ^p·α~_comm`)

The ordering-removal step of the main theorem (arXiv:1912.08854, `papers/rep.tex`
lines 129-139): the sum over innermost summands `H_γ` of the conjugation quantity
`α_comm` is bounded by `p! · Υ^p · α~_comm`.

**Assisted by Deepseek Harness**
-/
```

**`Prefactor.lean:14-33`**

```
/-!
# Error bounds with small prefactors (§5.1)

Tight-constant Trotter error bounds for the first-order Lie-Trotter and second-order Suzuki
formulas, following `papers/prefactor.tex` `sec:prefactor_pf12`.

The paper states these in terms of a Hermitian `H = Σ_γ H_γ` and the real-time evolution
`e^{-itH}`. Here, following the anti-Hermitian-generator convention of the surrounding theory,
we work with anti-Hermitian generators `K_γ` (`star (K γ) = -(K γ)`) and the evolution
`exp (t • Σ_γ K γ)`; the paper's `H_γ ↔ K_γ = -i H_γ`, `e^{-itH_γ} ↔ exp (t • K_γ)`, and
`[H_γ, H_γ'] ↔ ⁅K_γ, K_γ'⁆` (equal norm), so the constants `t²/2`, `t³/12`, `t³/24` are unchanged.

## Main results

* `firstOrder_twoTerm`, `secondOrder_twoTerm`: the two-summand (Γ = 2) tight bounds.
* `firstOrder_bound`, `secondOrder_bound`: the general-Γ bounds via triangle-inequality
  telescoping (prefactor.tex:45–50 and 105–114).

**Assisted by Deepseek Harness**
-/
```

**`Suzuki.lean:12-33`**

```
/-!
# The Lie-Trotter and Suzuki formulas

The first-order Lie-Trotter formula `∏_{γ=1}^Γ e^{t K_γ}` (`eq:pf1`) and the higher-order Suzuki
formulas `S_{2k}` (`eq:pf2k`) of arXiv:1912.08854 (`papers/prelim.tex` §2.3), in the paper's
`∏_{γ=1}^Γ A_γ = A_Γ ⋯ A_1` convention (0-based `Fin Γ` here), together with their representation
as `ProductFormulaData` (`lieTrotterData`, `suzuki2Data`, `suzukiData`) and the proof that the two
presentations evaluate identically.

## Main definitions

* `lieTrotter`, `suzuki2`, `suzukiU`, `suzuki`: the recursive closed forms.
* `lieTrotterData`, `suzuki2Data`, `suzukiData`: the `ProductFormulaData` forms.

## Main results

* `lieTrotter_eq_eval`: `lieTrotter K t = (lieTrotterData Γ).eval K t` (`prelim.tex:127,142`).
* `suzuki2_eq_eval`: `suzuki2 K t = (suzuki2Data Γ).eval K t` (`prelim.tex:136,142`).
* `suzuki_eq_eval`: `suzuki k K t = (suzukiData k Γ).eval K t` for `1 ≤ k`.

**Assisted by Deepseek Harness**
-/
```

**`Calculus.lean:14-32`**

```
/-!
# Calculus for normed algebra exponentials

Generic calculus lemmas for the exponential `NormedSpace.exp` in a normed algebra, together
with the general ℝ-algebra scalar/commutativity lemmas and the `Fin` / `finAntidiagonal` /
multinomial reindexing machinery they use, shared across the Trotter error theory
(arXiv:1912.08854).

## Main results

* `iteratedDeriv_exp_smul_const`: the `q`-th iterated derivative of `u ↦ exp (u • A)`.
* `iteratedDeriv_ofFn_prod`, `iteratedDeriv_list_prod_general`:
  the multinomial Leibniz expansion of the `n`-th iterated derivative of a finite product.
* `sum_piAntidiag_univ_equiv`, `multinomial_univ_equiv`: reindexing `piAntidiag` sums and
  multinomial coefficients by an equivalence of the index type.
* `contDiffAt_exp_smul_const`: `u ↦ exp (u • A)` is `C^m` at every point.

**Assisted by Deepseek Harness**
-/
```

**`Commutator.lean:15-47`**

```
/-!
# Commutators and nested commutators

Commutator foundations for the Trotter error theory (arXiv:1912.08854). We use the
associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A`, the adjoint map `ad A = [A, ·]`, and
its `q`-fold iteration `(ad A)^[q]` for the iterated commutator `ad_A^q(B)` of a single
operator, the iterated `ad` over a sequence of (possibly different) operators with
multiplicities, and the nested commutator `[H_p, ⋯ [H_1, H_0] ⋯]`. We also define the
`α`-norm quantities `α~_comm` and `α_comm` of the paper, together with their basic
norm bounds.

## Main definitions

* `adPow`: the `q`-fold iterated adjoint `(ad A)^q`, as an ℝ-linear endomorphism of `𝔸`.
* `adSequence`: the iterated `ad` over `A ⟨0⟩, …, A ⟨s-1⟩` with multiplicities
  `q ⟨0⟩, …, q ⟨s-1⟩`; `A ⟨0⟩` is innermost and `A ⟨s-1⟩` is outermost.
* `nestedComm`: the nested commutator `[H ⟨p⟩, [H ⟨p-1⟩, ⋯ [H ⟨1⟩, H ⟨0⟩] ⋯]]` with
  exactly `p` brackets, `H ⟨0⟩` innermost and `H ⟨p⟩` outermost.
* `nestedCommOfList`, `listIndexed`: the list-based nested commutator and its `Fin`-indexed
  realization.
* `αComm`: `α~_comm = Σ_{γ : Fin (p+1) → Fin Γ} ‖[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_{γ_1}]]‖`.
* `αCommConj`: the multinomial-weighted sum `Σ_{q₁+⋯+q_s = p}
  (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`.

## Main results

* `norm_commutator_le`: `‖⁅A, B⁆‖ ≤ 2 * ‖A‖ * ‖B‖`.
* `norm_adPow_le`: `‖ad_A^k(B)‖ ≤ (2 * ‖A‖)^k * ‖B‖`.
* `norm_adSequence_le`: the product bound for an iterated `ad` over a sequence.
* `αComm_nonneg`: `0 ≤ αComm p H`.

**Assisted by Deepseek Harness**
-/
```

**`OneNormScaling.lean:12-20`**

```
/-!
# Trotter error with `1`-norm scaling

This file states `lem:trotter_error_one_norm_scaling` and
`cor:trotter_number_one_norm_scaling` of arXiv:1912.08854 (§2.3): the Trotter
error of a `p`-th order product formula is bounded by a `1`-norm scaling, and the
corresponding Trotter number.

**Assisted by Deepseek Harness**
-/
```

**`ProductFormula.lean:13-45`**

```
/-!
# Product formulas

We define the general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of arXiv:1912.08854 (§2.3) and the associated
`p`-th order condition.

Following the paper's convention (`papers/prelim.tex` §2.1), the product
`∏_{γ=1}^{Γ} A_γ` denotes `A_Γ ⋯ A_2 A_1`, i.e. increasing indices from right to
left; we implement this with a reversed `List.finRange`. Since the factors
`e^{t a H}` do not commute, the product is taken with `List.prod` (ordered) rather
than `prod` (commutative) or `noncommProd` (which requires pairwise
commutativity).

## Main definitions

* `ProductFormulaData`: the data of a product formula `𝒮(t)` (stages `Υ`, summands `Γ`,
  coefficients `coeff`, permutations `perm`).
* `evalFactor`, `eval`, `generator`: the single factor, the full product, and the generator
  `a_{(υ,γ)} H_{π_υ(γ)}`.
* `evalIndexList`: the flattened factor-index order used by `eval`.
* `orderedSummands`, `orderedSummandsEval`, `reverseStages`: the permuted summands and the
  stage-reversal structure map.
* `orderedGenerators`, `suffixGenerators`, `fullGenerators`: the generators of the product
  formula in `evalIndexList` order.

## Main results

* `ProductFormulaData.eval_iteratedDeriv_succ`: the `(p + 1)`-st iterated derivative
  of `eval`, expanded as a multinomial Leibniz sum over `Fin Υ × Fin Γ`.
* `evalIndexList_eq_ofFn`, `evalIndexList_length`: the flattened index list as `List.ofFn`.

**Assisted by Deepseek Harness**
-/
```

### 3.2 `TimeOrderedExp.lean` — per-declaration docstrings

**`TimeOrderedExp.lean:322-325`** — documents **`timeOrderedExp_eq_integral`**

```
/-- `eq:int_eq` (prelim.tex:58): the integral equation
`exp_T H t₁ t₂ = 1 + ∫ τ in t₁..t₂, H τ * exp_T H t₁ τ`.
The proof commutes the `tsum` with the interval integral via the dominated convergence
theorem for series, using the two-sided termwise bound `norm_dysonTerm_le_abs`. -/
```

**`TimeOrderedExp.lean:382-384`** — documents **`timeOrderedExp_hasDerivAt`**

```
/-- `prelim.tex:44-49` (first rule): derivative with respect to the upper limit
`∂/∂t₂ exp_T(∫_{t₁}^{t₂} H) = H(t₂) · exp_T(∫_{t₁}^{t₂} H)`.
Follows from the integral equation and `intervalIntegral.integral_hasDerivAt_right`. -/
```

**`TimeOrderedExp.lean:438-440`** — documents **`timeOrderedExp_mul`**

```
/-- `prelim.tex:52`: the multiplicative property
`exp_T H t₁ t₃ = exp_T H t₂ t₃ · exp_T H t₁ t₂`. Both sides solve the ODE `U' = H·U` and agree
at `t₂`, so they are equal by `ode_solution_unique`. -/
```

**`TimeOrderedExp.lean:514-516`** — documents **`timeOrderedExp_const`**

```
/-- `prelim.tex:41` (the paper states the `0 → t` case `e^{tH}`; this is its arbitrary-interval
form): for the constant generator, the time-ordered exponential is the ordinary matrix
exponential `exp ((t₂ - t₁) • H)`. Proved directly from the Dyson series. -/
```

**`TimeOrderedExp.lean:526-531`** — documents **`timeOrderedExp_hasDerivAt_lower`**

```
/-- `prelim.tex:44-49` (second rule): derivative with respect to the lower limit
`∂/∂t₁ exp_T(∫_{t₁}^{t₂} H) = -exp_T(∫_{t₁}^{t₂} H) · H(t₁)`.

By the inverse relation, `exp_T H s t₂ = (exp_T H t₂ s)⁻¹`, so the result follows from the
derivative of the (ring) inversion `hasFDerivAt_ringInverse` composed with the upper-limit
derivative `timeOrderedExp_hasDerivAt`. -/
```

**`TimeOrderedExp.lean:641-642`** — documents **`timeOrderedExp_duhamel`**

```
/-- `lem:td_Duhamel` (variation of parameters): the unique solution of `U' = H · U + R`,
`U 0 = U₀`, is `exp_T(∫₀ᵗ H) · U₀ + ∫ τ in 0..t, exp_T(∫_τ^t H) · R τ`. -/
```

**`TimeOrderedExp.lean:675-676`** — documents **`timeOrderedExp_interaction_picture`**

```
/-- `lem:interaction_picture` (time-ordered evolution in the interaction picture):
`exp_T(∫₀ᵗ (A + B)) = exp_T(∫₀ᵗ A) · exp_T(∫₀ᵗ (exp_T A τ 0 · B τ · exp_T A 0 τ))`. -/
```

**`TimeOrderedExp.lean:738-739`** — documents **`fundamentalTheorem_timeOrderedExp_of_isUnit`**

```
/-- (⇒) of `lem:fte`: a `C¹` function that is pointwise a unit is generated by the continuous
generator `H t = deriv U t * Ring.inverse (U t)`. -/
```

**`TimeOrderedExp.lean:767`** — documents **`fundamentalTheorem_timeOrderedExp_of_timeOrderedExp`**

```
/-- (⇐) of `lem:fte`: `t ↦ exp_T H 0 t · U 0` is `C¹` and pointwise a unit when `U 0` is a unit. -/
```

**`TimeOrderedExp.lean:778-779`** — documents **`fundamentalTheorem_timeOrderedExp`**

```
/-- `lem:fte` (fundamental theorem of time-ordered evolution): `U` is `C¹` and pointwise a unit iff
it is `exp_T(∫₀ᵗ H) · U 0` for some continuous `H` and `U 0` is a unit. -/
```

**`TimeOrderedExp.lean:826-830`** — documents **`timeOrderedExp_norm_eq_one_of_skewAdjoint`**

```
/-- `lem:time_ordered_norm_bound` (item 2): when the generator `H` is pointwise skew-adjoint
(`star (H τ) = -H τ`), the time-ordered exponential is unitary, hence `‖exp_T H t₁ t₂‖ = 1`.
The proof shows `W t := star (U t) * U t` (with `U t := exp_T H t₁ t`) has derivative `0`, so `W`
is constant and `W t₂ = W t₁ = 1`; thus `U t₂` is unitary and the norm follows from the
C*-identity. -/
```

**`TimeOrderedExp.lean:946-952`** — documents **`timeOrderedExp_sub`**

```
/-- `cor:time_ordered_distance_bound` (difference representation): the difference of two
time-ordered exponentials equals the Duhamel integral
`∫ τ in t₁..t₂, exp_T(G,τ,t₂) · (H τ − G τ) · exp_T(H,t₁,τ)`.
The proof runs the `ode_solution_unique` argument on `D − X`, where
`D t = exp_T H t₁ t − exp_T G t₁ t` and
`X t = ∫ τ in t₁..t, exp_T G τ t · (H τ − G τ) · exp_T H t₁ τ`
solve the same inhomogeneous ODE `Y' = G·Y + (H−G)·exp_T H t₁` with the same initial value `0`. -/
```

**`TimeOrderedExp.lean:1049-1050`** — documents **`timeOrderedExp_dist_le`**

```
/-- `cor:time_ordered_distance_bound` (item 1, general):
`‖exp_T(∫ H) − exp_T(∫ G)‖ ≤ |∫ ‖H−G‖| · Real.exp |∫ (‖H‖+‖G‖)|`. -/
```

**`TimeOrderedExp.lean:1075-1076`** — documents **`timeOrderedExp_dist_le_of_skewAdjoint`**

```
/-- `cor:time_ordered_distance_bound` (item 2, skew): when `H` and `G` are pointwise
anti-Hermitian, `‖exp_T(∫ H) − exp_T(∫ G)‖ ≤ |∫ ‖H−G‖|`. -/
```

Additional flagged lines: `TimeOrderedExp.lean:242-243` (documents `timeOrderedExp_norm_le`):

```
/-- `lem:time_ordered_norm_bound`: `‖exp_T H t₁ t₂‖ ≤ Real.exp |∫ τ in t₁..t₂, ‖H τ‖|`
(the two-sided form, valid for both time orderings). -/
```

### 3.3 `CommutatorExpansion.lean` — per-declaration docstrings

**`CommutatorExpansion.lean:69-73`** — documents **`commutatorRemainder`**

```
/-- The operator-valued remainder `𝒞(τ)` of `thm:comm_exp_conj` (theory.tex:229-235). The outer
sum runs over 0-based layer indices `j : Fin s` with `k := j + 1` the 1-based index of the paper,
so `A j` is `A_k`, the antidiagonal condition `q₁ + ⋯ + q_k = p` is `q ∈ finAntidiagonal (j + 1) p`
with `q (Fin.last j) = q_k`, and `q_k ≠ 0` is `q (Fin.last j) ≠ 0`. The `ad` sequence is
`adSequence (A ∘ Fin.castLE …) q B = ad_{A_k}^{q_k} ⋯ ad_{A_1}^{q_1}(B)`. -/
```

**`CommutatorExpansion.lean:1467-1470`** — documents **`commutatorExpansion_conj`**

```
/-- `thm:comm_exp_conj` (theory.tex:222-236): the multi-layer conjugation expands as
`multiConj A B τ = Σ_{j < p} conjCoeff A B j · τ^j + commutatorRemainder A B p τ`,
where the `conjCoeff A B j` are the operators `C_j` independent of `τ`. -/
```

**`CommutatorExpansion.lean:915`** — documents **`norm_commutatorRemainder_le`**

```
/-- The spectral-norm bound of the commutator remainder (theory.tex:238-241, general operators). -/
```

**`CommutatorExpansion.lean:1033-1034`** — documents **`norm_commutatorRemainder_le_of_skewAdjoint`**

```
/-- The spectral-norm bound of the commutator remainder for anti-Hermitian operators
(theory.tex:242-244). -/
```

**`CommutatorExpansion.lean:49-52`** — documents **`multiConj`** (flagged for the inline `A₁`/`A_s` convention, no `label` token)

```
/-- The multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA₀} B e^{-τA₀}⋯e^{-τA_{s-1}}`, where
`A ⟨0⟩` is innermost (the paper's `A₁`, applied first) and `A ⟨s-1⟩` is outermost (the paper's
`A_s`). -/
```

**`CommutatorExpansion.lean:504-505`** — documents **`layerSum_le_αCommConj`**

```
/-- The layer sum is bounded by `αCommConj`: collapsing each `(j, q)` into the antidiagonal of
`Fin s` by padding with zeros (theory.tex:198-214, the `Σ_k Σ_q → Σ_{q₁+⋯+q_s=p}` step). -/
```

### 3.4 `CommutatorScaling.lean` — per-declaration docstrings

**`CommutatorScaling.lean:51-52`** — documents **`additiveKernel_summand_eq_multiConj`**

```
/-- Each additive-kernel summand is the `multiConj` of its suffix generators at `-τ`
(rep.tex:9, the `(υ,γ)`-th term of `𝒯`). -/
```

**`CommutatorScaling.lean:62-63`** — documents **`additiveKernel_full_eq_multiConj`**

```
/-- The full-product term of `additiveKernel` is the `multiConj` of all generators at `-τ`
(rep.tex:10). -/
```

**`CommutatorScaling.lean:73-74`** — documents **`additiveKernel_eq_sum_multiConj`**

```
/-- `additiveKernel P H τ = Σ_i multiConj A_i (gen_i) (-τ) − multiConj A_all (ΣH) (-τ)`
(rep.tex:5-12, the bridge to the commutator expansion). -/
```

**`CommutatorScaling.lean:127-128`** — documents **`additiveKernel_eq_commutatorRemainder_sum`**

```
/-- `thm:trotter_error_order_cond` cancellation step (theory.tex:258-264): under the order condition
`P.IsOrderOf p H`, the additive kernel is exactly the difference of the commutator remainders. -/
```

### 3.5 `ErrorTypes.lean` — per-declaration docstrings

**`ErrorTypes.lean:60`** — documents **`prefixFactorProd`**

```
/-- `∏_{j ≻ i}^{←} e^{t a_j H_j}`, the product of the factors strictly before `i`. -/
```

**`ErrorTypes.lean:65`** — documents **`strictSuffixFactorProd`**

```
/-- `∏_{j ≺ i}^{←} e^{t a_j H_j}`, the product of the factors strictly after `i`. -/
```

**`ErrorTypes.lean:70`** — documents **`suffixFactorProd`**

```
/-- `∏_{j ≤ i}^{←} e^{t a_j H_j}`, the product of the factor `i` and everything after it. -/
```

**`ErrorTypes.lean:75`** — documents **`invPrefixFactorProd`**

```
/-- `∏_{j ≻ i}^{→} e^{-t a_j H_j}`, the inverse of `prefixFactorProd`. -/
```

**`ErrorTypes.lean:80`** — documents **`invStrictSuffixFactorProd`**

```
/-- `∏_{j ≺ i}^{→} e^{-t a_j H_j}`, the inverse of `strictSuffixFactorProd`. -/
```

**`ErrorTypes.lean:240-241`** — documents **`additiveResidual`**

```
/-- The additive residual `ℛ(t)` of `type.tex:17-20`: `ℛ(t) = 𝒮'(t) - H·𝒮(t)`, so that
`d/dt 𝒮 = H·𝒮 + ℛ` (`type.tex:12`). -/
```

**`ErrorTypes.lean:246`** — documents **`eval_hasDerivAt_additive`**

```
/-- `d/dt 𝒮 = H·𝒮 + additiveResidual` (`type.tex:12`). -/
```

**`ErrorTypes.lean:253`** — documents **`exponentiatedGenerator`**

```
/-- The exponentiated generator `ℱ(t)` of `type.tex:54`. -/
```

**`ErrorTypes.lean:286`** — documents **`eval_mul_invStrictSuffix`**

```
/-- `P.eval H τ · invStrictSuffixFactorProd = prefixFactorProd · evalFactor`. -/
```

**`ErrorTypes.lean:298`** — documents **`invPrefix_mul_eval`**

```
/-- `P.eval H τ · invPrefixFactorProd = suffixFactorProd`. -/
```

**`ErrorTypes.lean:309-310`** — documents **`exponentiatedGenerator_mul_eval_eq_evalDeriv`**

```
/-- The exponentiated generator `ℱ(t)` satisfies `ℱ(t) · 𝒮(t) = d/dt 𝒮(t)` (type.tex:48-49):
the derivative `evalDeriv` written with the inverse prefix instead of the suffix. -/
```

**`ErrorTypes.lean:414`** — documents **`eval_hasDerivAt_exponentiated`**

```
/-- `d/dt 𝒮 = ℱ · 𝒮` (`type.tex:49`). -/
```

**`ErrorTypes.lean:423`** — documents **`additiveKernel`**

```
/-- The additive kernel `𝒯(τ)` of `type.tex:33-35`. -/
```

**`ErrorTypes.lean:431`** — documents **`exponentiatedError`**

```
/-- The exponentiated error `ℰ(τ) = ℱ(τ) - H` of `type.tex:62`. -/
```

**`ErrorTypes.lean:436`** — documents **`interactionGenerator`**

```
/-- The interaction-picture generator `τ ↦ e^{-τH} ℰ(τ) e^{τH}` used in `multiplicativeError`. -/
```

**`ErrorTypes.lean:441`** — documents **`multiplicativeError`**

```
/-- The multiplicative error `ℳ(t)` of `type.tex:72`. -/
```

**`ErrorTypes.lean:519`** — documents **`errorType_additive`**

```
/-- `thm:error_type` (additive): `𝒮(t) = e^{tH} + ∫₀ᵗ e^{(t−τ)H} 𝒮(τ) 𝒯(τ) dτ`. -/
```

**`ErrorTypes.lean:542`** — documents **`errorType_exponentiated`**

```
/-- `thm:error_type` (exponentiated): `𝒮(t) = exp_T(∫₀ᵗ (H + ℰ(τ)) dτ)`. -/
```

**`ErrorTypes.lean:560`** — documents **`errorType_multiplicative`**

```
/-- `thm:error_type` (multiplicative): `𝒮(t) = e^{tH} (1 + ℳ(t))`. -/
```

Additionally flagged (no `label` token but cites a paper file/line): `ErrorTypes.lean:169`
(`evalDeriv`):

```
/-- The factor-indexed derivative of `P.eval H` at time `t` (the paper's `d/dt 𝒮`). -/
```

**`ErrorTypes.lean:226`** — documents **`eval_hasDerivAt`**

```
/-- The first derivative of the product formula (`d/dt 𝒮` in `type.tex:47-48`). -/
```

### 3.6 `ExpSMulConj.lean` — per-declaration docstrings

**`ExpSMulConj.lean:132-134`** — documents **`expSMulConj_taylor`**

```
/-- Single-layer Taylor expansion (theory.tex:137-150):
`expSMulConj A X τ = Σ_{j<p} adPow A j X τ^j/j! +
  ∫₀^τ expSMulConj A (adPow A p X) (τ-s) s^{p-1}/(p-1)!`. -/
```

**`ExpSMulConj.lean:240-242`** — documents **`norm_expSMulConj_remainder_le`**

```
/-- Norm bound of the single-layer remainder (theory.tex:151-155):
`‖∫₀^τ expSMulConj A (adPow A p X) (τ-s) * s^{p-1}/(p-1)!‖ ≤
  ‖adPow A p X‖ * |τ|^p/p! * e^{2|τ|‖A‖}`. -/
```

### 3.7 `MainTheorem.lean` — per-declaration docstrings

**`MainTheorem.lean:45-48`** — documents **`norm_additiveKernel_le_of_rem_bound`**

```
/-- Shared skeleton of the additive-kernel norm bound (`thm:trotter_error_order_cond`): from
per-remainder bounds `‖remᵢ(−τ)‖ ≤ αᵢ · C` and `‖rem_all(−τ)‖ ≤ α_all · C` with `0 ≤ C`, and the
coefficient bound `Σᵢ αᵢ + α_all ≤ 2 Υ Σ_γ α_γ`, conclude
`‖additiveKernel P H τ‖ ≤ 2 Υ (Σ_γ α_γ) · C`. -/
```

**`MainTheorem.lean:91-92`** — documents **`norm_additiveKernel_le_of_skewAdjoint`**

```
/-- `thm:trotter_error_order_cond` (anti-Hermitian branch): the spectral norm of the additive
kernel is bounded by `2 Υ (Σ_γ α_comm) |τ|^p / p!`. -/
```

**`MainTheorem.lean:128-129`** — documents **`norm_additiveKernel_le`**

```
/-- `thm:trotter_error_comm_scaling` (general branch): the spectral norm of the additive kernel is
bounded by `2 Υ (Σ_γ α_comm) |τ|^p / p! · exp(2|τ| Υ Σ ‖H_γ‖)`. -/
```

**`MainTheorem.lean:196-197`** — documents **`norm_eval_mul_commutatorRemainderTerm_le`**

```
/-- The single suffix-remainder summand, scaled by `P.eval H τ`, telescopes to a single exponential
`exp (|τ| · Υ · Σ ‖H γ‖)` (rep.tex:50–113). -/
```

**`MainTheorem.lean:273-274`** — documents **`norm_eval_mul_commutatorRemainderTerm_ordered_le`**

```
/-- The single ordered-remainder summand, scaled by `P.eval H τ`, telescopes to a single exponential
`exp (|τ| · Υ · Σ ‖H γ‖)`. -/
```

**`MainTheorem.lean:327-328`** — documents **`norm_additiveResidual_le_of_rem_bound`**

```
/-- Shared skeleton of the additive-residual norm bound: from per-remainder bounds of the scaled
`P.eval H τ · remᵢ(-τ)` terms and the coefficient bound, conclude the telescoped residual bound. -/
```

**`MainTheorem.lean:373-374`** — documents **`norm_additiveResidual_le`**

```
/-- `thm:trotter_error_comm_scaling` (general branch): the additive residual telescopes to
`2 Υ (Σ_γ α_comm) |τ|^p / p! · exp(|τ| Υ Σ ‖H_γ‖)` (rep.tex:96–113). -/
```

**`MainTheorem.lean:414-415`** — documents **`eval_sub_exp_eq_integral_residual`**

```
/-- The additive error as an integral of the additive residual (the unfactored form of
`errorType_additive`). -/
```

**`MainTheorem.lean:429-430`** — documents **`trotter_error_bound_comm_scaling`**

```
/-- `thm:trotter_error_comm_scaling` (general branch): the explicit pointwise commuting-scaling
bound with the exponential prefactor `exp (2 t Υ Σ ‖H_γ‖)`. -/
```

**`MainTheorem.lean:518`** — documents **`trotter_error_comm_scaling`**

```
/-- `thm:trotter_error_comm_scaling` (general branch): the commuting-scaling bound as `t → ∞`. -/
```

**`MainTheorem.lean:540-541`** — documents **`trotter_error_bound_comm_scaling_of_skewAdjoint`**

```
/-- `eq:trotter_error_comm_scaling_bound` (anti-Hermitian): the explicit pointwise commuting-scaling
bound, valid for all `t ≥ 0`. -/
```

**`MainTheorem.lean:604`** — documents **`trotter_error_comm_scaling_of_skewAdjoint`**

```
/-- `thm:trotter_error_comm_scaling` (anti-Hermitian): the commuting-scaling bound as `t → ∞`. -/
```

**`MainTheorem.lean:625-627`** — documents **`multiplicativeError_eq_integral_residual`**

```
/-- The multiplicative error as an integral of the additive residual (rep.tex:115-123):
`ℳ(t) = ∫₀ᵗ e^{-τH} ℛ(τ) dτ`. Follows from `errorType_multiplicative` together with the additive
representation `𝒮(t) − e^{tH} = e^{tH} ∫₀ᵗ e^{-τH} ℛ(τ) dτ`. -/
```

**`MainTheorem.lean:662-664`** — documents **`multiplicative_error_bound_comm_scaling`**

```
/-- `thm:trotter_error_comm_scaling` (general branch, multiplicative): the explicit pointwise
commuting-scaling bound for the multiplicative error with exponential prefactor
`exp (2 t Υ Σ ‖H_γ‖)`. -/
```

**`MainTheorem.lean:753-754`** — documents **`multiplicative_error_comm_scaling`**

```
/-- `thm:trotter_error_comm_scaling` (general branch, multiplicative): the multiplicative-error
commuting-scaling bound as `t → ∞`. -/
```

**`MainTheorem.lean:795-796`** — documents **`multiplicative_error_bound_comm_scaling_of_skewAdjoint`**

```
/-- `thm:trotter_error_comm_scaling` (anti-Hermitian branch, multiplicative): the multiplicative
error pointwise commuting-scaling bound, valid for all `t ≥ 0` (no exponential prefactor). -/
```

**`MainTheorem.lean:809-810`** — documents **`multiplicative_error_comm_scaling_of_skewAdjoint`**

```
/-- `thm:trotter_error_comm_scaling` (anti-Hermitian branch, multiplicative): the
multiplicative-error commuting-scaling bound as `t → ∞`. -/
```

### 3.8 `OrderCondition.lean` — per-declaration docstrings

**`OrderCondition.lean:61-62`** — documents **`ProductFormulaData.IsOrderOf`**

```
/-- `P` is a `p`-th order formula on summands `H` if `‖𝒮(t) − e^{tH}‖ = O(t^{p+1})`
as `t → 0` (`prelim.tex:150`). -/
```

**`OrderCondition.lean:89-90`** — documents **`isBigO_norm_iff_iteratedDeriv_lt_eq_zero`**

```
/-- `lem:order_cond_deriv` in the `O(τ^p)` form: a smooth `F` satisfies `F = O(τ^p)` iff all its
iterated derivatives of order `< p` vanish at `0`. For `p = 0` both sides hold automatically. -/
```

**`OrderCondition.lean:117`** — documents **`orderCond_add`**

```
/-- Addition rule (order.tex:80): `F = O(τ^p)` and `G = O(τ^q)` imply `F + G = O(τ^{min p q})`. -/
```

**`OrderCondition.lean:142-143`** — documents **`orderCond_mul`**

```
/-- Multiplication rule (order.tex:81): `F = O(τ^p)` and `G = O(τ^q)` imply
`F * G = O(τ^{p+q})`. -/
```

**`OrderCondition.lean:158`** — documents **`orderCond_deriv_iff`**

```
/-- Differentiation rule (order.tex:82): `F = O(τ^{p+1})` iff `F 0 = 0` and `F' = O(τ^p)`. -/
```

**`OrderCondition.lean:198`** — documents **`orderCond_integral_iff`**

```
/-- Integration rule (order.tex:83): `F = O(τ^p)` iff `∫₀ᵗ F = O(t^{p+1})`. -/
```

**`OrderCondition.lean:415-419`** — documents **`iteratedIntegralMonomial`**

```
/-- The canonical nested iterated integral of a monomial: `Γ` nested integrals, the `(i+1)`-st
integration variable carrying the power `p i`, each integral running from `0` to the immediately
preceding variable (the outermost from `0` to `t`). This is the sequential specialization of the
paper's `lem:monomial`; the general form (each inner upper limit an arbitrary earlier variable)
has the same order `t^{Σp + Γ}` by the same induction. -/
```

**`OrderCondition.lean:465`** — documents **`monomial_integral_order`**

```
/-- `lem:monomial`: the canonical nested iterated integral of a monomial is `O(t^{Σp + Γ})`. -/
```

**`OrderCondition.lean:761-763`** — documents **`errorOrderCond_iff`**

```
/-- `thm:error_order_cond` (order.tex:124): the additive (`𝒯 = O(τ^p)`), exponentiated
(`ℰ = O(τ^p)`), and multiplicative (`ℳ = O(t^{p+1})`) order conditions are all equivalent to the
`p`-th order condition `𝒮(t) = e^{tH} + O(t^{p+1})`. -/
```

**`OrderCondition.lean:612-613`** — documents **`errorOrderCond_additive_iff`**

```
/-- `thm:error_order_cond`, additive part: the additive-kernel order condition `𝒯 = O(τ^p)` is
equivalent to the `p`-th order condition `𝒮(t) = e^{tH} + O(t^{p+1})`. -/
```

**`OrderCondition.lean:688-689`** — documents **`errorOrderCond_exponentiated_iff`**

```
/-- `thm:error_order_cond`, exponentiated part: the exponentiated-error order condition
`ℰ = O(τ^p)` is equivalent to the `p`-th order condition. -/
```

**`OrderCondition.lean:726-727`** — documents **`errorOrderCond_multiplicative_iff`**

```
/-- `thm:error_order_cond`, multiplicative part: the multiplicative-error order condition
`ℳ = O(t^{p+1})` is equivalent to the `p`-th order condition. -/
```

**`OrderCondition.lean:371-372`** — documents **`orderCond_exp_iff`**

```
/-- Exponentiation rule (order.tex:84): `F = G + O(τ^p)` iff
`exp_T(∫₀ᵗ F) = exp_T(∫₀ᵗ G) + O(t^{p+1})`. -/
```

*(Note: `OrderCondition.lean:847-849` documents `polynomial_isBigO_iff_coeffs_zero` and cites
`theory.tex:258-264` — quoted in §5 below.)*

### 3.9 `OrderingRemoval.lean` — per-declaration docstrings

**`OrderingRemoval.lean:221-223`** — documents **`αCommConj_sum_le_αComm`**

```
/-- rep.tex:129-139 (ordering removal): the sum over innermost summands of the conjugation
`α_comm` is bounded by `p! · Υ^p · α~_comm` — each multinomial coefficient is ≤ `p!`, and each
nested-commutator pattern recurs in at most `Υ^p` stage placements. -/
```

**`OrderingRemoval.lean:262-265`** — documents **`sum_αCommConj_orderedSummandsEval_le`**

```
/-- The `α_comm` sum over the `evalIndexList`-ordered summands (rather than the raw
`orderedSummands`) is bounded by `p! · Υ^p · α~_comm`. This is `αCommConj_sum_le_αComm` in the
form the pointwise bounds use, via `orderedSummands (reverseStages P) H = orderedSummandsEval P
H`. -/
```

**`OrderingRemoval.lean:273-274`** — documents **`two_mul_commScaling_div_factorial_le`**

```
/-- The commuting-scaling coefficient `2 Υ Σ_γ α_γ / p!` is bounded by `2 Υ^{p+1} α~_comm`
(rep.tex:96-113): the last algebraic step shared by all four commuting-scaling bounds. -/
```

**`OrderingRemoval.lean:189`** — documents **`sum_adSequence_norm_le`**

```
/-- For each `γ`, the sum over all `q` of the nested-commutator norms is bounded by
`Υ^p · Σ_{γ' : γ'⟨0⟩=γ} ‖nestedComm (H ∘ γ')‖` (the paper's rep.tex:135–137). -/
```

### 3.10 `Prefactor.lean` — per-declaration docstrings

**`Prefactor.lean:47-49`** — documents **`exp_mul_exp_sub_exp_add_eq_integral`**

```
/-- The two-summand additive error identity (`prefactor.tex:16`, in anti-Hermitian-generator
form): for `S₁(t) = e^{tB} e^{tA}` and `H = A + B`,
`S₁(t) - e^{tH} = ∫₀ᵗ e^{(t-τ)H} (e^{τB} A e^{-τB} - A) e^{τB} e^{τA} dτ`. -/
```

**`Prefactor.lean:112-113`** — documents **`firstOrder_twoTerm`**

```
/-- The two-summand first-order Lie-Trotter bound (`prefactor.tex:29`, anti-Hermitian-generator
form): for anti-Hermitian `A, B`, `‖e^{tB} e^{tA} - e^{t(A+B)}‖ ≤ (t²/2) · ‖⁅B, A⁆‖`. -/
```

**`Prefactor.lean:224-225`** — documents **`firstOrder_bound`**

```
/-- `prop:pf1_bound` (prefactor.tex:45–50, anti-Hermitian-generator form): the tight first-order
Lie-Trotter bound for general `Γ`. -/
```

**`Prefactor.lean:288-289`** — documents **`secondOrderKernel`**

```
/-- The second-order kernel `𝒯₂(τ)` of prefactor.tex:60, anti-Hermitian-generator form:
`e^{τB} (A/2) e^{-τB} - A/2 - e^{-(τ/2)A} B e^{(τ/2)A} + B`. -/
```

**`Prefactor.lean:295`** — documents **`secondOrder_sub_eq_integral`**

```
/-- The second-order Duhamel identity (prefactor.tex:52–57, anti-Hermitian-generator form). -/
```

**`Prefactor.lean:417-418`** — documents **`expSMulConj_taylor_two`**

```
/-- The `p = 2` specialization of the single-layer Taylor expansion:
`expSMulConj A X τ = X + ⁅A, X⁆ * τ + ∫₀^τ expSMulConj A (adPow A 2 X) (τ-s) * s`. -/
```

**`Prefactor.lean:431-432`** — documents **`secondOrderKernel_eq_remainder`**

```
/-- The second-order kernel is the difference of two `p = 2` Taylor remainders
(prefactor.tex:63–68, anti-Hermitian-generator form). -/
```

**`Prefactor.lean:445-446`** — documents **`norm_expSMulConj_taylor_remainder_le_of_skew`**

```
/-- Norm bound for a single-layer `p = 2` Taylor remainder under an anti-Hermitian generator:
`‖∫₀^τ expSMulConj A Y (τ-s) * s‖ ≤ ‖Y‖ · |τ|²/2`. -/
```

**`Prefactor.lean:480-481`** — documents **`norm_secondOrderKernel_le`**

```
/-- The second-order kernel bound (prefactor.tex:82–85, anti-Hermitian-generator form):
`‖𝒯₂(τ)‖ ≤ (τ²/4) ‖adPow B 2 A‖ + (τ²/8) ‖adPow A 2 B‖`. -/
```

**`Prefactor.lean:507-508`** — documents **`secondOrder_twoTerm`**

```
/-- The two-summand second-order Suzuki bound (prefactor.tex:82–85, anti-Hermitian-generator
form): `‖e^{(t/2)A} e^{tB} e^{(t/2)A} - e^{t(A+B)}‖ ≤ (t³/12)‖⁅B,⁅B,A⁆⁆‖ + (t³/24)‖⁅A,⁅A,B⁆⁆‖`. -/
```

**`Prefactor.lean:620-621`** — documents **`secondOrder_bound`**

```
/-- `prop:pf2_bound` (prefactor.tex:105–114, anti-Hermitian-generator form): the tight second-order
Suzuki bound for general `Γ`. -/
```

**`Prefactor.lean:42`** (a non-docstring comment, quoted for completeness)

```
/- The associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A`, matching `Commutator.lean`. -/
```

### 3.11 `Suzuki.lean` — per-declaration docstrings

**`Suzuki.lean:48-50`** — documents **`lieTrotter`**

```
/-- The first-order Lie-Trotter formula `∏_{γ=1}^Γ e^{t K_γ} = e^{t K_{Γ-1}} ⋯ e^{t K_0}` (the
paper's `∏_{γ=1}^Γ A_γ = A_Γ ⋯ A_1` convention, in 0-based `Fin Γ`), defined by peeling the
innermost (rightmost) factor `K 0`. -/
```

**`Suzuki.lean:57-60`** — documents **`suzuki2`**

```
/-- The second-order Suzuki formula, defined recursively by peeling the outermost (index-`0`)
factor: `S₂(K, t) = e^{(t/2)K₀} · S₂(K ∘ Fin.succ, t) · e^{(t/2)K₀}`. This is the ordered product
`e^{(t/2)K₀} ⋯ e^{(t/2)K_{Γ-1}} · e^{(t/2)K_{Γ-1}} ⋯ e^{(t/2)K₀}` (the paper's
`∏_{γ=Γ}^1 e^{(t/2)K_γ} · ∏_{γ=1}^Γ e^{(t/2)K_γ}`, in anti-Hermitian-generator form). -/
```

**`Suzuki.lean:67-68`** — documents **`suzukiU`**

```
/-- `u_k = 1 / (4 - 4^{1/(2k-1)})`, the `eq:pf2k` scaling constant (meaningful for `k ≥ 2`; the
recursion `suzuki (k+2)` below only applies it to an argument `≥ 2`). -/
```

**`Suzuki.lean:72-74`** — documents **`suzuki`**

```
/-- The higher-order Suzuki formula `S_{2k}` (`eq:pf2k`): `suzuki 1 = suzuki2`, and for `k ≥ 2`
`suzuki k K t = suzuki (k-1) K (u_k t)² · suzuki (k-1) K ((1-4u_k) t) · suzuki (k-1) K (u_k t)²`.
The `suzuki 0` case is a junk identity. -/
```

**`Suzuki.lean:84-85`** — documents **`lieTrotterData`**

```
/-- The Lie-Trotter formula as a `ProductFormulaData`: `Υ = 1`, all coefficients `1`, identity
permutation (`eq:pf1`). -/
```

**`Suzuki.lean:91-92`** — documents **`suzuki2Data`**

```
/-- The second-order Suzuki formula as a `ProductFormulaData`: `Υ = 2`, all coefficients `1/2`,
stage `0` in order and stage `1` reversed (`eq:pf2k`). -/
```

**`Suzuki.lean:135`** — documents **`lieTrotter_eq_eval`**

```
/-- `lieTrotter` is `(lieTrotterData Γ).eval` (`prelim.tex:127,142`). -/
```

**`Suzuki.lean:199`** — documents **`suzuki2_eq_eval`**

```
/-- `suzuki2` is `(suzuki2Data Γ).eval` (`prelim.tex:136,142`). -/
```

**`Suzuki.lean:277-278`** — documents **`suzukiData`**

```
/-- The higher-order Suzuki formula `S_{2k}` as a `ProductFormulaData` (`eq:pf2k`, with
`Υ = 2 · 5^{k-1}` stages and alternately reversed permutations). -/
```

**`Suzuki.lean:293-294`** — documents **`suzukiData_succ_eval`**

```
/-- The `(k + 2)`-nd Suzuki data evaluates as the paper's `S_{2k}` recursion
(`eq:pf2k`): `S_{2k}(t) = S_{2k-2}(u_k t)² · S_{2k-2}((1-4u_k) t) · S_{2k-2}(u_k t)²`. -/
```

**`Suzuki.lean:335-336`** — documents **`suzuki_eq_eval`**

```
/-- `suzuki` is `(suzukiData k Γ).eval` (`prelim.tex:136,142`), for the meaningful range `1 ≤ k`
(the `suzuki 0` case is a junk identity). -/
```

**`Suzuki.lean:264`** — documents **`suzukiStages`**

```
/-- The number of stages `Υ = 2 · 5^{k-1}` of the `k`-th Suzuki formula (`eq:pf2k`). -/
```

### 3.12 `Calculus.lean` — per-declaration docstrings

**`Calculus.lean:300-303`** — documents **`taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below`**

```
/-! ### CS19 Supplementary Lemma 1: big-O scaling iff derivatives vanish at 0 -/

/-- If the first `n` iterated derivatives of `F` at `x₀` vanish, then the `n`-th Taylor
polynomial of `F` at `x₀` is just the leading term `(x - x₀)^n • ((n! : ℝ)⁻¹ • F⁽ⁿ⁾(x₀))`. -/
```

**`Calculus.lean:321-322`** — documents **`isBigO_norm_iff_iteratedDeriv_eq_zero`**

```
/-- A smooth function `F` satisfies `‖F t‖ = O(t^(p + 1))` as `t → 0` if and only if its
first `p` iterated derivatives vanish at `0` (CS19, Supplementary Lemma 1). -/
```

**`Calculus.lean:540-542`** — documents **`norm_pow_mul_exp_le`**

```
/-- For a single element, the norm of `H^k * exp (s • H)` is bounded by
`‖H‖^k * Real.exp (s * ‖H‖)` whenever `s ≥ 0` (the paper's single-element bound,
prelim.tex:186–187). -/
```

**`Calculus.lean:436-437`** — documents **`taylor_paper_scalar_eq`**

```
/-- The scalar identity used to pass from the standard integral remainder to the paper's
substituted form: `t * (t - u * t)^p / p! = (p + 1) * (1 - u)^p * t^(p + 1) / (p + 1)!`. -/
```

**`Calculus.lean:473-474`** — documents **`taylor_integral_remainder_iteratedDeriv_zero_paper`**

```
/-- Taylor's theorem with the integral remainder in the paper's substituted form
(`s = u * t`): `f t = (p + 1) • ∫₀¹ (1 - u)^p * t^(p + 1) / (p + 1)! • f⁽ᵖ⁺¹⁾(u * t) du`. -/
```

### 3.13 `OneNormScaling.lean` — per-declaration docstrings

**`OneNormScaling.lean:84-85`** — documents **`norm_iteratedDeriv_F_le`**

```
/-- The `(p+1)`-st derivative of the error `F = eval − exp` is bounded by the paper's
two-term bound (prelim.tex:186–187), valid for `0 ≤ u ≤ 1`, `0 ≤ t`. -/
```

**`OneNormScaling.lean:111-113`** — documents **`norm_taylor_le_of_deriv_bound`**

```
/-- If the first `p` iterated derivatives of `F` vanish at `0` and `F⁽ᵖ⁺¹⁾` is bounded by `D`
on `u·t` for `u ∈ [0,1]`, then `‖F t‖ ≤ t^(p+1)/(p+1)! · D` for `t ≥ 0`
(Taylor's theorem with integral remainder, prelim.tex:168–172). -/
```

**`OneNormScaling.lean:167`** — documents **`isBigO_pow_le_target_left`**

```
/-- For `t ≤ 0` near `0`, the target `(S·t)^{p+1} e^{t·a}` dominates `t^{p+1}`. -/
```

**`OneNormScaling.lean:191-192`** — documents **`paper_bound_le_target`**

```
/-- The paper's explicit bound (eq:trotter_error_one_norm_scaling_bound), simplified to the
target scaling for `0 ≤ t ≤ 1`. -/
```

**`OneNormScaling.lean:238-239`** — documents **`trotter_error_bound_one_norm_scaling`**

```
/-- `eq:trotter_error_one_norm_scaling_bound`: the explicit pointwise Trotter-error bound,
valid for all `t ≥ 0`. -/
```

**`OneNormScaling.lean:259-260`** — documents **`trotter_error_one_norm_scaling`**

```
/-- `lem:trotter_error_one_norm_scaling` (general branch): for a `p`-th order product
formula, `‖𝒮(t) − e^{tH}‖ = 𝒪((Σ_γ ‖H_γ‖ t)^{p+1} e^{tΥ Σ_γ ‖H_γ‖})` as `t → 0`. -/
```

**`OneNormScaling.lean:380-381`** — documents **`eval_iteratedDeriv_norm_le_skew`**

```
/-- The `(p+1)`-st derivative of `eval` is bounded by `(Υ·Σ_γ ‖H_γ‖)^{p+1}` in the
anti-Hermitian case. -/
```

**`OneNormScaling.lean:436-437`** — documents **`norm_iteratedDeriv_F_le_skew`**

```
/-- The `(p+1)`-st derivative of the error is bounded by `(ΥS)^{p+1} + S^{p+1}` in the
anti-Hermitian case, for all `u`, `t`. -/
```

**`OneNormScaling.lean:464-465`** — documents **`trotter_error_bound_one_norm_scaling_of_skew_adjoint`**

```
/-- `eq:trotter_error_one_norm_scaling_bound` in the anti-Hermitian case: the explicit pointwise
bound, valid for all `t ≥ 0`. -/
```

**`OneNormScaling.lean:486-487`** — documents **`trotter_error_one_norm_scaling_of_skew_adjoint`**

```
/-- `lem:trotter_error_one_norm_scaling` (anti-Hermitian branch): the exponential
factor drops out when the `H_γ` are anti-Hermitian. -/
```

**`OneNormScaling.lean:619-621`** — documents **`trotter_number_one_norm_scaling`**

```
/-- `cor:trotter_number_one_norm_scaling`: for anti-Hermitian summands, the `r`-step
Trotter error decays as `O(r^{-p})` as `r → ∞`; equivalently, `r = O(ε^{-1/p})` steps
suffice for accuracy `ε`. -/
```

### 3.14 `ProductFormula.lean` — per-declaration docstrings

**`ProductFormula.lean:59-62`** — documents **`ProductFormulaData`**

```
/-- The data of a general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` (`eq:pf`): `Υ` stages, `Γ` summands, real coefficients
`a_{(υ,γ)}` uniformly bounded by `1` in absolute value, and per-stage permutations
`π_υ`. -/
```

**`ProductFormula.lean:142-143`** — documents **`eval_iteratedDeriv_succ`**

```
/-- The `(p + 1)`-st iterated derivative of `eval`, expanded as a multinomial Leibniz sum over
multi-indices on `Fin Υ × Fin Γ` (the paper's `𝒮^{(p+1)}(ut)` expansion, prelim.tex:174–178). -/
```

**`ProductFormula.lean:285-286`** — documents **`eval_iteratedDeriv_norm_le`**

```
/-- The `(p + 1)`-st iterated derivative norm bound (prelim.tex:182–185):
`‖𝒮^{(p+1)}(ut)‖ ≤ (Υ · Σ_γ ‖H_γ‖)^{p+1} · Real.exp (t · Υ · Σ_γ ‖H_γ‖)`. -/
```

**`ProductFormula.lean:203-204`** — documents **`norm_factor_le`**

```
/-- Per-factor norm bound: `‖(a • H)^q * exp (u t a • H)‖ ≤ ‖H‖^q * Real.exp (t * ‖H‖)`
(prelim.tex:183–184). -/
```

**`ProductFormula.lean:201`** — a section header comment (`/-! ### Norm bounds for the derivative expansion (prelim.tex:182–188) -/`)

**`ProductFormula.lean:476-479`** — documents **`orderedSummands`**

```
/-- The product formula's permuted summands `H_{π_υ(γ)}`, as a `Fin (Υ * Γ)`-indexed list in
`evalIndexList` order (the paper's `\overrightarrow{\{H_{π_υ(γ)}\}}`). The index
`i = υ * Γ + γ` carries the summand `H_{π_υ(γ)}`; `i.divNat` is the stage and `i.modNat` the
summand index within the stage. -/
```

### 3.15 `Commutator.lean` and `Integrals.lean`

Only the module headers (quoted in §3.1) cite the paper. No per-declaration docstring in either
file mentions a paper label. (`Commutator.lean`'s `αComm`/`αCommConj` docstrings say "the paper's
`α~_comm`" / "the paper's `α_comm(A_s, …, A_1, B)`", i.e. informal references without a label or
file name; quoted here for completeness:)

**`Commutator.lean:87-89`** — documents **`αComm`**

```
/-- The paper's `α~_comm`: the sum of the norms of all nested commutators
`[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_{γ_1}]]` over all tuples `γ : Fin (p + 1) → Fin Γ`
(repeated indices allowed). -/
```

**`Commutator.lean:94-95`** — documents **`αCommConj`**

```
/-- The paper's `α_comm(A_s, …, A_1, B)`: the multinomial-weighted sum
`Σ_{q₁+⋯+q_s = p} (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`. -/
```

---

## 4. Mapping table

Sorted by paper file, then by the order the labels appear in that file (line numbers in the `.tex`
source). "Lean declaration" = `TrotterError.<name>`.

### `prelim.tex` — §2.2 time-ordered evolutions, §2.3 product formulas + 1-norm bound

| Lean declaration | File:line | Paper label(s) cited | Paper section/file |
|---|---|---|---|
| *(module header)* | `TimeOrderedExp.lean:11` | `arXiv:1912.08854` §2.2 | prelim.tex §2.2 (`sec:prelim_expT`, l.39) |
| `timeOrderedExp_const` | `TimeOrderedExp.lean:517` | `prelim.tex:41` (constant-generator case `e^{tH}`) | prelim.tex l.41 |
| `timeOrderedExp_hasDerivAt` | `TimeOrderedExp.lean:385` | `prelim.tex:44-49` (1st differentiation rule) | prelim.tex l.44–49 |
| `timeOrderedExp_hasDerivAt_lower` | `TimeOrderedExp.lean:532` | `prelim.tex:44-49` (2nd differentiation rule) | prelim.tex l.44–49 |
| `timeOrderedExp_mul` | `TimeOrderedExp.lean:441` | `prelim.tex:52` (multiplicative property) | prelim.tex l.52 |
| `timeOrderedExp_eq_integral` | `TimeOrderedExp.lean:326` | `eq:int_eq` (`prelim.tex:58`) | prelim.tex l.57–59 |
| `timeOrderedExp_duhamel` | `TimeOrderedExp.lean:643` | `lem:td_Duhamel` | prelim.tex l.61–72 (`sec:prelim_expT`) |
| `timeOrderedExp_interaction_picture` | `TimeOrderedExp.lean:677` | `lem:interaction_picture` | prelim.tex l.75–87 |
| `fundamentalTheorem_timeOrderedExp` | `TimeOrderedExp.lean:780` | `lem:fte` | prelim.tex l.93–102 |
| `fundamentalTheorem_timeOrderedExp_of_isUnit` | `TimeOrderedExp.lean:740` | `lem:fte` (⇒ direction) | prelim.tex l.93–102 |
| `fundamentalTheorem_timeOrderedExp_of_timeOrderedExp` | `TimeOrderedExp.lean:768` | `lem:fte` (⇐ direction) | prelim.tex l.93–102 |
| `timeOrderedExp_norm_le` | `TimeOrderedExp.lean:244` | `lem:time_ordered_norm_bound` (item 1) | prelim.tex l.105–112 |
| `timeOrderedExp_norm_eq_one_of_skewAdjoint` | `TimeOrderedExp.lean:831` | `lem:time_ordered_norm_bound` (item 2) | prelim.tex l.105–112 |
| `timeOrderedExp_sub` | `TimeOrderedExp.lean:953` | `cor:time_ordered_distance_bound` (difference representation) | prelim.tex l.113–122 |
| `timeOrderedExp_dist_le` | `TimeOrderedExp.lean:1051` | `cor:time_ordered_distance_bound` (item 1) | prelim.tex l.113–122 |
| `timeOrderedExp_dist_le_of_skewAdjoint` | `TimeOrderedExp.lean:1077` | `cor:time_ordered_distance_bound` (item 2) | prelim.tex l.113–122 |
| `ProductFormulaData` | `ProductFormula.lean:63` | `eq:pf` | prelim.tex l.142–146 (`sec:prelim_pf`) |
| `lieTrotterData` | `Suzuki.lean:86` | `eq:pf1` | prelim.tex l.127–131 |
| `suzukiU` | `Suzuki.lean:69` | `eq:pf2k` | prelim.tex l.132–140 |
| `suzuki` | `Suzuki.lean:75` | `eq:pf2k` | prelim.tex l.132–140 |
| `suzuki2Data` | `Suzuki.lean:93` | `eq:pf2k` | prelim.tex l.132–140 |
| `suzukiStages` | `Suzuki.lean:265` | `eq:pf2k` (`Υ = 2·5^{k-1}`) | prelim.tex l.146 |
| `suzukiData` | `Suzuki.lean:279` | `eq:pf2k` | prelim.tex l.132–140 |
| `suzukiData_succ_eval` | `Suzuki.lean:295` | `eq:pf2k` | prelim.tex l.132–140 |
| `lieTrotter_eq_eval` | `Suzuki.lean:136` | `prelim.tex:127,142` | prelim.tex l.127–146 |
| `suzuki2_eq_eval` | `Suzuki.lean:200` | `prelim.tex:136,142` | prelim.tex l.127–146 |
| `suzuki_eq_eval` | `Suzuki.lean:337` | `prelim.tex:136,142` | prelim.tex l.127–146 |
| `ProductFormulaData.IsOrderOf` | `OrderCondition.lean:63` | `prelim.tex:150` (`𝒮(t) = e^{tH} + O(t^{p+1})`) | prelim.tex l.148–151 |
| `norm_taylor_le_of_deriv_bound` | `OneNormScaling.lean:114` | `prelim.tex:168–172` (Taylor w/ integral remainder) | prelim.tex l.167–172 |
| `eval_iteratedDeriv_succ` | `ProductFormula.lean:144` | `prelim.tex:174–178` (`𝒮^{(p+1)}(ut)` expansion) | prelim.tex l.174–178 |
| `eval_iteratedDeriv_norm_le` | `ProductFormula.lean:287` | `prelim.tex:182–185` | prelim.tex l.180–189 |
| `norm_factor_le` | `ProductFormula.lean:205` | `prelim.tex:183–184` | prelim.tex l.180–189 |
| `norm_pow_mul_exp_le` | `Calculus.lean:543` | `prelim.tex:186–187` (single-element bound) | prelim.tex l.186–187 |
| `norm_iteratedDeriv_F_le` | `OneNormScaling.lean:86` | `prelim.tex:186–187` (two-term bound) | prelim.tex l.186–189 |
| `paper_bound_le_target` | `OneNormScaling.lean:193` | `eq:trotter_error_one_norm_scaling_bound` | prelim.tex l.191–198 |
| `trotter_error_bound_one_norm_scaling` | `OneNormScaling.lean:240` | `eq:trotter_error_one_norm_scaling_bound` | prelim.tex l.191–198 |
| `trotter_error_bound_one_norm_scaling_of_skew_adjoint` | `OneNormScaling.lean:466` | `eq:trotter_error_one_norm_scaling_bound` | prelim.tex l.191–198 |
| `trotter_error_one_norm_scaling` | `OneNormScaling.lean:261` | `lem:trotter_error_one_norm_scaling` (+ `eq:one_norm_error_imag`) | prelim.tex l.154–166 |
| `trotter_error_one_norm_scaling_of_skew_adjoint` | `OneNormScaling.lean:488` | `lem:trotter_error_one_norm_scaling` (anti-Hermitian branch, `eq:one_norm_error_real`) | prelim.tex l.154–166 |
| `trotter_number_one_norm_scaling` | `OneNormScaling.lean:622` | `cor:trotter_number_one_norm_scaling` | prelim.tex l.213–219 |

### `type.tex` — Appendix A (proof of `thm:error_type`)

| Lean declaration | File:line | Paper label(s) cited | Paper section/file |
|---|---|---|---|
| `eval_hasDerivAt` | `ErrorTypes.lean:227` | `type.tex:47-48` (`d/dt 𝒮`) | type.tex l.47–48 |
| `eval_hasDerivAt_additive` | `ErrorTypes.lean:247` | `type.tex:12` (`d/dt 𝒮 = H·𝒮 + ℛ`) | type.tex l.12 |
| `additiveResidual` | `ErrorTypes.lean:242` | `type.tex:17-20` (residual `ℛ`), `type.tex:12` | type.tex l.12, 17–20 |
| `eval_hasDerivAt_exponentiated` | `ErrorTypes.lean:415` | `type.tex:49` (`d/dt 𝒮 = ℱ·𝒮`) | type.tex l.48–49 |
| `exponentiatedGenerator` | `ErrorTypes.lean:254` | `type.tex:54` (generator `ℱ(t)`) | type.tex l.54 |
| `exponentiatedGenerator_mul_eval_eq_evalDeriv` | `ErrorTypes.lean:311` | `type.tex:48-49` | type.tex l.48–49 |
| `additiveKernel` | `ErrorTypes.lean:424` | `type.tex:33-35` (kernel `𝒯(τ)`) | type.tex l.33–35 |
| `exponentiatedError` | `ErrorTypes.lean:432` | `type.tex:62` (`ℰ(τ) = ℱ(τ) − H`) | type.tex l.62 |
| `multiplicativeError` | `ErrorTypes.lean:442` | `type.tex:72` (`ℳ(t)`) | type.tex l.72 |
| `errorType_additive` | `ErrorTypes.lean:520` | `thm:error_type` (additive form) | theory.tex l.57–82 (`thm:error_type`), proved in type.tex |
| `errorType_exponentiated` | `ErrorTypes.lean:543` | `thm:error_type` (exponentiated form) | theory.tex l.57–82, type.tex |
| `errorType_multiplicative` | `ErrorTypes.lean:561` | `thm:error_type` (multiplicative form) | theory.tex l.57–82, type.tex |

### `order.tex` — Appendix B (order conditions)

| Lean declaration | File:line | Paper label(s) cited | Paper section/file |
|---|---|---|---|
| `isBigO_norm_iff_iteratedDeriv_lt_eq_zero` | `OrderCondition.lean:91` | `lem:order_cond_deriv` (`O(τ^p)` form) | order.tex l.13–24 |
| `monomial_integral_order` | `OrderCondition.lean:466` | `lem:monomial` | order.tex l.54–63 |
| `iteratedIntegralMonomial` | `OrderCondition.lean:420` | `lem:monomial` (sequential specialization) | order.tex l.54–63 |
| `orderCond_add` | `OrderCondition.lean:118` | `prop:order_cond_rule` (1. Addition, order.tex:80) | order.tex l.76–86 |
| `orderCond_mul` | `OrderCondition.lean:144` | `prop:order_cond_rule` (2. Multiplication, order.tex:81) | order.tex l.76–86 |
| `orderCond_deriv_iff` | `OrderCondition.lean:159` | `prop:order_cond_rule` (3. Differentiation, order.tex:82) | order.tex l.76–86 |
| `orderCond_integral_iff` | `OrderCondition.lean:199` | `prop:order_cond_rule` (4. Integration, order.tex:83) | order.tex l.76–86 |
| `orderCond_exp_iff` | `OrderCondition.lean:373` | `prop:order_cond_rule` (5. Exponentiation, order.tex:84) | order.tex l.76–86 |
| `errorOrderCond_additive_iff` | `OrderCondition.lean:614` | `thm:error_order_cond` (additive part) | order.tex l.124–130; theory.tex l.103–119 |
| `errorOrderCond_exponentiated_iff` | `OrderCondition.lean:690` | `thm:error_order_cond` (exponentiated part) | order.tex l.124–130; theory.tex l.103–119 |
| `errorOrderCond_multiplicative_iff` | `OrderCondition.lean:728` | `thm:error_order_cond` (multiplicative part) | order.tex l.124–130; theory.tex l.103–119 |
| `errorOrderCond_iff` | `OrderCondition.lean:764` | `thm:error_order_cond` (`order.tex:124`) | order.tex l.124–130; theory.tex l.103–119 |

### `theory.tex` — §3 (types, order conditions, representation) + `thm:comm_exp_conj` / `thm:trotter_error_comm_scaling`

| Lean declaration | File:line | Paper label(s) cited | Paper section/file |
|---|---|---|---|
| `expSMulConj_taylor` | `ExpSMulConj.lean:135` | `theory.tex:137-150` (single-layer Taylor) | theory.tex §3.3 (l.137–150) |
| `norm_expSMulConj_remainder_le` | `ExpSMulConj.lean:243` | `theory.tex:151-155` | theory.tex l.151–155 |
| `layerSum_le_αCommConj` | `CommutatorExpansion.lean:506` | `theory.tex:198-214` (`Σ_k Σ_q → Σ_{q₁+⋯+q_s=p}`) | theory.tex l.198–214 |
| `commutatorExpansion_conj` | `CommutatorExpansion.lean:1471` | `thm:comm_exp_conj` (`theory.tex:222-236`) | theory.tex l.221–249 |
| `commutatorRemainder` | `CommutatorExpansion.lean:74` | `thm:comm_exp_conj` (`theory.tex:229-235`) | theory.tex l.229–235 |
| `norm_commutatorRemainder_le` | `CommutatorExpansion.lean:916` | `theory.tex:238-241` (general operators) | theory.tex l.237–241 |
| `norm_commutatorRemainder_le_of_skewAdjoint` | `CommutatorExpansion.lean:1035` | `theory.tex:242-244` (anti-Hermitian) | theory.tex l.241–245 |
| `additiveKernel_eq_commutatorRemainder_sum` | `CommutatorScaling.lean:129` | `thm:trotter_error_order_cond` cancellation step (`theory.tex:258-264`) | theory.tex l.251–266 |
| `polynomial_isBigO_iff_coeffs_zero` | `OrderCondition.lean:850` | `theory.tex:258-264` (coefficient cancellation) | theory.tex l.251–266 |
| `trotter_error_bound_comm_scaling_of_skewAdjoint` | `MainTheorem.lean:542` | `eq:trotter_error_comm_scaling_bound` | theory.tex l.269–282 (`thm:trotter_error_comm_scaling`) |
| `norm_additiveKernel_le` | `MainTheorem.lean:130` | `thm:trotter_error_comm_scaling` (general branch) | theory.tex l.269–282 |
| `norm_additiveKernel_le_of_skewAdjoint` | `MainTheorem.lean:93` | `thm:trotter_error_order_cond` — **label mismatch**, see §6.1 (should be `thm:trotter_error_comm_scaling`) | theory.tex l.269–282 |
| `norm_additiveKernel_le_of_rem_bound` | `MainTheorem.lean:49` | `thm:trotter_error_order_cond` — **label mismatch**, see §6.1 | theory.tex l.269–282 |
| `norm_additiveResidual_le` | `MainTheorem.lean:375` | `thm:trotter_error_comm_scaling` (general branch) | theory.tex l.269–282 |
| `trotter_error_bound_comm_scaling` | `MainTheorem.lean:431` | `thm:trotter_error_comm_scaling` (general branch) | theory.tex l.269–282 |
| `trotter_error_comm_scaling` | `MainTheorem.lean:519` | `thm:trotter_error_comm_scaling` (general branch) | theory.tex l.269–282 |
| `trotter_error_comm_scaling_of_skewAdjoint` | `MainTheorem.lean:605` | `thm:trotter_error_comm_scaling` (anti-Hermitian) | theory.tex l.269–282 |
| `multiplicative_error_bound_comm_scaling` | `MainTheorem.lean:665` | `thm:trotter_error_comm_scaling` (general, multiplicative) | theory.tex l.269–282 |
| `multiplicative_error_comm_scaling` | `MainTheorem.lean:755` | `thm:trotter_error_comm_scaling` (general, multiplicative) | theory.tex l.269–282 |
| `multiplicative_error_bound_comm_scaling_of_skewAdjoint` | `MainTheorem.lean:797` | `thm:trotter_error_comm_scaling` (anti-Hermitian, multiplicative) | theory.tex l.269–282 |
| `multiplicative_error_comm_scaling_of_skewAdjoint` | `MainTheorem.lean:811` | `thm:trotter_error_comm_scaling` (anti-Hermitian, multiplicative) | theory.tex l.269–282 |

### `rep.tex` — Appendix C (proof of `thm:trotter_error_comm_scaling`)

| Lean declaration | File:line | Paper label(s) cited | Paper section/file |
|---|---|---|---|
| `additiveKernel_eq_sum_multiConj` | `CommutatorScaling.lean:75` | `rep.tex:5-12` | rep.tex l.5–12 |
| `additiveKernel_summand_eq_multiConj` | `CommutatorScaling.lean:53` | `rep.tex:9` | rep.tex l.9 |
| `additiveKernel_full_eq_multiConj` | `CommutatorScaling.lean:64` | `rep.tex:10` | rep.tex l.10 |
| `norm_eval_mul_commutatorRemainderTerm_le` | `MainTheorem.lean:198` | `rep.tex:50–113` | rep.tex l.50–113 |
| `norm_additiveResidual_le` | `MainTheorem.lean:375` | `rep.tex:96–113` | rep.tex l.96–113 |
| `two_mul_commScaling_div_factorial_le` | `OrderingRemoval.lean:275` | `rep.tex:96-113` | rep.tex l.96–113 |
| `multiplicativeError_eq_integral_residual` | `MainTheorem.lean:628` | `rep.tex:115-123` | rep.tex l.115–125 |
| `αCommConj_sum_le_αComm` | `OrderingRemoval.lean:224` | `rep.tex:129-139` | rep.tex l.129–139 |
| `sum_adSequence_norm_le` | `OrderingRemoval.lean:190` | `rep.tex:135–137` | rep.tex l.135–138 |
| `sum_αCommConj_orderedSummandsEval_le` | `OrderingRemoval.lean:266` | (rep.tex:129-139, via `αCommConj_sum_le_αComm`) | rep.tex l.129–139 |
| `trotter_error_comm_scaling` (+ 7 siblings) | `MainTheorem.lean:519` etc. | `thm:trotter_error_comm_scaling` | rep.tex l.141 (`\thmcomm*` restatement) |

### `prefactor.tex` — §5.1 (first/second-order tight bounds)

| Lean declaration | File:line | Paper label(s) cited | Paper section/file |
|---|---|---|---|
| `exp_mul_exp_sub_exp_add_eq_integral` | `Prefactor.lean:50` | `prefactor.tex:16` | prefactor.tex l.10–17 |
| `firstOrder_twoTerm` | `Prefactor.lean:114` | `prefactor.tex:29` | prefactor.tex l.27–30 |
| `firstOrder_bound` | `Prefactor.lean:226` | `prop:pf1_bound` — **label does not exist in the source**, see §6.1 (position = prefactor.tex:45–50) | prefactor.tex l.45–50 |
| `secondOrder_sub_eq_integral` | `Prefactor.lean:296` | `prefactor.tex:52–57` | prefactor.tex l.52–57 |
| `secondOrderKernel` | `Prefactor.lean:290` | `prefactor.tex:60` (`𝒯₂`) | prefactor.tex l.58–62 |
| `secondOrderKernel_eq_remainder` | `Prefactor.lean:433` | `prefactor.tex:63–68` | prefactor.tex l.63–68 |
| `norm_secondOrderKernel_le` | `Prefactor.lean:482` | `prefactor.tex:82–85` | prefactor.tex l.80–85 |
| `secondOrder_twoTerm` | `Prefactor.lean:509` | `prefactor.tex:82–85` | prefactor.tex l.80–85 |
| `secondOrder_bound` | `Prefactor.lean:622` | `prop:pf2_bound` — **label does not exist in the source**, see §6.1 (position = prefactor.tex:105–114) | prefactor.tex l.105–114 |

### Cross-cutting (module headers)

| Lean declaration | File:line | Paper label(s) cited | Paper section/file |
|---|---|---|---|
| *(header)* | `CommutatorExpansion.lean:14` | `arXiv:1912.08854`, `thm:comm_exp_conj`, `theory.tex:184-249` | theory.tex §3.3 |
| *(header)* | `CommutatorScaling.lean:13` | `rep.tex:5-12`, `theory.tex:251-266`, `thm:trotter_error_comm_scaling` | rep.tex, theory.tex |
| *(header)* | `ErrorTypes.lean:13` | `thm:error_type`, `papers/type.tex`, `arXiv:1912.08854` (Appendix A) | theory.tex / type.tex |
| *(header)* | `ExpSMulConj.lean:12` | `arXiv:1912.08854`, `theory.tex:137-155` | theory.tex |
| *(header)* | `MainTheorem.lean:14` | `arXiv:1912.08854`, `thm:trotter_error_comm_scaling`, `rep.tex:129–139`, `theory.tex:251–266` | theory.tex / rep.tex |
| *(header)* | `OrderCondition.lean:14` | `prop:order_cond_rule` (`order.tex:76-86`), `lem:monomial`, `thm:error_order_cond` (`order.tex:124`), `prelim.tex:150` | order.tex / prelim.tex |
| *(header)* | `OrderingRemoval.lean:11` | `arXiv:1912.08854`, `rep.tex:129-139` | rep.tex |
| *(header)* | `Prefactor.lean:14` | `papers/prefactor.tex` `sec:prefactor_pf12`, `prefactor.tex:45–50`, `105–114` | prefactor.tex §5.1 |
| *(header)* | `Suzuki.lean:12` | `eq:pf1`, `eq:pf2k`, `arXiv:1912.08854`, `prelim.tex:127,136,142` | prelim.tex §2.3 |
| *(header)* | `OneNormScaling.lean:12` | `lem:trotter_error_one_norm_scaling`, `cor:trotter_number_one_norm_scaling`, `arXiv:1912.08854` §2.3 | prelim.tex §2.3 |
| *(header)* | `ProductFormula.lean:13` | `arXiv:1912.08854` §2.3, `papers/prelim.tex` §2.1 | prelim.tex |
| *(header)* | `Calculus.lean:14` | `arXiv:1912.08854` | — |
| *(header)* | `Commutator.lean:15` | `arXiv:1912.08854` | — |
| *(header)* | `Integrals.lean:11` | `arXiv:1912.08854` | — |
| *(header)* | `ListLemmas.lean:11` | `arXiv:1912.08854` | — |
| *(header)* | `TimeOrderedExp.lean:11` | `arXiv:1912.08854` §2.2 | prelim.tex §2.2 |

---

## 5. Declarations with no paper reference in the docstring that look like named paper results ("needs manual mapping")

These are top-level **named theorems** (and a few foundational named definitions) whose docstrings
carry no paper label, but which plainly correspond to named paper results or to a labelled step of
a paper proof. They should be mapped by hand.

### 5.1 Direct correspondences that are likely intended but unlabelled

| Lean declaration | File:line | Likely paper result | Why it needs a manual decision |
|---|---|---|---|
| `norm_additiveKernel_le_of_rem_bound` | `MainTheorem.lean:49` | `thm:trotter_error_comm_scaling` (proof skeleton) | Docstring cites `thm:trotter_error_order_cond`, which is not a label in the paper (see §6.1) |
| `norm_additiveKernel_le_of_skewAdjoint` | `MainTheorem.lean:93` | `thm:trotter_error_comm_scaling` (anti-Hermitian branch) | Same mislabel |
| `norm_additiveResidual_le_of_rem_bound` | `MainTheorem.lean:329` | rep.tex l.96–113 (proof skeleton) | Docstring has no citation at all |
| `norm_eval_mul_commutatorRemainderTerm_ordered_le` | `MainTheorem.lean:275` | rep.tex l.50–113 | Docstring has no citation (its sibling `norm_eval_mul_commutatorRemainderTerm_le` does) |
| `eval_sub_exp_eq_integral_residual` | `MainTheorem.lean:416` | `thm:error_type` / rep.tex l.5 (additive form, unfactored) | Cites only `errorType_additive`, no label |
| `norm_multiplicativeError_le_norm_sub_of_skewAdjoint` | `MainTheorem.lean:776` | rep.tex l.115–125 (multiplicative ≈ additive under skew-adjointness) | No citation |
| `isBigO_norm_iff_iteratedDeriv_eq_zero` | `Calculus.lean:323` | CS19 Supplementary Lemma 1 = `lem:order_cond_deriv` (order.tex l.11–24) | Cites `CS19` by author, not by paper label |
| `taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below` | `Calculus.lean:304` | order.tex l.26–32 (L'Hôpital step of `lem:order_cond_deriv`) | Cites `CS19` only |
| `taylor_integral_remainder_iteratedDeriv_zero` | `Calculus.lean:449` | prelim.tex l.168–172 (Taylor with integral remainder) | No citation |
| `taylor_integral_remainder_iteratedDeriv_zero_paper` | `Calculus.lean:475` | prelim.tex l.170–171 (paper's substituted form) | Docstring says "the paper's substituted form" without a label |
| `taylor_paper_scalar_eq` | `Calculus.lean:438` | prelim.tex l.170–171 | "the paper's substituted form", no label |
| `contDiff_timeOrderedExp_of_contDiff` | `OrderCondition.lean:233` | prelim.tex l.40 (continuity/smoothness standing assumption) | No citation |
| `iteratedDeriv_timeOrderedExp_succ` | `OrderCondition.lean:259` | order.tex l.90–124 (Faulhaber/Leibniz recursion in the exponentiation rule proof) | No citation |
| `timeOrderedExp_iteratedDeriv_eq_iff` | `OrderCondition.lean:292` | order.tex l.88–123 (core of the exponentiation rule proof) | No citation |
| `contDiff_additiveKernel`, `contDiff_exponentiatedError` | `OrderCondition.lean:531`, `559` | prelim.tex l.40 / theory.tex l.105 ("infinitely differentiable") | Standing hypothesis, no citation |
| `sum_αCommConj_suffix_add_ordered_le` | `ProductFormula.lean:764` | rep.tex l.25–34 (the `Σ_{(υ,γ)} α_comm ≤ 2Υ Σ_γ α_comm` step) | No citation |
| `sum_norm_fullGenerators_eq`, `sum_norm_orderedGenerators_le`, `sum_norm_suffixGenerators_le`, `sum_norm_prod` | `ProductFormula.lean:547,572,589,272` | rep.tex l.29–32 (norm bookkeeping `Σ_{(υ,γ)}‖H‖ = Υ Σ_γ ‖H‖`) | No citation |
| `αCommConj_suffixGenerators_le`, `αCommConj_orderedGenerators_le`, `αCommConj_fullGenerators_eq`, `sum_αCommConj_perm` | `ProductFormula.lean:693,678,666,650` | rep.tex l.25–32 (coefficient dropping / suffix extension / permutation reindexing) | No citation |
| `αCommConj_nonneg`, `αCommConj_sum_le`, `αCommConj_smul_le`, `αCommConj_smul_fun_le`, `αCommConj_cast`, `αCommConj_succ_le`, `αCommConj_natAdd_le` | `Commutator.lean:616,490,453,437,464,549,586` | theory.tex l.217–219 / rep.tex l.130–133 (elementary properties of `α_comm`) | No citation |
| `norm_commutator_le`, `norm_adPow_le`, `norm_adSequence_le` | `Commutator.lean:104,113,126` | rep.tex l.99–106 (`‖ad^{q}…(B)‖` estimates) | No citation |
| `multinomial_le_factorial` | `Commutator.lean:264` | rep.tex l.133–134 (`binom ≤ p!`) | No citation |
| `fiber_card_le`, `orderedLayers_stageOf_injective`, `adSequence_orderedSummands_eq_nestedComm` | `OrderingRemoval.lean:151,123,86` | rep.tex l.138–139 (`Υ^p` stage-placement counting) | No citation |
| `exp_mul_exp_sub_exp_add_eq_integral` | `Prefactor.lean:50` | prefactor.tex l.11–17 | Docstring cites `prefactor.tex:16`, so *is* mapped (listed for contrast) |
| `norm_lieTrotter_le_one_of_skew`, `norm_suzuki2_le_one_of_skew` | `Prefactor.lean:209,598` | prefactor.tex l.34–40 (unitarity of the telescope) | No citation |
| `expSMulConj_sub_eq_integral` | `ExpSMulConj.lean:92` | theory.tex l.140–145 / prefactor.tex l.20 (FTC for the conjugation) | No citation |
| `expSMulConj_hasDerivAt` | `ExpSMulConj.lean:74` | theory.tex l.140–145 | No citation |
| `norm_expSMulConj_le` | `ExpSMulConj.lean:202` | theory.tex l.151–155 (pre-skew norm bound) | No citation |
| `norm_expSMulConj_le_of_skewAdjoint` | `ExpSMulConj.lean:226` | theory.tex l.220 ("when these operators are anti-Hermitian …") | No citation |
| `norm_conj_smul_integral_le`, `norm_absorbed_conj_smul_integral_le`, `norm_exp_mul_expSMulConj_le`, `norm_conj_smul_integral_le_of_norm_conj_le`, `norm_integral_smul_conj_le` | `CommutatorExpansion.lean:169,241,197,136,91` | theory.tex l.198–215 (the beta-integral estimate) | No citation |
| `norm_commutatorRemainderTerm_le`, `norm_commutatorRemainderTerm_le_of_skewAdjoint`, `norm_commutatorRemainder_le_of_term_bound`, `norm_mul_commutatorRemainder_le_of_term_bound` | `CommutatorExpansion.lean:756,970,822,870` | theory.tex l.198–244 | No citation |
| `norm_ofFn_drop_prod_le_one_of_skewAdjoint` | `CommutatorExpansion.lean:926` | theory.tex l.220–245 (skew branch) | No citation |
| `norm_eval_le`, `norm_eval_le_one_of_skew` | `ProductFormula.lean:620`, `OneNormScaling.lean:588` | prelim.tex l.184 / rep.tex l.101 | No citation |
| `multiplicativeError` (definition) | `ErrorTypes.lean:442` | theory.tex l.74–80 | Docstring cites `type.tex:72` ⇒ mapped |
| `isUnit_eval`, `inverse_isBigO_one_of_continuous_unit`, `isBigO_norm_one_of_continuous`, `orderCond_mul_left`, `orderCond_mul_right` | `OrderCondition.lean:502,514,483,488,495` | order.tex l.80–81 (`O(1)` bookkeeping) | No citation |
| `errorType_*`-adjacent `eval_zero` | `ProductFormula.lean:121` | theory.tex l.55 / type.tex (`𝒮(0) = I`) | No citation |
| `norm_additiveKernel_le_of_rem_bound`/`norm_additiveResidual_le_of_rem_bound` | (see above) | — | — |

### 5.2 Whole files with no per-declaration paper references

* `ListLemmas.lean` (16 declarations) — pure `List`/`Fin` infrastructure.
* `Integrals.lean` (7 declarations) — generic interval-integral identities.
* `Commutator.lean` (49 declarations) — commutator infrastructure; only `αComm`/`αCommConj`
  mention "the paper's" informally.
* `Calculus.lean` (41 declarations) — generic calculus; only the three `prelim.tex`-cited items
  are labelled.

---

## 6. Places where the formalization differs from (or goes beyond) the paper

### 6.1 Docstring labels that do not exist in the paper source

1. **`thm:trotter_error_order_cond`** — cited by `MainTheorem.lean:45` and `MainTheorem.lean:91`.
   The paper's label is **`thm:trotter_error_comm_scaling`** (theory.tex l.270). There is a
   *different* theorem labelled `thm:error_order_cond` (theory.tex l.104). Both Lean docstrings
   describe commutator-scaling content (α_comm, `|τ|^p/p!`), not the order-condition theorem, so
   these are almost certainly intended as `thm:trotter_error_comm_scaling`. **Recommend fixing.**
2. **`prop:pf1_bound`** — cited by `Prefactor.lean:224`. The paper's first-order proposition
   (prefactor.tex l.45–50) is **unlabelled** in the source.
3. **`prop:pf2_bound`** — cited by `Prefactor.lean:620`. The paper's second-order proposition
   (prefactor.tex l.105–114) is likewise **unlabelled**.
4. **`eq:trotter_error_comm_scaling_bound`** — cited by `MainTheorem.lean:540`. No such `\label`
   exists; the corresponding display is the unlabelled equation at theory.tex l.273–276 inside
   `thm:trotter_error_comm_scaling`.

### 6.2 Stated-by-the-author differences

1. **Operator convention: Hermitian Hamiltonians vs. anti-Hermitian generators.**
   `Prefactor.lean:14-33` (module header) states it explicitly:
   > "The paper states these in terms of a Hermitian `H = Σ_γ H_γ` and the real-time evolution
   > `e^{-itH}`. Here, following the anti-Hermitian-generator convention of the surrounding theory,
   > we work with anti-Hermitian generators `K_γ` (`star (K γ) = -(K γ)`) and the evolution
   > `exp (t • Σ_γ K γ)`; the paper's `H_γ ↔ K_γ = -i H_γ`, `e^{-itH_γ} ↔ exp (t • K_γ)`, and
   > `[H_γ, H_γ'] ↔ ⁅K_γ, K_γ'⁆` (equal norm), so the constants `t²/2`, `t³/12`, `t³/24` are unchanged."
   This makes every `Prefactor.lean` proposition/equation reference a *renaming* of the paper's
   Hermitian statement, not a literal transcription.
2. **`timeOrderedExp_const` is stated for an arbitrary interval, not `0 → t`.**
   `TimeOrderedExp.lean:514`:
   > "`prelim.tex:41` (the paper states the `0 → t` case `e^{tH}`; this is its arbitrary-interval form)"
3. **`lem:monomial` is formalized in a sequential specialization.**
   `OrderCondition.lean:415-419`:
   > "This is the sequential specialization of the paper's `lem:monomial`; the general form (each
   > inner upper limit an arbitrary earlier variable) has the same order `t^{Σp + Γ}` by the same
   > induction."
   The paper's `lem:monomial` (order.tex l.54–63) allows `τ_{<γ} ∈ {τ, τ_1, …, τ_{γ-1}}`
   arbitrarily; `iteratedIntegralMonomial` always uses the immediately preceding variable.
4. **Norm hypotheses are weakened relative to the paper's matrix setting.**
   `norm_dysonTerm_le_abs` (`TimeOrderedExp.lean:195-196`) is documented as
   > "valid without `NormOneClass`"
   and `summable_dysonTerm_abs` (`:225`) as
   > "without `NormOneClass`".
   Likewise `norm_eval_le`/`norm_additiveKernel_le` etc. require the explicit hypothesis
   `[NormOneClass 𝔸]` (i.e. `‖1‖ = 1`), which is automatic for the paper's complex matrices but
   must be assumed in a general `NormedRing`. `timeOrderedExp_norm_le` carries `[NormOneClass 𝔸]`
   even though the paper's `lem:time_ordered_norm_bound` item 1 has no such side condition.
5. **Order-0 (`p = 0`) boundary cases.**
   `isBigO_norm_iff_iteratedDeriv_lt_eq_zero` (`OrderCondition.lean:90`) notes
   > "For `p = 0` both sides hold automatically."
   `suzuki 0` is explicitly called a **junk identity** (`Suzuki.lean:74`, `:336`), and
   `suzuki_eq_eval` is only stated for `1 ≤ k`; `suzukiData 0 Γ := lieTrotterData Γ`, which does
   *not* evaluate to `suzuki 0`'s junk value.
6. **Two-sidedness of the time-ordered exponential is a theorem, not a definition.**
   `TimeOrderedExp.lean:65-68` on `timeOrderedExp`:
   > "for `t₂ < t₁` it is the inverse evolution (**a theorem, not built into the definition**)."
   The paper instead *defines* `expT(∫_{t₂}^{t₁})` as the inverse of `expT(∫_{t₁}^{t₂})`
   (prelim.tex l.43).
7. **Oriented interval integrals replace the paper's `0 ≤ τ ≤ t` side conditions.**
   `TimeOrderedExp.lean:58-60`:
   > "The interval integral is oriented, so this is defined for every `t : ℝ` (not only `t ≥ t₁`)."
   Hence many lemmas (e.g. `timeOrderedExp_norm_le`, `timeOrderedExp_dist_le`,
   `timeOrderedExp_eq_integral`) are stated for all `t₁ t₂ : ℝ`, whereas the paper assumes
   `0 ≤ τ ≤ t` (prelim.tex l.40).
8. **`IsBigO` norm-wraps the right-hand side, so `τ^p` behaves as `|τ|^p`.**
   `OrderCondition.lean:17-20`:
   > "the `IsBigO` relation norm-wraps its right-hand side, so `τ^p` acts as `|τ|^p`."
   The paper writes `O(τ^p)` with `|τ|^p` intended (order.tex l.5). This also means the
   formalization of `O(τ^p)` is a one-sided (two-sided-neighbourhood) limit at 0, matching
   order.tex l.5, but the paper's explicit-constant form `‖F(τ)‖ ≤ c|τ|^p for |τ| ≤ t₀` is
   replaced by `IsBigO` at `𝓝 0`.
9. **The 1-norm and commutator-scaling asymptotic statements use `=O[𝓝 0]`/`=O[atTop]`.**
   `trotter_error_one_norm_scaling` etc. state `=O[𝓝 (0:ℝ)]`, and `trotter_error_comm_scaling`
   states `=O[Filter.atTop]` — i.e. the paper's `\cO{·}` (large-`t`, prelim.tex l.28) is
   formalized as `atTop`, and the paper's `\OO{·}` (small-`τ`) as `𝓝 0`. Also note the
   `Lemma (Trotter error with 1-norm scaling)` in prelim.tex writes `\cO{}` (large-`t` convention)
   for a *small-`t`* statement; the Lean version uses `𝓝 0` there.
10. **Exponent prefactor: the formalization uses the improved `2`, not the paper's displayed `4`.**
    rep.tex l.36–44 displays `exp(4tΥΣ‖H_γ‖)` for the "final integration" bound and then l.44–50
    announces the improvement to prefactor `2`; `trotter_error_bound_comm_scaling`
    (`MainTheorem.lean:436`) and `trotter_error_bound_comm_scaling_of_skewAdjoint` use the
    `2 t Υ Σ‖H_γ‖` form matching `thm:trotter_error_comm_scaling` (theory.tex l.274–275).
    This should be recorded as matching the *improved* statement, not rep.tex l.36–44.
11. **The `IsOrderOf` predicate is a definition, not a paper object.**
    `OrderCondition.lean:61-62` defines "`P` is a `p`-th order formula on summands `H` if
    `‖𝒮(t) − e^{tH}‖ = O(t^{p+1})` as `t → 0` (`prelim.tex:150`)". The paper states this as a
    property of `𝒮` in running text (prelim.tex l.148–151) rather than as a named definition.
12. **`cat:pf` label convention.** `ProductFormula.lean:59-62` cites `eq:pf`; the label is at
    prelim.tex l.144, attached to the `\begin{equation}` opened at l.143.
13. **`eq:pf1`/`eq:pf2k` are cited by *definition* docstrings, not by *theorem* docstrings.**
    `lieTrotterData`, `suzukiU`, `suzuki`, `suzuki2Data`, `suzukiStages`, `suzukiData` all cite
    `eq:pf1`/`eq:pf2k`; these are the paper's *displayed definitions*, so the mapping is
    definition-to-definition, not statement-to-statement.
14. **Left/right product convention is handled by a reversed list.**
    `ProductFormula.lean:20-25`:
    > "Following the paper's convention (`papers/prelim.tex` §2.1), the product `∏_{γ=1}^{Γ} A_γ`
    > denotes `A_Γ ⋯ A_2 A_1`, i.e. increasing indices from right to left; we implement this with a
    > reversed `List.finRange`. Since the factors `e^{t a H}` do not commute, the product is taken
    > with `List.prod` (ordered) rather than `prod` (commutative) or `noncommProd` (which requires
    > pairwise commutativity)."
    Correspondingly the paper's 1-based indices become 0-based `Fin Γ`, and `A₁`/`A_s` of
    `thm:comm_exp_conj` become `A ⟨0⟩`/`A ⟨s-1⟩` (see `CommutatorExpansion.lean:50-52` and the
    0-based/1-based remark in `commutatorRemainder`'s docstring, `CommutatorExpansion.lean:69-73`).
15. **`cor:trotter_number_one_norm_scaling` is restated as an `O(r^{-p})` asymptotic.**
    `OneNormScaling.lean:619-621`:
    > "for anti-Hermitian summands, the `r`-step Trotter error decays as `O(r^{-p})` as `r → ∞`;
    > equivalently, `r = O(ε^{-1/p})` steps suffice for accuracy `ε`."
    The paper's corollary (prelim.tex l.213–219) is phrased as "`‖𝒮^r(t/r) − e^{tH}‖ = O(ε)`
    provided `r = O((Σ‖H_γ‖t)^{1+1/p}/ε^{1/p})`"; the `ε`-accuracy form is not formalized, only
    the equivalent `r^{-p}` decay.
16. **Private helper declarations are excluded from the formal statement.** The six `private`
    lemmas (`concat_generator_castAdd`, `concat_generator_natAdd`, `concat_evalFactor_castAdd`,
    `concat_evalFactor_natAdd` in `ProductFormula.lean`; `lie_smul_half_mul_coe`,
    `lie_mul_neg_half_coe` in `Prefactor.lean`) have no paper counterpart.
17. **`OrderCondition.lean:36-37` standing hypothesis.**
    > "All rules are stated for smooth generators (the paper's standing hypothesis 'infinitely
    > differentiable', order.tex:78)."
    `orderCond_add`/`orderCond_mul` in `OrderCondition.lean` carry no `ContDiff` hypothesis, but
    `orderCond_deriv_iff`, `orderCond_integral_iff`, `orderCond_exp_iff` do (`ContDiff ℝ ∞`).
    The paper's `prop:order_cond_rule` assumes infinite differentiability globally.

### 6.3 Labels cited that resolve correctly (for reassurance)

`eq:int_eq`, `lem:td_Duhamel`, `lem:interaction_picture`, `lem:fte`,
`lem:time_ordered_norm_bound`, `cor:time_ordered_distance_bound`, `eq:pf1`, `eq:pf2k`, `eq:pf`,
`thm:error_type`, `thm:error_order_cond`, `lem:order_cond_deriv`, `lem:monomial`,
`prop:order_cond_rule`, `thm:comm_exp_conj`, `thm:trotter_error_comm_scaling`,
`lem:trotter_error_one_norm_scaling`, `cor:trotter_number_one_norm_scaling`,
`eq:trotter_error_one_norm_scaling_bound` — all exist in the paper source and all but the last
are `\label`s (the last is an equation label at prelim.tex l.191).

---

## 7. Paper results in scope NOT formalized (gap list)

| Paper label | File:line | Why it matters |
|---|---|---|
| `cor:trotter_number_comm_scaling` | theory.tex l.283–289 | The commutator-scaling Trotter-number corollary: no Lean declaration mentions it |
| `eq:unitary_conjugation` | theory.tex l.132 | Intermediate display in the conjugation argument; no Lean name |
| `prop:pf4_bound_2term`, `prop:pf4_bound_3term` | pf2k.tex l.143, 158 | Fourth-order Suzuki bounds ("small prefactors", §5.2) — no `pf2k.tex` reference anywhere in the Lean tree |
| `lem:norm_delta_H`, `lem:norm_nested_comm` | local-observable.tex l.16, 59 | Local-observable error bounds — not in scope of this file set |
| `lem:sum_scaling`, `prop:tuv_base`, `lem:commutation_rule`, `prop:tuv_induction`, `thm:pf-electron` | electron.tex | Electronic-structure applications — out of scope |
| `thm:pf-cluster`, `thm:pf-local`, `lem:power-law-sum`, `thm:pf-power-law`, `thm:pf-weak-power-law`, `thm:pf-quasi-local`, `prop:pf-local-obs`, `lem:relative`, `lem:sum_scaling` | cluster.tex, local.tex, power-law.tex, app.tex | Applications — out of scope |
| `eq:one_norm_error_imag`, `eq:one_norm_error_real` | prelim.tex l.158, 163 | The two displayed specializations inside `lem:trotter_error_one_norm_scaling`; the Lean general/skew theorems cover them but do not cite the equation labels |
| `sec:prefactor_pf2k` | prefactor.tex l.118 | §5.2 (higher-order/numerical) — no Lean counterpart |
