/-
Prove2Me solution for `TrotterError.norm_commutatorRemainder_le`.

Generated from the FQFP TrotterError development by skeleton subtraction:
every declaration reachable from the target is re-emitted, module-system
machinery removed, in module-dependency order.

Source: https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects/tree/d6bfac12d15bc59fcc5f90206ac3312da602eb3d
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Multinomial

-- ===== from FQFP.TrotterError.Calculus =====
/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/



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


namespace TrotterError

open NormedSpace
open Asymptotics
open Finset
open scoped Topology BigOperators ContDiff algebraMap

/-- The `q`-th iterated derivative of `u ↦ exp (u • A)` is `u ↦ A^q * exp (u • A)`. -/
theorem iteratedDeriv_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (q : ℕ) :
    iteratedDeriv q (fun u : ℝ => exp (u • A)) = fun u : ℝ => A ^ q * exp (u • A) := by
  induction q with
  | zero =>
      simp [iteratedDeriv_zero]
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [((hasDerivAt_exp_smul_const' A t).const_mul (A ^ q)).deriv]
      simp [pow_succ, mul_assoc]

/-! ### Multinomial Leibniz expansion for finite products -/

/-- `ContDiffAt` for the pointwise product of a finite list of functions. -/
lemma contDiffAt_list_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ) (t : ℝ)
    (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) :
    ContDiffAt ℝ n (fun t : ℝ => (l.map (fun i => f i t)).prod) t := by
  induction l with
  | nil => simpa using (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℝ => (1 : 𝔸)) t)
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ContDiffAt.mul (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

/-- A natural-number cast factors through the real scalar action:
`(a : 𝔸) * x * ((b : ℝ) • y) = ((a * b : ℕ) : ℝ) • (x * y)`. -/
lemma natCast_mul_smul_eq {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (a b : ℕ) (x y : 𝔸) :
    (a : 𝔸) * x * ((b : ℝ) • y) = ((a * b : ℕ) : ℝ) • (x * y) := by
  rw [(algebraMap.coe_natCast (R := ℝ) (A := 𝔸) a).symm, ← Algebra.smul_def (a : ℝ) x,
    smul_mul_assoc, mul_smul_comm, smul_smul, ← Nat.cast_mul]

/-- The multinomial coefficient is invariant under renaming the index type by an injective map. -/
lemma multinomial_image {α β : Type*} [DecidableEq β] (s : Finset α) (e : α → β)
    (he : Set.InjOn e s) (f : β → ℕ) :
    Nat.multinomial (s.image e) f = Nat.multinomial s (f ∘ e) := by
  simp [Nat.multinomial, Finset.sum_image he, Finset.prod_image he, Function.comp_apply]

/-- The multinomial recursion for `Fin (m + 1)`, splitting off the index `0`. -/
lemma multinomial_fin_succ {m : ℕ} (k : ℕ) (q : Fin m → ℕ) :
    Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) =
      (k + ∑ i : Fin m, q i).choose k * Nat.multinomial (Finset.univ : Finset (Fin m)) q := by
  have huniv : (Finset.univ : Finset (Fin (m + 1))) =
      insert (0 : Fin (m + 1)) (Finset.univ.image (Fin.succ : Fin m → Fin (m + 1))) := by
    ext i
    simp [Fin.image_succ_univ]
  rw [huniv, Nat.multinomial_insert (show (0 : Fin (m + 1)) ∉
      Finset.univ.image (Fin.succ : Fin m → Fin (m + 1)) by
    simp [Fin.image_succ_univ])]
  simp only [Fin.cons_zero]
  have hinj : Set.InjOn (Fin.succ : Fin m → Fin (m + 1))
      (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    intro a _ b _ h
    exact Fin.succ_injective m h
  rw [Finset.sum_image hinj, multinomial_image (Finset.univ : Finset (Fin m))
    (Fin.succ : Fin m → Fin (m + 1)) hinj (Fin.cons k q)]
  have hsum :
      (∑ x : Fin m, ((Fin.cons k q : Fin (m + 1) → ℕ) (Fin.succ x))) = ∑ x : Fin m, q x := rfl
  have hcomp : ((Fin.cons k q : Fin (m + 1) → ℕ) ∘ Fin.succ) = q := rfl
  rw [hsum, hcomp]

/-- The antidiagonal of `Fin (m + 1)` fibers over that of `Fin m` by the value at `0`. -/
lemma sum_finAntidiagonal_succ {𝔸 : Type*} [AddCommMonoid 𝔸] (m n : ℕ)
    (G : (Fin (m + 1) → ℕ) → 𝔸) :
    (∑ q' ∈ Finset.finAntidiagonal (m + 1) n, G q') =
      ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k), G (Fin.cons k q) := by
  rw [Finset.sum_sigma']
  refine (Finset.sum_bij (fun x _ => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_finAntidiagonal, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hx' : x.1 ∈ Finset.range (n + 1) ∧ x.2 ∈ Finset.finAntidiagonal m (n - x.1) :=
      Finset.mem_sigma.mp hx
    have hle : x.1 ≤ n := by simpa using Finset.mem_range.mp hx'.1
    have hsum : (∑ i : Fin m, x.2 i) = n - x.1 := by
      simpa using Finset.mem_finAntidiagonal.mp hx'.2
    rw [hsum, Nat.add_sub_of_le hle]
  · intro x₁ _ x₂ _ h
    obtain ⟨h1, h2⟩ := Fin.cons_inj.mp h
    exact Sigma.ext h1 (heq_of_eq h2)
  · intro q' hq'
    have hsum : (∑ i : Fin (m + 1), q' i) = n := Finset.mem_finAntidiagonal.mp hq'
    have hsplit : q' 0 + (∑ i : Fin m, q' (Fin.succ i)) = n := by
      simpa [Fin.sum_univ_succ] using hsum
    refine ⟨⟨q' 0, Fin.tail q'⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_range]
        have hle : q' 0 ≤ n := by
          rw [← hsplit]
          exact Nat.le_add_right _ _
        exact Nat.lt_succ_of_le hle
      · rw [Finset.mem_finAntidiagonal]
        have htail : (∑ i : Fin m, q' (Fin.succ i)) = n - q' 0 := by
          rw [← hsplit, Nat.add_sub_cancel_left]
        simpa [Fin.tail] using htail
    · exact Fin.cons_self_tail q'
  · intro x _
    rfl

/-- The `Fin m` antidiagonal coincides with `piAntidiag` on `univ`. -/
lemma finAntidiagonal_eq_piAntidiag_univ (m n : ℕ) :
    Finset.finAntidiagonal m n = Finset.piAntidiag (Finset.univ : Finset (Fin m)) n := by
  ext f
  simp [Finset.mem_finAntidiagonal, Finset.mem_piAntidiag]

/-- The antidiagonal over the empty index type. -/
lemma finAntidiagonal_zero (n : ℕ) : Finset.finAntidiagonal 0 n = if n = 0 then {0} else ∅ := by
  ext f
  rw [Finset.mem_finAntidiagonal]
  by_cases h : n = 0
  · subst n
    simp [funext_iff]
  · simp only [if_neg h, Finset.notMem_empty, iff_false, Fin.sum_univ_zero]
    intro hsum
    exact h hsum.symm

/-- The `n`-th iterated derivative of a finite product of functions is the multinomial Leibniz
expansion, indexed by `Finset.finAntidiagonal`. -/
theorem iteratedDeriv_ofFn_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {m : ℕ} (f : Fin m → ℝ → 𝔸) (n : ℕ) (t : ℝ)
    (hf : ∀ i, ContDiffAt ℝ n (f i) t) :
    iteratedDeriv n (fun t : ℝ => (List.ofFn (fun i : Fin m => f i t)).prod) t =
      ∑ q ∈ Finset.finAntidiagonal m n,
        (Nat.multinomial (Finset.univ : Finset (Fin m)) q : ℝ) •
          (List.ofFn (fun i : Fin m => iteratedDeriv (q i) (f i) t)).prod := by
  induction m generalizing n t with
  | zero =>
      cases n with
      | zero => simp [iteratedDeriv_zero, finAntidiagonal_zero]
      | succ n => simp [iteratedDeriv_const, finAntidiagonal_zero]
  | succ m ih =>
      let g : Fin m → ℝ → 𝔸 := fun i => f i.succ
      calc
        iteratedDeriv n (fun t : ℝ => (List.ofFn (fun i : Fin (m + 1) => f i t)).prod) t
            = iteratedDeriv n
                ((f 0) * (fun t : ℝ => (List.ofFn (fun i : Fin m => g i t)).prod)) t := by
                congr 1
                funext t
                rw [List.ofFn_succ]
                rfl
        _ = ∑ k ∈ Finset.range (n + 1), n.choose k * iteratedDeriv k (f 0) t *
              iteratedDeriv (n - k) (fun t : ℝ => (List.ofFn (fun i : Fin m => g i t)).prod) t := by
                rw [iteratedDeriv_mul (hf 0) (by
                  simpa [List.ofFn_eq_map] using
                    contDiffAt_list_prod (List.finRange m) g n t (fun i _ => hf i.succ))]
        _ = ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k),
              n.choose k * iteratedDeriv k (f 0) t *
                ((Nat.multinomial (Finset.univ : Finset (Fin m)) q : ℝ) •
                  (List.ofFn (fun i : Fin m => iteratedDeriv (q i) (g i) t)).prod) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [ih g (n - k) t (fun i => (hf i.succ).of_le (mod_cast Nat.sub_le n k)),
                  Finset.mul_sum]
        _ = ∑ k ∈ Finset.range (n + 1), ∑ q ∈ Finset.finAntidiagonal m (n - k),
              (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) : ℝ) •
                (List.ofFn (fun i : Fin (m + 1) =>
                  iteratedDeriv (((Fin.cons k q : Fin (m + 1) → ℕ) i)) (f i) t)).prod := by
                apply Finset.sum_congr rfl
                intro k hk
                apply Finset.sum_congr rfl
                intro q hq
                have hle : k ≤ n := by simpa using Finset.mem_range.mp hk
                have hqsum : (∑ i : Fin m, q i) = n - k := by
                  simpa using Finset.mem_finAntidiagonal.mp hq
                rw [natCast_mul_smul_eq (n.choose k)
                  (Nat.multinomial (Finset.univ : Finset (Fin m)) q)
                  (iteratedDeriv k (f 0) t)
                  ((List.ofFn (fun i : Fin m => iteratedDeriv (q i) (g i) t)).prod)]
                have hrec : Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) (Fin.cons k q) =
                    n.choose k * Nat.multinomial (Finset.univ : Finset (Fin m)) q := by
                  rw [multinomial_fin_succ, hqsum, Nat.add_sub_of_le hle]
                rw [hrec]
                congr 1
                rw [List.ofFn_succ]
                simp [g, Fin.cons_zero, Fin.cons_succ]
        _ = ∑ q' ∈ Finset.finAntidiagonal (m + 1) n,
              (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) q' : ℝ) •
                (List.ofFn (fun i : Fin (m + 1) => iteratedDeriv (q' i) (f i) t)).prod := by
                rw [sum_finAntidiagonal_succ m n (fun q' =>
                  (Nat.multinomial (Finset.univ : Finset (Fin (m + 1))) q' : ℝ) •
                    (List.ofFn (fun i : Fin (m + 1) => iteratedDeriv (q' i) (f i) t)).prod)]

/-- The `n`-th iterated derivative of the product of a family indexed by an arbitrary list `l`
is the multinomial Leibniz expansion, with multi-indices indexed by the positions `Fin l.length`. -/
theorem iteratedDeriv_list_prod_general {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ) (t : ℝ)
    (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) :
    iteratedDeriv n (fun t : ℝ => (l.map (fun i => f i t)).prod) t =
      ∑ q ∈ Finset.piAntidiag (Finset.univ : Finset (Fin l.length)) n,
        (Nat.multinomial (Finset.univ : Finset (Fin l.length)) q : ℝ) •
          (List.ofFn (fun j : Fin l.length => iteratedDeriv (q j) (f (l.get j)) t)).prod := by
  have hprod : (fun t : ℝ => (List.ofFn (fun j : Fin l.length => f (l.get j) t)).prod) =
      fun t : ℝ => (l.map (fun i => f i t)).prod := by
    funext t
    congr 1
    simpa using (List.ofFn_getElem_eq_map l (fun i : ι => f i t))
  rw [← hprod]
  simpa [finAntidiagonal_eq_piAntidiag_univ] using
    iteratedDeriv_ofFn_prod (fun j : Fin l.length => f (l.get j)) n t
      (fun j => hf (l.get j) (List.get_mem l j))

/-- Reindexing a sum over `Finset.piAntidiag univ` by an equivalence of the index type. -/
lemma sum_piAntidiag_univ_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (e : α ≃ β) (n : ℕ) {𝕄 : Type*} [AddCommMonoid 𝕄] (G : (α → ℕ) → 𝕄) :
    (∑ q ∈ Finset.piAntidiag (Finset.univ : Finset α) n, G q) =
      ∑ q' ∈ Finset.piAntidiag (Finset.univ : Finset β) n, G (q' ∘ e) := by
  refine Finset.sum_bij (fun q _ => q ∘ e.symm) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_piAntidiag] at hq ⊢
    constructor
    · exact (Equiv.sum_comp e.symm q).trans hq.1
    · intro b hb
      simp
  · intro q₁ hq₁ q₂ hq₂ h
    funext x
    have hx : x = e.symm (e x) := (e.symm_apply_apply x).symm
    rw [hx]
    exact congr_fun h (e x)
  · intro q' hq'
    refine ⟨q' ∘ e, ?_, ?_⟩
    · rw [Finset.mem_piAntidiag] at hq' ⊢
      constructor
      · exact (Equiv.sum_comp e q').trans hq'.1
      · intro a ha; simp
    · ext b; simp
  · intro q hq
    apply congrArg G
    funext x
    simp

/-- The multinomial coefficient over `univ` is invariant under reindexing by an equivalence. -/
lemma multinomial_univ_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (q : β → ℕ) :
    Nat.multinomial (Finset.univ : Finset β) q =
      Nat.multinomial (Finset.univ : Finset α) (q ∘ e) := by
  classical
  rw [← Finset.image_univ_equiv e]
  exact multinomial_image (Finset.univ : Finset α) e (fun a _ b _ h ↦ e.injective h) q

/-- `u ↦ exp (u • A)` is `C^m` at every point. -/
lemma contDiffAt_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) (m : ℕ) (t : ℝ) :
    ContDiffAt ℝ m (fun u : ℝ => exp (u • A)) t :=
  (NormedSpace.exp_analytic (t • A)).contDiffAt.comp t
    (ContDiffAt.smul (f := fun u : ℝ => u) (g := fun _ : ℝ => A) contDiffAt_id contDiffAt_const)

/-- `u ↦ exp (u • A)` is smooth. -/
lemma contDiff_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : 𝔸) :
    ContDiff ℝ ∞ (fun t : ℝ => exp (t • A)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact ((NormedSpace.exp_analytic (t • A)).contDiffAt).comp t
    (ContDiffAt.smul (f := fun u : ℝ => u) (g := fun _ : ℝ => A) contDiffAt_id contDiffAt_const)

/-! ### CS19 Supplementary Lemma 1: big-O scaling iff derivatives vanish at 0 -/

/-- If the first `n` iterated derivatives of `F` at `x₀` vanish, then the `n`-th Taylor
polynomial of `F` at `x₀` is just the leading term `(x - x₀)^n • ((n! : ℝ)⁻¹ • F⁽ⁿ⁾(x₀))`. -/
lemma taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (n : ℕ) {x₀ x : ℝ}
    (h0 : ∀ k < n, iteratedDeriv k F x₀ = 0) :
    taylorWithinEval F n Set.univ x₀ x =
      (x - x₀) ^ n • ((Nat.factorial n : ℝ)⁻¹ • iteratedDeriv n F x₀) := by
  rw [taylor_within_apply, Finset.sum_range_succ]
  have hsum : (∑ k ∈ Finset.range n, ((Nat.factorial k : ℝ)⁻¹ * (x - x₀) ^ k) •
      iteratedDerivWithin k F Set.univ x₀) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    rw [iteratedDerivWithin_univ, h0 k hkn, smul_zero]
  rw [hsum, zero_add]
  simp only [iteratedDerivWithin_univ]
  rw [mul_smul, smul_comm]

/-- A smooth function `F` satisfies `‖F t‖ = O(t^(p + 1))` as `t → 0` if and only if its
first `p` iterated derivatives vanish at `0` (CS19, Supplementary Lemma 1). -/
theorem isBigO_norm_iff_iteratedDeriv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun t : ℝ => ‖F t‖) =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1)) ↔
      ∀ j : ℕ, j ≤ p → iteratedDeriv j F 0 = 0 := by
  classical
  constructor
  · intro hbig; by_contra hnot
    have hex : ∃ j : ℕ, j ≤ p ∧ iteratedDeriv j F 0 ≠ 0 := by
      by_contra h; apply hnot
      intro j hj; by_contra hjz
      exact h ⟨j, hj, hjz⟩
    rcases hex with ⟨j₀, hj₀_le, hj₀_nz⟩
    have hex' : ∃ j : ℕ, iteratedDeriv j F 0 ≠ 0 := ⟨j₀, hj₀_nz⟩
    let j := Nat.find hex'
    have hj_nz : iteratedDeriv j F 0 ≠ 0 := Nat.find_spec hex'
    have hj_min : ∀ k < j, iteratedDeriv k F 0 = 0 := by
      intro k hk
      by_contra hk'
      exact (Nat.find_min hex' hk) hk'
    have hj_le : j ≤ p := le_trans (Nat.find_min' hex' hj₀_nz) hj₀_le
    have hbigF : F =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1)) := isBigO_norm_left.mp hbig
    rw [isBigO_iff] at hbigF
    rcases hbigF with ⟨C₁, hbigF⟩
    have hbigF' : ∀ᶠ t in 𝓝 (0 : ℝ), ‖F t‖ ≤ C₁ * |t| ^ (p + 1) := by
      filter_upwards [hbigF] with t ht
      simpa [norm_pow] using ht
    have hFj : ContDiff ℝ j F := hF.of_le (mod_cast le_top)
    have htaylor : (fun x : ℝ => F x - taylorWithinEval F j Set.univ 0 x) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ j) := by
      simpa using (taylor_isLittleO_univ (f := F) (x₀ := 0) (n := j) hFj)
    let c : E := ((Nat.factorial j : ℝ)⁻¹) • iteratedDeriv j F 0
    have htaylor' : (fun x : ℝ => F x - x ^ j • c) =o[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ j) := by
      refine htaylor.congr_left (fun x => ?_)
      rw [taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below F j (x₀ := 0) (x := x) hj_min]
      simp [c]
    have hc_nz : c ≠ 0 := smul_ne_zero (inv_ne_zero (by positivity)) hj_nz
    have hrem : ∀ᶠ x in 𝓝 (0 : ℝ), ‖F x - x ^ j • c‖ ≤ (‖c‖ / 2) * |x| ^ j := by
      filter_upwards [htaylor'.def (show 0 < ‖c‖ / 2 by positivity)] with x hx
      simpa [norm_pow] using hx
    have hlower : ∀ᶠ x in 𝓝 (0 : ℝ), (‖c‖ / 2) * |x| ^ j ≤ ‖F x‖ := by
      filter_upwards [hrem] with x hx
      have hnorm : ‖x ^ j • c‖ = ‖c‖ * |x| ^ j := by
        rw [norm_smul, norm_pow, Real.norm_eq_abs, mul_comm]
      have htri : ‖x ^ j • c‖ - ‖F x‖ ≤ ‖F x - x ^ j • c‖ := by
        have h := norm_sub_norm_le (x ^ j • c) (F x)
        simpa [norm_sub_rev] using h
      linarith [hnorm, htri, hx]
    have hcombine : ∀ᶠ x in 𝓝 (0 : ℝ), (‖c‖ / 2) * |x| ^ j ≤ C₁ * |x| ^ (p + 1) := by
      filter_upwards [hlower, hbigF'] with x hlow hbig
      exact hlow.trans hbig
    have hO_scaled : (fun x : ℝ => (‖c‖ / 2) * |x| ^ j) =O[𝓝 (0 : ℝ)]
        (fun x : ℝ => |x| ^ (p + 1)) := by
      refine IsBigO.of_bound C₁ ?_
      filter_upwards [hcombine] with x hx
      rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hO : (fun x : ℝ => |x| ^ j) =O[𝓝 (0 : ℝ)] (fun x : ℝ => |x| ^ (p + 1)) :=
      (isBigO_const_mul_left_iff (f := fun x : ℝ => |x| ^ j) (g := fun x : ℝ => |x| ^ (p + 1))
        (c := ‖c‖ / 2) (l := 𝓝 (0 : ℝ)) (by positivity)).1 hO_scaled
    have ho : (fun x : ℝ => |x| ^ (p + 1)) =o[𝓝 (0 : ℝ)] (fun x : ℝ => |x| ^ j) := by
      simpa [Real.norm_eq_abs] using
        (isLittleO_norm_pow_norm_pow (E' := ℝ) (m := j) (n := p + 1) (by lia))
    have hfreq0 : ∃ᶠ x in 𝓝 (0 : ℝ), x ≠ 0 := by
      rw [Filter.frequently_iff]
      intro U hU
      rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hU⟩
      refine ⟨ε / 2, hU ?_, ne_of_gt (div_pos hε (by norm_num))⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_of_nonneg (by positivity)]
      linarith
    have hfreq : ∃ᶠ x in 𝓝 (0 : ℝ), |x| ^ j ≠ 0 :=
      hfreq0.mono fun x hx => pow_ne_zero j (abs_ne_zero.mpr hx)
    exact (isLittleO_irrefl hfreq) (hO.trans_isLittleO ho)
  · intro h0
    have hFp1 : ContDiff ℝ (p + 1) F := hF.of_le (mod_cast le_top)
    have htaylor : (fun x : ℝ => F x - taylorWithinEval F (p + 1) Set.univ 0 x) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ (p + 1)) := by
      simpa using (taylor_isLittleO_univ (f := F) (x₀ := 0) (n := p + 1) hFp1)
    let a : E := ((Nat.factorial (p + 1) : ℝ)⁻¹) • iteratedDeriv (p + 1) F 0
    have htaylor' : (fun x : ℝ => F x - x ^ (p + 1) • a) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ (p + 1)) := by
      refine htaylor.congr_left (fun x => ?_)
      rw [taylorWithinEval_eq_smul_of_iteratedDeriv_eq_zero_below F (p + 1) (x₀ := 0) (x := x)
        (fun k hk => h0 k (Nat.lt_succ_iff.mp hk))]
      simp [a]
    have hbig_smul : (fun x : ℝ => x ^ (p + 1) • a) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ (p + 1)) := by
      refine IsBigO.of_bound ‖a‖ ?_
      filter_upwards with x
      simp [norm_smul, mul_comm]
    have hbig_F : (fun x : ℝ => F x) =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ (p + 1)) :=
      (hbig_smul.add htaylor'.isBigO).congr_left (fun x => by abel)
    exact isBigO_norm_left.mpr hbig_F

/-! ### Taylor's theorem with integral remainder (vanishing derivatives at 0) -/

/-- If the first `p` iterated derivatives of `f` vanish at `0`, then the `p`-th Taylor polynomial
of `f` on `uIcc 0 t` (with base point `0`) vanishes, provided `t ≠ 0`. -/
lemma taylorWithinEval_eq_zero_of_iteratedDeriv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0)
    (ht : t ≠ 0) :
    taylorWithinEval f p (Set.uIcc 0 t) 0 t = 0 := by
  rw [taylor_within_apply]
  have hud : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc (Ne.symm ht)
  apply Finset.sum_eq_zero
  intro k hk
  have hk_le_p : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk_le : k ≤ p + 1 := le_trans hk_le_p (Nat.le_succ p)
  rw [iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le (mod_cast hk_le))
    (by simp)]
  simp [h0 k hk_le_p]

/-- The scalar identity used to pass from the standard integral remainder to the paper's
substituted form: `t * (t - u * t)^p / p! = (p + 1) * (1 - u)^p * t^(p + 1) / (p + 1)!`. -/
lemma taylor_paper_scalar_eq (p : ℕ) (t u : ℝ) :
    t * ((t - u * t) ^ p / (Nat.factorial p : ℝ)) =
      (p + 1 : ℝ) * ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp
  rw [mul_pow]
  push_cast
  ring

/-- Taylor's theorem with the integral remainder for a function whose first `p` iterated
derivatives vanish at `0`: `f t = ∫₀ᵗ ((t - s)^p / p!) • f⁽ᵖ⁺¹⁾(s) ds`. -/
theorem taylor_integral_remainder_iteratedDeriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) :
    f t = ∫ s in (0 : ℝ)..t,
      ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s := by
  by_cases ht : t = 0
  · subst t
    simpa using (h0 0 (Nat.zero_le p))
  · have hud : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc (Ne.symm ht)
    have hpoly : taylorWithinEval f p (Set.uIcc (0 : ℝ) t) 0 t = 0 :=
      taylorWithinEval_eq_zero_of_iteratedDeriv_eq_zero hf h0 ht
    have hmain := taylor_integral_remainder (f := f) (x₀ := 0) (x := t) (n := p) hf.contDiffOn
    have hf_t : f t = ∫ s in (0 : ℝ)..t,
        ((t - s) ^ p / (Nat.factorial p : ℝ)) •
          iteratedDerivWithin (p + 1) f (Set.uIcc (0 : ℝ) t) s := by
      simpa [hpoly] using hmain
    rw [hf_t]
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    exact congrArg (fun y => ((t - s) ^ p / (Nat.factorial p : ℝ)) • y)
      (iteratedDerivWithin_eq_iteratedDeriv hud hf.contDiffAt (Set.uIoo_subset_uIcc_self hs))

/-- Taylor's theorem with the integral remainder in the paper's substituted form
(`s = u * t`): `f t = (p + 1) • ∫₀¹ (1 - u)^p * t^(p + 1) / (p + 1)! • f⁽ᵖ⁺¹⁾(u * t) du`. -/
theorem taylor_integral_remainder_iteratedDeriv_zero_paper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {p : ℕ} {t : ℝ}
    (hf : ContDiff ℝ (p + 1) f)
    (h0 : ∀ k ≤ p, iteratedDeriv k f 0 = 0) :
    f t = (p + 1 : ℝ) • ∫ u in (0 : ℝ)..(1 : ℝ),
      ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) •
        iteratedDeriv (p + 1) f (u * t) := by
  rw [taylor_integral_remainder_iteratedDeriv_zero hf h0]
  calc
    ∫ s in (0 : ℝ)..t, ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s
        = t • ∫ u in (0 : ℝ)..(1 : ℝ),
            ((t - u * t) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f (u * t) := by
            simpa [mul_zero, one_mul] using
              (intervalIntegral.smul_integral_comp_mul_right
                (f := fun s => ((t - s) ^ p / (Nat.factorial p : ℝ)) • iteratedDeriv (p + 1) f s)
                (a := 0) (b := 1) (c := t)).symm
    _ = (p + 1 : ℝ) • ∫ u in (0 : ℝ)..(1 : ℝ),
          ((1 - u) ^ p * (t ^ (p + 1) / (Nat.factorial (p + 1) : ℝ))) •
            iteratedDeriv (p + 1) f (u * t) := by
          simp only [← intervalIntegral.integral_smul]
          apply intervalIntegral.integral_congr_uIoo
          intro u _
          simp only [smul_smul]
          exact congrArg₂ (fun r y => r • y) (taylor_paper_scalar_eq p t u) rfl

/-! ### Norm bounds for the exponential -/

section NormExpBounds

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- Each term of the exponential series is bounded by `‖a‖^n / n!`. -/
lemma norm_exp_term_le [NormOneClass 𝔸] (a : 𝔸) (n : ℕ) :
    ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ ≤ ‖a‖ ^ n / Nat.factorial n := by
  rw [norm_smul, norm_inv, ← Rat.norm_cast_real, Real.norm_eq_abs, inv_mul_eq_div]
  norm_cast; gcongr
  exact norm_pow_le ..

/-- The norm of the exponential is bounded by the exponential of the norm:
`‖exp a‖ ≤ Real.exp ‖a‖` for a general normed algebra. -/
lemma norm_exp_le [NormOneClass 𝔸] (a : 𝔸) : ‖exp a‖ ≤ Real.exp ‖a‖ := by
  rw [NormedSpace.exp_eq_tsum ℚ, Real.exp_eq_exp_ℝ,
    ← (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq]
  have hnsumm : Summable fun n ↦ ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ :=
    (Real.summable_pow_div_factorial ‖a‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (norm_exp_term_le a)
  calc
    _ ≤ ∑' n, ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ := norm_tsum_le_tsum_norm hnsumm
    _ ≤ ∑' n, ‖a‖ ^ n / Nat.factorial n :=
      hnsumm.tsum_le_tsum (norm_exp_term_le a) (Real.summable_pow_div_factorial ‖a‖)

end NormExpBounds

/-- In a C*-algebra, the exponential of an anti-Hermitian (`star a = -a`) multiple is unitary,
hence has norm `1`: `‖exp (t • a)‖ = 1`. -/
lemma norm_exp_smul_of_skewAdjoint {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] {a : 𝔸} (ha : star a = -a) (t : ℝ) :
    ‖exp (t • a)‖ = 1 := by
  have hta : star (t • a) = -(t • a) := by
    rw [StarModule.star_smul, ha, smul_neg, star_trivial]
  exact CStarRing.norm_of_mem_unitary
    (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr hta))

/-- For a single element, the norm of `H^k * exp (s • H)` is bounded by
`‖H‖^k * Real.exp (s * ‖H‖)` whenever `s ≥ 0` (the paper's single-element bound,
prelim.tex:186–187). -/
theorem norm_pow_mul_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedSpace ℝ 𝔸] [NormOneClass 𝔸] (H : 𝔸) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ‖H ^ k * exp (s • H)‖ ≤ ‖H‖ ^ k * Real.exp (s * ‖H‖) := by
  calc
    ‖H ^ k * exp (s • H)‖ ≤ ‖H ^ k‖ * ‖exp (s • H)‖ := norm_mul_le _ _
    _ ≤ ‖H‖ ^ k * Real.exp ‖s • H‖ := mul_le_mul (norm_pow_le H k) (norm_exp_le (s • H))
          (norm_nonneg _) (pow_nonneg (norm_nonneg H) k)
    _ = ‖H‖ ^ k * Real.exp (s * ‖H‖) := by
        congr 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]

/-! ### Finset / `finAntidiagonal` / multinomial reindexing -/

/-- The antidiagonal of `Fin (m + 1)` fibers over that of `Fin m` by the value at the last index,
via `Fin.snoc`. -/
lemma sum_finAntidiagonal_snoc {𝔸 : Type*} [AddCommMonoid 𝔸] (m n : ℕ)
    (G : (Fin (m + 1) → ℕ) → 𝔸) :
    (∑ q' ∈ finAntidiagonal (m + 1) n, G q') =
      ∑ k ∈ range (n + 1), ∑ q ∈ finAntidiagonal m (n - k), G (Fin.snoc q k) := by
  rw [sum_sigma']
  refine (sum_bij (fun x _ => Fin.snoc x.2 x.1) ?_ ?_ ?_ ?_).symm
  · intro x hx
    rw [mem_finAntidiagonal, Fin.sum_snoc]
    have hx' : x.1 ∈ range (n + 1) ∧ x.2 ∈ finAntidiagonal m (n - x.1) :=
      mem_sigma.mp hx
    have hle : x.1 ≤ n := by simpa using mem_range.mp hx'.1
    have hsum : (∑ i : Fin m, x.2 i) = n - x.1 := by
      simpa using mem_finAntidiagonal.mp hx'.2
    rw [hsum, Nat.sub_add_cancel hle]
  · intro x₁ _ x₂ _ h
    obtain ⟨hq, hk⟩ := Fin.snoc_inj.mp h
    exact Sigma.ext hk (heq_of_eq hq)
  · intro q' hq'
    have hsum : (∑ i : Fin (m + 1), q' i) = n := mem_finAntidiagonal.mp hq'
    have hsplit : (∑ i : Fin m, q' i.castSucc) + q' (Fin.last m) = n := by
      simpa [Fin.sum_univ_castSucc] using hsum
    refine ⟨⟨q' (Fin.last m), Fin.init q'⟩, ?_, Fin.snoc_init_self q'⟩
    rw [mem_sigma]; constructor
    · rw [mem_range]
      have hle : q' (Fin.last m) ≤ n := by
        rw [← hsplit]
        exact Nat.le_add_left _ _
      exact Nat.lt_succ_of_le hle
    · rw [mem_finAntidiagonal]
      have hinit : (∑ i : Fin m, q' i.castSucc) = n - q' (Fin.last m) := by
        rw [← hsplit, Nat.add_sub_cancel_right]
      simpa [Fin.init] using hinit
  · tauto

/-- Appending a zero multiplicity does not change the multinomial coefficient. -/
lemma multinomial_snoc_zero {m : ℕ} (q : Fin m → ℕ) :
    Nat.multinomial (univ : Finset (Fin (m + 1))) (Fin.snoc q 0) =
      Nat.multinomial (univ : Finset (Fin m)) q := by
  simp only [Nat.multinomial]
  rw [Fin.sum_snoc, Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Reindexing `range (n+1)` minus `0` to `range n` by `k ↦ k + 1`. -/
lemma sum_range_filter_ne_zero {𝔸 : Type*} [AddCommMonoid 𝔸] (n : ℕ) (f : ℕ → 𝔸) :
    (∑ k ∈ (range (n + 1)).filter (fun k => k ≠ 0), f k) =
      ∑ k ∈ range n, f (k + 1) := by
  refine (sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [mem_filter, mem_range]
    exact ⟨Nat.add_lt_add_right (mem_range.mp hk) 1, Nat.succ_ne_zero k⟩
  · intros; lia
  · intro b hb
    rw [mem_filter, mem_range] at hb
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb.2
    refine ⟨b - 1, ?_, ?_⟩
    · rw [mem_range]; lia
    · lia
  · tauto

/-- The sum over `finAntidiagonal (s + 1) p` filtered by nonzero last entry equals the sum over the
`k ≥ 1` slices of the `Fin.snoc` fibration. -/
lemma sum_finAntidiagonal_filter_last_ne_zero {𝔸 : Type*} [AddCommMonoid 𝔸] (s p : ℕ)
    (G : (Fin (s + 1) → ℕ) → 𝔸) :
    (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0), G q) =
      ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
        G (Fin.snoc q (k + 1)) := by
  rw [sum_filter, sum_finAntidiagonal_snoc]
  simp only [Fin.snoc_last]
  trans (∑ x ∈ (range (p + 1)).filter (fun x => x ≠ 0),
      ∑ q ∈ finAntidiagonal s (p - x), G (Fin.snoc q x))
  · rw [sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases h : x = 0 <;> simp [h]
  · rw [sum_range_filter_ne_zero]

/-- The product of factorials of a snoc'd multiplicity factors into the outer `j!` and the inner
product. -/
lemma factorial_prod_snoc {s : ℕ} (q : Fin s → ℕ) (j : ℕ) :
    (∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ)) =
      (∏ i : Fin s, (Nat.factorial (q i) : ℝ)) * (Nat.factorial j : ℝ) := by
  rw [Fin.prod_univ_castSucc (fun i : Fin (s + 1) =>
    (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- The inverse factorial coefficient of a snoc'd multiplicity factors as `j!⁻¹ · ∏qᵢ!⁻¹`. -/
lemma factorial_inv_snoc {s : ℕ} (q : Fin s → ℕ) (j : ℕ) :
    (Nat.factorial j : ℝ)⁻¹ * (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ =
      (∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))⁻¹ := by
  rw [← mul_inv, mul_comm (Nat.factorial j : ℝ) (∏ i : Fin s, (Nat.factorial (q i) : ℝ)),
    factorial_prod_snoc]

/-- Reindexing the double sum over `{(j, i) | j < p, i < p - j}` (equivalently `i + j < p`)
to the sum over `{(m, i) | m < p, i ≤ m}` via `m = i + j`. -/
lemma sum_range_add_antidiagonal {𝔸 : Type*} [AddCommMonoid 𝔸] (p : ℕ) (f : ℕ → ℕ → 𝔸) :
    (∑ j ∈ range p, ∑ i ∈ range (p - j), f i j) =
      ∑ m ∈ range p, ∑ i ∈ range (m + 1), f i (m - i) := by
  rw [Finset.sum_sigma' (s := range p) (t := fun j => range (p - j)) (f := fun j i => f i j),
    Finset.sum_sigma' (s := range p) (t := fun m => range (m + 1)) (f := fun m i => f i (m - i))]
  refine Finset.sum_bij (fun x _ => ⟨x.2 + x.1, x.2⟩) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_sigma] at hx
    rcases hx with ⟨hx1, hx2⟩
    rw [mem_range] at hx1 hx2
    rw [mem_sigma]
    constructor
    · rw [mem_range]
      exact (Nat.lt_sub_iff_add_lt).mp hx2
    · rw [mem_range]
      exact Nat.lt_succ_of_le (Nat.le_add_right x.2 x.1)
  · intro a₁ _ a₂ _ h
    rcases a₁ with ⟨j₁, i₁⟩
    rcases a₂ with ⟨j₂, i₂⟩
    have hi : i₁ = i₂ := congrArg Sigma.snd h
    have hj : j₁ = j₂ := by
      have hsum : i₁ + j₁ = i₂ + j₂ := congrArg Sigma.fst h
      subst hi
      exact Nat.add_left_cancel hsum
    subst hj
    subst hi
    rfl
  · intro b hb
    rw [mem_sigma] at hb
    rcases hb with ⟨hb1, hb2⟩
    rw [mem_range] at hb1 hb2
    refine ⟨⟨b.1 - b.2, b.2⟩, ?_, ?_⟩
    · rw [mem_sigma]
      constructor
      · rw [mem_range]
        exact lt_of_le_of_lt (Nat.sub_le b.1 b.2) hb1
      · rw [mem_range]
        have hle : b.2 ≤ b.1 := Nat.le_of_lt_succ hb2
        have hsum : b.2 + (b.1 - b.2) = b.1 := by rw [add_comm, Nat.sub_add_cancel hle]
        exact (Nat.lt_sub_iff_add_lt).mpr (by simpa [hsum] using hb1)
    · rcases b with ⟨m, i⟩
      have hle : i ≤ m := Nat.le_of_lt_succ hb2
      congr
      simpa [add_comm] using (Nat.sub_add_cancel hle)
  · intro x _
    congr
    rw [Nat.add_comm]
    exact (Nat.add_sub_cancel_right x.1 x.2).symm

/-- Reindexing `j ↦ p - j - 1` over the antidiagonal fibers: the sum over `j < p` of the
`Fin.snoc q (p - j)`-fiber equals the sum over `k < p` of the `Fin.snoc q (k + 1)`-fiber. -/
lemma sum_range_finAntidiagonal_reflect {s p : ℕ} {𝔸 : Type*} [AddCommMonoid 𝔸]
    (G : (Fin (s + 1) → ℕ) → 𝔸) :
    (∑ j ∈ range p, ∑ q ∈ finAntidiagonal s j, G (Fin.snoc q (p - j))) =
      ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)), G (Fin.snoc q (k + 1)) := by
  calc
    (∑ j ∈ range p, ∑ q ∈ finAntidiagonal s j, G (Fin.snoc q (p - j)))
        = ∑ j ∈ range p, ∑ q ∈ finAntidiagonal s (p - ((p - 1 - j) + 1)),
            G (Fin.snoc q ((p - 1 - j) + 1)) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hj' : j < p := mem_range.mp hj
              have h1 : p - ((p - 1 - j) + 1) = j := by lia
              have h2 : (p - 1 - j) + 1 = p - j := by lia
              rw [h1, h2]
    _ = ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)), G (Fin.snoc q (k + 1)) := by
              simpa using (Finset.sum_range_reflect
                (fun k => ∑ q ∈ finAntidiagonal s (p - (k + 1)), G (Fin.snoc q (k + 1))) p)

/-! ### General exponential and continuity lemmas -/

/-- `exp (-x) * exp x = 1`. -/
lemma exp_neg_mul_self {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸) :
    exp (-x) * exp x = 1 := by
  simpa using (exp_add_of_commute (Commute.refl x).neg_left).symm

/-- `exp x * exp (-x) = 1`. -/
lemma exp_mul_neg_self {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸) :
    exp x * exp (-x) = 1 := by
  simpa using (exp_add_of_commute (Commute.refl x).neg_right).symm

/-- `t ↦ exp (t • A)` is continuous (over `ℝ`). -/
lemma continuous_exp_smul_const {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (A : 𝔸) : Continuous (fun t : ℝ => exp (t • A)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (contDiffAt_exp_smul_const A 1 t).continuousAt

/-! ### General scalar / norm / star lemmas -/

/-- In an ℝ-algebra, the scalar action `r • a` equals right multiplication `a * (r : 𝔸)`. -/
lemma smul_eq_mul_right {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (r : ℝ) (a : 𝔸) :
    r • a = a * (r : 𝔸) := by
  rw [Algebra.smul_def, Algebra.commutes]

/-- The Taylor coefficient `(j! : ℝ)⁻¹ * τ^j` acting by `•` equals the paper's form
`(j! : ℝ)⁻¹ • x * (τ : 𝔸)^j`. -/
lemma pow_smul_eq_smul_mul {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (j : ℕ) (x : 𝔸) (τ : ℝ) :
    ((Nat.factorial j : ℝ)⁻¹ * τ ^ j) • x = (Nat.factorial j : ℝ)⁻¹ • x * (τ : 𝔸) ^ j := by
  rw [mul_smul, smul_eq_mul_right (τ ^ j) x]
  simp

/-- `(r • a) * (c : 𝔸) = (r * c) • a` for scalars `r, c : ℝ`. -/
lemma smul_mul_cast {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (r c : ℝ) (a : 𝔸) :
    (r • a) * (c : 𝔸) = (r * c) • a := by
  rw [smul_eq_mul_right r a, smul_eq_mul_right (r * c) a, mul_assoc, ← map_mul (algebraMap ℝ 𝔸) r c]

/-- Combining the scalar factors of the single-layer remainder integrand. -/
lemma scalar_combine (k j : ℕ) (d τ u : ℝ) (hd : d ≠ 0) :
    (d⁻¹ * ((τ - u) ^ k / (Nat.factorial k : ℝ))) * τ ^ j =
      (τ - u) ^ k * τ ^ j / ((Nat.factorial k : ℝ) * d) := by
  have hk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  field_simp [hd, hk]

/-- `|c| ≤ 1` implies `‖c • A‖ ≤ ‖A‖` in any normed algebra. -/
lemma norm_smul_le_of_abs_le_one {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸]
    (c : ℝ) (A : 𝔸) (hc : |c| ≤ 1) : ‖c • A‖ ≤ ‖A‖ := by
  calc
    ‖c • A‖ = |c| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖A‖ := one_mul _

/-- For `u ≤ 1`, `0 ≤ t`, and `|c| ≤ 1`, the exponential argument `(u * t) * ‖c • A‖` is at
most `t * ‖A‖`. -/
lemma norm_smul_exp_arg_le {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸]
    (c : ℝ) (A : 𝔸) (hc : |c| ≤ 1) (u t : ℝ) (ht : 0 ≤ t) (hu1 : u ≤ 1) :
    (u * t) * ‖c • A‖ ≤ t * ‖A‖ := by
  have hc' : u * |c| ≤ 1 := by
    simpa using mul_le_mul hu1 hc (abs_nonneg _) zero_le_one
  have hle : u * t * |c| ≤ t := by
    calc
      u * t * |c| = t * (u * |c|) := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left hc' ht
      _ = t := mul_one _
  calc
    (u * t) * ‖c • A‖ = u * t * |c| * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ ≤ t * ‖A‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- `(s • A)` commutes with `A`. -/
lemma commute_smul_self {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : 𝔸) (s : ℝ) :
    Commute (s • A) A := by
  rw [commute_iff_eq, smul_mul_assoc, mul_smul_comm]

/-- `star (c • A) = -(c • A)` whenever `star A = -A` and `c` is real. -/
lemma star_smul_of_skew {𝔸 : Type*} [Star 𝔸] [AddGroup 𝔸] [DistribSMul ℝ 𝔸] [StarModule ℝ 𝔸]
    {A : 𝔸} {c : ℝ} (hA : star A = -A) :
    star (c • A) = -(c • A) := by
  rw [StarModule.star_smul, hA, star_trivial, smul_neg]

/-- A sum of anti-Hermitian elements is anti-Hermitian. -/
lemma sum_skewAdjoint {𝔸 : Type*} [AddCommGroup 𝔸] [StarAddMonoid 𝔸] {ι : Type*} [Fintype ι]
    (H : ι → 𝔸) (h : ∀ i, star (H i) = -(H i)) :
    star (∑ i : ι, H i) = -(∑ i : ι, H i) := by
  calc
    star (∑ i : ι, H i) = ∑ i : ι, star (H i) := star_sum Finset.univ H
    _ = ∑ i : ι, -(H i) := by simp [h]
    _ = -(∑ i : ι, H i) := by simp

end TrotterError


-- ===== from FQFP.TrotterError.Commutator =====
/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/



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


namespace TrotterError

open Finset LieAlgebra
open scoped algebraMap

/- The associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A` on any ring, so that the
standard Lie-bracket lemmas (`lie_add`, `lie_smul`, …) are available. -/
attribute [local instance] LieRing.ofAssociativeRing

/-! ### Basic commutator objects -/

@[simp] lemma ad_pow_succ {R 𝔸 : Type*} [CommRing R] [Ring 𝔸] [LieAlgebra R 𝔸] (A : 𝔸) (q : ℕ)
    (B : 𝔸) : ((ad R 𝔸 A) ^ (q + 1)) B = ⁅A, ((ad R 𝔸 A) ^ q) B⁆ := by simp [pow_succ']

/-- The `q`-fold iterated adjoint `ad_A^q = (ad A)^q`, as an ℝ-linear endomorphism of `𝔸`. -/
abbrev adPow {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (q : ℕ) : Module.End ℝ 𝔸 :=
  (ad ℝ 𝔸 A) ^ q

/-- The iterated `ad` over a sequence of operators with multiplicities,
`ad_{A ⟨s-1⟩}^{q ⟨s-1⟩} ⋯ ad_{A ⟨0⟩}^{q ⟨0⟩}(B)`, where `A ⟨0⟩` is applied first
(innermost) and `A ⟨s-1⟩` is applied last (outermost). -/
def adSequence {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) : 𝔸 :=
  match s with
  | 0 => B
  | s + 1 =>
      adPow (A (Fin.last s)) (q (Fin.last s))
        (adSequence (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc) B)

/-- The nested commutator `[H ⟨p⟩, [H ⟨p-1⟩, ⋯ [H ⟨1⟩, H ⟨0⟩] ⋯]]` with exactly `p`
brackets: `H ⟨0⟩` is innermost and `H ⟨p⟩` is outermost. -/
def nestedComm {𝔸 : Type*} [Ring 𝔸] {p : ℕ} (H : Fin (p + 1) → 𝔸) : 𝔸 :=
  match p with
  | 0 => H ⟨0, by simp⟩
  | p + 1 => ⁅H ⟨p + 1, by simp⟩, nestedComm (fun i : Fin (p + 1) => H i.castSucc)⁆

/-- The paper's `α~_comm`: the sum of the norms of all nested commutators
`[H_{γ_{p+1}}, ⋯ [H_{γ_2}, H_{γ_1}]]` over all tuples `γ : Fin (p + 1) → Fin Γ`
(repeated indices allowed). -/
noncomputable def αComm {𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ)
    (H : Fin Γ → 𝔸) : ℝ :=
  ∑ γ : Fin (p + 1) → Fin Γ, ‖nestedComm (H ∘ γ)‖

/-- The paper's `α_comm(A_s, …, A_1, B)`: the multinomial-weighted sum
`Σ_{q₁+⋯+q_s = p} (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`. -/
noncomputable def αCommConj {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ q ∈ Finset.finAntidiagonal s p,
    (Nat.multinomial (Finset.univ : Finset (Fin s)) q : ℝ) * ‖adSequence A q B‖

/-! ### Norm bounds -/

/-- The norm of a commutator is bounded by `2 * ‖A‖ * ‖B‖`. -/
theorem norm_commutator_le {𝔸 : Type*} [NormedRing 𝔸] (A B : 𝔸) :
    ‖⁅A, B⁆‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  rw [Ring.lie_def]
  calc
    ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le (A * B) (B * A)
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add (norm_mul_le A B) (norm_mul_le B A)
    _ = 2 * ‖A‖ * ‖B‖ := by ring

/-- The norm of the `k`-fold iterated commutator is bounded by `(2 * ‖A‖)^k * ‖B‖`. -/
theorem norm_adPow_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (k : ℕ) (B : 𝔸) :
    ‖adPow A k B‖ ≤ (2 * ‖A‖) ^ k * ‖B‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        ‖adPow A (k + 1) B‖ = ‖⁅A, adPow A k B⁆‖ := by rw [ad_pow_succ]
        _ ≤ 2 * ‖A‖ * ‖adPow A k B‖ := norm_commutator_le A (adPow A k B)
        _ ≤ 2 * ‖A‖ * ((2 * ‖A‖) ^ k * ‖B‖) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * ‖A‖) ^ (k + 1) * ‖B‖ := by rw [pow_succ]; ring

/-- The norm of an iterated `ad` over a sequence is bounded by the product of the
per-step bounds `(2 * ‖A i‖) ^ (q i)`. -/
theorem norm_adSequence_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    ‖adSequence A q B‖ ≤ (∏ i : Fin s, (2 * ‖A i‖) ^ (q i)) * ‖B‖ := by
  induction s with
  | zero => simp [adSequence]
  | succ s ih =>
      calc
        ‖adSequence A q B‖
            = ‖adPow (A (Fin.last s)) (q (Fin.last s))
                (adSequence (fun i : Fin s => A i.castSucc)
                  (fun i : Fin s => q i.castSucc) B)‖ := by
                rw [adSequence]
        _ ≤ (2 * ‖A (Fin.last s)‖) ^ (q (Fin.last s)) *
              ‖adSequence (fun i : Fin s => A i.castSucc)
                (fun i : Fin s => q i.castSucc) B‖ :=
              norm_adPow_le (A (Fin.last s)) (q (Fin.last s))
                (adSequence (fun i : Fin s => A i.castSucc)
                  (fun i : Fin s => q i.castSucc) B)
        _ ≤ (2 * ‖A (Fin.last s)‖) ^ (q (Fin.last s)) *
              ((∏ i : Fin s, (2 * ‖A i.castSucc‖) ^ (q i.castSucc)) * ‖B‖) :=
              mul_le_mul_of_nonneg_left
                (ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc))
                (by positivity)
        _ = (∏ i : Fin (s + 1), (2 * ‖A i‖) ^ (q i)) * ‖B‖ := by
              rw [Fin.prod_univ_castSucc]
              ring

/-- `αComm p H` is a sum of norms, hence nonnegative. -/
theorem αComm_nonneg {𝔸 : Type*} [NormedRing 𝔸] {Γ : ℕ} (p : ℕ) (H : Fin Γ → 𝔸) :
    0 ≤ αComm p H := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-! ### Linear and algebraic properties of `adPow` -/

/-- Appending a zero multiplicity on the outermost layer does not change `adSequence`. -/
lemma adSequence_snoc_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q 0) B = adSequence (fun i : Fin m => A i.castSucc) q B := by
  rw [adSequence]
  simp [Fin.snoc_last]

/-- Appending a multiplicity on the outermost layer of `adSequence`: the `k`-fold commutator of
`A ⟨m⟩` applied to the inner sequence. -/
lemma adSequence_snoc {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {m : ℕ} (A : Fin (m + 1) → 𝔸)
    (q : Fin m → ℕ) (k : ℕ) (B : 𝔸) :
    adSequence A (Fin.snoc q k) B =
      adPow (A (Fin.last m)) k (adSequence (fun i : Fin m => A i.castSucc) q B) := by
  rw [adSequence]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

/-- `adSequence A q` commutes with ℝ-scalar multiplication in its last argument `B`. -/
lemma adSequence_smul {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (r : ℝ) (X : 𝔸) :
    adSequence A q (r • X) = r • adSequence A q X := by
  induction s with
  | zero => simp [adSequence]
  | succ s ih =>
      rw [adSequence, ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc)]
      exact (adPow (A (Fin.last s)) (q (Fin.last s))).map_smul r
        (adSequence (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc) X)

/-! ### The nested commutator of a list -/

/-- `nestedComm` commutes with reindexing a tuple by a `Fin.cast`. -/
lemma nestedComm_cast {𝔸 : Type*} [Ring 𝔸] {n m : ℕ} (h : n = m) (H : Fin (m + 1) → 𝔸) :
    nestedComm (H ∘ Fin.cast (congrArg (· + 1) h)) = nestedComm H := by
  subst h
  rfl

/-- The nested commutator of a list with an innermost seed: `nestedCommOfList b [x₁, …, xₙ] =
⁅xₙ, ⋯ ⁅x₁, b⁆ ⋯⁆` (the head `x₁` is innermost and the last element `xₙ` is outermost). -/
def nestedCommOfList {𝔸 : Type*} [Ring 𝔸] (b : 𝔸) : List 𝔸 → 𝔸 :=
  List.foldl (fun acc X => ⁅X, acc⁆) b

@[simp] lemma nestedCommOfList_nil {𝔸 : Type*} [Ring 𝔸] (b : 𝔸) :
    nestedCommOfList b [] = b := rfl

@[simp] lemma nestedCommOfList_append {𝔸 : Type*} [Ring 𝔸] (b X : 𝔸) (L : List 𝔸) :
    nestedCommOfList b (L ++ [X]) = ⁅X, nestedCommOfList b L⁆ := by
  rw [nestedCommOfList, List.foldl_append]
  rfl

/-- `nestedCommOfList b (L ++ replicate k X) = adPow X k (nestedCommOfList b L)`: the `k`
outermost copies of `X` contribute the `k`-fold iterated commutator. -/
lemma nestedCommOfList_append_replicate {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (b X : 𝔸) (L : List 𝔸)
    (k : ℕ) :
    nestedCommOfList b (L ++ List.replicate k X) = adPow X k (nestedCommOfList b L) := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [List.replicate_succ', ← List.append_assoc, nestedCommOfList_append, ad_pow_succ, ih]

/-- The tuple `Fin (L.length + 1) → 𝔸` with `0 ↦ b` and `t + 1 ↦ f (L[t])`. -/
def listIndexed {ι 𝔸 : Type*} (b : 𝔸) (L : List ι) (f : ι → 𝔸) : Fin (L.length + 1) → 𝔸 :=
  Fin.cons b (fun t : Fin L.length => f (L[t.val]'t.2))

/-- `nestedComm` peels the outermost element of a `Fin.cons`-built tuple. -/
lemma nestedComm_cons_succ {𝔸 : Type*} [Ring 𝔸] {n : ℕ} (b : 𝔸) (tail : Fin (n + 1) → 𝔸) :
    nestedComm (Fin.cons b tail) =
      ⁅tail (Fin.last n), nestedComm (Fin.cons b (fun i : Fin n => tail i.castSucc))⁆ := by
  rw [nestedComm]
  apply congrArg₂ (fun x y : 𝔸 => ⁅x, y⁆)
  · rw [show ((⟨n + 1, by simp⟩ : Fin (n + 2)) = Fin.succ (Fin.last n)) by rfl]
    rw [Fin.cons_succ]
  · congr 1
    funext i
    refine Fin.cases ?zero ?succ i
    · simp [Fin.cons_zero]
    · intro j
      rw [Fin.castSucc_succ, Fin.cons_succ, Fin.cons_succ]

/-- `nestedComm` of a `Fin.cons`-built tuple equals the list nested commutator of the
`List.ofFn` image of the tail. -/
lemma nestedComm_ofFn_cons {𝔸 : Type*} [Ring 𝔸] {n : ℕ} (b : 𝔸) (tail : Fin n → 𝔸) :
    nestedComm (Fin.cons b tail) = nestedCommOfList b (List.ofFn tail) := by
  induction n with
  | zero => simp [Fin.cons, List.ofFn, nestedComm]
  | succ n ih =>
      rw [nestedComm_cons_succ, List.ofFn_succ_last, nestedCommOfList_append,
        ih (fun i : Fin n => tail i.castSucc)]

/-- `nestedComm` of `listIndexed` is the list nested commutator. -/
lemma nestedComm_listIndexed {𝔸 : Type*} [Ring 𝔸] {ι : Type*} (b : 𝔸) (L : List ι)
    (f : ι → 𝔸) :
    nestedComm (listIndexed b L f) = nestedCommOfList b (L.map f) := by
  rw [listIndexed, nestedComm_ofFn_cons]
  congr 1
  rw [List.ofFn_eq_map]
  rw [show (List.finRange L.length).map (fun t => f (L[t.val]'t.2)) =
      ((List.finRange L.length).map (fun t => L[t.val]'t.2)).map f by
    rw [List.map_map]
    rfl]
  rw [List.map_getElem_finRange]

/-! ### Multinomial coefficients are bounded by `p!` -/

/-- Every multinomial coefficient is at most the factorial of the total degree: the multinomial
`Nat.multinomial s f` divides `(∑ f)!` (via `Nat.multinomial_spec`), and the complementary product
of factorials is `≥ 1`. -/
lemma multinomial_le_factorial {α : Type*} (s : Finset α) (f : α → ℕ) :
    Nat.multinomial s f ≤ Nat.factorial (∑ i ∈ s, f i) := by
  have hspec := Nat.multinomial_spec s f
  have hprod : 1 ≤ ∏ i ∈ s, (f i).factorial := one_le_prod (fun i _ => Nat.factorial_pos _)
  calc
    Nat.multinomial s f = Nat.multinomial s f * 1 := by rw [mul_one]
    _ ≤ Nat.multinomial s f * (∏ i ∈ s, (f i).factorial) := Nat.mul_le_mul_left _ hprod
    _ = (∏ i ∈ s, (f i).factorial) * Nat.multinomial s f := by rw [mul_comm]
    _ = (∑ i ∈ s, f i).factorial := hspec

/-! ### The list of layer indices -/

/-- The list of the non-innermost operators of `expandTuple f q b`, each `f i` repeated `q i`
times, in increasing order of `i`. -/
def layersOf {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) : List α :=
  (List.finRange s).flatMap fun i => List.replicate (q i) (f i)

/-- `layersOf f q` has length `∑ q`. -/
lemma layersOf_length {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) :
    (layersOf f q).length = ∑ i : Fin s, q i := by
  induction s with
  | zero => simp [layersOf]
  | succ s ih =>
      rw [layersOf, List.finRange_succ]
      simp only [List.flatMap_cons, List.flatMap_map, List.length_append, List.length_replicate]
      change q 0 + (layersOf (f ∘ Fin.succ) (q ∘ Fin.succ)).length = ∑ i : Fin (s + 1), q i
      rw [ih (f ∘ Fin.succ) (q ∘ Fin.succ)]
      simp [Fin.sum_univ_succ]

/-- `layersOf` commutes with post-composition. -/
lemma layersOf_map {α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) :
    layersOf (g ∘ f) q = (layersOf f q).map g := by
  rw [layersOf, layersOf, List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  simp [List.map_replicate]

/-- The list of indices, each `i : Fin s` repeated `q i` times. -/
def layerIndices {s : ℕ} (q : Fin s → ℕ) : List (Fin s) := layersOf (fun i : Fin s => i) q

/-- The index `i` occurs exactly `q i` times in `layerIndices q`. -/
lemma layersOf_count {s : ℕ} (q : Fin s → ℕ) (i : Fin s) :
    (layersOf (fun i : Fin s => i) q).count i = q i := by
  induction s with
  | zero => exact Fin.elim0 i
  | succ s ih =>
      rw [layersOf, List.finRange_succ_last]
      simp only [List.flatMap_append, List.flatMap_map, List.flatMap_singleton]
      rw [List.count_append]
      refine Fin.lastCases ?_ ?_ i
      · change List.count (Fin.last s)
            (layersOf (Fin.castSucc ∘ (fun i : Fin s => i)) (q ∘ Fin.castSucc)) +
              List.count (Fin.last s) (List.replicate (q (Fin.last s)) (Fin.last s)) =
            q (Fin.last s)
        rw [layersOf_map Fin.castSucc (fun i : Fin s => i) (q ∘ Fin.castSucc)]
        have hmem : Fin.last s ∉
            (layersOf (fun i : Fin s => i) (q ∘ Fin.castSucc)).map Fin.castSucc := by
          intro h
          rw [List.mem_map] at h
          rcases h with ⟨x, -, hx⟩
          exact (Fin.castSucc_lt_last x).ne hx
        rw [List.count_eq_zero_of_not_mem hmem, List.count_replicate]
        simp
      · intro j
        change List.count j.castSucc
            (layersOf (Fin.castSucc ∘ (fun i : Fin s => i)) (q ∘ Fin.castSucc)) +
              List.count j.castSucc (List.replicate (q (Fin.last s)) (Fin.last s)) =
            q j.castSucc
        rw [layersOf_map Fin.castSucc (fun i : Fin s => i) (q ∘ Fin.castSucc),
          List.count_map_of_injective _ Fin.castSucc (Fin.castSucc_injective s) j,
          ih (q ∘ Fin.castSucc) j]
        have hne : Fin.last s ≠ j.castSucc := (Fin.castSucc_lt_last j).ne'
        rw [List.count_replicate]
        simp [hne]

/-! ### Expanding a multiplicity vector into a tuple -/

/-- Expand a multiplicity vector `q : Fin s → ℕ` into a tuple of length `∑ q + 1`: the entry at
position `0` is `b`, and the entries at positions `1` through `∑ q` are the layer operators
`f i`, each repeated `q i` times. -/
def expandTuple {α} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    Fin (∑ i : Fin s, q i + 1) → α :=
  Fin.cons b (fun t : Fin (∑ i : Fin s, q i) =>
    f ((layerIndices q)[t.val]'(by simp [layerIndices, layersOf_length])))

/-- The entry at position `0` of `expandTuple` is the innermost `b`. -/
lemma expandTuple_zero {α : Type*} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    expandTuple f q b 0 = b := by
  simp [expandTuple]

/-- The entry at position `t + 1` of `expandTuple f q b` is `f` applied to the `t`-th layer
index. -/
lemma expandTuple_succ {α : Type*} {s : ℕ} (f : Fin s → α) (q : Fin s → ℕ) (b : α) (t : ℕ)
    (ht : t < ∑ i : Fin s, q i) :
    expandTuple f q b ⟨t + 1, Nat.succ_lt_succ ht⟩ =
      f ((layersOf (fun i : Fin s => i) q)[t]'(by simpa [layersOf_length] using ht)) := by
  rw [expandTuple]
  rw [show (⟨t + 1, Nat.succ_lt_succ ht⟩ : Fin ((∑ i : Fin s, q i) + 1)) =
      Fin.succ (⟨t, ht⟩ : Fin (∑ i : Fin s, q i)) by simp]
  rw [Fin.cons_succ]
  congr

/-- `expandTuple` is natural in the target:
`expandTuple (g ∘ f) q (g b) = g ∘ expandTuple f q b`. -/
lemma expandTuple_nat {α β : Type*} {s : ℕ} (g : α → β) (f : Fin s → α) (q : Fin s → ℕ) (b : α) :
    expandTuple (g ∘ f) q (g b) = g ∘ expandTuple f q b := by
  funext j
  refine Fin.cases ?zero ?succ j
  · simp [Function.comp_apply, expandTuple_zero]
  · intro t
    change expandTuple (g ∘ f) q (g b) ⟨t.val + 1, by exact Nat.succ_lt_succ t.isLt⟩ =
      g (expandTuple f q b ⟨t.val + 1, by exact Nat.succ_lt_succ t.isLt⟩)
    rw [expandTuple_succ (g ∘ f) q (g b) t.val t.isLt]
    simp [expandTuple_succ f q b t.val t.isLt]

/-- `adSequence A q B` equals the list nested commutator of the layers. -/
lemma adSequence_eq_nestedCommOfList {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A q B = nestedCommOfList B (layersOf A q) := by
  induction s with
  | zero => simp [adSequence, layersOf]
  | succ s ih =>
      rw [adSequence, ih (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc)]
      have hlayers : layersOf A q = layersOf (fun i : Fin s => A i.castSucc)
          (fun i : Fin s => q i.castSucc) ++
          List.replicate (q (Fin.last s)) (A (Fin.last s)) := by
        simp [layersOf, List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
      rw [hlayers, nestedCommOfList_append_replicate]

/-- `adSequence A q B` is exactly the nested commutator of the expanded tuple. -/
lemma adSequence_eq_nestedComm_expandTuple {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A q B = nestedComm (expandTuple A q B) := by
  rw [adSequence_eq_nestedCommOfList A q B]
  rw [show layersOf A q = (layerIndices q).map A by
    rw [layerIndices]
    exact layersOf_map A (fun i : Fin s => i) q]
  rw [← nestedComm_listIndexed B (layerIndices q) A]
  rw [show expandTuple A q B =
      listIndexed B (layerIndices q) A ∘ Fin.cast (congrArg (· + 1)
        (show (∑ i : Fin s, q i) = (layerIndices q).length by
          rw [layerIndices, layersOf_length])) by
    ext j
    refine Fin.cases ?zero ?succ j
    · simp [expandTuple, listIndexed, Fin.cons_zero]
    · intro t
      simp [expandTuple, listIndexed, Fin.cons_succ, Fin.cast_succ_eq, Fin.val_cast]]
  rw [nestedComm_cast (show (∑ i : Fin s, q i) = (layerIndices q).length by
    rw [layerIndices, layersOf_length]) (listIndexed B (layerIndices q) A)]

/-! ### Coefficient-dropping for `αCommConj` -/

/-- `adPow (c • A) k X = c ^ k • adPow A k X`. -/
lemma adPow_smul_left {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (c : ℝ) (A : 𝔸) (k : ℕ) (X : 𝔸) :
    adPow (c • A) k X = c ^ k • adPow A k X := by
  induction k with
  | zero => simp [adPow]
  | succ k ih =>
      rw [ad_pow_succ, ad_pow_succ, ih, smul_lie, lie_smul, smul_smul, pow_succ, mul_comm]

/-- `adSequence (fun i => c i • A i) q B = (∏ i, c i ^ q i) • adSequence A q B`. -/
lemma adSequence_smul_fun {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (c : Fin s → ℝ)
    (A : Fin s → 𝔸) (q : Fin s → ℕ) (B : 𝔸) :
    adSequence (fun i => c i • A i) q B = (∏ i : Fin s, (c i) ^ q i) • adSequence A q B := by
  induction s with
  | zero => simp [adSequence]
  | succ s ih =>
      rw [adSequence, adSequence, ih (fun i => c i.castSucc) (fun i => A i.castSucc)
          (fun i => q i.castSucc), adPow_smul_left, (adPow (A (Fin.last s))
          (q (Fin.last s))).map_smul, smul_smul, Fin.prod_univ_castSucc, mul_comm]

/-- `αCommConj (fun i => c i • A i) B p ≤ αCommConj A B p` for `|c i| ≤ 1`. -/
lemma αCommConj_smul_fun_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (c : Fin s → ℝ) (A : Fin s → 𝔸) (hc : ∀ i, |c i| ≤ 1) (B : 𝔸) (p : ℕ) :
    αCommConj (fun i => c i • A i) B p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  apply sum_le_sum
  intro q hq
  rw [adSequence_smul_fun c A q B, norm_smul, Real.norm_eq_abs]
  have hprod : |∏ i : Fin s, (c i) ^ q i| ≤ 1 := by
    rw [abs_prod]
    exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hc i))
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) hprod) (Nat.cast_nonneg _)

/-- `αCommConj A (c • B) p ≤ αCommConj A B p` for `|c| ≤ 1`. -/
lemma αCommConj_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸) (c : ℝ) (hc : |c| ≤ 1) (B : 𝔸) (p : ℕ) :
    αCommConj A (c • B) p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  apply sum_le_sum
  intro q hq
  rw [adSequence_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) hc) (Nat.cast_nonneg _)

/-- `αCommConj` is invariant under `Fin.cast` reindexing. -/
lemma αCommConj_cast {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s t : ℕ} (h : s = t) (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (fun i : Fin t => A (Fin.cast h.symm i)) B p = αCommConj A B p := by
  subst h
  simp [αCommConj]

/-! ### Sum-splitting and reindexing -/

/-- `adSequence A q (∑ γ, H γ) = ∑ γ, adSequence A q (H γ)`. -/
lemma adSequence_sum {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (q : Fin s → ℕ)
    {ι : Type*} [Fintype ι] (H : ι → 𝔸) :
    adSequence A q (∑ γ : ι, H γ) = ∑ γ : ι, adSequence A q (H γ) := by
  induction s with
  | zero => simp [adSequence]
  | succ s ih =>
      unfold adSequence
      rw [ih (fun i => A i.castSucc) (fun i => q i.castSucc)]
      change (adPow (A (Fin.last s)) (q (Fin.last s))).toAddMonoidHom
          (∑ γ : ι, adSequence (fun i => A i.castSucc) (fun i => q i.castSucc) (H γ)) =
        ∑ γ : ι, (adPow (A (Fin.last s)) (q (Fin.last s))).toAddMonoidHom
          (adSequence (fun i => A i.castSucc) (fun i => q i.castSucc) (H γ))
      exact map_sum (adPow (A (Fin.last s)) (q (Fin.last s))).toAddMonoidHom
        (fun γ : ι => adSequence (fun i => A i.castSucc) (fun i => q i.castSucc) (H γ))
        (univ : Finset ι)

/-- `αCommConj A (∑ γ, H γ) p ≤ ∑ γ, αCommConj A (H γ) p`. -/
lemma αCommConj_sum_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin s → 𝔸) {ι : Type*} [Fintype ι] (H : ι → 𝔸) (p : ℕ) :
    αCommConj A (∑ γ : ι, H γ) p ≤ ∑ γ : ι, αCommConj A (H γ) p := by
  rw [αCommConj]
  calc
    (∑ q ∈ finAntidiagonal s p,
        (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
          ‖adSequence A q (∑ γ : ι, H γ)‖)
        = ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              ‖∑ γ : ι, adSequence A q (H γ)‖ := by
              apply sum_congr rfl
              intro q hq
              rw [adSequence_sum A q H]
    _ ≤ ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              (∑ γ : ι, ‖adSequence A q (H γ)‖) := by
              apply sum_le_sum
              intro q hq
              exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)
    _ = ∑ γ : ι, ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
              ‖adSequence A q (H γ)‖ := by
              simp_rw [mul_sum]
              rw [sum_comm]
    _ = ∑ γ : ι, αCommConj A (H γ) p := by rfl

/-! ### Suffix extension (peel innermost zeros) -/

/-- Prepending a zero multiplicity shifts the layers: the innermost `f 0` contributes nothing and
each `f (i.succ)` becomes the `i`-th layer. -/
lemma layersOf_cons_zero {α : Type*} {s : ℕ} (f : Fin (s + 1) → α) (q : Fin s → ℕ) :
    layersOf f (Fin.cons 0 q) = layersOf (fun i : Fin s => f i.succ) q := by
  rw [layersOf, layersOf, List.finRange_succ]
  simp only [List.flatMap_cons, List.flatMap_map, Fin.cons_zero, List.replicate_zero,
    List.nil_append]
  apply List.flatMap_congr
  intro j _
  simp

/-- `adSequence A (Fin.cons 0 q) B = adSequence (fun i => A i.succ) q B`: a zero innermost
multiplicity lets the innermost `A ⟨0⟩` drop out. -/
lemma adSequence_cons_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) :
    adSequence A (Fin.cons 0 q) B = adSequence (fun i : Fin s => A i.succ) q B := by
  rw [adSequence_eq_nestedCommOfList A (Fin.cons 0 q) B,
    adSequence_eq_nestedCommOfList (fun i : Fin s => A i.succ) q B]
  rw [layersOf_cons_zero A q]

/-- `Nat.multinomial (Fin.cons 0 q) = Nat.multinomial q`: prepending a zero multiplicity does not
change the multinomial coefficient. -/
lemma multinomial_cons_zero {s : ℕ} (q : Fin s → ℕ) :
    Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.cons 0 q) =
      Nat.multinomial (univ : Finset (Fin s)) q := by
  unfold Nat.multinomial
  rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
  simp [Nat.factorial_zero]

/-- Dropping the innermost summand does not increase `αCommConj`. -/
lemma αCommConj_succ_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (fun i : Fin s => A i.succ) B p ≤ αCommConj A B p := by
  rw [αCommConj, αCommConj]
  calc
    (∑ q ∈ finAntidiagonal s p,
        (Nat.multinomial (univ : Finset (Fin s)) q : ℝ) *
          ‖adSequence (fun i => A i.succ) q B‖)
        = ∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.cons 0 q) : ℝ) *
              ‖adSequence A (Fin.cons 0 q) B‖ := by
              apply sum_congr rfl
              intro q hq
              rw [adSequence_cons_zero A q B, multinomial_cons_zero q]
    _ = ∑ q' ∈ (finAntidiagonal s p).image (Fin.cons 0),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := by
              rw [sum_image]
              intro q₁ hq₁ q₂ hq₂ h
              funext i
              simpa using (congrFun h (i.succ))
    _ ≤ ∑ q' ∈ finAntidiagonal (s + 1) p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro q hq
                rw [mem_image] at hq
                rcases hq with ⟨q₀, hq₀, rfl⟩
                rw [mem_finAntidiagonal]
                rw [mem_finAntidiagonal] at hq₀
                rw [Fin.sum_univ_succ]
                simpa using hq₀
              · intro q _ _
                exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-- `αCommConj` of the last `n` entries of `A : Fin (m + n) → 𝔸` (indexed by `Fin.natAdd m`)
is bounded by the full `αCommConj`. -/
lemma αCommConj_natAdd_le {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {m n : ℕ} (A : Fin (m + n) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj (A ∘ Fin.natAdd m) B p ≤ αCommConj A B p := by
  induction m with
  | zero =>
      rw [show A ∘ Fin.natAdd 0 = (fun i : Fin n => A (Fin.cast (Nat.zero_add n).symm i)) by
        funext i
        apply congrArg A
        apply Fin.ext
        rw [Fin.val_natAdd, Fin.val_cast]
        exact Nat.zero_add i.val]
      exact (αCommConj_cast (Nat.zero_add n) A B p).le
  | succ m ih =>
      let e : (m + 1) + n = (m + n) + 1 := Nat.succ_add m n
      rw [show A ∘ Fin.natAdd (m + 1) =
          (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) ∘ Fin.natAdd m by
        funext i
        apply congrArg A
        apply Fin.ext
        rw [Fin.val_natAdd, Fin.val_cast, Fin.val_succ, Fin.val_natAdd]
        exact Nat.succ_add m i.val]
      calc
        αCommConj ((fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) ∘ Fin.natAdd m) B p
            ≤ αCommConj (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ)) B p :=
                ih (fun j : Fin (m + n) => A (Fin.cast e.symm j.succ))
        _ ≤ αCommConj (A ∘ Fin.cast e.symm) B p :=
                αCommConj_succ_le (A ∘ Fin.cast e.symm) B p
        _ = αCommConj A B p := αCommConj_cast e A B p

/-- `αCommConj A B p` is a sum of nonnegative terms, hence nonnegative. -/
lemma αCommConj_nonneg {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸)
    (p : ℕ) : 0 ≤ αCommConj A B p :=
  sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

end TrotterError


-- ===== from FQFP.TrotterError.Integrals =====
/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/


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


namespace TrotterError

open NormedSpace MeasureTheory
open scoped algebraMap

/-- The beta-type integral `∫ u in uIoc 0 τ, |τ - u|^(q-1) du = |τ|^q / q`, for `1 ≤ q`. -/
lemma integral_abs_sub_pow_uIoc (q : ℕ) (τ : ℝ) (hq : 1 ≤ q) :
    (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1)) = |τ| ^ q / (q : ℝ) := by
  have h := integral_pow_abs_sub_uIoc (a := τ) (b := (0 : ℝ)) (n := q - 1)
  calc
    (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1))
        = (∫ u in Set.uIoc (τ : ℝ) 0, |u - τ| ^ (q - 1)) := by
            rw [Set.uIoc_comm (a := (0 : ℝ)) (b := τ)]
            exact setIntegral_congr_fun measurableSet_uIoc
              (fun u _ => congrArg (fun t : ℝ => t ^ (q - 1)) (abs_sub_comm τ u))
    _ = |τ| ^ q / (q : ℝ) := by
            rw [h]
            have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
              norm_cast
              rw [Nat.sub_add_cancel hq]
            rw [Nat.sub_add_cancel hq, hcast, abs_sub_comm (0 : ℝ) τ, sub_zero]

/-- `∫₀^τ |s|^(p-1)/(p-1)! ds = |τ|^p/p!` over the unordered interval, for `1 ≤ p`. -/
lemma integral_abs_pow_sub_div_factorial_uIoc (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) =
      |τ| ^ p / (Nat.factorial p : ℝ) := by
  have hfac : Nat.factorial p = p * Nat.factorial (p - 1) := by
    simpa [Nat.sub_add_cancel hp] using Nat.factorial_succ (p - 1)
  calc
    (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))
        = (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1)) / (Nat.factorial (p - 1) : ℝ) := by
            rw [integral_div]
    _ = (|τ| ^ p / (p : ℝ)) / (Nat.factorial (p - 1) : ℝ) := by
            have hp' : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
              rw [Nat.cast_sub hp]
              ring
            have hpow : (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1)) = |τ| ^ p / (p : ℝ) := by
              have h := integral_pow_abs_sub_uIoc (a := 0) (b := τ) (n := p - 1)
              rw [Nat.sub_add_cancel hp, hp'] at h
              simpa using h
            rw [hpow]
    _ = |τ| ^ p / (Nat.factorial p : ℝ) := by
            rw [hfac, Nat.cast_mul]
            field_simp

/-- `|∫₀^τ |s|^(p-1)/(p-1)! ds| = |τ|^p/p!` for `1 ≤ p`. -/
lemma abs_integral_abs_pow_div_factorial (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    |∫ s in 0..τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)|
      = |τ| ^ p / (Nat.factorial p : ℝ) := by
  rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
  have hnonneg : 0 ≤ (∫ s in Set.uIoc (0 : ℝ) τ, |s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) :=
    setIntegral_nonneg measurableSet_uIoc (fun s _ => by positivity)
  rw [abs_of_nonneg hnonneg, integral_abs_pow_sub_div_factorial_uIoc p τ hp]

/-- The standard Taylor remainder integral equals the paper's substituted form:
`∫₀^τ (τ-s)^n/n! • F s = ∫₀^τ F (τ-s) * (s^n/n!)`. -/
lemma integral_smul_eq_integral_mul_sub {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (F : ℝ → 𝔸) (n : ℕ) (τ : ℝ) :
    (∫ s in 0..τ, ((τ - s) ^ n / (Nat.factorial n : ℝ)) • F s) =
      ∫ s in 0..τ, F (τ - s) * ((s ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
  calc
    (∫ s in 0..τ, ((τ - s) ^ n / (Nat.factorial n : ℝ)) • F s)
        = ∫ s in 0..τ, F s * (((τ - s) ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
            apply intervalIntegral.integral_congr_uIoo
            intro s hs
            exact smul_eq_mul_right (((τ - s) ^ n / (Nat.factorial n : ℝ))) (F s)
    _ = ∫ s in 0..τ, F (τ - s) * ((s ^ n / (Nat.factorial n : ℝ)) : 𝔸) := by
            simpa using (intervalIntegral.integral_comp_sub_left (a := 0) (b := τ) (d := τ)
              (f := fun u => F (τ - u) * ((u ^ n / (Nat.factorial n : ℝ)) : 𝔸)))

/-- `∫₀¹ (1-u)^p du = 1/(p+1)`. -/
lemma intervalIntegral_one_sub_pow (p : ℕ) :
    (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p) = (1 : ℝ) / ((p + 1 : ℕ) : ℝ) := by
  calc
    (∫ u in (0 : ℝ)..(1 : ℝ), (1 - u) ^ p)
        = ∫ u in (0 : ℝ)..(1 : ℝ), u ^ p := by
            simpa using (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ p)
              (a := 0) (b := 1) (d := 1))
    _ = (1 : ℝ) / ((p + 1 : ℕ) : ℝ) := by
        have hp : (p + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero p
        rw [integral_pow, one_pow, zero_pow hp]
        simp

/-- `∫₀ᵗ C · |τ|^p / p! dτ = (C / p!) · t^{p+1}/(p+1)`, for `t ≥ 0`. -/
lemma intervalIntegral_const_mul_abs_pow_div_factorial (C : ℝ) (p : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) =
      (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by
  calc
    ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ)
        = ∫ τ in 0..t, (C / (Nat.factorial p : ℝ)) * |τ| ^ p := by
            apply intervalIntegral.integral_congr_uIoo
            intro τ _
            ring
    _ = (C / (Nat.factorial p : ℝ)) * ∫ τ in 0..t, |τ| ^ p := by
            rw [intervalIntegral.integral_const_mul]
    _ = (C / (Nat.factorial p : ℝ)) * ∫ τ in 0..t, τ ^ p := by
            congr 1
            apply intervalIntegral.integral_congr_uIoo
            intro τ hτ
            have hτ_pos : 0 < τ := by simpa [Set.uIoo, min_eq_left ht] using hτ.1
            simp [abs_of_nonneg hτ_pos.le]
    _ = (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by simp

/-- `∫₀ᵗ (C · |τ|^p / p!) · E dτ = (C / p!) · E · t^{p+1}/(p+1)`, for `t ≥ 0` and any constant
`E`. -/
lemma intervalIntegral_const_mul_abs_pow_div_factorial_mul (C E : ℝ) (p : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * E =
      (C / (Nat.factorial p : ℝ)) * E * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by
  calc
    ∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ) * E
        = (∫ τ in 0..t, C * |τ| ^ p / (Nat.factorial p : ℝ)) * E := by
            rw [intervalIntegral.integral_mul_const]
    _ = (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) * E := by
            rw [intervalIntegral_const_mul_abs_pow_div_factorial C p t ht]
    _ = (C / (Nat.factorial p : ℝ)) * E * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by ring

end TrotterError


-- ===== from FQFP.TrotterError.ListLemmas =====
/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/


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


namespace TrotterError.List

open scoped Topology ContDiff

/-! ### Products over sublists -/

/-- The product over `l.drop k` splits as `f (l.get k)` times the product over `l.drop (k + 1)`. -/
lemma prod_drop_eq_get_mul {ι M : Type*} [Monoid M] (l : List ι) (f : ι → M) (k : Fin l.length) :
    ((l.drop (k : ℕ)).map f).prod = f (l.get k) * ((l.drop ((k : ℕ) + 1)).map f).prod := by
  rw [← List.cons_get_drop_succ (l := l) (n := k)]
  simp only [List.map_cons, List.prod_cons]

/-- Splitting the product `(l.map f).prod` at the occurrence of `i`: it is the product over the
prefix strictly before `i`, times `f i`, times the product over the suffix strictly after `i`. -/
@[to_additive]
lemma prod_map_eq_take_mul_get_mul_drop {ι M : Type*} [BEq ι] [LawfulBEq ι] [Monoid M]
    (l : List ι) (f : ι → M) (i : ι) (hi : i ∈ l) :
    (l.map f).prod = ((l.take (l.idxOf i)).map f).prod * f i *
      ((l.drop (l.idxOf i + 1)).map f).prod := by
  have hidx : l.idxOf i < l.length := List.idxOf_lt_length_iff.mpr hi
  have hcons : i :: l.drop (l.idxOf i + 1) = l.drop (l.idxOf i) := by
    calc
      _ = l[l.idxOf i] :: l.drop (l.idxOf i + 1) := by
          rw [List.getElem_idxOf hidx]
      _ = l.drop (l.idxOf i) := List.cons_getElem_drop_succ (l := l) (n := l.idxOf i) (h := hidx)
  calc
    (l.map f).prod = ((l.take (l.idxOf i) ++ l.drop (l.idxOf i)).map f).prod := by
        rw [List.take_append_drop (l.idxOf i) l]
    _ = ((l.take (l.idxOf i)).map f).prod * ((l.drop (l.idxOf i)).map f).prod := by
        rw [List.map_append, List.prod_append]
    _ = ((l.take (l.idxOf i)).map f).prod * ((i :: l.drop (l.idxOf i + 1)).map f).prod := by
        rw [← hcons]
    _ = ((l.take (l.idxOf i)).map f).prod * (f i * ((l.drop (l.idxOf i + 1)).map f).prod) := by
        rw [List.map_cons, List.prod_cons]
    _ = ((l.take (l.idxOf i)).map f).prod * f i * ((l.drop (l.idxOf i + 1)).map f).prod := by
        rw [mul_assoc]

/-- If `g i` is a right inverse of `f i` for every `i`, then the product of `f` over `l` times the
product of `g` over `l.reverse` is `1`. -/
lemma prod_mul_rev_eq_one_of_mul_eq_one {ι M : Type*} [Monoid M] (l : List ι) (f g : ι → M)
    (hfg : ∀ i, f i * g i = 1) : (l.map f).prod * (l.reverse.map g).prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_one]
      calc
        _ = f a * ((l.map f).prod * (l.reverse.map g).prod) * g a := by simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hfg a]

/-- If `g i` is a left inverse of `f i` for every `i`, then the product of `g` over `l.reverse`
times the product of `f` over `l` is `1`. -/
lemma rev_mul_prod_eq_one_of_mul_eq_one {ι M : Type*} [Monoid M] (l : List ι) (f g : ι → M)
    (hgf : ∀ i, g i * f i = 1) : (l.reverse.map g).prod * (l.map f).prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_one]
      calc
        _ = (l.reverse.map g).prod * (g a * f a) * (l.map f).prod := by simp only [mul_assoc]
        _ = 1 := by rw [hgf a, mul_one, ih]

/-! ### Reindexing a sum by a nodup list -/

/-- A sum over positions `Fin l.length` reindexes to a sum over the (pairwise distinct) elements
of `l`, using `l.idxOf i` as the inverse of `l.get`. -/
lemma sum_get_eq_sum_idxOf {ι A : Type*} [Fintype ι] [BEq ι] [LawfulBEq ι] [AddCommMonoid A]
    {l : List ι} (hnodup : l.Nodup) (hmem : ∀ i : ι, i ∈ l) (G : ι → ℕ → A) :
    (∑ k : Fin l.length, G (l.get k) (k : ℕ)) = ∑ i : ι, G i (l.idxOf i) := by
  refine (Finset.sum_bij (fun i _ => ⟨l.idxOf i, List.idxOf_lt_length_iff.mpr (hmem i)⟩)
    (fun i _ => Finset.mem_univ _) ?_ ?_ ?_).symm
  · intro a₁ ha₁ a₂ ha₂ h
    have h₁ := List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a₁))
    have h₂ := List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a₂))
    exact h₁.symm.trans ((congrArg l.get h).trans h₂)
  · intro b hb
    refine ⟨l.get b, Finset.mem_univ _, ?_⟩
    ext; exact List.get_idxOf hnodup b
  · intro a ha
    rw [List.idxOf_get (List.idxOf_lt_length_iff.mpr (hmem a))]

/-! ### Derivative of an ordered product -/

/-- The product rule for an ordered `List.prod`: the derivative of `t ↦ (l.map (f · t)).prod` is
the sum over positions `k` of the `k`-th factor differentiated, surrounded by the earlier and later
factors. -/
lemma hasDerivAt_list_prod {ι 𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (l : List ι) (f : ι → ℝ → 𝔸) (Df : ι → ℝ → 𝔸)
    (hf : ∀ i ∈ l, ∀ t : ℝ, HasDerivAt (f i) (Df i t) t) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (l.map (fun i => f i s)).prod)
      (∑ k : Fin l.length,
        ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t *
          ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t := by
  induction l with
  | nil => simpa using (hasDerivAt_const t (1 : 𝔸))
  | cons a l ih =>
      have hf' : ∀ i ∈ l, ∀ t : ℝ, HasDerivAt (f i) (Df i t) t := by
        intro i hi s
        exact hf i (List.mem_cons_of_mem a hi) s
      have ih' : HasDerivAt (fun s : ℝ => (l.map (fun i => f i s)).prod)
          (∑ k : Fin l.length,
            ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t *
              ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t := ih hf'
      have hfa : HasDerivAt (f a) (Df a t) t := hf a (show a ∈ a :: l from List.mem_cons_self) t
      have hprod : HasDerivAt (fun s : ℝ => f a s * (l.map (fun i => f i s)).prod)
          (Df a t * (l.map (fun i => f i t)).prod + f a t *
            (∑ k : Fin l.length,
              ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t *
                ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod)) t := hfa.mul ih'
      have hsum :
          (∑ k : Fin (l.length + 1),
            (((a :: l).take (k : ℕ)).map (fun i => f i t)).prod * Df ((a :: l).get k) t *
              (((a :: l).drop ((k : ℕ) + 1)).map (fun i => f i t)).prod)
            = Df a t * (l.map (fun i => f i t)).prod + f a t *
                (∑ k : Fin l.length,
                  ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) t *
                    ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) := by
        rw [Fin.sum_univ_succ]
        congr 1; · simp
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp [mul_assoc]
      change HasDerivAt (fun s : ℝ => f a s * (l.map (fun i => f i s)).prod)
        (∑ k : Fin (l.length + 1),
          (((a :: l).take (k : ℕ)).map (fun i => f i t)).prod * Df ((a :: l).get k) t *
            (((a :: l).drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t
      rwa [hsum]

/-- The pointwise product of a finite list of smooth functions is smooth. -/
lemma contDiff_list_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸)
    (hf : ∀ i ∈ l, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (fun t : ℝ => (l.map (fun i => f i t)).prod) := by
  induction l with
  | nil => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : 𝔸)))
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ContDiff.mul (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

/-! ### Products of `List.ofFn` suffixes -/

/-- Peeling the outermost entry off a dropped suffix of a `List.ofFn`: the reverse product of the
suffix of `f : Fin (s+1) → 𝔸` is `f (Fin.last s)` times the reverse product of the corresponding
suffix of the inner `Fin s` sequence. -/
lemma ofFn_castSucc_drop_reverse_prod {s} {𝔸 : Type*} [Monoid 𝔸] (f : Fin (s + 1) → 𝔸) (k : ℕ)
    (hk : k ≤ s) :
    f (Fin.last s) * ((List.ofFn (fun i : Fin s => f i.castSucc)).drop k).reverse.prod
      = ((List.ofFn f).drop k).reverse.prod := by
  rw [List.ofFn_succ', List.concat_eq_append]
  rw [List.drop_append_of_le_length (l₁ := List.ofFn (fun i : Fin s => f i.castSucc))
    (l₂ := [f (Fin.last s)]) (by simpa using hk)]
  rw [List.reverse_concat', List.prod_cons]

/-- Peeling the outermost entry off a dropped suffix of a `List.ofFn` (no reversal): the product of
the suffix of `f : Fin (s+1) → 𝔸` is the product of the inner `Fin s` suffix times
`f (Fin.last s)`. -/
lemma ofFn_castSucc_drop_prod {s} {𝔸 : Type*} [Monoid 𝔸] (f : Fin (s + 1) → 𝔸) (k : ℕ)
    (hk : k ≤ s) :
    ((List.ofFn (fun i : Fin s => f i.castSucc)).drop k).prod * f (Fin.last s)
      = ((List.ofFn f).drop k).prod := by
  rw [List.ofFn_succ', List.concat_eq_append]
  rw [List.drop_append_of_le_length (l₁ := List.ofFn (fun i : Fin s => f i.castSucc))
    (l₂ := [f (Fin.last s)]) (by simpa using hk)]
  rw [List.prod_append, List.prod_singleton]

/-- `List.ofFn` of the `get`-composition equals the `map`: for a list `l` and a function `f`,
`ofFn (fun i => f (l.get i)) = l.map f`. -/
lemma ofFn_get_comp {α β : Type*} (l : List α) (f : α → β) :
    List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f := by
  change List.ofFn (f ∘ List.get l) = List.map f l
  rw [← List.map_ofFn, List.ofFn_get]

/-- `List.product` of two `List.ofFn` lists is the `List.ofFn` of the `divNat`/`modNat` pairing. -/
lemma product_ofFn {α β : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → β) :
    List.product (List.ofFn f) (List.ofFn g) =
      List.ofFn (fun k : Fin (m * n) => (f k.divNat, g k.modNat)) := by
  change List.ofFn f ×ˢ List.ofFn g = List.ofFn (fun k : Fin (m * n) => (f k.divNat, g k.modNat))
  induction m with
  | zero => simp [List.nil_product]
  | succ m ih =>
      by_cases hn : n = 0
      · subst n; simp
      · rw [List.ofFn_succ, List.product_cons, List.map_ofFn, ih (fun i => f i.succ)]
        rw [List.ofFn_congr (show (m + 1) * n = n + m * n by rw [Nat.succ_mul, Nat.add_comm])
          (fun k : Fin ((m + 1) * n) => (f k.divNat, g k.modNat))]
        rw [List.ofFn_add]
        congr 1
        · congr 1
          funext j
          simp only [Function.comp_apply]
          apply Prod.ext
          · apply congrArg f
            apply Fin.ext
            rw [Fin.coe_divNat, Fin.val_cast, Fin.val_castLE]
            simpa using (Nat.div_eq_of_lt j.isLt : j.val / n = 0).symm
          · apply congrArg g
            apply Fin.ext
            rw [Fin.coe_modNat, Fin.val_cast, Fin.val_castLE]
            simpa using (Nat.mod_eq_of_lt j.isLt : j.val % n = j.val).symm
        · congr 1
          funext k
          apply Prod.ext
          · apply congrArg f
            apply Fin.ext
            rw [Fin.val_succ, Fin.coe_divNat, Fin.coe_divNat, Fin.val_cast, Fin.val_natAdd]
            rw [show (n + k.val) / n = k.val / n + 1 by
              rw [congrArg (fun x => (x + k.val) / n) (Nat.mul_one n).symm]
              rw [Nat.mul_add_div (Nat.pos_of_ne_zero hn) 1 k.val, Nat.add_comm]]
          · apply congrArg g
            apply Fin.ext
            rw [Fin.coe_modNat, Fin.coe_modNat, Fin.val_cast, Fin.val_natAdd,
              congrArg (fun x => (x + k.val) % n) (Nat.mul_one n).symm, Nat.mul_add_mod]

/-! ### `List.finRange` / `Fin.cast` reindexing -/

/-- `List.finRange (n + m)` splits into the `n`-part and the `m`-part. -/
lemma finRange_add {n m : ℕ} :
    List.finRange (n + m) =
      (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  rw [show List.finRange (n + m) = List.ofFn (fun i : Fin (n + m) => i) from rfl]
  rw [List.ofFn_add, List.ofFn_eq_map, List.ofFn_eq_map]
  rfl

/-- The reversed `finRange` splits accordingly. -/
lemma finRange_reverse_add {n m : ℕ} :
    (List.finRange (n + m)).reverse =
      (List.finRange m).reverse.map (Fin.natAdd n) ++
        (List.finRange n).reverse.map (Fin.castAdd m) := by
  rw [finRange_add, List.reverse_append, List.map_reverse, List.map_reverse]

/-- Mapping `g ∘ Fin.revPerm` over the reversed `finRange` is mapping `g` over `finRange`. -/
lemma finRange_reverse_map_comp_revPerm {n : ℕ} {α : Type*} (g : Fin n → α) :
    ((List.finRange n).reverse).map (g ∘ Fin.revPerm) = (List.finRange n).map g := by
  rw [List.finRange_reverse, List.map_map]
  congr 1
  funext γ
  change g (Fin.revPerm (Fin.rev γ)) = g γ
  rw [Fin.revPerm_apply, Fin.rev_rev]

/-- Reindex a `Fin`-indexed sum along `Fin.cast`. -/
lemma sum_fin_cast {s t : ℕ} (h : s = t) {A : Type*} [AddCommMonoid A] (f : Fin s → A) :
    (∑ i : Fin t, f (Fin.cast h.symm i)) = ∑ i : Fin s, f i := by
  subst h
  simp

end TrotterError.List


-- ===== from FQFP.TrotterError.TimeOrderedExp =====
/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/


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


namespace TrotterError

open NormedSpace
open scoped Topology BigOperators Interval

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-! ### The Dyson series -/

/-- The `n`-th term of the Dyson (Neumann/Picard) series for the time-ordered exponential:
`D₀ = 1` and `D_{n+1}(t) = ∫ τ in t₁..t, H τ * D_n τ`. The interval integral is oriented,
so this is defined for every `t : ℝ` (not only `t ≥ t₁`). -/
noncomputable def dysonTerm (H : ℝ → 𝔸) (t₁ : ℝ) : ℕ → ℝ → 𝔸
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ τ in t₁..t, H τ * dysonTerm H t₁ n τ

/-- The time-ordered exponential `exp_T(∫_{t₁}^{t₂} H(τ) dτ)`, defined for a continuous
generator `H` as the sum of the Dyson series. For `t₁ ≤ t₂` this is the unique solution of
`U' = H·U`, `U(t₁) = 1`; for `t₂ < t₁` it is the inverse evolution (a theorem, not
built into the definition). -/
noncomputable def timeOrderedExp (H : ℝ → 𝔸) (t₁ t₂ : ℝ) : 𝔸 :=
  ∑' n : ℕ, dysonTerm H t₁ n t₂

/-! ### Continuity of the Dyson terms -/

/-- Each Dyson term `D_n` is continuous (as a function of `t`) when `H` is continuous. -/
lemma continuous_dysonTerm (H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) (n : ℕ) :
    Continuous (dysonTerm H t₁ n) := by
  induction n with
  | zero => simpa [dysonTerm] using continuous_const
  | succ n ih =>
      have hg : Continuous fun τ : ℝ => H τ * dysonTerm H t₁ n τ := hH.mul ih
      rw [dysonTerm]
      exact (intervalIntegral.differentiable_integral_of_continuous hg).continuous

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

/-! ### Norm bound of the Dyson terms -/

omit [CompleteSpace 𝔸] in
/-- The `n`-th Dyson term is bounded by `‖1‖ · |∫_{t₁}^{t} ‖H‖|^n / n!` for all `t` (both
orientations), valid without `NormOneClass`. -/
lemma norm_dysonTerm_le_abs (H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) (n : ℕ) (t : ℝ) :
    ‖dysonTerm H t₁ n t‖ ≤ ‖(1 : 𝔸)‖ * |∫ u in t₁..t, ‖H u‖| ^ n / Nat.factorial n := by
  induction n generalizing t with
  | zero => simp [dysonTerm]
  | succ n ih =>
      rw [dysonTerm]
      let B : ℝ → ℝ := fun τ =>
        ‖H τ‖ * (‖(1 : 𝔸)‖ * |∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n)
      calc
        ‖∫ τ in t₁..t, H τ * dysonTerm H t₁ n τ‖
            ≤ |∫ τ in t₁..t, B τ| := by
                refine intervalIntegral.norm_integral_le_abs_of_norm_le
                  (f := fun τ => H τ * dysonTerm H t₁ n τ) (g := B) ?_ ?_
                · filter_upwards with τ
                  calc
                    ‖H τ * dysonTerm H t₁ n τ‖ ≤ ‖H τ‖ * ‖dysonTerm H t₁ n τ‖ := norm_mul_le _ _
                    _ ≤ B τ := mul_le_mul_of_nonneg_left (ih τ) (norm_nonneg (H τ))
                · exact (by fun_prop : Continuous B).intervalIntegrable t₁ t
        _ = ‖(1 : 𝔸)‖ * |∫ τ in t₁..t, ‖H τ‖ * |∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n| := by
                rw [show (fun τ => B τ) =
                    fun τ => ‖(1 : 𝔸)‖ * (‖H τ‖ * |∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n) by
                  funext τ; dsimp [B]; ring, intervalIntegral.integral_const_mul, abs_mul,
                  abs_of_nonneg (norm_nonneg (1 : 𝔸))]
        _ = ‖(1 : 𝔸)‖ * |∫ u in t₁..t, ‖H u‖| ^ (n + 1) / Nat.factorial (n + 1) := by
                rw [abs_integral_mul_abs_integral_pow_div_factorial (fun u => ‖H u‖) hH.norm
                  (fun _ => norm_nonneg _) t₁ t n]
                ring

/-- The Dyson series is summable for all `t₁ t₂` (both orientations), without `NormOneClass`. -/
lemma summable_dysonTerm_abs (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    Summable (fun n : ℕ => dysonTerm H t₁ n t₂) := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial |(∫ τ in t₁..t₂, ‖H τ‖)|).mul_left ‖(1 : 𝔸)‖) ?_
  intro n
  simpa [mul_div_assoc'] using norm_dysonTerm_le_abs H hH t₁ n t₂

/-! ### The norm bound -/

/-- `Real.exp x = ∑' n, x^n / n!` (the exponential series), in `HasSum` form. -/
lemma Real.hasSum_pow_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / Nat.factorial n) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]
  exact (Real.summable_pow_div_factorial x).hasSum

omit [CompleteSpace 𝔸] in
/-- `lem:time_ordered_norm_bound`: `‖exp_T H t₁ t₂‖ ≤ Real.exp |∫ τ in t₁..t₂, ‖H τ‖|`
(the two-sided form, valid for both time orderings). -/
lemma timeOrderedExp_norm_le [NormOneClass 𝔸] (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    ‖timeOrderedExp H t₁ t₂‖ ≤ Real.exp |∫ τ in t₁..t₂, ‖H τ‖| := by
  rw [timeOrderedExp]
  refine tsum_of_norm_bounded (f := fun n : ℕ => dysonTerm H t₁ n t₂)
    (g := fun n : ℕ => |∫ τ in t₁..t₂, ‖H τ‖| ^ n / Nat.factorial n)
    (a := Real.exp |∫ τ in t₁..t₂, ‖H τ‖|) ?_ ?_
  · exact Real.hasSum_pow_div_factorial |∫ τ in t₁..t₂, ‖H τ‖|
  · intro n
    simpa using norm_dysonTerm_le_abs H hH t₁ n t₂

/-! ### The initial condition -/

omit [CompleteSpace 𝔸] in
/-- `exp_T H t₁ t₁ = 1`: the `D₀` term is `1` and all higher terms vanish because the
interval `[t₁, t₁]` has integral `0`. -/
lemma timeOrderedExp_initial (H : ℝ → 𝔸) (t₁ : ℝ) : timeOrderedExp H t₁ t₁ = 1 := by
  rw [timeOrderedExp, tsum_eq_single (0 : ℕ)]
  · simp [dysonTerm]
  · intro n hn
    cases n with
    | zero => contradiction
    | succ n => simp [dysonTerm]

/-! ### Continuity of the solution -/

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

/-- For continuous `H`, the solution `t ↦ exp_T H t₁ t` is continuous. The Dyson series
converges locally uniformly (its sup norm on any compact interval is summable), so its sum
is continuous. -/
lemma continuous_timeOrderedExp (H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) :
    Continuous (fun t => timeOrderedExp H t₁ t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let a : ℝ := t₀ - 1
  let b : ℝ := t₀ + 1
  let M : ℝ := |(∫ u in t₁..a, ‖H u‖)| + |(∫ u in t₁..b, ‖H u‖)|
  let u : ℕ → ℝ := fun n => ‖(1 : 𝔸)‖ * M ^ n / Nat.factorial n
  have hM_le : ∀ t, t ∈ Set.Icc a b → |(∫ u in t₁..t, ‖H u‖)| ≤ M := by
    intro t ht
    exact abs_integral_le_abs_integral_of_mem_Icc hH.norm (fun _ => norm_nonneg _) t₁ a b t ht
  have hOn_sum : ContinuousOn (fun t => ∑' n : ℕ, dysonTerm H t₁ n t) (Set.Icc a b) := by
    refine continuousOn_tsum (u := u) (f := fun n => dysonTerm H t₁ n) (s := Set.Icc a b) ?_ ?_ ?_
    · intro n
      exact (continuous_dysonTerm H hH t₁ n).continuousOn
    · simpa [u, mul_div_assoc'] using (Real.summable_pow_div_factorial M).mul_left ‖(1 : 𝔸)‖
    · intro n t ht
      refine (norm_dysonTerm_le_abs H hH t₁ n t).trans ?_
      have hle : |(∫ u in t₁..t, ‖H u‖)| ^ n / Nat.factorial n ≤ M ^ n / Nat.factorial n :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM_le t ht) n) (by positivity)
      simpa [mul_div_assoc'] using mul_le_mul_of_nonneg_left hle (norm_nonneg (1 : 𝔸))
  have hOn : ContinuousOn (fun t => timeOrderedExp H t₁ t) (Set.Icc a b) := by
    simpa [timeOrderedExp] using hOn_sum
  exact hOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-! ### The integral equation -/

/-- `eq:int_eq` (prelim.tex:58): the integral equation
`exp_T H t₁ t₂ = 1 + ∫ τ in t₁..t₂, H τ * exp_T H t₁ τ`.
The proof commutes the `tsum` with the interval integral via the dominated convergence
theorem for series, using the two-sided termwise bound `norm_dysonTerm_le_abs`. -/
lemma timeOrderedExp_eq_integral (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    timeOrderedExp H t₁ t₂ = 1 + ∫ τ in t₁..t₂, H τ * timeOrderedExp H t₁ τ := by
  let bound : ℕ → ℝ → ℝ := fun n τ =>
    (‖H τ‖ * ‖(1 : 𝔸)‖) * (|∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n)
  have hDCT : HasSum (fun n : ℕ => ∫ τ in t₁..t₂, H τ * dysonTerm H t₁ n τ)
      (∫ τ in t₁..t₂, H τ * timeOrderedExp H t₁ τ) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (a := t₁) (b := t₂) (bound := bound)
      (f := fun τ => H τ * timeOrderedExp H t₁ τ) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (hH.mul (continuous_dysonTerm H hH t₁ n)).aestronglyMeasurable.mono_measure
        MeasureTheory.Measure.restrict_le_self
    · intro n
      filter_upwards with τ hτ
      calc
        ‖H τ * dysonTerm H t₁ n τ‖ ≤ ‖H τ‖ * ‖dysonTerm H t₁ n τ‖ := norm_mul_le _ _
        _ ≤ ‖H τ‖ * (‖(1 : 𝔸)‖ * |∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n) :=
            mul_le_mul_of_nonneg_left (norm_dysonTerm_le_abs H hH t₁ n τ) (norm_nonneg (H τ))
        _ = bound n τ := by ring
    · filter_upwards with τ hτ
      simpa [bound] using
        (Real.summable_pow_div_factorial |(∫ u in t₁..τ, ‖H u‖)|).mul_left (‖H τ‖ * ‖(1 : 𝔸)‖)
    · -- `∑' n, bound n τ = ‖H τ‖ * ‖1‖ * Real.exp |∫ ‖H‖|`, which is continuous in τ.
      have hbound_tsum : ∀ τ, (∑' n, bound n τ) =
          ‖H τ‖ * ‖(1 : 𝔸)‖ * Real.exp |∫ u in t₁..τ, ‖H u‖| := by
        intro τ
        have hhasSum : HasSum (fun n =>
            (‖H τ‖ * ‖(1 : 𝔸)‖) * (|∫ u in t₁..τ, ‖H u‖| ^ n / Nat.factorial n))
            ((‖H τ‖ * ‖(1 : 𝔸)‖) * Real.exp |∫ u in t₁..τ, ‖H u‖|) :=
          (Real.hasSum_pow_div_factorial |(∫ u in t₁..τ, ‖H u‖)|).mul_left (‖H τ‖ * ‖(1 : 𝔸)‖)
        simpa [bound] using hhasSum.tsum_eq
      have hcont : Continuous (fun τ => ‖H τ‖ * ‖(1 : 𝔸)‖ * Real.exp |∫ u in t₁..τ, ‖H u‖|) := by
        fun_prop
      have hfeq : (fun τ => ∑' n, bound n τ) =
          fun τ => ‖H τ‖ * ‖(1 : 𝔸)‖ * Real.exp |∫ u in t₁..τ, ‖H u‖| := by
        funext τ
        exact hbound_tsum τ
      simpa [hfeq] using hcont.intervalIntegrable t₁ t₂
    · filter_upwards with τ hτ
      simpa [timeOrderedExp] using (summable_dysonTerm_abs H hH t₁ τ).hasSum.mul_left (H τ)
  have hsplit : (∑' n : ℕ, dysonTerm H t₁ n t₂) =
      dysonTerm H t₁ 0 t₂ + ∑' n : ℕ, dysonTerm H t₁ (n + 1) t₂ :=
    (summable_dysonTerm_abs H hH t₁ t₂).tsum_eq_zero_add
  rw [timeOrderedExp, hsplit]
  have hd0 : dysonTerm H t₁ 0 t₂ = 1 := by simp [dysonTerm]
  rw [hd0]; congr 1
  have hsum1 : (∑' n : ℕ, dysonTerm H t₁ (n + 1) t₂) =
      ∑' n : ℕ, ∫ τ in t₁..t₂, H τ * dysonTerm H t₁ n τ := by
    apply tsum_congr
    intro n
    rw [dysonTerm]
  rw [hsum1]
  exact hDCT.tsum_eq

/-! ### Derivative with respect to the upper limit -/

/-- `prelim.tex:44-49` (first rule): derivative with respect to the upper limit
`∂/∂t₂ exp_T(∫_{t₁}^{t₂} H) = H(t₂) · exp_T(∫_{t₁}^{t₂} H)`.
Follows from the integral equation and `intervalIntegral.integral_hasDerivAt_right`. -/
lemma timeOrderedExp_hasDerivAt (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => timeOrderedExp H t₁ s) (H t₂ * timeOrderedExp H t₁ t₂) t₂ := by
  have hfcont : Continuous (fun τ => H τ * timeOrderedExp H t₁ τ) :=
    hH.mul (continuous_timeOrderedExp H hH t₁)
  have hderiv_integral : HasDerivAt (fun s => ∫ τ in t₁..s, H τ * timeOrderedExp H t₁ τ)
      (H t₂ * timeOrderedExp H t₁ t₂) t₂ :=
    intervalIntegral.integral_hasDerivAt_right (hfcont.intervalIntegrable t₁ t₂)
      hfcont.aestronglyMeasurable.stronglyMeasurableAtFilter hfcont.continuousAt
  have heq : (fun s => timeOrderedExp H t₁ s) =
      fun s => 1 + ∫ τ in t₁..s, H τ * timeOrderedExp H t₁ τ := by
    funext s
    rw [timeOrderedExp_eq_integral H hH t₁ s]
  rw [heq]
  exact hderiv_integral.const_add 1

/-! ### Uniqueness of solutions to the ODE -/

omit [CompleteSpace 𝔸] in
/-- Uniqueness of solutions to the ODE `U' = H·U`: two functions solving `U' = H·U` pointwise and
agreeing at one time `t₀` agree everywhere. The continuity of `H` is used only to obtain a uniform
Lipschitz constant on the compact interval between `t₀` and each target point. -/
lemma ode_solution_unique (H : ℝ → 𝔸) (hH : Continuous H) {f g : ℝ → 𝔸}
    (hf : ∀ t, HasDerivAt f (H t * f t) t) (hg : ∀ t, HasDerivAt g (H t * g t) t)
    (t₀ : ℝ) (heq : f t₀ = g t₀) : f = g := by
  funext t
  let a : ℝ := min t t₀ - 1
  let b : ℝ := max t t₀ + 1
  have ht₀ : t₀ ∈ Set.Ioo a b := by
    constructor <;> linarith [min_le_right t t₀, le_max_right t t₀]
  have ht : t ∈ Set.Ioo a b := by
    constructor <;> linarith [min_le_left t t₀, le_max_left t t₀]
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨t₀, ⟨le_of_lt ht₀.1, le_of_lt ht₀.2⟩⟩ (hH.norm.continuousOn)
  let M : NNReal := ⟨‖H x‖, norm_nonneg (H x)⟩
  have hM : ∀ s ∈ Set.Icc a b, ‖H s‖ ≤ (M : ℝ) := fun s hs => (isMaxOn_iff.mp hmax) s hs
  have hv : ∀ s ∈ Set.Ioo a b, LipschitzOnWith M (fun y : 𝔸 => H s * y) Set.univ := by
    intro s hs
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    calc
      dist (H s * x) (H s * y) = ‖H s * (x - y)‖ := by
          rw [dist_eq_norm, mul_sub]
      _ ≤ ‖H s‖ * ‖x - y‖ := norm_mul_le _ _
      _ ≤ (M : ℝ) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (hM s (Set.Ioo_subset_Icc_self hs)) (norm_nonneg (x - y))
      _ = M * dist x y := by simp [dist_eq_norm]
  have hres := ODE_solution_unique_of_mem_Ioo
    (v := fun s y => H s * y) (s := fun _ => Set.univ) (K := M)
    (f := f) (g := g) (a := a) (b := b) (t₀ := t₀) hv ht₀
    (fun s hs => ⟨hf s, trivial⟩) (fun s hs => ⟨hg s, trivial⟩) heq
  exact hres ht

/-! ### The multiplicative property -/

/-- `prelim.tex:52`: the multiplicative property
`exp_T H t₁ t₃ = exp_T H t₂ t₃ · exp_T H t₁ t₂`. Both sides solve the ODE `U' = H·U` and agree
at `t₂`, so they are equal by `ode_solution_unique`. -/
lemma timeOrderedExp_mul (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ t₃ : ℝ) :
    timeOrderedExp H t₁ t₃ = timeOrderedExp H t₂ t₃ * timeOrderedExp H t₁ t₂ := by
  have hf : ∀ t, HasDerivAt (fun s => timeOrderedExp H t₁ s) (H t * timeOrderedExp H t₁ t) t :=
    fun t => timeOrderedExp_hasDerivAt H hH t₁ t
  have hg : ∀ t, HasDerivAt (fun s => timeOrderedExp H t₂ s * timeOrderedExp H t₁ t₂)
      (H t * (timeOrderedExp H t₂ t * timeOrderedExp H t₁ t₂)) t := by
    intro t
    simpa [mul_assoc] using
      (timeOrderedExp_hasDerivAt H hH t₂ t).mul_const (timeOrderedExp H t₁ t₂)
  have heq : timeOrderedExp H t₁ t₂ =
      timeOrderedExp H t₂ t₂ * timeOrderedExp H t₁ t₂ := by
    rw [timeOrderedExp_initial H t₂, one_mul]
  exact congr_fun (ode_solution_unique H hH hf hg t₂ heq) t₃

/-! ### Invertibility -/

/-- The inverse evolution: `exp_T H t₁ t₂ · exp_T H t₂ t₁ = 1`. -/
lemma timeOrderedExp_mul_inv_self (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    timeOrderedExp H t₁ t₂ * timeOrderedExp H t₂ t₁ = 1 := by
  have h := timeOrderedExp_mul H hH t₂ t₁ t₂
  rw [timeOrderedExp_initial H t₂] at h
  exact h.symm

/-- The inverse evolution, other side: `exp_T H t₂ t₁ · exp_T H t₁ t₂ = 1`. -/
lemma timeOrderedExp_inv_mul_self (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    timeOrderedExp H t₂ t₁ * timeOrderedExp H t₁ t₂ = 1 := by
  have h := timeOrderedExp_mul H hH t₁ t₂ t₁
  rw [timeOrderedExp_initial H t₁] at h
  exact h.symm

/-- Every time-ordered exponential is a unit. -/
lemma isUnit_timeOrderedExp (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    IsUnit (timeOrderedExp H t₁ t₂) := isUnit_iff_exists.mpr ⟨timeOrderedExp H t₂ t₁,
  timeOrderedExp_mul_inv_self H hH t₁ t₂, timeOrderedExp_inv_mul_self H hH t₁ t₂⟩

/-! ### Constant generator -/

/-- `∫ τ in a..b, (τ - a)^n = (b - a)^(n+1) / (n+1)`. -/
lemma integral_sub_pow (a b : ℝ) (n : ℕ) :
    (∫ τ in a..b, (τ - a) ^ n) = (b - a) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
  have hfun : (fun τ : ℝ => (τ - a) ^ n) = fun τ => (τ + (-a)) ^ n := by
    funext τ
    rw [sub_eq_add_neg]
  rw [hfun, intervalIntegral.integral_comp_add_right (f := fun σ : ℝ => σ ^ n) (d := -a),
    integral_pow]
  simp [sub_eq_add_neg]

/-- For the constant generator, the `n`-th Dyson term is `(n!⁻¹ : ℝ) • ((t - t₁) • H)^n`. -/
lemma dysonTerm_const (H : 𝔸) (t₁ : ℝ) (n : ℕ) (t : ℝ) :
    dysonTerm (fun _ : ℝ => H) t₁ n t = (Nat.factorial n : ℝ)⁻¹ • ((t - t₁) • H) ^ n := by
  induction n generalizing t with
  | zero => simp [dysonTerm]
  | succ n ih =>
      simp_rw [dysonTerm, ih, mul_smul_comm]
      rw [intervalIntegral.integral_smul]
      have hkey : (∫ τ in t₁..t, H * ((τ - t₁) • H) ^ n) =
          ((n + 1 : ℕ) : ℝ)⁻¹ • ((t - t₁) • H) ^ (n + 1) := by
        calc
          (∫ τ in t₁..t, H * ((τ - t₁) • H) ^ n)
              = ∫ τ in t₁..t, (τ - t₁) ^ n • H ^ (n + 1) := by
                  apply intervalIntegral.integral_congr_uIoo
                  intro τ hτ
                  dsimp
                  rw [smul_pow, mul_smul_comm, ← pow_succ']
          _ = (∫ τ in t₁..t, (τ - t₁) ^ n) • H ^ (n + 1) :=
                  intervalIntegral.integral_smul_const (f := fun τ => (τ - t₁) ^ n)
                    (c := H ^ (n + 1))
          _ = (((t - t₁) ^ (n + 1)) / ((n + 1 : ℕ) : ℝ)) • H ^ (n + 1) := by
                  rw [integral_sub_pow t₁ t n]
          _ = ((n + 1 : ℕ) : ℝ)⁻¹ • ((t - t₁) • H) ^ (n + 1) := by
                  rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← smul_pow]
      rw [hkey, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]

/-- `prelim.tex:41` (the paper states the `0 → t` case `e^{tH}`; this is its arbitrary-interval
form): for the constant generator, the time-ordered exponential is the ordinary matrix
exponential `exp ((t₂ - t₁) • H)`. Proved directly from the Dyson series. -/
lemma timeOrderedExp_const (H : 𝔸) (t₁ t₂ : ℝ) :
    timeOrderedExp (fun _ => H) t₁ t₂ = exp ((t₂ - t₁) • H) := by
  rw [timeOrderedExp, NormedSpace.exp_eq_tsum ℝ]
  apply tsum_congr
  intro n
  rw [dysonTerm_const H t₁ n t₂]

/-! ### Derivative with respect to the lower limit -/

/-- `prelim.tex:44-49` (second rule): derivative with respect to the lower limit
`∂/∂t₁ exp_T(∫_{t₁}^{t₂} H) = -exp_T(∫_{t₁}^{t₂} H) · H(t₁)`.

By the inverse relation, `exp_T H s t₂ = (exp_T H t₂ s)⁻¹`, so the result follows from the
derivative of the (ring) inversion `hasFDerivAt_ringInverse` composed with the upper-limit
derivative `timeOrderedExp_hasDerivAt`. -/
lemma timeOrderedExp_hasDerivAt_lower (H : ℝ → 𝔸) (hH : Continuous H) (t₁ t₂ : ℝ) :
    HasDerivAt (fun s => timeOrderedExp H s t₂) (-(timeOrderedExp H t₁ t₂ * H t₁)) t₁ := by
  let u : ℝ → 𝔸ˣ := fun s =>
    ⟨timeOrderedExp H t₂ s, timeOrderedExp H s t₂,
      timeOrderedExp_mul_inv_self H hH t₂ s, timeOrderedExp_inv_mul_self H hH t₂ s⟩
  have hderiv : HasDerivAt (Ring.inverse ∘ fun s => timeOrderedExp H t₂ s)
      (-(timeOrderedExp H t₁ t₂ * H t₁)) t₁ := by
    have H₁ : HasFDerivAt Ring.inverse _ (u t₁ : 𝔸) := hasFDerivAt_ringInverse (𝕜 := ℝ) (u t₁)
    have H₂ : HasDerivAt (fun s => timeOrderedExp H t₂ s) (H t₁ * timeOrderedExp H t₂ t₁) t₁ :=
      timeOrderedExp_hasDerivAt H hH t₂ t₁
    have hu_inv : (((u t₁)⁻¹ : 𝔸ˣ) : 𝔸) = timeOrderedExp H t₁ t₂ := rfl
    simpa [hu_inv, mul_assoc, timeOrderedExp_inv_mul_self H hH t₁ t₂] using
      (H₁.comp_hasDerivAt t₁ H₂)
  have hfun : (fun s => timeOrderedExp H s t₂) = Ring.inverse ∘ fun s => timeOrderedExp H t₂ s := by
    funext s
    have h := Ring.inverse_unit (u s)
    simpa [u] using h.symm
  rwa [hfun]

/-! ### Continuity in the lower limit -/

/-- For continuous `H`, the time-ordered exponential `t ↦ exp_T H t t₂` is continuous in its lower
limit. -/
lemma continuous_timeOrderedExp_lower (H : ℝ → 𝔸) (hH : Continuous H) (t₂ : ℝ) :
    Continuous (fun t => timeOrderedExp H t t₂) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (timeOrderedExp_hasDerivAt_lower H hH t t₂).continuousAt

/-! ### Duhamel / variation of parameters -/

/-- Left multiplication by a constant commutes with the interval integral (for a general normed
ℝ-algebra). -/
lemma integral_mul_left (c : 𝔸) (f : ℝ → 𝔸) (hf : Continuous f) (a b : ℝ) :
    (∫ x in a..b, c * f x) = c * ∫ x in a..b, f x := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    (ContinuousLinearMap.mul ℝ 𝔸 c).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

/-- The Duhamel (variation-of-parameters) particular integral factors through the forward evolution:
`∫ τ in t₀..t, exp_T H τ t · R τ = exp_T H t₀ t · ∫ τ in t₀..t, exp_T H τ t₀ · R τ`, using the
multiplicative property `exp_T H τ t = exp_T H t₀ t · exp_T H τ t₀`. -/
lemma duhamelParticular_factor (H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R)
    (t₀ t : ℝ) :
    (∫ τ in t₀..t, timeOrderedExp H τ t * R τ) =
      timeOrderedExp H t₀ t * ∫ τ in t₀..t, timeOrderedExp H τ t₀ * R τ := by
  calc
    (∫ τ in t₀..t, timeOrderedExp H τ t * R τ)
        = ∫ τ in t₀..t, (timeOrderedExp H t₀ t * timeOrderedExp H τ t₀) * R τ := by
            apply intervalIntegral.integral_congr_uIoo
            intro τ hτ
            simp [timeOrderedExp_mul H hH τ t₀ t]
    _ = ∫ τ in t₀..t, timeOrderedExp H t₀ t * (timeOrderedExp H τ t₀ * R τ) := by
            apply intervalIntegral.integral_congr_uIoo
            intro τ hτ
            simp [mul_assoc]
    _ = timeOrderedExp H t₀ t * ∫ τ in t₀..t, timeOrderedExp H τ t₀ * R τ := integral_mul_left
            (timeOrderedExp H t₀ t) (fun τ => timeOrderedExp H τ t₀ * R τ)
              ((continuous_timeOrderedExp_lower H hH t₀).mul hR) t₀ t

/-- The Duhamel particular solution `t ↦ ∫ τ in t₀..t, exp_T H τ t · R τ` solves the inhomogeneous
ODE with zero initial value: its derivative is `R t + H t · (that integral)`. -/
lemma duhamelParticular_hasDerivAt (H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R)
    (t₀ t : ℝ) :
    HasDerivAt (fun s => ∫ τ in t₀..s, timeOrderedExp H τ s * R τ)
      (R t + H t * ∫ τ in t₀..t, timeOrderedExp H τ t * R τ) t := by
  let Ψ : ℝ → 𝔸 := fun s => ∫ τ in t₀..s, timeOrderedExp H τ t₀ * R τ
  have hfeq : (fun s => ∫ τ in t₀..s, timeOrderedExp H τ s * R τ) =
      fun s => timeOrderedExp H t₀ s * Ψ s := by
    funext s
    exact duhamelParticular_factor H R hH hR t₀ s
  have hΨderiv : HasDerivAt Ψ (timeOrderedExp H t t₀ * R t) t := by
    have hcont : Continuous (fun τ => timeOrderedExp H τ t₀ * R τ) :=
      (continuous_timeOrderedExp_lower H hH t₀).mul hR
    exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable t₀ t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hderiv : HasDerivAt (fun s => timeOrderedExp H t₀ s * Ψ s)
      (H t * (timeOrderedExp H t₀ t * Ψ t) + R t) t := by
    have h1 := (timeOrderedExp_hasDerivAt H hH t₀ t).mul hΨderiv
    have hderiv_eq : (H t * timeOrderedExp H t₀ t) * Ψ t +
          timeOrderedExp H t₀ t * (timeOrderedExp H t t₀ * R t)
        = H t * (timeOrderedExp H t₀ t * Ψ t) + R t := by
      rw [mul_assoc, ← mul_assoc (timeOrderedExp H t₀ t) (timeOrderedExp H t t₀) (R t),
        timeOrderedExp_mul_inv_self H hH t₀ t, one_mul]
    exact hderiv_eq ▸ h1
  rw [hfeq]
  simpa [duhamelParticular_factor H R hH hR t₀ t, add_comm] using hderiv

/-- The closed-form solution of `U' = H · U + R`, `U 0 = U₀`, satisfies the ODE: its derivative is
`H t · (that expression) + R t`. -/
lemma timeOrderedExp_duhamel_hasDerivAt (H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R)
    (U₀ : 𝔸) (t : ℝ) :
    HasDerivAt (fun s => timeOrderedExp H 0 s * U₀ + ∫ τ in 0..s, timeOrderedExp H τ s * R τ)
      (H t * (timeOrderedExp H 0 t * U₀ + ∫ τ in 0..t, timeOrderedExp H τ t * R τ) + R t) t := by
  have hhom := (timeOrderedExp_hasDerivAt H hH 0 t).mul_const U₀
  have hpart := duhamelParticular_hasDerivAt H R hH hR 0 t
  have hsum := hhom.add hpart
  have hderiv_eq : (H t * timeOrderedExp H 0 t) * U₀ +
        (R t + H t * ∫ τ in 0..t, timeOrderedExp H τ t * R τ)
      = H t * (timeOrderedExp H 0 t * U₀ + ∫ τ in 0..t, timeOrderedExp H τ t * R τ) + R t := by
    rw [mul_add, ← mul_assoc]
    abel
  exact hderiv_eq ▸ hsum

omit [CompleteSpace 𝔸] in
/-- The closed-form solution of `U' = H · U + R` has initial value `U₀`. -/
lemma timeOrderedExp_duhamel_initial (H R : ℝ → 𝔸) (U₀ : 𝔸) :
    timeOrderedExp H 0 0 * U₀ + ∫ τ in 0..0, timeOrderedExp H τ 0 * R τ = U₀ := by
  rw [timeOrderedExp_initial H 0, one_mul, intervalIntegral.integral_same, add_zero]

/-- `lem:td_Duhamel` (variation of parameters): the unique solution of `U' = H · U + R`,
`U 0 = U₀`, is `exp_T(∫₀ᵗ H) · U₀ + ∫ τ in 0..t, exp_T(∫_τ^t H) · R τ`. -/
lemma timeOrderedExp_duhamel (H R : ℝ → 𝔸) (hH : Continuous H) (hR : Continuous R)
    {U : ℝ → 𝔸} (U₀ : 𝔸) (hU : ∀ t, HasDerivAt U (H t * U t + R t) t) (hU0 : U 0 = U₀) (t : ℝ) :
    U t = timeOrderedExp H 0 t * U₀ + ∫ τ in 0..t, timeOrderedExp H τ t * R τ := by
  let F : ℝ → 𝔸 := fun s => timeOrderedExp H 0 s * U₀ + ∫ τ in 0..s, timeOrderedExp H τ s * R τ
  have hF : ∀ s, HasDerivAt F (H s * F s + R s) s := by
    intro s
    simpa [F] using timeOrderedExp_duhamel_hasDerivAt H R hH hR U₀ s
  have hF0 : F 0 = U₀ := by
    simpa [F] using timeOrderedExp_duhamel_initial H R U₀
  let d : ℝ → 𝔸 := fun s => U s - F s
  have hd : ∀ s, HasDerivAt d (H s * d s) s := by
    intro s
    have hsub := (hU s).sub (hF s)
    have hderiv_eq : (H s * U s + R s) - (H s * F s + R s) = H s * (U s - F s) := by
      rw [mul_sub]
      abel
    simpa [d] using (hderiv_eq ▸ hsub)
  have hd0 : d 0 = 0 := by
    dsimp [d]
    rw [hU0, hF0, sub_self]
  have hzero : ∀ s, HasDerivAt (fun _ : ℝ => (0 : 𝔸)) (H s * (0 : 𝔸)) s := by
    intro s
    simpa using (hasDerivAt_const (x := s) (c := (0 : 𝔸)))
  have hd_eq_zero : d = fun _ : ℝ => (0 : 𝔸) := ode_solution_unique H hH hd hzero 0 hd0
  have hU_eq_F : U = F := by
    funext s
    have hds : d s = 0 := congr_fun hd_eq_zero s
    exact sub_eq_zero.mp hds
  simpa [F] using congr_fun hU_eq_F t

/-! ### Interaction picture -/

/-- `lem:interaction_picture` (time-ordered evolution in the interaction picture):
`exp_T(∫₀ᵗ (A + B)) = exp_T(∫₀ᵗ A) · exp_T(∫₀ᵗ (exp_T A τ 0 · B τ · exp_T A 0 τ))`. -/
lemma timeOrderedExp_interaction_picture (A B : ℝ → 𝔸) (hA : Continuous A) (hB : Continuous B)
    (t : ℝ) :
    timeOrderedExp (fun τ => A τ + B τ) 0 t =
      timeOrderedExp A 0 t * timeOrderedExp (fun τ =>
        timeOrderedExp A τ 0 * B τ * timeOrderedExp A 0 τ) 0 t := by
  let H : ℝ → 𝔸 := fun τ => A τ + B τ
  let Bt : ℝ → 𝔸 := fun τ => timeOrderedExp A τ 0 * B τ * timeOrderedExp A 0 τ
  have hH : Continuous H := hA.add hB
  have hBt : Continuous Bt :=
    ((continuous_timeOrderedExp_lower A hA 0).mul hB).mul (continuous_timeOrderedExp A hA 0)
  have hUderiv : ∀ s, HasDerivAt (fun r => timeOrderedExp A 0 r * timeOrderedExp Bt 0 r)
      (H s * (timeOrderedExp A 0 s * timeOrderedExp Bt 0 s)) s := by
    intro s
    have h1 := (timeOrderedExp_hasDerivAt A hA 0 s).mul (timeOrderedExp_hasDerivAt Bt hBt 0 s)
    have hkey : (A s * timeOrderedExp A 0 s) * timeOrderedExp Bt 0 s
        + timeOrderedExp A 0 s * (Bt s * timeOrderedExp Bt 0 s)
        = (A s + B s) * (timeOrderedExp A 0 s * timeOrderedExp Bt 0 s) := by
      rw [add_mul]
      congr 1
      · rw [mul_assoc]
      · let E : 𝔸 := timeOrderedExp A 0 s
        let Ei : 𝔸 := timeOrderedExp A s 0
        let F : 𝔸 := timeOrderedExp Bt 0 s
        have hBts : Bt s = Ei * B s * E := rfl
        have hEi : E * Ei = 1 := by
          simpa [E, Ei] using timeOrderedExp_mul_inv_self A hA 0 s
        change E * (Bt s * F) = B s * (E * F)
        rw [hBts]
        calc
          E * ((Ei * B s * E) * F)
              = E * ((Ei * B s) * (E * F)) :=
                  congrArg (fun x => E * x) (mul_assoc (Ei * B s) E F)
          _ = (E * (Ei * B s)) * (E * F) := (mul_assoc E (Ei * B s) (E * F)).symm
          _ = ((E * Ei) * B s) * (E * F) :=
                  congrArg (fun x => x * (E * F)) ((mul_assoc E Ei (B s)).symm)
          _ = B s * (E * F) := by rw [hEi, one_mul]
    simpa [H] using (hkey ▸ h1)
  have hLHSderiv : ∀ s, HasDerivAt (fun r => timeOrderedExp H 0 r) (H s * timeOrderedExp H 0 s) s :=
    fun s => timeOrderedExp_hasDerivAt H hH 0 s
  have hU0 : timeOrderedExp A 0 0 * timeOrderedExp Bt 0 0 = 1 := by
    rw [timeOrderedExp_initial A 0, timeOrderedExp_initial Bt 0, mul_one]
  have huniq := ode_solution_unique H hH hLHSderiv hUderiv 0
    (by rw [timeOrderedExp_initial H 0, hU0])
  simpa [H, Bt] using congr_fun huniq t

/-! ### Fundamental theorem of time-ordered evolution -/

/-- For continuous `H`, the solution `t ↦ exp_T H t₁ t` is `C¹`. -/
lemma contDiff_timeOrderedExp (H : ℝ → 𝔸) (hH : Continuous H) (t₁ : ℝ) :
    ContDiff ℝ 1 (fun t => timeOrderedExp H t₁ t) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro t
    exact (timeOrderedExp_hasDerivAt H hH t₁ t).differentiableAt
  · have hderiv :
        deriv (fun t => timeOrderedExp H t₁ t) = fun t => H t * timeOrderedExp H t₁ t := by
      funext t
      exact (timeOrderedExp_hasDerivAt H hH t₁ t).deriv
    rw [hderiv]
    exact hH.mul (continuous_timeOrderedExp H hH t₁)

/-- (⇒) of `lem:fte`: a `C¹` function that is pointwise a unit is generated by the continuous
generator `H t = deriv U t * Ring.inverse (U t)`. -/
lemma fundamentalTheorem_timeOrderedExp_of_isUnit (U : ℝ → 𝔸) (hU : ContDiff ℝ 1 U)
    (hunit : ∀ t, IsUnit (U t)) :
    IsUnit (U 0) ∧ ∃ H : ℝ → 𝔸, Continuous H ∧ ∀ t, U t = timeOrderedExp H 0 t * U 0 := by
  refine ⟨hunit 0, ?_⟩
  let H : ℝ → 𝔸 := fun t => deriv U t * Ring.inverse (U t)
  have hInvCont : Continuous (fun t => Ring.inverse (U t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (differentiableAt_inverse (𝕜 := ℝ) (hunit t)).continuousAt.comp
      hU.continuous.continuousAt
  have hH : Continuous H := (contDiff_one_iff_deriv.mp hU).2.mul hInvCont
  have hHasDeriv : ∀ t, HasDerivAt U (H t * U t) t := by
    intro t
    have hd : HasDerivAt U (deriv U t) t := ((contDiff_one_iff_deriv.mp hU).1 t).hasDerivAt
    have hkey : (deriv U t * Ring.inverse (U t)) * U t = deriv U t := by
      rw [mul_assoc, Ring.inverse_mul_cancel (U t) (hunit t), mul_one]
    simpa [H, hkey] using hd
  have hTODeriv : ∀ t, HasDerivAt (fun s => timeOrderedExp H 0 s * U 0)
      (H t * (timeOrderedExp H 0 t * U 0)) t := by
    intro t
    simpa [mul_assoc] using (timeOrderedExp_hasDerivAt H hH 0 t).mul_const (U 0)
  have heq0 : U 0 = timeOrderedExp H 0 0 * U 0 := by
    rw [timeOrderedExp_initial H 0, one_mul]
  refine ⟨H, hH, ?_⟩
  intro t
  exact congr_fun (ode_solution_unique H hH hHasDeriv hTODeriv 0 heq0) t

/-- (⇐) of `lem:fte`: `t ↦ exp_T H 0 t · U 0` is `C¹` and pointwise a unit when `U 0` is a unit. -/
lemma fundamentalTheorem_timeOrderedExp_of_timeOrderedExp (U : ℝ → 𝔸) (hU0 : IsUnit (U 0))
    (H : ℝ → 𝔸) (hH : Continuous H) (hEq : ∀ t, U t = timeOrderedExp H 0 t * U 0) :
    ContDiff ℝ 1 U ∧ ∀ t, IsUnit (U t) := by
  refine ⟨?_, ?_⟩
  · have hUfun : U = fun t => timeOrderedExp H 0 t * U 0 := by
      funext t; exact hEq t
    exact hUfun ▸ (contDiff_timeOrderedExp H hH 0).mul contDiff_const
  · intro t
    exact hEq t ▸ (isUnit_timeOrderedExp H hH 0 t).mul hU0

/-- `lem:fte` (fundamental theorem of time-ordered evolution): `U` is `C¹` and pointwise a unit iff
it is `exp_T(∫₀ᵗ H) · U 0` for some continuous `H` and `U 0` is a unit. -/
lemma fundamentalTheorem_timeOrderedExp (U : ℝ → 𝔸) :
    (ContDiff ℝ 1 U ∧ ∀ t, IsUnit (U t)) ↔
      IsUnit (U 0) ∧ ∃ H : ℝ → 𝔸, Continuous H ∧ ∀ t, U t = timeOrderedExp H 0 t * U 0 := by
  constructor
  · rintro ⟨hU, hunit⟩
    exact fundamentalTheorem_timeOrderedExp_of_isUnit U hU hunit
  · rintro ⟨hU0, H, hH, hEq⟩
    exact fundamentalTheorem_timeOrderedExp_of_timeOrderedExp U hU0 H hH hEq

/-- The generator in the fundamental theorem is unique: any two continuous generators `H₁, H₂`
with `U t = exp_T Hᵢ 0 t · U 0` coincide (they both equal `deriv U · Ring.inverse (U ·)`). -/
lemma fundamentalTheorem_timeOrderedExp_unique (U : ℝ → 𝔸) (hU0 : IsUnit (U 0))
    (H₁ H₂ : ℝ → 𝔸) (hH₁ : Continuous H₁) (hH₂ : Continuous H₂)
    (hEq₁ : ∀ t, U t = timeOrderedExp H₁ 0 t * U 0)
    (hEq₂ : ∀ t, U t = timeOrderedExp H₂ 0 t * U 0) :
    H₁ = H₂ := by
  funext t
  have hUt : IsUnit (U t) := hEq₁ t ▸ (isUnit_timeOrderedExp H₁ hH₁ 0 t).mul hU0
  have hderiv₁ : deriv U t = (H₁ t * timeOrderedExp H₁ 0 t) * U 0 := by
    have hUfun₁ : U = fun s => timeOrderedExp H₁ 0 s * U 0 := by
      funext s; exact hEq₁ s
    have h := (timeOrderedExp_hasDerivAt H₁ hH₁ 0 t).mul_const (U 0)
    conv_lhs => rw [hUfun₁]
    exact h.deriv
  have hderiv₂ : deriv U t = (H₂ t * timeOrderedExp H₂ 0 t) * U 0 := by
    have hUfun₂ : U = fun s => timeOrderedExp H₂ 0 s * U 0 := by
      funext s; exact hEq₂ s
    have h := (timeOrderedExp_hasDerivAt H₂ hH₂ 0 t).mul_const (U 0)
    conv_lhs => rw [hUfun₂]
    exact h.deriv
  have hEqU : H₁ t * U t = H₂ t * U t := by
    calc
      H₁ t * U t = (H₁ t * timeOrderedExp H₁ 0 t) * U 0 := by
          rw [hEq₁ t, ← mul_assoc]
      _ = (H₂ t * timeOrderedExp H₂ 0 t) * U 0 := by rw [← hderiv₁, hderiv₂]
      _ = H₂ t * U t := by rw [mul_assoc, ← hEq₂ t]
  have hcancel := congrArg (fun x => x * Ring.inverse (U t)) hEqU
  calc
    H₁ t = H₁ t * U t * Ring.inverse (U t) := by
        rw [mul_assoc, Ring.mul_inverse_cancel (U t) hUt, mul_one]
    _ = H₂ t * U t * Ring.inverse (U t) := hcancel
    _ = H₂ t := by
        rw [mul_assoc, Ring.mul_inverse_cancel (U t) hUt, mul_one]

/-! ### The norm-equals-one branch for skew generators -/

/-- `lem:time_ordered_norm_bound` (item 2): when the generator `H` is pointwise skew-adjoint
(`star (H τ) = -H τ`), the time-ordered exponential is unitary, hence `‖exp_T H t₁ t₂‖ = 1`.
The proof shows `W t := star (U t) * U t` (with `U t := exp_T H t₁ t`) has derivative `0`, so `W`
is constant and `W t₂ = W t₁ = 1`; thus `U t₂` is unitary and the norm follows from the
C*-identity. -/
lemma timeOrderedExp_norm_eq_one_of_skewAdjoint
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : ℝ → 𝔸) (hH : Continuous H) (hskew : ∀ τ, star (H τ) = -H τ) (t₁ t₂ : ℝ) :
    ‖timeOrderedExp H t₁ t₂‖ = 1 := by
  let U : ℝ → 𝔸 := fun t => timeOrderedExp H t₁ t
  let W : ℝ → 𝔸 := fun t => star (U t) * U t
  have hUderiv : ∀ t, HasDerivAt U (H t * U t) t := fun t =>
    timeOrderedExp_hasDerivAt H hH t₁ t
  have hstarUderiv : ∀ t, HasDerivAt (fun s => star (U s)) (star (H t * U t)) t := by
    intro t
    have hcomp : HasDerivAt (((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) ∘ U)
        (((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) (H t * U t)) t :=
      (((starL' ℝ : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸).hasFDerivAt.comp_hasDerivAt t (hUderiv t))
    have hfun : (⇑(starL' ℝ : 𝔸 ≃L[ℝ] 𝔸)) ∘ U = fun s => star (U s) := by
      funext s; simp
    simpa [hfun] using hcomp
  have hWderiv : ∀ t, HasDerivAt W 0 t := by
    intro t
    have hmul : HasDerivAt (fun s => star (U s) * U s)
        (star (H t * U t) * U t + star (U t) * (H t * U t)) t :=
      (hstarUderiv t).mul (hUderiv t)
    have hkey : star (H t * U t) * U t + star (U t) * (H t * U t) = 0 := by
      rw [star_mul, hskew t, mul_assoc, ← mul_add, ← add_mul]
      simp
    simpa [W] using (hkey ▸ hmul)
  have hWdiff : Differentiable ℝ W := fun t => (hWderiv t).differentiableAt
  have hWderiv_eq : ∀ t, deriv W t = 0 := fun t => (hWderiv t).deriv
  have hWconst : W t₂ = W t₁ := is_const_of_deriv_eq_zero hWdiff hWderiv_eq t₂ t₁
  have hWt₁ : W t₁ = 1 := by
    simp [W, U, timeOrderedExp_initial H t₁]
  have hstar_mul_self : star (timeOrderedExp H t₁ t₂) * timeOrderedExp H t₁ t₂ = 1 := by
    simpa [W, U] using hWconst.trans hWt₁
  have hmem : timeOrderedExp H t₁ t₂ ∈ unitary 𝔸 :=
    IsUnit.mem_unitary_of_star_mul_self (isUnit_timeOrderedExp H hH t₁ t₂) hstar_mul_self
  exact CStarRing.norm_of_mem_unitary hmem

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

/-! ### Difference of two time-ordered exponentials -/

/-- `cor:time_ordered_distance_bound` (difference representation): the difference of two
time-ordered exponentials equals the Duhamel integral
`∫ τ in t₁..t₂, exp_T(G,τ,t₂) · (H τ − G τ) · exp_T(H,t₁,τ)`.
The proof runs the `ode_solution_unique` argument on `D − X`, where
`D t = exp_T H t₁ t − exp_T G t₁ t` and
`X t = ∫ τ in t₁..t, exp_T G τ t · (H τ − G τ) · exp_T H t₁ τ`
solve the same inhomogeneous ODE `Y' = G·Y + (H−G)·exp_T H t₁` with the same initial value `0`. -/
lemma timeOrderedExp_sub (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G) (t₁ t₂ : ℝ) :
    timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂ =
      ∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ := by
  let R : ℝ → 𝔸 := fun τ => (H τ - G τ) * timeOrderedExp H t₁ τ
  let D : ℝ → 𝔸 := fun t => timeOrderedExp H t₁ t - timeOrderedExp G t₁ t
  let X : ℝ → 𝔸 := fun t => ∫ τ in t₁..t, timeOrderedExp G τ t * R τ
  have hR : Continuous R := (hH.sub hG).mul (continuous_timeOrderedExp H hH t₁)
  have hD : ∀ t, HasDerivAt D (G t * D t + R t) t := by
    intro t
    have hsub := (timeOrderedExp_hasDerivAt H hH t₁ t).sub (timeOrderedExp_hasDerivAt G hG t₁ t)
    have hderiv_eq : (H t * timeOrderedExp H t₁ t) - (G t * timeOrderedExp G t₁ t)
        = G t * D t + R t := by
      dsimp [D, R]; noncomm_ring
    simpa [D] using (hderiv_eq ▸ hsub)
  have hX : ∀ t, HasDerivAt X (G t * X t + R t) t := by
    intro t
    simpa [X, add_comm] using duhamelParticular_hasDerivAt G R hG hR t₁ t
  have hD0 : D t₁ = 0 := by simp [D, timeOrderedExp_initial]
  have hX0 : X t₁ = 0 := by simp [X]
  let d : ℝ → 𝔸 := fun s => D s - X s
  have hd : ∀ s, HasDerivAt d (G s * d s) s := by
    intro s
    have hderiv_eq : (G s * D s + R s) - (G s * X s + R s) = G s * (D s - X s) := by
      noncomm_ring
    exact hderiv_eq ▸ ((hD s).sub (hX s))
  have hd0 : d t₁ = 0 := by simp [d, hD0, hX0]
  have hzero : ∀ s, HasDerivAt (fun _ : ℝ => (0 : 𝔸)) (G s * (0 : 𝔸)) s := by
    intro s; simpa using hasDerivAt_const s 0
  have hd_eq_zero : d = fun _ : ℝ => (0 : 𝔸) := ode_solution_unique G hG hd hzero t₁ hd0
  have hDt : D t₂ = X t₂ := sub_eq_zero.mp (congr_fun hd_eq_zero t₂)
  calc
    timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂
        = ∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * R τ := hDt
    _ = ∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ := by
            apply intervalIntegral.integral_congr
            intro τ _
            dsimp [R]; rw [← mul_assoc]

/-! ### Distance bounds -/

omit [CompleteSpace 𝔸] in
/-- Pointwise bound for the integrand of the general distance bound: for `τ` in the unordered
interval between `t₁` and `t₂`,
`‖exp_T(G,τ,t₂) · (H τ − G τ) · exp_T(H,t₁,τ)‖ ≤ Real.exp |∫ ‖H‖+‖G‖| · ‖H τ − G τ‖`. -/
lemma norm_timeOrderedExp_sub_integrand_le [NormOneClass 𝔸] (H G : ℝ → 𝔸) (hH : Continuous H)
    (hG : Continuous G) (t₁ t₂ τ : ℝ) (hτ : τ ∈ Set.uIcc t₁ t₂) :
    ‖timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖ ≤
      Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| * ‖H τ - G τ‖ := by
  calc
    ‖timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖
        ≤ ‖timeOrderedExp G τ t₂ * (H τ - G τ)‖ * ‖timeOrderedExp H t₁ τ‖ := norm_mul_le _ _
    _ ≤ ‖timeOrderedExp G τ t₂‖ * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * Real.exp |∫ u in t₁..τ, ‖H u‖| := by
        have hG_le := timeOrderedExp_norm_le G hG τ t₂
        have hH_le := timeOrderedExp_norm_le H hH t₁ τ
        have h1 : ‖timeOrderedExp G τ t₂‖ * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖
            ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖ := by
          have hleft : ‖timeOrderedExp G τ t₂‖ * ‖H τ - G τ‖
              ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ :=
            mul_le_mul_of_nonneg_right hG_le (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right hleft (norm_nonneg _)
        have h2 : Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖
            ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * Real.exp |∫ u in t₁..τ, ‖H u‖| := by
          have hnonneg : 0 ≤ Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ :=
            mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hH_le hnonneg
        exact h1.trans h2
    _ ≤ Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| * ‖H τ - G τ‖ := by
        have hsum : |∫ u in τ..t₂, ‖G u‖| + |∫ u in t₁..τ, ‖H u‖|
            ≤ |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| := by
          have hle : |∫ u in τ..t₂, ‖G u‖| + |∫ u in t₁..τ, ‖H u‖|
              ≤ |∫ u in t₁..t₂, ‖G u‖ + ‖H u‖| :=
            abs_integral_add_le_abs_integral_of_mem_uIcc (f := fun u => ‖G u‖)
              (g := fun u => ‖H u‖) (hf := hG.norm) (hg := hH.norm)
              (hfnn := fun _ => norm_nonneg _) (hgnn := fun _ => norm_nonneg _)
              (a := t₁) (b := t₂) (x := τ) hτ
          have hcomm : (∫ u in t₁..t₂, ‖G u‖ + ‖H u‖) = ∫ u in t₁..t₂, ‖H u‖ + ‖G u‖ := by
            apply intervalIntegral.integral_congr
            intro u _; simp [add_comm]
          simpa [hcomm] using hle
        have hcoef : Real.exp |∫ u in τ..t₂, ‖G u‖| * Real.exp |∫ u in t₁..τ, ‖H u‖|
            ≤ Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| := by
          calc
            Real.exp |∫ u in τ..t₂, ‖G u‖| * Real.exp |∫ u in t₁..τ, ‖H u‖|
                = Real.exp (|∫ u in τ..t₂, ‖G u‖| + |∫ u in t₁..τ, ‖H u‖|) :=
                    (Real.exp_add _ _).symm
            _ ≤ Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| := Real.exp_le_exp_of_le hsum
        calc
          Real.exp |∫ u in τ..t₂, ‖G u‖| * ‖H τ - G τ‖ * Real.exp |∫ u in t₁..τ, ‖H u‖|
              = (Real.exp |∫ u in τ..t₂, ‖G u‖| * Real.exp |∫ u in t₁..τ, ‖H u‖|) *
                  ‖H τ - G τ‖ := by
                  ring
          _ ≤ Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖| * ‖H τ - G τ‖ :=
                  mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

/-- `cor:time_ordered_distance_bound` (item 1, general):
`‖exp_T(∫ H) − exp_T(∫ G)‖ ≤ |∫ ‖H−G‖| · Real.exp |∫ (‖H‖+‖G‖)|`. -/
lemma timeOrderedExp_dist_le [NormOneClass 𝔸] (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G)
    (t₁ t₂ : ℝ) :
    ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖ ≤
      |∫ τ in t₁..t₂, ‖H τ - G τ‖| * Real.exp (|∫ τ in t₁..t₂, ‖H τ‖ + ‖G τ‖|) := by
  let K : ℝ := Real.exp |∫ u in t₁..t₂, ‖H u‖ + ‖G u‖|
  calc
    ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖
        = ‖∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖ := by
            rw [timeOrderedExp_sub H G hH hG t₁ t₂]
    _ ≤ |∫ τ in t₁..t₂, K * ‖H τ - G τ‖| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun τ => timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ)
              (g := fun τ => K * ‖H τ - G τ‖) ?_ ?_
            · rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with τ hτ
              simpa [K] using
                (norm_timeOrderedExp_sub_integrand_le H G hH hG t₁ t₂ τ
                  (Set.uIoc_subset_uIcc hτ))
            · have hcont : Continuous fun τ => K * ‖H τ - G τ‖ := by fun_prop
              exact hcont.intervalIntegrable t₁ t₂
    _ = |∫ τ in t₁..t₂, ‖H τ - G τ‖| * Real.exp (|∫ τ in t₁..t₂, ‖H τ‖ + ‖G τ‖|) := by
            rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
              mul_comm]

/-- `cor:time_ordered_distance_bound` (item 2, skew): when `H` and `G` are pointwise
anti-Hermitian, `‖exp_T(∫ H) − exp_T(∫ G)‖ ≤ |∫ ‖H−G‖|`. -/
lemma timeOrderedExp_dist_le_of_skewAdjoint
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H G : ℝ → 𝔸) (hH : Continuous H) (hG : Continuous G)
    (hHskew : ∀ τ, star (H τ) = -H τ) (hGskew : ∀ τ, star (G τ) = -G τ) (t₁ t₂ : ℝ) :
    ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖ ≤ |∫ τ in t₁..t₂, ‖H τ - G τ‖| := by
  calc
    ‖timeOrderedExp H t₁ t₂ - timeOrderedExp G t₁ t₂‖
        = ‖∫ τ in t₁..t₂, timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖ := by
            rw [timeOrderedExp_sub H G hH hG t₁ t₂]
    _ ≤ |∫ τ in t₁..t₂, ‖H τ - G τ‖| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun τ => timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ)
              (g := fun τ => ‖H τ - G τ‖) ?_ ?_
            · filter_upwards with τ
              calc
                ‖timeOrderedExp G τ t₂ * (H τ - G τ) * timeOrderedExp H t₁ τ‖
                    ≤ ‖timeOrderedExp G τ t₂ * (H τ - G τ)‖ * ‖timeOrderedExp H t₁ τ‖ :=
                        norm_mul_le _ _
                _ ≤ ‖timeOrderedExp G τ t₂‖ * ‖H τ - G τ‖ * ‖timeOrderedExp H t₁ τ‖ :=
                        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
                _ = ‖H τ - G τ‖ := by
                        rw [timeOrderedExp_norm_eq_one_of_skewAdjoint G hG hGskew τ t₂,
                          timeOrderedExp_norm_eq_one_of_skewAdjoint H hH hHskew t₁ τ]
                        simp
            · exact (by fun_prop : Continuous fun τ => ‖H τ - G τ‖).intervalIntegrable t₁ t₂

end TrotterError


-- ===== from FQFP.TrotterError.ExpSMulConj =====
/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/


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


namespace TrotterError

open NormedSpace MeasureTheory
open scoped ContDiff algebraMap

/-- Single conjugation `e^{τA} X e^{-τA} = exp (τ • A) * X * exp ((-τ) • A)`. -/
noncomputable def expSMulConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (τ : ℝ) : 𝔸 :=
  exp (τ • A) * X * exp ((-τ) • A)

/-- `A` commutes with `exp (t • A)`, since both live in the commutative-with-`A` subalgebra
generated by `A`. -/
lemma exp_smul_comm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : 𝔸) (t : ℝ) : Commute A (exp (t • A)) :=
  ((Commute.refl A).smul_right t).exp_right

/-- The conjugation `t ↦ expSMulConj A Y t` is smooth. -/
lemma contDiff_expSMulConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A Y : 𝔸) :
    ContDiff ℝ ∞ (fun t : ℝ => expSMulConj A Y t) := by
  unfold expSMulConj
  exact ((contDiff_exp_smul_const A).mul contDiff_const).mul
    ((contDiff_exp_smul_const A).comp contDiff_neg)

/-- The conjugation `t ↦ expSMulConj A Y t` is continuous. -/
@[fun_prop]
lemma continuous_expSMulConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A Y : 𝔸) :
    Continuous (fun t : ℝ => expSMulConj A Y t) :=
  (contDiff_expSMulConj A Y).continuous

/-- Derivative of the conjugation:
`d/dτ expSMulConj A X τ = expSMulConj A ⁅A, X⁆ τ`
(i.e. `e^{τA} [A, X] e^{-τA}`). -/
theorem expSMulConj_hasDerivAt {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A X : 𝔸) (τ : ℝ) :
    HasDerivAt (fun s => expSMulConj A X s) (expSMulConj A ⁅A, X⁆ τ) τ := by
  have hneg : HasDerivAt (fun s : ℝ => exp ((-s) • A)) (-A * exp ((-τ) • A)) τ := by
    have h := hasDerivAt_exp_smul_const' (-A) τ
    convert h using 2 <;> simp
  have hmain : HasDerivAt (fun s : ℝ => exp (s • A) * X * exp ((-s) • A))
      (exp (τ • A) * (A * X - X * A) * exp ((-τ) • A)) τ := by
    have h' : HasDerivAt (fun s : ℝ => exp (s • A) * X * exp ((-s) • A))
        (((A * exp (τ • A)) * X) * exp ((-τ) • A) +
          (exp (τ • A) * X) * (-A * exp ((-τ) • A))) τ :=
      (hasDerivAt_exp_smul_const' A τ).mul_const X |>.mul hneg
    convert h' using 1
    noncomm_ring [(exp_smul_comm A τ).eq, (exp_smul_comm A (-τ)).eq]
  simpa [expSMulConj, Ring.lie_def] using hmain

/-- Fundamental theorem of calculus for the conjugation:
`expSMulConj A X τ - X = ∫ s in 0..τ, expSMulConj A ⁅A, X⁆ s`. -/
theorem expSMulConj_sub_eq_integral {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A X : 𝔸) (τ : ℝ) :
    expSMulConj A X τ - X = ∫ s in 0..τ, expSMulConj A ⁅A, X⁆ s := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) τ,
      HasDerivAt (fun s => expSMulConj A X s) (expSMulConj A ⁅A, X⁆ x) x :=
    fun x _ => expSMulConj_hasDerivAt A X x
  have hint : IntervalIntegrable (fun s => expSMulConj A ⁅A, X⁆ s) volume 0 τ :=
    (continuous_expSMulConj A ⁅A, X⁆).intervalIntegrable 0 τ
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => expSMulConj A X s) (f' := fun s => expSMulConj A ⁅A, X⁆ s)
    (a := 0) (b := τ) hderiv hint
  rw [h]; simp [expSMulConj]

/-- The `j`-th iterated derivative of `τ ↦ expSMulConj A X τ` is
`τ ↦ expSMulConj A (adPow A j X) τ`. -/
lemma iteratedDeriv_expSMulConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A X : 𝔸) (j : ℕ) :
    iteratedDeriv j (fun τ => expSMulConj A X τ) = fun τ => expSMulConj A (adPow A j X) τ := by
  induction j with
  | zero => simp [iteratedDeriv_zero]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [(expSMulConj_hasDerivAt A (adPow A j X) t).deriv, ad_pow_succ]

/-- The `j`-th iterated derivative of `τ ↦ expSMulConj A X τ` at `0` is `adPow A j X`. -/
theorem iteratedDeriv_expSMulConj_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A X : 𝔸) (j : ℕ) :
    iteratedDeriv j (fun τ => expSMulConj A X τ) 0 = adPow A j X := by
  rw [iteratedDeriv_expSMulConj]; simp [expSMulConj]

/-- At `τ = 0`, the Taylor polynomial `∑_{j<p} (j! : ℝ)⁻¹ • (adPow A j X * 0^j)` equals `X`. -/
lemma taylor_poly_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (p : ℕ) (hp : 1 ≤ p) :
    (∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X * (0 : 𝔸) ^ j)) = X := by
  simpa [adPow] using (Finset.sum_eq_single_of_mem (s := Finset.range p)
    (a := 0) (f := fun j => (Nat.factorial j : ℝ)⁻¹ • (adPow A j X * (0 : 𝔸) ^ j))
    (Finset.mem_range.mpr (lt_of_lt_of_le zero_lt_one hp))
    (by intro b _ hb0; rw [zero_pow hb0, mul_zero, smul_zero]))

/-- Single-layer Taylor expansion (theory.tex:137-150):
`expSMulConj A X τ = Σ_{j<p} adPow A j X τ^j/j! +
  ∫₀^τ expSMulConj A (adPow A p X) (τ-s) s^{p-1}/(p-1)!`. -/
theorem expSMulConj_taylor {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A X : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    expSMulConj A X τ =
      (∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X) * (τ ^ j : 𝔸))
      + ∫ s in 0..τ, expSMulConj A (adPow A p X) (τ - s) *
          ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸) := by
  let f : ℝ → 𝔸 := fun s => expSMulConj A X s
  let Y : 𝔸 := adPow A p X
  have hf : ContDiff ℝ ∞ f := contDiff_expSMulConj A X
  by_cases hτ : τ = 0
  · subst τ
    simp only [expSMulConj, zero_smul, neg_zero, exp_zero, one_mul, mul_one,
      intervalIntegral.integral_same, add_zero, smul_mul_assoc, map_zero]
    exact (taylor_poly_zero A X p hp).symm
  · have hud : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) τ) := uniqueDiffOn_uIcc (Ne.symm hτ)
    have hfOn : ContDiffOn ℝ p f (Set.uIcc (0 : ℝ) τ) :=
      (hf.contDiffOn.mono (Set.subset_univ _)).of_le (mod_cast le_top)
    have hTaylor := taylor_integral_remainder (f := f) (x₀ := 0) (x := τ) (n := p - 1)
      (by simpa [Nat.sub_add_cancel hp] using hfOn)
    rw [Nat.sub_add_cancel hp] at hTaylor
    have hTaylor' : f τ = taylorWithinEval f (p - 1) (Set.uIcc (0 : ℝ) τ) 0 τ
        + ∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
            iteratedDerivWithin p f (Set.uIcc (0 : ℝ) τ) s := by
      rw [← hTaylor]
      abel
    have hpoly : taylorWithinEval f (p - 1) (Set.uIcc (0 : ℝ) τ) 0 τ
        = ∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X) * (τ ^ j : 𝔸) := by
      rw [taylor_within_apply, Nat.sub_add_cancel hp]
      simp only [sub_zero]
      apply Finset.sum_congr rfl
      intro j _
      rw [iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le (mod_cast le_top))
        (by simp)]
      rw [iteratedDeriv_expSMulConj_zero, pow_smul_eq_smul_mul]
    have hintegral : (∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
          iteratedDerivWithin p f (Set.uIcc (0 : ℝ) τ) s) =
        ∫ s in 0..τ, expSMulConj A Y (τ - s) *
          ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸) := by
      calc
        (∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
              iteratedDerivWithin p f (Set.uIcc (0 : ℝ) τ) s)
            = ∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
                iteratedDeriv p f s := by
                apply intervalIntegral.integral_congr_uIoo
                intro s hs
                change ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
                    iteratedDerivWithin p f (Set.uIcc (0 : ℝ) τ) s =
                  ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • iteratedDeriv p f s
                rw [iteratedDerivWithin_eq_iteratedDeriv hud
                  (hf.contDiffAt.of_le (mod_cast le_top)) (Set.uIoo_subset_uIcc_self hs)]
        _ = ∫ s in 0..τ, ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) •
              expSMulConj A Y s := by
                apply intervalIntegral.integral_congr_uIoo
                intro s _
                change ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • iteratedDeriv p f s =
                  ((τ - s) ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • expSMulConj A Y s
                rw [show iteratedDeriv p f s = expSMulConj A Y s by
                  simpa [f, Y] using congr_fun (iteratedDeriv_expSMulConj A X p) s]
        _ = ∫ s in 0..τ, expSMulConj A Y (τ - s) *
              ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸) :=
                integral_smul_eq_integral_mul_sub (fun s => expSMulConj A Y s) (p - 1) τ
    change f τ = (∑ j ∈ Finset.range p, (Nat.factorial j : ℝ)⁻¹ • (adPow A j X) * (τ ^ j : 𝔸))
      + ∫ s in 0..τ, expSMulConj A (adPow A p X) (τ - s) *
          ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)
    rw [hTaylor', hpoly, hintegral]

/-- The norm of a single conjugation is bounded by `‖Y‖ * exp (2 * |t| * ‖A‖)`. -/
theorem norm_expSMulConj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormOneClass 𝔸] (A Y : 𝔸) (t : ℝ) :
    ‖expSMulConj A Y t‖ ≤ ‖Y‖ * Real.exp (2 * |t| * ‖A‖) := by
  calc
    ‖exp (t • A) * Y * exp ((-t) • A)‖
        ≤ ‖exp (t • A)‖ * ‖Y‖ * ‖exp ((-t) • A)‖ :=
            (norm_mul_le (exp (t • A) * Y) (exp ((-t) • A))).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le (exp (t • A)) Y) (norm_nonneg _))
    _ ≤ Real.exp (|t| * ‖A‖) * ‖Y‖ * Real.exp (|t| * ‖A‖) := by
            have h1 : ‖exp (t • A)‖ ≤ Real.exp (|t| * ‖A‖) := by
              simpa [norm_smul] using norm_exp_le (t • A)
            have h2 : ‖exp ((-t) • A)‖ ≤ Real.exp (|t| * ‖A‖) := by
              simpa [norm_smul] using norm_exp_le ((-t) • A)
            exact mul_le_mul (mul_le_mul h1 (le_refl ‖Y‖) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
    _ = ‖Y‖ * Real.exp (2 * |t| * ‖A‖) := by
            calc
              Real.exp (|t| * ‖A‖) * ‖Y‖ * Real.exp (|t| * ‖A‖)
                  = ‖Y‖ * (Real.exp (|t| * ‖A‖) * Real.exp (|t| * ‖A‖)) := by ring
              _ = ‖Y‖ * Real.exp (|t| * ‖A‖ + |t| * ‖A‖) := by rw [Real.exp_add]
              _ = ‖Y‖ * Real.exp (2 * |t| * ‖A‖) := by ring_nf

/-- The norm of a single conjugation is at most `‖X‖` when `A` is anti-Hermitian (the exponential
factors are unitary). -/
lemma norm_expSMulConj_le_of_skewAdjoint {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    [CompleteSpace 𝔸] (A X : 𝔸) (hskew : star A = -A) (u : ℝ) :
    ‖expSMulConj A X u‖ ≤ ‖X‖ := by
  unfold expSMulConj
  have h1 : ‖exp (u • A) * X‖ ≤ ‖X‖ := by
    simpa [norm_exp_smul_of_skewAdjoint hskew u] using norm_mul_le (exp (u • A)) X
  have h2 : ‖exp (-u • A)‖ ≤ 1 := (norm_exp_smul_of_skewAdjoint hskew (-u)).le
  calc
    ‖exp (u • A) * X * exp (-u • A)‖
        ≤ ‖exp (u • A) * X‖ * ‖exp (-u • A)‖ := norm_mul_le _ _
    _ ≤ ‖X‖ * 1 := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg X)
    _ = ‖X‖ := by rw [mul_one]

/-- Norm bound of the single-layer remainder (theory.tex:151-155):
`‖∫₀^τ expSMulConj A (adPow A p X) (τ-s) * s^{p-1}/(p-1)!‖ ≤
  ‖adPow A p X‖ * |τ|^p/p! * e^{2|τ|‖A‖}`. -/
theorem norm_expSMulConj_remainder_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (A X : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    ‖∫ s in 0..τ, expSMulConj A (adPow A p X) (τ - s) *
        ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖
      ≤ ‖adPow A p X‖ * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ‖A‖) := by
  let Y : 𝔸 := adPow A p X
  let C : ℝ := ‖Y‖ * Real.exp (2 * |τ| * ‖A‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg Y) (Real.exp_nonneg _)
  have hpoint : ∀ s ∈ Set.uIoc (0 : ℝ) τ,
      ‖expSMulConj A Y (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖
        ≤ C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) := by
    intro s hs
    have habs : |τ - s| ≤ |τ| :=
      (by simpa [sub_zero] using Set.abs_sub_right_of_mem_uIcc (Set.uIoc_subset_uIcc hs))
    have hsmul : expSMulConj A Y (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸) =
        (s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • expSMulConj A Y (τ - s) :=
      (smul_eq_mul_right (s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) (expSMulConj A Y (τ - s))).symm
    have hnormY : ‖expSMulConj A Y (τ - s)‖ ≤ ‖Y‖ * Real.exp (2 * |τ| * ‖A‖) := by
      refine (norm_expSMulConj_le A Y (τ - s)).trans ?_
      have harg : 2 * |τ - s| * ‖A‖ ≤ 2 * |τ| * ‖A‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs (by norm_num)) (norm_nonneg A)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (norm_nonneg Y)
    calc
      ‖expSMulConj A Y (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖
          = ‖(s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) • expSMulConj A Y (τ - s)‖ := by rw [hsmul]
      _ = |s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)| * ‖expSMulConj A Y (τ - s)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) * ‖expSMulConj A Y (τ - s)‖ := by
            rw [abs_div, abs_pow, abs_of_pos (by positivity : 0 < (Nat.factorial (p - 1) : ℝ))]
      _ ≤ (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) *
            (‖Y‖ * Real.exp (2 * |τ| * ‖A‖)) := by gcongr
      _ = C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) := by dsimp [C]; ring
  have hcont_g : Continuous (fun s : ℝ => C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))) := by
    fun_prop
  calc
    ‖∫ s in 0..τ, expSMulConj A Y (τ - s) * ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸)‖
        ≤ |∫ s in 0..τ, C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun s => expSMulConj A Y (τ - s) *
                ((s ^ (p - 1) / (Nat.factorial (p - 1) : ℝ)) : 𝔸))
              (g := fun s => C * (|s| ^ (p - 1) / (Nat.factorial (p - 1) : ℝ))) ?_ ?_
            · rw [ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with s hs
              exact hpoint s hs
            · exact hcont_g.intervalIntegrable 0 τ
    _ = C * (|τ| ^ p / (Nat.factorial p : ℝ)) := by
            rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hC,
              abs_integral_abs_pow_div_factorial p τ hp]
    _ = ‖Y‖ * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ‖A‖) := by dsimp [C]; ring

/-- The single conjugation `expSMulConj A · τ` as an ℝ-linear endomorphism of `𝔸`. -/
noncomputable def expSMulConjLin {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : 𝔸)
    (τ : ℝ) : 𝔸 →ₗ[ℝ] 𝔸 where
  toFun := fun X => expSMulConj A X τ
  map_add' _ _ := by unfold expSMulConj; noncomm_ring
  map_smul' _ _ := by simp [expSMulConj]

end TrotterError


-- ===== from FQFP.TrotterError.CommutatorExpansion =====
/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/



/-!
# Multi-layer conjugation: commutator expansion and remainder norm bounds

The multi-layer conjugation results for the Trotter error theory (arXiv:1912.08854): the
commutator expansion of `e^{τA_s} ⋯ e^{τA_1} B e^{-τA_1} ⋯ e^{-τA_s}` and the norm bounds
of its remainder (theory.tex:184-249).

## Main definitions

* `multiConj`: the multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA₀} B e^{-τA₀}⋯e^{-τA_{s-1}}`.
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


namespace TrotterError

open NormedSpace MeasureTheory Finset
open TrotterError.List
open scoped ContDiff algebraMap

/-! ### Multi-layer conjugation `thm:comm_exp_conj` -/

/-- The multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA₀} B e^{-τA₀}⋯e^{-τA_{s-1}}`, where
`A ⟨0⟩` is innermost (the paper's `A₁`, applied first) and `A ⟨s-1⟩` is outermost (the paper's
`A_s`). -/
noncomputable def multiConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) : 𝔸 :=
  (List.ofFn (fun i : Fin s => exp (τ • A i))).reverse.prod * B *
    (List.ofFn (fun i : Fin s => exp (-τ • A i))).prod

/-- The single `(j, q)` summand of `commutatorRemainder`. -/
@[irreducible]
noncomputable def commutatorRemainderTerm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) : 𝔸 :=
  ((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod *
    (∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
      expSMulConj (A j) (adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B) u) *
    ((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod

/-- The operator-valued remainder `𝒞(τ)` of `thm:comm_exp_conj` (theory.tex:229-235). The outer
sum runs over 0-based layer indices `j : Fin s` with `k := j + 1` the 1-based index of the paper,
so `A j` is `A_k`, the antidiagonal condition `q₁ + ⋯ + q_k = p` is `q ∈ finAntidiagonal (j + 1) p`
with `q (Fin.last j) = q_k`, and `q_k ≠ 0` is `q (Fin.last j) ≠ 0`. The `ad` sequence is
`adSequence (A ∘ Fin.castLE …) q B = ad_{A_k}^{q_k} ⋯ ad_{A₁}^{q₁}(B)`. -/
noncomputable def commutatorRemainder {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : 𝔸 :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    commutatorRemainderTerm A B τ j q

/-- The `τ^j` coefficient of the multi-layer conjugation, as the multinomial-weighted sum
`Σ_{q ∈ finAntidiagonal s j} (∏ i, q_i!⁻¹) • adSequence A q B`. -/
noncomputable def conjCoeff {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (j : ℕ) : 𝔸 :=
  ∑ q ∈ finAntidiagonal s j,
    ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A q B

/-! ### Norm bounds for `thm:comm_exp_conj` -/

/-- The integral-norm estimation shared by the general and skew-adjoint remainder bounds: given a
nonnegative `C` and a pointwise bound for the smul'd conjugation, the beta integral yields
`C * |τ|^m / D * |τ|^q / q`. -/
lemma norm_integral_smul_conj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ ≤
      C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
  have hcont_g : Continuous (fun u : ℝ => C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) := by
    fun_prop
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖
        ≤ |∫ u in 0..τ, C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun u => (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
                (expSMulConj A X u))
              (g := fun u => C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) ?_ ?_
            · rw [ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with u hu
              exact hpoint u hu
            · exact hcont_g.intervalIntegrable 0 τ
    _ = C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
            rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
            have hnonneg : 0 ≤ (∫ u in Set.uIoc (0 : ℝ) τ,
                C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) :=
              setIntegral_nonneg measurableSet_uIoc (fun u _ => by positivity)
            rw [abs_of_nonneg hnonneg]
            have hint : (∫ u in Set.uIoc (0 : ℝ) τ, (|τ - u| ^ (q - 1) * |τ| ^ m / D)) =
                (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
              calc
                (∫ u in Set.uIoc (0 : ℝ) τ, (|τ - u| ^ (q - 1) * |τ| ^ m / D))
                    = (∫ u in Set.uIoc (0 : ℝ) τ, (|τ| ^ m / D) * |τ - u| ^ (q - 1)) := by
                        apply setIntegral_congr_fun measurableSet_uIoc
                        intro u _
                        ring
                _ = (|τ| ^ m / D) * (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1)) := by
                        rw [integral_const_mul]
                _ = (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
                        rw [integral_abs_sub_pow_uIoc q τ hq]
            rw [integral_const_mul, hint]
            ring

/-- The norm of the `expSMulConj` integral is bounded by `C · |τ|^(q+m) / (q · D)` whenever the
conjugation is pointwise bounded by `C`. Shared by the general and skew-adjoint branches. -/
lemma norm_conj_smul_integral_le_of_norm_conj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hconj : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖expSMulConj A X u‖ ≤ C) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤
      C * |τ| ^ (q + m) / ((q : ℝ) * D) := by
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by
    intro u hu
    have habs : |(τ - u) ^ (q - 1) * τ ^ m / D| = |τ - u| ^ (q - 1) * |τ| ^ m / D := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_nonneg (le_of_lt hD)]
    have hsmul : ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ =
        (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖expSMulConj A X u‖ := by
      rw [norm_smul, Real.norm_eq_abs, habs]
    calc
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
          = (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖expSMulConj A X u‖ := hsmul
      _ ≤ (|τ - u| ^ (q - 1) * |τ| ^ m / D) * C :=
              mul_le_mul_of_nonneg_left (hconj u hu) (by positivity)
      _ = C * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by ring
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) :=
            norm_integral_smul_conj_le A X q m D hq hD τ C hC hpoint
    _ = C * |τ| ^ (q + m) / ((q : ℝ) * D) := by
            have hq_ne : (q : ℝ) ≠ 0 := by positivity
            have hDne : D ≠ 0 := ne_of_gt hD
            field_simp [hq_ne, hDne]
            ring

/-- The norm of the integral in one remainder summand is bounded by `‖X‖ · |τ|^(q+m) / (q · D) ·
e^{2|τ|‖A‖}`. Here the integrand is `((τ-u)^(q-1) · τ^m / D) • (e^{uA} X e^{-uA})`. -/
lemma norm_conj_smul_integral_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * |τ| * ‖A‖) := by
  let C : ℝ := ‖X‖ * Real.exp (2 * |τ| * ‖A‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg X) (Real.exp_nonneg _)
  have hconj : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖expSMulConj A X u‖ ≤ C := by
    intro u hu
    refine (norm_expSMulConj_le A X u).trans ?_
    have harg : 2 * |u| * ‖A‖ ≤ 2 * |τ| * ‖A‖ := by
      have habs_u : |u| ≤ |τ| := by
        simpa using Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hu)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs_u (by norm_num))
        (norm_nonneg A)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (norm_nonneg X)
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * |τ| ^ (q + m) / ((q : ℝ) * D) :=
            norm_conj_smul_integral_le_of_norm_conj_le A X q m D hq hD τ C hC hconj
    _ = ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * |τ| * ‖A‖) := by
            dsimp [C]
            ring_nf

/-- For `0 ≤ τ` and `u ∈ [0, -τ]`, the absorbed conjugation `e^{τA} e^{uA} X e^{-uA}` has norm
at most `‖X‖ · e^{τ‖A‖}`: the two inner exponentials `e^{(τ+u)A}` and `e^{-uA}` telescope to a
single factor of `τ`. -/
lemma norm_exp_mul_expSMulConj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (τ u : ℝ) (hτ : 0 ≤ τ)
    (hu : u ∈ Set.uIcc (0 : ℝ) (-τ)) :
    ‖exp (τ • A) * expSMulConj A X u‖ ≤ ‖X‖ * Real.exp (τ * ‖A‖) := by
  have hu' : u ∈ Set.uIcc (-τ) (0 : ℝ) := by simpa [Set.uIcc_comm] using hu
  have hu'' : u ∈ Set.Icc (-τ) (0 : ℝ) := by
    rwa [Set.uIcc_of_le (neg_nonpos.mpr hτ)] at hu'
  have hge : -τ ≤ u := hu''.1
  have hle0 : u ≤ 0 := hu''.2
  have hτu : 0 ≤ τ + u := by linarith
  have hcomm : Commute (τ • A) (u • A) := (Commute.refl A).smul_left τ |>.smul_right u
  have h_exp : exp (τ • A) * exp (u • A) = exp ((τ + u) • A) := by
    rw [add_smul τ u A]
    exact (exp_add_of_commute hcomm).symm
  have h_prod : exp (τ • A) * expSMulConj A X u = exp ((τ + u) • A) * X * exp (-u • A) := by
    rw [expSMulConj, ← mul_assoc, ← mul_assoc, h_exp]
  have h1 : ‖exp ((τ + u) • A)‖ ≤ Real.exp ((τ + u) * ‖A‖) := by
    have hnorm : ‖(τ + u) • A‖ = (τ + u) * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτu]
    simpa [hnorm] using norm_exp_le ((τ + u) • A)
  have h2 : ‖exp (-u • A)‖ ≤ Real.exp ((-u) * ‖A‖) := by
    have hnorm : ‖u • A‖ = (-u) * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hle0]
    simpa [hnorm] using norm_exp_le (-u • A)
  calc
    ‖exp (τ • A) * expSMulConj A X u‖
        = ‖exp ((τ + u) • A) * X * exp (-u • A)‖ := by rw [h_prod]
    _ ≤ ‖exp ((τ + u) • A)‖ * ‖X‖ * ‖exp (-u • A)‖ := by
            exact (norm_mul_le (exp ((τ + u) • A) * X) (exp (-u • A))).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le (exp ((τ + u) • A)) X) (norm_nonneg _))
    _ ≤ Real.exp ((τ + u) * ‖A‖) * ‖X‖ * Real.exp ((-u) * ‖A‖) := by
            exact mul_le_mul (mul_le_mul h1 (le_refl ‖X‖) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
    _ = ‖X‖ * Real.exp (τ * ‖A‖) := by
            have harg : (τ + u) * ‖A‖ + (-u) * ‖A‖ = τ * ‖A‖ := by ring
            calc
              Real.exp ((τ + u) * ‖A‖) * ‖X‖ * Real.exp ((-u) * ‖A‖)
                  = ‖X‖ * (Real.exp ((τ + u) * ‖A‖) * Real.exp ((-u) * ‖A‖)) := by ring
              _ = ‖X‖ * Real.exp ((τ + u) * ‖A‖ + (-u) * ‖A‖) := by rw [Real.exp_add]
              _ = ‖X‖ * Real.exp (τ * ‖A‖) := by rw [harg]

/-- The norm of the integral of the *absorbed* conjugation `e^{τA} e^{uA} X e^{-uA}` times the
scalar `(-τ-u)^(q-1) (-τ)^m / D` is bounded by `‖X‖ |τ|^(q+m)/(q·D) e^{τ‖A‖}` — one factor of
`τ` instead of the naive `2|τ|`. -/
lemma norm_absorbed_conj_smul_integral_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (q m : ℕ) (D : ℝ)
    (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖∫ u in 0..(-τ), (((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
        (exp (τ • A) * expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (τ * ‖A‖) := by
  let C : ℝ := ‖X‖ * Real.exp (τ * ‖A‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg X) (Real.exp_nonneg _)
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) (-τ),
      ‖(((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) • (exp (τ • A) * expSMulConj A X u)‖
        ≤ C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) := by
    intro u hu
    have habs : |(-τ - u) ^ (q - 1) * (-τ) ^ m / D| = |-τ - u| ^ (q - 1) * |-τ| ^ m / D := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_nonneg (le_of_lt hD)]
    have hsmul : ‖(((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
        (exp (τ • A) * expSMulConj A X u)‖ =
        (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) * ‖exp (τ • A) * expSMulConj A X u‖ := by
      rw [norm_smul, Real.norm_eq_abs, habs]
    have hconj : ‖exp (τ • A) * expSMulConj A X u‖ ≤ C :=
      norm_exp_mul_expSMulConj_le A X τ u hτ (Set.uIoc_subset_uIcc hu)
    calc
      ‖(((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) • (exp (τ • A) * expSMulConj A X u)‖
          = (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) * ‖exp (τ • A) * expSMulConj A X u‖ := hsmul
      _ ≤ (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) * C := by gcongr
      _ = C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) := by ring
  have hcont_g : Continuous (fun u : ℝ => C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)) := by
    fun_prop
  calc
    ‖∫ u in 0..(-τ), (((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
        (exp (τ • A) * expSMulConj A X u)‖
        ≤ |∫ u in 0..(-τ), C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun u => (((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
                (exp (τ • A) * expSMulConj A X u))
              (g := fun u => C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)) ?_ ?_
            · rw [ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with u hu
              exact hpoint u hu
            · exact hcont_g.intervalIntegrable 0 (-τ)
    _ = C * (|-τ| ^ m / D) * (|-τ| ^ q / (q : ℝ)) := by
            rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
            have hnonneg : 0 ≤ (∫ u in Set.uIoc (0 : ℝ) (-τ),
                C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)) :=
              setIntegral_nonneg measurableSet_uIoc (fun u _ => by positivity)
            rw [abs_of_nonneg hnonneg]
            have hint : (∫ u in Set.uIoc (0 : ℝ) (-τ), (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)) =
                (|-τ| ^ m / D) * (|-τ| ^ q / (q : ℝ)) := by
              calc
                (∫ u in Set.uIoc (0 : ℝ) (-τ), (|-τ - u| ^ (q - 1) * |-τ| ^ m / D))
                    = (∫ u in Set.uIoc (0 : ℝ) (-τ), (|-τ| ^ m / D) * |-τ - u| ^ (q - 1)) := by
                        apply setIntegral_congr_fun measurableSet_uIoc
                        intro u _
                        ring
                _ = (|-τ| ^ m / D) * (∫ u in Set.uIoc (0 : ℝ) (-τ), |-τ - u| ^ (q - 1)) := by
                        rw [integral_const_mul]
                _ = (|-τ| ^ m / D) * (|-τ| ^ q / (q : ℝ)) := by
                        rw [integral_abs_sub_pow_uIoc q (-τ) hq]
            rw [integral_const_mul, hint]
            ring
    _ = ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (τ * ‖A‖) := by
            dsimp [C]
            have hq_ne : (q : ℝ) ≠ 0 := by positivity
            have hDne : D ≠ 0 := ne_of_gt hD
            rw [abs_neg]
            field_simp [hq_ne, hDne]
            ring

/-- Peeling the last entry off the prefix `(ofFn f).take (j+1)`: its product is the product of
`(ofFn f).take j` times `f j`. -/
lemma ofFn_take_succ_prod {s : ℕ} {𝔸 : Type*} [Monoid 𝔸] (f : Fin s → 𝔸) (j : Fin s) :
    ((List.ofFn f).take ((j : ℕ) + 1)).prod = ((List.ofFn f).take (j : ℕ)).prod * f j := by
  have htake : (List.ofFn f).take ((j : ℕ) + 1) = (List.ofFn f).take (j : ℕ) ++ [f j] := by
    rw [← List.take_concat_get' (List.ofFn f) (j : ℕ) (by simp)]
    simp [List.getElem_ofFn]
  rw [htake, List.prod_append, List.prod_singleton]

/-- The telescoping `(∏_k e^{τA_k}) · (e^{-τA_{s-1}} ⋯ e^{-τA_{j+1}}) = e^{τA_0} ⋯ e^{τA_j}`: the
outer exponential factors beyond layer `j` cancel against the reversed dropped suffix. -/
lemma prod_exp_mul_drop_reverse_telescope {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) :
    (List.ofFn (fun k : Fin s => exp (τ • A k))).prod *
      (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod
      = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod := by
  have hsplit : (List.ofFn (fun k : Fin s => exp (τ • A k))).prod =
      ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod *
        ((List.ofFn (fun k : Fin s => exp (τ • A k))).drop ((j : ℕ) + 1)).prod := by
    simpa only [List.prod_append] using
      (congrArg List.prod (List.take_append_drop ((j : ℕ) + 1)
        (List.ofFn (fun k : Fin s => exp (τ • A k))))).symm
  have hcancel : ((List.ofFn (fun k : Fin s => exp (τ • A k))).drop ((j : ℕ) + 1)).prod *
      (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod = 1 := by
    have hmapL : ((List.ofFn (fun k : Fin s => exp (τ • A k))).drop ((j : ℕ) + 1)) =
        (((List.ofFn A).drop ((j : ℕ) + 1)).map (fun x : 𝔸 => exp (τ • x))) := by
      rw [List.ofFn_comp' A (fun x => exp (τ • x)), ← List.map_drop]
    have hmapR : (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse) =
        ((((List.ofFn A).drop ((j : ℕ) + 1)).map (fun x : 𝔸 => exp (-τ • x))).reverse) := by
      rw [List.ofFn_comp' A (fun x => exp (-τ • x)), ← List.map_drop]
    rw [hmapL, hmapR]
    simpa [List.map_reverse] using prod_mul_rev_eq_one_of_mul_eq_one
      (l := (List.ofFn A).drop ((j : ℕ) + 1))
      (f := fun x : 𝔸 => exp (τ • x))
      (g := fun x : 𝔸 => exp (-τ • x))
      (hfg := fun x => by simpa [neg_smul] using exp_mul_neg_self (τ • x))
  calc
    (List.ofFn (fun k : Fin s => exp (τ • A k))).prod *
      (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod
        = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod *
            ((List.ofFn (fun k : Fin s => exp (τ • A k))).drop ((j : ℕ) + 1)).prod *
            (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod := by
              rw [hsplit]
    _ = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod * 1 := by
              rw [mul_assoc, hcancel]
    _ = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod := by rw [mul_one]

/-- The product of the norms of exponentials `∏ᵢ ‖exp (tᵢ • Aᵢ)‖` is bounded by
`exp (Σᵢ |tᵢ| · ‖Aᵢ‖)`. -/
lemma norm_prod_exp_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {ι : Type*} (l : List ι)
    (A : ι → 𝔸) (t : ι → ℝ) :
    (l.map (fun i => ‖exp (t i • A i)‖)).prod ≤
      Real.exp ((l.map (fun i => |t i| * ‖A i‖)).sum) := by
  calc
    (l.map (fun i => ‖exp (t i • A i)‖)).prod
        ≤ (l.map (fun i => Real.exp (|t i| * ‖A i‖))).prod := by
            have hle : ∀ i ∈ l, ‖exp (t i • A i)‖ ≤ Real.exp (|t i| * ‖A i‖) := by
              intro i _
              simpa [norm_smul] using norm_exp_le (t i • A i)
            have hnonneg : ∀ i ∈ l, 0 ≤ ‖exp (t i • A i)‖ := by
              intro i _
              exact norm_nonneg (exp (t i • A i))
            exact List.prod_map_le_prod_map₀
              (f := fun i => ‖exp (t i • A i)‖)
              (g := fun i => Real.exp (|t i| * ‖A i‖))
              (s := l) hnonneg hle
    _ = Real.exp ((l.map (fun i => |t i| * ‖A i‖)).sum) := by
            rw [Real.exp_list_sum, List.map_map]
            rfl

/-- The norm of the product of `exp (τ • A i)` over a sublist `l` of `Fin s` is bounded by
`exp (|τ| * (l.map ‖A ·‖).sum)`. -/
lemma norm_prod_exp_smul_list_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {s : ℕ} (A : Fin s → 𝔸) (l : List (Fin s)) (τ : ℝ) :
    ‖(l.map (fun i => exp (τ • A i))).prod‖ ≤
      Real.exp (|τ| * (l.map (fun i => ‖A i‖)).sum) := by
  have h := norm_prod_exp_smul_le (l := l) (A := A) (t := fun _ : Fin s => τ)
  calc
    ‖(l.map (fun i => exp (τ • A i))).prod‖
        ≤ (l.map (fun i => ‖exp (τ • A i)‖)).prod := by
            simpa [List.map_map, Function.comp_def] using
              List.norm_prod_le (l.map (fun i => exp (τ • A i)))
    _ ≤ Real.exp ((l.map (fun i => |τ| * ‖A i‖)).sum) := h
    _ = Real.exp (|τ| * (l.map (fun i => ‖A i‖)).sum) := by rw [List.sum_map_mul_left]

/-- The norm of the outer (left) exponential product of a remainder summand is bounded by
`exp (Σ_{i ≥ k} |τ| · ‖A i‖)`, expressed as a `List` sum over the dropped suffix. -/
lemma norm_ofFn_drop_reverse_prod_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) :
    ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := by
  have h := norm_prod_exp_smul_le (l := (List.ofFn (fun i : Fin s => i)).drop k)
    (A := A) (t := fun _ : Fin s => τ)
  have hmap : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => ‖exp (τ • A i)‖) =
      (List.ofFn (fun i : Fin s => ‖exp (τ • A i)‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  have hmap' : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => |τ| * ‖A i‖) =
      (List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  rw [hmap, hmap'] at h
  calc
    ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.prod‖
        ≤ (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.map
            (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
    _ = (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map
            (fun x : 𝔸 => ‖x‖)).prod := by
            rw [List.map_reverse, List.prod_reverse]
    _ = ((List.ofFn (fun i : Fin s => ‖exp (τ • A i)‖)).drop k).prod := by
            rw [List.map_drop, ← List.ofFn_comp']
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := h

/-- The norms of the strictly-smaller layers, `A j`, and the strictly-larger layers partition the
total norm sum: `(take j).sum + ‖A j‖ + (drop (j+1)).sum = Σ_i ‖A i‖`. -/
lemma sum_norm_take_add_point_add_drop {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸)
    (j : Fin s) :
    ((List.ofFn (fun i : Fin s => ‖A i‖)).take (j : ℕ)).sum + ‖A j‖ +
      ((List.ofFn (fun i : Fin s => ‖A i‖)).drop ((j : ℕ) + 1)).sum = ∑ i : Fin s, ‖A i‖ := by
  let l : List ℝ := List.ofFn (fun i : Fin s => ‖A i‖)
  have hdrop : (l.drop (j : ℕ)).sum = ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum := by
    have hcons := List.cons_getElem_drop_succ (l := l) (n := (j : ℕ)) (h := by simp [l])
    rw [← hcons, List.sum_cons]
    simp [l, List.getElem_ofFn]
  calc
    (l.take (j : ℕ)).sum + ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum
        = (l.take (j : ℕ)).sum + (l.drop (j : ℕ)).sum := by rw [hdrop]; ring
    _ = l.sum := by simp
    _ = ∑ i : Fin s, ‖A i‖ := by simp [l, List.sum_ofFn]

/-- The sum of the norms of `A j` and the strictly-larger layers is at most the total norm sum. -/
lemma norm_point_add_drop_sum_le {s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) :
    ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum ≤ ∑ i : Fin s, ‖A i‖ := by
  let l : List ℝ := List.ofFn (fun i : Fin s => ‖A i‖)
  have hlen : (j : ℕ) < l.length := by simp [l]
  have hsplit : (l.drop (j : ℕ)).sum = ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum := by
    have hcons := List.cons_getElem_drop_succ (l := l) (n := (j : ℕ)) (h := hlen)
    rw [← hcons, List.sum_cons]
    simp [l]
  calc
    ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum = (l.drop (j : ℕ)).sum := hsplit.symm
    _ ≤ l.sum := by
        have hnonneg : ∀ a ∈ l, (0 : ℝ) ≤ a := by
          intro a ha
          rcases (List.mem_ofFn' (fun i : Fin s => ‖A i‖) a).mp (by simpa [l] using ha) with ⟨i, hi⟩
          rw [← hi]
          exact norm_nonneg (A i)
        exact (List.drop_sublist (j : ℕ) l).sum_le_sum hnonneg
    _ = ∑ i : Fin s, ‖A i‖ := by simp [l, List.sum_ofFn]

/-! ### Completion: layering the remainder sum into `αCommConj` -/

/-- The layer-by-layer sum of multinomial-weighted `adSequence` norms appearing in the bound of
`commutatorRemainder`, summed over the 1-based layers `1..s`. -/
noncomputable def layerSum {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖

/-- Splitting `αCommConj` over `Fin (s + 1)` into the inner `Fin s` part (zero on the last
layer) and the part with nonzero outermost multiplicity. -/
lemma αCommConj_snoc_split {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj A B p = αCommConj (fun i : Fin s => A i.castSucc) B p +
      ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
        (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖ := by
  calc
    αCommConj A B p
        = ∑ q' ∈ finAntidiagonal (s + 1) p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := rfl
    _ = ∑ k ∈ range (p + 1), ∑ q ∈ finAntidiagonal s (p - k),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q k) : ℝ) *
              ‖adSequence A (Fin.snoc q k) B‖ := by
              rw [sum_finAntidiagonal_snoc]
    _ = (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) +
          (∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q 0) : ℝ) *
              ‖adSequence A (Fin.snoc q 0) B‖) := by
              rw [sum_range_succ', Nat.sub_zero]
    _ = (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) +
          αCommConj (fun i : Fin s => A i.castSucc) B p := by
              rw [show (∑ q ∈ finAntidiagonal s p,
                (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q 0) : ℝ) *
                  ‖adSequence A (Fin.snoc q 0) B‖) =
                αCommConj (fun i : Fin s => A i.castSucc) B p from by
                simp [αCommConj, adSequence_snoc_zero, multinomial_snoc_zero]]
    _ = αCommConj (fun i : Fin s => A i.castSucc) B p +
          (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖) := by
              rw [add_comm, sum_finAntidiagonal_filter_last_ne_zero]

/-- The layer sum is bounded by `αCommConj`: collapsing each `(j, q)` into the antidiagonal of
`Fin s` by padding with zeros (theory.tex:198-214, the `Σ_k Σ_q → Σ_{q₁+⋯+q_s=p}` step). -/
lemma layerSum_le_αCommConj {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) :
    layerSum A B p ≤ αCommConj A B p := by
  induction s with
  | zero =>
      simp only [layerSum, αCommConj]
      exact sum_nonneg (fun q _ => mul_nonneg (by positivity) (norm_nonneg _))
  | succ s ih =>
      rw [layerSum, Fin.sum_univ_castSucc]
      have hsplit : (∑ j : Fin s,
          (fun j : Fin (s + 1) =>
            ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
              (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
                ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖) j.castSucc)
          = layerSum (fun i : Fin s => A i.castSucc) B p := rfl
      rw [hsplit, αCommConj_snoc_split A B p]
      exact add_le_add (ih (fun i : Fin s => A i.castSucc)) (le_refl _)

/-- The scalar coefficient in one remainder summand equals `multinomial(q) · |τ|^p / p!`. -/
lemma coeff_eq_multinomial_div_factorial {j p : ℕ} (q : Fin (j + 1) → ℕ) (τ : ℝ)
    (hsum : (∑ i : Fin (j + 1), q i) = p) (hlast : 1 ≤ q (Fin.last j)) :
    |τ| ^ p / ((q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
        ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
  have hfac : (q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) =
      (Nat.factorial (q (Fin.last j)) : ℝ) := by
    rw [← Nat.cast_mul]
    congr 1
    have h := Nat.factorial_succ (q (Fin.last j) - 1)
    rw [Nat.sub_add_cancel hlast] at h
    exact h.symm
  have hden : (q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
        (∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) =
      ∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ) := by
    rw [hfac, Fin.prod_univ_castSucc, mul_comm]
  have hms : (∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ)) *
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) = (Nat.factorial p : ℝ) := by
    have h' := Nat.multinomial_spec (s := (univ : Finset (Fin (j + 1)))) (f := q)
    rw [hsum] at h'
    exact_mod_cast h'
  rw [hden]
  have hfac_p : (Nat.factorial p : ℝ) ≠ 0 := by positivity
  have hprod : (∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i _ => by positivity)
  field_simp [hfac_p, hprod]
  rw [← hms]; ring

/-- The telescoped remainder summand (with left context `L`): the norm of
`L · (∏_k e^{τA_k}) · commutatorRemainderTerm A B (-τ) j q` telescopes to a single exponential
`exp(|τ| (C + Σ_k ‖A_k‖))`, with `‖L‖ ≤ exp(|τ| C)`. -/
lemma norm_mul_commutatorRemainderTerm_le {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (A : Fin s → 𝔸) (B : 𝔸) (L : 𝔸) (C : ℝ) (p : ℕ) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (τ : ℝ) (hτ : 0 ≤ τ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0)
    (hL : ‖L‖ ≤ Real.exp (|τ| * C)) :
    ‖L * (List.ofFn (fun k : Fin s => exp (τ • A k))).prod *
        commutatorRemainderTerm A B (-τ) j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
        |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
  let X : 𝔸 := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  let E : List 𝔸 := List.ofFn (fun k : Fin s => exp (τ • A k))
  let En : List 𝔸 := List.ofFn (fun k : Fin s => exp (-τ • A k))
  let N : List ℝ := List.ofFn (fun k : Fin s => ‖A k‖)
  let m : ℕ := q (Fin.last j)
  let r : ℕ := ∑ i : Fin j, q i.castSucc
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hlast' : 1 ≤ q (Fin.last j) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hlast)
  have hD : 0 < D := by positivity
  have hcont : Continuous (fun u : ℝ => (((-τ - u) ^ (m - 1) *
      (-τ) ^ r / D) : ℝ) • expSMulConj (A j) X u) := by
    fun_prop
  have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
    rw [add_comm]
    exact (Fin.sum_univ_castSucc (f := q)).symm.trans hsum
  have h_unfold : commutatorRemainderTerm A B (-τ) j q =
      ((En.drop ((j : ℕ) + 1)).reverse.prod *
        (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
            D) : ℝ) • expSMulConj (A j) X u) *
        (E.drop ((j : ℕ) + 1)).prod) := by
    unfold commutatorRemainderTerm
    simp [X, D, E, En, m, r]
  have h_eq : L * E.prod * commutatorRemainderTerm A B (-τ) j q =
      L * (E.take (j : ℕ)).prod *
        (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
            D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
        (E.drop ((j : ℕ) + 1)).prod := by
    rw [h_unfold]
    calc
      L * E.prod * ((En.drop ((j : ℕ) + 1)).reverse.prod *
          (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
              D) : ℝ) • expSMulConj (A j) X u) *
          (E.drop ((j : ℕ) + 1)).prod)
          = L * (E.prod * (En.drop ((j : ℕ) + 1)).reverse.prod) *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by ac_rfl
      _ = L * (E.take ((j : ℕ) + 1)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by
              rw [prod_exp_mul_drop_reverse_telescope A j τ]
      _ = L * (E.take (j : ℕ)).prod * exp (τ • A j) *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by
              rw [ofFn_take_succ_prod (fun k : Fin s => exp (τ • A k)) j]
              ac_rfl
      _ = L * (E.take (j : ℕ)).prod *
            (exp (τ • A j) * (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^
              (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod := by
              ac_rfl
      _ = L * (E.take (j : ℕ)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod := by
              congr 3
              rw [← integral_mul_left (exp (τ • A j))
                (fun u => (((-τ - u) ^ (m - 1) * (-τ) ^ r / D) : ℝ) •
                  expSMulConj (A j) X u) hcont 0 (-τ)]
              apply intervalIntegral.integral_congr_uIoo
              intro u _
              change exp (τ • A j) * (((-τ - u) ^ (m - 1) * (-τ) ^
                  (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u =
                (((-τ - u) ^ (m - 1) * (-τ) ^ r / D) : ℝ) •
                  (exp (τ • A j) * expSMulConj (A j) X u)
              rw [mul_smul_comm]
  have htake : ‖(E.take (j : ℕ)).prod‖ ≤ Real.exp (|τ| * (N.take (j : ℕ)).sum) := by
    simpa [E, N, List.map_take, List.map_ofFn, Function.comp_def] using
      norm_prod_exp_smul_list_le A ((List.ofFn (fun k : Fin s => k)).take (j : ℕ)) τ
  have hdrop : ‖(E.drop ((j : ℕ) + 1)).prod‖ ≤ Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) := by
    simpa [E, N, List.map_drop, List.map_ofFn, Function.comp_def] using
      norm_prod_exp_smul_list_le A ((List.ofFn (fun k : Fin s => k)).drop ((j : ℕ) + 1)) τ
  have hint : ‖∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
        D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) *
        Real.exp (τ * ‖A j‖) :=
    norm_absorbed_conj_smul_integral_le (A j) X (q (Fin.last j)) (∑ i : Fin j, q i.castSucc) D
      hlast' hD τ hτ
  have hcomb : Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
        Real.exp (τ * ‖A j‖) * Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) =
      Real.exp (|τ| * (C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, abs_of_nonneg hτ]
    ring_nf
  have hexp_arg : C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum =
      C + ∑ k : Fin s, ‖A k‖ := by
    calc
      C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum
          = C + ((N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum) := by ring
      _ = C + ∑ k : Fin s, ‖A k‖ := by simpa [N] using sum_norm_take_add_point_add_drop A j
  calc
    ‖L * E.prod * commutatorRemainderTerm A B (-τ) j q‖
        = ‖L * (E.take (j : ℕ)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod‖ := by rw [h_eq]
    _ ≤ ‖L‖ * ‖(E.take (j : ℕ)).prod‖ *
            ‖∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)‖ *
            ‖(E.drop ((j : ℕ) + 1)).prod‖ := by
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
            (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
                ((q (Fin.last j) : ℝ) * D) * Real.exp (τ * ‖A j‖)) *
            Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) := by
            refine mul_le_mul
              (mul_le_mul (mul_le_mul hL htake (by positivity) (by positivity)) hint
                (by positivity) (by positivity))
              hdrop (by positivity) (by positivity)
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
            (Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
              Real.exp (τ * ‖A j‖) * Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum)) := by
            ring_nf
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
            Real.exp (|τ| * (C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum)) := by
            rw [hcomb]
    _ = ‖X‖ * (|τ| ^ p / ((q (Fin.last j) : ℝ) * D)) *
            Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
            rw [hqsum, hexp_arg]
    _ = ‖X‖ * ((Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ)) *
            Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
            dsimp [D]
            rw [← mul_assoc, coeff_eq_multinomial_div_factorial q τ hsum hlast']
    _ = ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
            dsimp [X]
            ring

/-- Combining the exponential factors of one remainder summand into the global exponential. -/
lemma exp_bound_combine {s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) :
    Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
      Real.exp (2 * |τ| * ‖A j‖) *
        Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) ≤
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  have hS : ((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum =
      |τ| * ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum := by
    rw [List.ofFn_comp' (f := fun i : Fin s => ‖A i‖) (g := fun x : ℝ => |τ| * x),
      ← List.map_drop, List.sum_map_mul_left, List.map_id']
  calc
    Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
        Real.exp (2 * |τ| * ‖A j‖) *
          Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum)
        = Real.exp (2 * (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum +
              |τ| * ‖A j‖)) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 1; ring
    _ ≤ Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              apply Real.exp_le_exp.mpr
              rw [hS]
              have hle : ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum ≤
                  ∑ i : Fin s, ‖A i‖ := norm_point_add_drop_sum_le A j
              have h1 : 2 * (|τ| * ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum +
                    |τ| * ‖A j‖) = 2 * |τ| * (‖A j‖ +
                      ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum) := by ring
              rw [h1]
              simpa [mul_assoc] using (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hle (abs_nonneg τ)) (by norm_num : 0 ≤ (2 : ℝ)))

/-- The norm of the outer (right) exponential product is bounded by the same suffix exponential. -/
lemma norm_ofFn_drop_prod_exp_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) :
    ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := by
  have h := norm_prod_exp_smul_le (l := (List.ofFn (fun i : Fin s => i)).drop k)
    (A := A) (t := fun _ : Fin s => -τ)
  have hmap : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => ‖exp (-τ • A i)‖) =
      (List.ofFn (fun i : Fin s => ‖exp (-τ • A i)‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  have hmap' : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => |-τ| * ‖A i‖) =
      (List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
    simp [abs_neg]
  rw [hmap, hmap'] at h
  calc
    ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).prod‖
        ≤ (((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).map
            (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
    _ = ((List.ofFn (fun i : Fin s => ‖exp (-τ • A i)‖)).drop k).prod := by
            rw [List.map_drop, ← List.ofFn_comp']
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := h

/-- The norm bound of a single remainder summand. -/
lemma norm_commutatorRemainderTerm_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ)
    (j : Fin s) (q : Fin (j + 1) → ℕ) (hq : q ∈ finAntidiagonal (j + 1) p)
    (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B τ j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  let X : 𝔸 := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hD : 0 < D := by positivity
  have houterL : ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) :=
    norm_ofFn_drop_reverse_prod_exp_le A (j + 1) τ
  have houterR : ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) :=
    norm_ofFn_drop_prod_exp_le A (j + 1) τ
  have hint : ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        D) : ℝ) • (expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) *
        Real.exp (2 * |τ| * ‖A j‖) := by
        simpa [D] using norm_conj_smul_integral_le (A j) X (q (Fin.last j))
          (∑ i : Fin j, q i.castSucc) D (by lia) hD τ
  have hcoeff : |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
    have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
      calc
        q (Fin.last j) + (∑ i : Fin j, q i.castSucc)
            = (∑ i : Fin j, q i.castSucc) + q (Fin.last j) := by rw [add_comm]
        _ = ∑ i : Fin (j + 1), q i := (Fin.sum_univ_castSucc (f := q)).symm
        _ = p := hsum
    rw [hqsum, ← mul_assoc]
    exact coeff_eq_multinomial_div_factorial q τ hsum (by lia)
  calc
    ‖commutatorRemainderTerm A B τ j q‖
        ≤ ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ *
            ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
                D) : ℝ) • (expSMulConj (A j) X u)‖ *
            ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ := by
              unfold commutatorRemainderTerm
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
            (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
              ((q (Fin.last j) : ℝ) * D) *
              Real.exp (2 * |τ| * ‖A j‖)) *
            Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) := by gcongr
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
          (Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
            Real.exp (2 * |τ| * ‖A j‖) *
            Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum)) := by ring
    _ ≤ ‖X‖ * ((Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ)) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              rw [hcoeff]; gcongr
              exact exp_bound_combine A j τ
    _ = ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              dsimp [X]; ring

/-- Shared summation skeleton of the commutator-remainder norm bound: given a pointwise bound
`‖commutatorRemainderTerm A B τ j q‖ ≤ ‖adSequence … q B‖ · multinomial(q) · |τ|^p/p! · F` with
nonnegative `F`, the total remainder is bounded by `αCommConj A B p · |τ|^p/p! · F`. -/
lemma norm_commutatorRemainder_le_of_term_bound {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (F : ℝ)
    (hF : 0 ≤ F)
    (hterm : ∀ j : Fin s, ∀ q : Fin (j + 1) → ℕ,
      q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0) →
        ‖commutatorRemainderTerm A B τ j q‖ ≤
          ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
              (Nat.factorial p : ℝ) * F) :
    ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) * F := by
  rw [commutatorRemainder]
  have h1 : ‖∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖commutatorRemainderTerm A B τ j q‖ := by
    apply norm_sum_le_of_le
    intros; exact norm_sum_le ..
  have h2 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * F :=
    sum_le_sum (fun j _ => sum_le_sum (fun q hq => hterm j q hq))
  have h3 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * F ≤
      αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) * F := by
    have hlayer : layerSum A B p ≤ αCommConj A B p := layerSum_le_αCommConj A B p
    have hnonneg : 0 ≤ |τ| ^ p / (Nat.factorial p : ℝ) * F := by positivity
    have hmain : (∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
        (fun q => q (Fin.last j) ≠ 0),
          (‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ)) *
            (|τ| ^ p / (Nat.factorial p : ℝ) * F)) ≤
        αCommConj A B p * (|τ| ^ p / (Nat.factorial p : ℝ) * F) := by
      simp_rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (by simpa [layerSum, mul_comm] using hlayer) hnonneg
    simpa [div_eq_mul_inv, mul_assoc] using hmain
  exact h1.trans (h2.trans h3)

/-- Shared summation skeleton of the left-multiplied commutator-remainder norm bound: given a
pointwise bound `‖M · commutatorRemainderTerm A B τ j q‖ ≤ ‖adSequence … q B‖ · multinomial(q) ·
|τ|^p/p! · F` with nonnegative `F`, the total left-multiplied remainder is bounded by
`αCommConj A B p · |τ|^p/p! · F`. -/
lemma norm_mul_commutatorRemainder_le_of_term_bound {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (M : 𝔸) (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (F : ℝ)
    (hF : 0 ≤ F)
    (hterm : ∀ j : Fin s, ∀ q : Fin (j + 1) → ℕ,
      q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0) →
        ‖M * commutatorRemainderTerm A B τ j q‖ ≤
          ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
              (Nat.factorial p : ℝ) * F) :
    ‖M * commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) * F := by
  rw [commutatorRemainder]
  simp_rw [Finset.mul_sum]
  have h1 : ‖∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), M * commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖M * commutatorRemainderTerm A B τ j q‖ := by
    apply norm_sum_le_of_le
    intros; exact norm_sum_le ..
  have h2 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖M * commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * F :=
    sum_le_sum (fun j _ => sum_le_sum (fun q hq => hterm j q hq))
  have h3 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * F ≤
      αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) * F := by
    have hlayer : layerSum A B p ≤ αCommConj A B p := layerSum_le_αCommConj A B p
    have hnonneg : 0 ≤ |τ| ^ p / (Nat.factorial p : ℝ) * F := by positivity
    have hmain : (∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
        (fun q => q (Fin.last j) ≠ 0),
          (‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ)) *
            (|τ| ^ p / (Nat.factorial p : ℝ) * F)) ≤
        αCommConj A B p * (|τ| ^ p / (Nat.factorial p : ℝ) * F) := by
      simp_rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (by simpa [layerSum, mul_comm] using hlayer) hnonneg
    simpa [div_eq_mul_inv, mul_assoc] using hmain
  exact h1.trans (h2.trans h3)

/-- The spectral-norm bound of the commutator remainder (theory.tex:238-241, general operators). -/
theorem solution_helper {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  refine norm_commutatorRemainder_le_of_term_bound A B p τ
    (Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖)) (le_of_lt (Real.exp_pos _)) ?_
  intro j q hq
  exact norm_commutatorRemainderTerm_le A B p τ j q (mem_filter.mp hq).1 (mem_filter.mp hq).2

/-- The product of the norms of skew-exponentials `exp (τ • A i)` is at most `1`. -/
lemma norm_ofFn_drop_prod_le_one_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (hskew : ∀ i, star (A i) = -A i)
    (k : ℕ) (τ : ℝ) :
    (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map (fun x : 𝔸 => ‖x‖)).prod ≤ 1 := by
  have hle : ∀ i ∈ (List.ofFn (fun i : Fin s => i)).drop k, ‖exp (τ • A i)‖ ≤ 1 := by
    intro i _
    exact (norm_exp_smul_of_skewAdjoint (hskew i) τ).le
  have hnonneg : ∀ i ∈ (List.ofFn (fun i : Fin s => i)).drop k, 0 ≤ ‖exp (τ • A i)‖ := by
    intro i _
    exact norm_nonneg (exp (τ • A i))
  have h := List.prod_map_le_prod_map₀
    (f := fun i : Fin s => ‖exp (τ • A i)‖)
    (g := fun _ : Fin s => (1 : ℝ))
    (s := (List.ofFn (fun i : Fin s => i)).drop k) hnonneg hle
  calc
    (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map (fun x : 𝔸 => ‖x‖)).prod
        = (((List.ofFn (fun i : Fin s => i)).drop k).map
            (fun i : Fin s => ‖exp (τ • A i)‖)).prod := by
              rw [List.map_drop, List.map_ofFn, List.map_drop, List.map_ofFn]
              rfl
    _ ≤ (((List.ofFn (fun i : Fin s => i)).drop k).map (fun _ : Fin s => (1 : ℝ))).prod := h
    _ = 1 := by
      rw [List.map_drop, List.map_ofFn]
      apply List.prod_eq_one
      intro x hx
      have hx' : x ∈ List.ofFn (fun _ : Fin s => (1 : ℝ)) :=
        (List.drop_sublist k (List.ofFn (fun _ : Fin s => (1 : ℝ)))).subset hx
      rcases (List.mem_ofFn' (fun _ : Fin s => (1 : ℝ)) x).mp hx' with ⟨i, hi⟩
      rw [← hi]

/-- The norm of the integral in one skew-adjoint remainder summand is bounded by
`‖X‖ · |τ|^(q+m) / (q · D)` (no exponential factor). -/
lemma norm_conj_smul_integral_le_of_skew {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (hskew : star A = -A) (q m : ℕ) (D : ℝ)
    (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) := by
  refine norm_conj_smul_integral_le_of_norm_conj_le A X q m D hq hD τ ‖X‖ (norm_nonneg X) ?_
  intro u _
  exact norm_expSMulConj_le_of_skewAdjoint A X hskew u

/-- The norm bound of a single remainder summand in the skew-adjoint case. -/
lemma norm_commutatorRemainderTerm_le_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ)
    (τ : ℝ) (hskew : ∀ i, star (A i) = -A i) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B τ j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ) := by
  let X : 𝔸 := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hlast_le : 1 ≤ q (Fin.last j) := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hlast)
  have hD : 0 < D := by positivity
  have houterL :
      ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ ≤ 1 := by
    calc
      ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖
          ≤ (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.map
              (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
      _ = (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).map
              (fun x : 𝔸 => ‖x‖)).prod := by rw [List.map_reverse, List.prod_reverse]
      _ ≤ 1 := norm_ofFn_drop_prod_le_one_of_skewAdjoint A hskew (j + 1) τ
  have houterR : ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ ≤ 1 := by
    calc
      ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖
          ≤ (((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).map
              (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
      _ ≤ 1 := by simpa using norm_ofFn_drop_prod_le_one_of_skewAdjoint A hskew (j + 1) (-τ)
  have hint : ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        D) : ℝ) • (expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) := by
        simpa [D] using norm_conj_smul_integral_le_of_skew (A j) X (hskew j) (q (Fin.last j))
          (∑ i : Fin j, q i.castSucc) D hlast_le hD τ
  have hcoeff : |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
    have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
      calc
        q (Fin.last j) + (∑ i : Fin j, q i.castSucc)
            = (∑ i : Fin j, q i.castSucc) + q (Fin.last j) := by rw [add_comm]
        _ = ∑ i : Fin (j + 1), q i := (Fin.sum_univ_castSucc (f := q)).symm
        _ = p := hsum
    rw [hqsum, ← mul_assoc]
    exact coeff_eq_multinomial_div_factorial q τ hsum hlast_le
  calc
    ‖commutatorRemainderTerm A B τ j q‖
        ≤ ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ *
            ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
                D) : ℝ) • (expSMulConj (A j) X u)‖ *
            ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ := by
              unfold commutatorRemainderTerm
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
          ((q (Fin.last j) : ℝ) * D)) * 1 := by gcongr
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D)) := by ring
    _ = ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) := by rw [hcoeff]; dsimp [X]; ring

/-- The spectral-norm bound of the commutator remainder for anti-Hermitian operators
(theory.tex:242-244). -/
theorem norm_commutatorRemainder_le_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ)
    (hskew : ∀ i, star (A i) = -A i) :
    ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) := by
  simpa [mul_one] using (norm_commutatorRemainder_le_of_term_bound A B p τ 1 (by norm_num)
    (fun j q hq => by
      simpa [mul_one] using norm_commutatorRemainderTerm_le_of_skewAdjoint A B p τ hskew j q
        (mem_filter.mp hq).1 (mem_filter.mp hq).2))

/-! ### The expansion theorem `commutatorExpansion_conj` -/

/-- Peeling the outermost layer off `multiConj`:
`multiConj A B τ = e^{τA⟨s⟩} (multiConj (A∘castSucc) B τ) e^{-τA⟨s⟩}`. -/
lemma multiConj_succ {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) :
    multiConj A B τ =
      expSMulConj (A (Fin.last s)) (multiConj (fun i : Fin s => A i.castSucc) B τ) τ := by
  unfold multiConj expSMulConj
  have hleft : (List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).reverse.prod =
      exp (τ • A (Fin.last s)) *
        (List.ofFn (fun i : Fin s => exp (τ • A i.castSucc))).reverse.prod := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.reverse_concat', List.prod_cons]
  have hright : (List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).prod =
      (List.ofFn (fun i : Fin s => exp (-τ • A i.castSucc))).prod *
        exp (-τ • A (Fin.last s)) := by
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.prod_append, List.prod_singleton]
  rw [hleft, hright]
  noncomm_ring

/-- One summand of the `(s+1)`-layer coefficient, rewritten through the outermost `ad` layer. -/
lemma conjCoeff_snoc_summand {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (q : Fin s → ℕ) (j : ℕ) :
    (Nat.factorial j : ℝ)⁻¹ •
        adPow (A (Fin.last s)) j
          ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
            adSequence (fun i : Fin s => A i.castSucc) q B) =
      ((∏ i : Fin (s + 1), (Nat.factorial ((Fin.snoc q j : Fin (s + 1) → ℕ) i) : ℝ))⁻¹ : ℝ) •
        adSequence A (Fin.snoc q j) B := by
  rw [(adPow (A (Fin.last s)) j).map_smul, ← mul_smul, adSequence_snoc, factorial_inv_snoc]

/-- The `m`-th coefficient of the `(s+1)`-layer expansion is obtained from the inner `s`-layer
coefficients by one further `ad` layer. -/
lemma conjCoeff_succ {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ}
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (m : ℕ) :
    conjCoeff A B m = ∑ j ∈ range (m + 1),
      ((Nat.factorial j : ℝ)⁻¹ : ℝ) •
        adPow (A (Fin.last s)) j (conjCoeff (fun i : Fin s => A i.castSucc) B (m - j)) := by
  rw [conjCoeff, sum_finAntidiagonal_snoc s m
    (fun q' => ((∏ i : Fin (s + 1), (Nat.factorial (q' i) : ℝ))⁻¹ : ℝ) • adSequence A q' B)]
  apply sum_congr rfl
  intro j _; rw [conjCoeff]; symm
  have hsum : adPow (A (Fin.last s)) j (∑ q ∈ finAntidiagonal s (m - j),
      (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
        adSequence (fun i : Fin s => A i.castSucc) q B) =
      ∑ q ∈ finAntidiagonal s (m - j),
        adPow (A (Fin.last s)) j
          ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
            adSequence (fun i : Fin s => A i.castSucc) q B) :=
    map_sum (adPow (A (Fin.last s)) j).toAddMonoidHom
      (fun q => (∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ •
        adSequence (fun i : Fin s => A i.castSucc) q B)
      (finAntidiagonal s (m - j))
  rw [hsum, smul_sum]
  apply sum_congr rfl
  intro q _
  exact conjCoeff_snoc_summand A B q j

/-! ### Auxiliary algebra and reindexing lemmas for `commutatorExpansion_conj` -/

/-- Conjugation commutes with right multiplication by a central scalar:
`expSMulConj A (X * (r : 𝔸)) τ = expSMulConj A X τ * (r : 𝔸)`. -/
lemma expSMulConj_mul_cast {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (r : ℝ) (τ : ℝ) :
    expSMulConj A (X * (r : 𝔸)) τ = expSMulConj A X τ * (r : 𝔸) := by
  rw [← smul_eq_mul_right r X]
  calc
    expSMulConj A (r • X) τ = r • expSMulConj A X τ := (expSMulConjLin A τ).map_smul' r X
    _ = expSMulConj A X τ * (r : 𝔸) := smul_eq_mul_right r (expSMulConj A X τ)

/-- `expSMulConj A · τ` distributes over a finite sum. -/
lemma expSMulConj_map_sum {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : 𝔸) (τ : ℝ) {ι : Type*} (s : Finset ι) (f : ι → 𝔸) :
    expSMulConj A (∑ x ∈ s, f x) τ = ∑ x ∈ s, expSMulConj A (f x) τ := by
  change (expSMulConjLin A τ).toAddMonoidHom (∑ x ∈ s, f x) =
    ∑ x ∈ s, (expSMulConjLin A τ).toAddMonoidHom (f x)
  exact map_sum (expSMulConjLin A τ).toAddMonoidHom f s

/-- Right multiplication by a central scalar `(c : 𝔸)` commutes with the interval integral. -/
lemma integral_mul_cast {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (F : ℝ → 𝔸) (c : ℝ)
    (τ : ℝ) :
    (∫ u in 0..τ, F u) * (c : 𝔸) = ∫ u in 0..τ, F u * (c : 𝔸) := by
  rw [← smul_eq_mul_right c (∫ u in 0..τ, F u), ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr_uIoo
  intro u _
  exact smul_eq_mul_right c (F u)

/-- The single-layer Taylor remainder term, weighted by `d⁻¹` and `τ^j`, rewritten as the
`commutatorRemainderTerm` integrand `((τ-u)^k * τ^j / (k! * d)) • expSMulConj A X u`. -/
lemma expSMulConj_taylor_remainder_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (k j : ℕ) (d : ℝ) (τ : ℝ) (hd : d ≠ 0) :
    (d⁻¹ • (∫ u in 0..τ, expSMulConj A X (τ - u) * ((u ^ k / (Nat.factorial k : ℝ)) : 𝔸)))
        * (τ ^ j : 𝔸)
      = ∫ u in 0..τ, ((τ - u) ^ k * τ ^ j / ((Nat.factorial k : ℝ) * d)) •
          expSMulConj A X u := by
  have hsub : (∫ u in 0..τ, expSMulConj A X (τ - u) * ((u ^ k / (Nat.factorial k : ℝ)) : 𝔸)) =
        ∫ u in 0..τ, ((τ - u) ^ k / (Nat.factorial k : ℝ)) • expSMulConj A X u :=
    (integral_smul_eq_integral_mul_sub (fun u => expSMulConj A X u) k τ).symm
  rw [hsub, ← intervalIntegral.integral_smul, ← map_pow (algebraMap ℝ 𝔸) τ j]
  rw [integral_mul_cast (fun u => d⁻¹ • (((τ - u) ^ k / (Nat.factorial k : ℝ)) •
    expSMulConj A X u)) (τ ^ j) τ]
  apply intervalIntegral.integral_congr_uIoo
  intro u _
  dsimp
  rw [← mul_smul, smul_mul_cast]
  congr 1
  exact scalar_combine k j d τ u hd

/-! ### Structural lemmas for the induction step of `commutatorExpansion_conj` -/

/-- `Fin.castSucc` after `Fin.castLE` at a `Fin s` index agrees with `Fin.castLE` at the lifted
bound: restricting to the first `j + 1` layers coincides whether one first drops to the inner
`Fin s` sequence or works directly on `Fin (s + 1)`. -/
lemma comp_castSucc_castLE {s} {𝔸 : Type*} (A : Fin (s + 1) → 𝔸) (j : Fin s) :
    (fun i : Fin s => A i.castSucc) ∘ Fin.castLE (Nat.succ_le_of_lt j.2)
      = A ∘ Fin.castLE (Nat.succ_le_of_lt j.castSucc.2) := by
  funext i
  simp

/-- Conjugating an inner-layer remainder term by the outermost layer yields the corresponding
outer-layer remainder term at the same (inner) layer index. -/
lemma expSMulConj_commutatorRemainderTerm {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) :
    expSMulConj (A (Fin.last s)) (commutatorRemainderTerm (fun i : Fin s => A i.castSucc) B τ j q) τ
      = commutatorRemainderTerm A B τ j.castSucc q := by
  unfold commutatorRemainderTerm expSMulConj
  let L_inner : 𝔸 :=
    ((List.ofFn (fun i : Fin s => exp (τ • A i.castSucc))).drop (j + 1)).reverse.prod
  let I_inner : 𝔸 := ∫ u in 0..τ,
    (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
    expSMulConj (A j.castSucc)
      (adSequence ((fun i : Fin s => A i.castSucc) ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B) u
  let R_inner : 𝔸 := ((List.ofFn (fun i : Fin s => exp (-τ • A i.castSucc))).drop (j + 1)).prod
  let L_outer : 𝔸 :=
    ((List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).drop (j.castSucc + 1)).reverse.prod
  let I_outer : 𝔸 := ∫ u in 0..τ,
    (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
    expSMulConj (A j.castSucc)
      (adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.castSucc.2)) q B) u
  let R_outer : 𝔸 :=
    ((List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).drop (j.castSucc + 1)).prod
  change exp (τ • A (Fin.last s)) * ((L_inner * I_inner) * R_inner) * exp (-τ • A (Fin.last s))
      = (L_outer * I_outer) * R_outer
  have hL : exp (τ • A (Fin.last s)) * L_inner = L_outer := by
    have hk : j + 1 ≤ s := Nat.succ_le_of_lt j.2
    dsimp [L_inner, L_outer]
    simpa using (ofFn_castSucc_drop_reverse_prod
      (f := fun i : Fin (s + 1) => exp (τ • A i)) (k := j + 1) hk)
  have hR : R_inner * exp (-τ • A (Fin.last s)) = R_outer := by
    have hk : j + 1 ≤ s := Nat.succ_le_of_lt j.2
    dsimp [R_inner, R_outer]
    simpa using (ofFn_castSucc_drop_prod (f := fun i : Fin (s + 1) => exp (-τ • A i))
      (k := j + 1) hk)
  have hI : I_inner = I_outer := by
    dsimp [I_inner, I_outer]
    apply intervalIntegral.integral_congr_uIoo
    intro u _
    simp [comp_castSucc_castLE A j]
  calc
    exp (τ • A (Fin.last s)) * ((L_inner * I_inner) * R_inner) * exp (-τ • A (Fin.last s))
        = (exp (τ • A (Fin.last s)) * L_inner) * I_inner *
            (R_inner * exp (-τ • A (Fin.last s))) := by
            noncomm_ring
    _ = (L_outer * I_outer) * R_outer := by rw [hL, hI, hR]

/-- Decomposing `commutatorRemainder` over `s + 1` layers into the inner remainder conjugated by the
outermost layer plus the outermost-layer remainder. -/
lemma commutatorRemainder_succ {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    commutatorRemainder A B p τ =
      expSMulConj (A (Fin.last s)) (commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
  rw [commutatorRemainder, Fin.sum_univ_castSucc]
  congr 1
  · symm
    rw [commutatorRemainder, expSMulConj_map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [expSMulConj_map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact expSMulConj_commutatorRemainderTerm A B τ j q

/-! ### Reassembly lemmas for the polynomial and remainder parts -/

/-- The polynomial part of the single-layer Taylor expansion reassembles, after reindexing by the
total degree, into `Σ_{m < p} conjCoeff A B m · τ^m`. -/
lemma conjCoeff_sum_of_taylor {s} {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    (∑ j ∈ range p,
        (∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
          (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) * (τ ^ i : 𝔸))
          * (τ ^ j : 𝔸))
      = ∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸) := by
  calc
    (∑ j ∈ range p, (∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
        (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) * (τ ^ i : 𝔸))
          * (τ ^ j : 𝔸))
        = ∑ j ∈ range p, ∑ i ∈ range (p - j),
            ((Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j))) *
              (τ ^ (i + j) : 𝔸) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              rw [mul_assoc]
              rw [show (τ ^ i : 𝔸) * (τ ^ j : 𝔸) = (τ ^ (i + j) : 𝔸) by rw [← pow_add]]
    _ = ∑ m ∈ range p, ∑ i ∈ range (m + 1),
            ((Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B (m - i)))) *
              (τ ^ m : 𝔸) := by
              rw [sum_range_add_antidiagonal p
                (fun i j => ((Nat.factorial i : ℝ)⁻¹ •
                  (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j))) *
                    (τ ^ (i + j) : 𝔸))]
              apply Finset.sum_congr rfl
              intro m hm
              apply Finset.sum_congr rfl
              intro i hi
              have hi' : i ≤ m := Nat.le_of_lt_succ (mem_range.mp hi)
              congr 1
              rw [show i + (m - i) = m by lia]
    _ = ∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸) := by
              apply Finset.sum_congr rfl
              intro m _
              rw [← Finset.sum_mul]
              congr 1
              rw [conjCoeff_succ A B m]

/-- The outermost-layer (`j = Fin.last s`) remainder term, written as the smul-integral of the
conjugated `adPow A' (k + 1)` applied to the inner `adSequence`. -/
lemma commutatorRemainderTerm_last {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (τ : ℝ) (q : Fin s → ℕ) (m : ℕ) :
    commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q m) =
      ∫ u in 0..τ, (((τ - u) ^ (m - 1) * τ ^ (∑ i : Fin s, q i) /
          ((Nat.factorial (m - 1) : ℝ) * ∏ i : Fin s, (Nat.factorial (q i) : ℝ)))) •
        expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) m (adSequence (fun i : Fin s => A i.castSucc) q B)) u := by
  unfold commutatorRemainderTerm
  have hL : ((List.ofFn (fun i : Fin (s + 1) => exp (τ • A i))).drop
      ((Fin.last s : ℕ) + 1)) = [] := by
    rw [Fin.val_last]
    exact List.drop_eq_nil_of_le (by simp)
  have hR : ((List.ofFn (fun i : Fin (s + 1) => exp (-τ • A i))).drop
      ((Fin.last s : ℕ) + 1)) = [] := by
    rw [Fin.val_last]
    exact List.drop_eq_nil_of_le (by simp)
  rw [hL, hR]
  simp [adSequence_snoc]

/-- The single `j`-th Taylor remainder of the outermost conjugation, expanded over the
`finAntidiagonal s j` fibers and matched against the outermost-layer `commutatorRemainderTerm`s. -/
lemma expSMulConj_taylor_remainder_conjCoeff {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p j : ℕ) (τ : ℝ) :
    (∫ u in 0..τ, expSMulConj (A (Fin.last s))
        (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸)
      = ∑ q ∈ finAntidiagonal s j,
          commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
  let A' : 𝔸 := A (Fin.last s)
  let A_inner : Fin s → 𝔸 := fun i => A i.castSucc
  calc
    (∫ u in 0..τ, expSMulConj A' (adPow A' (p - j) (conjCoeff A_inner B j)) (τ - u) *
        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸)
        = (∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
            (∫ u in 0..τ, expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
              ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) * (τ ^ j : 𝔸) := by
              congr 1
              have had : adPow A' (p - j) (conjCoeff A_inner B j) =
                  ∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B) := by
                rw [conjCoeff]
                have h : adPow A' (p - j) (∑ q ∈ finAntidiagonal s j,
                    ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B) =
                    ∑ q ∈ finAntidiagonal s j, adPow A' (p - j)
                      (((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B) :=
                  map_sum (adPow A' (p - j)).toAddMonoidHom
                    (fun q =>
                      ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A_inner q B)
                    (finAntidiagonal s j)
                rw [h]
                apply Finset.sum_congr rfl
                intro q _
                exact (adPow A' (p - j)).map_smul' ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹)
                  (adSequence A_inner q B)
              rw [had]
              have hpoint : ∀ u : ℝ, expSMulConj A' (∑ q ∈ finAntidiagonal s j,
                  ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                  ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)
                  = ∑ q ∈ finAntidiagonal s j, ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) := by
                intro u
                rw [expSMulConj_map_sum (A := A') (τ := τ - u) (s := finAntidiagonal s j)
                  (f := fun q => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    adPow A' (p - j) (adSequence A_inner q B))]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro q _
                have hsmul : expSMulConj A' (((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (adPow A' (p - j) (adSequence A_inner q B))) (τ - u)
                    = ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                      expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) :=
                  (expSMulConjLin A' (τ - u)).map_smul' ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹)
                    (adPow A' (p - j) (adSequence A_inner q B))
                rw [hsmul, smul_mul_assoc]
              rw [intervalIntegral.integral_congr_uIoo (fun u _ => hpoint u)]
              have hint : ∀ q ∈ finAntidiagonal s j, IntervalIntegrable
                  (fun u : ℝ => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) volume 0 τ := by
                intro q _
                have hc : Continuous
                  (fun u : ℝ => ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) •
                    (expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                      ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))) := by
                  refine Continuous.smul continuous_const ?_
                  rw [show (fun u : ℝ =>
                      expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) *
                        ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸))
                        = fun u : ℝ => (u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) •
                          expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B)) (τ - u) by
                    funext u
                    rw [← smul_eq_mul_right]]
                  refine Continuous.smul (by fun_prop) ?_
                  exact (continuous_expSMulConj A' (adPow A' (p - j) (adSequence A_inner q B))).comp
                    (continuous_const.sub continuous_id)
                exact hc.intervalIntegrable 0 τ
              rw [intervalIntegral.integral_finsetSum hint]
              apply Finset.sum_congr rfl
              intro q _
              rw [intervalIntegral.integral_smul]
    _ = ∑ q ∈ finAntidiagonal s j,
          commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro q hq
              have hd : (∏ i : Fin s, (Nat.factorial (q i) : ℝ)) ≠ 0 := by positivity
              have hsum : (∑ i : Fin s, q i) = j := mem_finAntidiagonal.mp hq
              rw [expSMulConj_taylor_remainder_smul (A := A')
                (X := adPow A' (p - j) (adSequence A_inner q B))
                (k := p - j - 1) (j := j) (d := ∏ i : Fin s, (Nat.factorial (q i) : ℝ)) (τ := τ) hd]
              rw [commutatorRemainderTerm_last A B τ q (p - j), hsum]

/-- Summing the single-layer Taylor remainders over `j < p` and reindexing by the antidiagonal
fiber gives the outermost-layer part of `commutatorRemainder`. -/
lemma taylor_remainder_sum {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    (∑ j ∈ range p,
        (∫ u in 0..τ, expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
          ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸))
      = ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
          commutatorRemainderTerm A B τ (Fin.last s) q := by
  calc
    (∑ j ∈ range p,
        (∫ u in 0..τ, expSMulConj (A (Fin.last s))
          (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j)) (τ - u) *
          ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸))
        = ∑ j ∈ range p, ∑ q ∈ finAntidiagonal s j,
            commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (p - j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact expSMulConj_taylor_remainder_conjCoeff A B p j τ
    _ = ∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            commutatorRemainderTerm A B τ (Fin.last s) (Fin.snoc q (k + 1)) := by
              exact sum_range_finAntidiagonal_reflect
                (fun q' => commutatorRemainderTerm A B τ (Fin.last s) q')
    _ = ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
          commutatorRemainderTerm A B τ (Fin.last s) q := by
              exact (sum_finAntidiagonal_filter_last_ne_zero s p
                (fun q => commutatorRemainderTerm A B τ (Fin.last s) q)).symm

/-- The single-layer Taylor expansion of `expSMulConj A' (Σ_{j<p} C_j · τ^j) τ`, split into the
reassembled polynomial `Σ_{m<p} conjCoeff A B m · τ^m` plus the outermost-layer remainder. -/
lemma expSMulConj_taylor_poly {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (A : Fin (s + 1) → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    expSMulConj (A (Fin.last s))
        (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ
      = (∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸))
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
  calc
    expSMulConj (A (Fin.last s))
      (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ
        = ∑ j ∈ range p, expSMulConj (A (Fin.last s))
            (conjCoeff (fun i : Fin s => A i.castSucc) B j) τ * (τ ^ j : 𝔸) := by
              rw [expSMulConj_map_sum]
              apply Finset.sum_congr rfl
              intro j _
              rw [← map_pow (algebraMap ℝ 𝔸) τ j]
              exact expSMulConj_mul_cast (A (Fin.last s))
                (conjCoeff (fun i : Fin s => A i.castSucc) B j) (τ ^ j) τ
    _ = ∑ j ∈ range p, ((∑ i ∈ range (p - j), (Nat.factorial i : ℝ)⁻¹ •
              (adPow (A (Fin.last s)) i (conjCoeff (fun i : Fin s => A i.castSucc) B j)) *
              (τ ^ i : 𝔸))
            + ∫ u in 0..τ, expSMulConj (A (Fin.last s))
                (adPow (A (Fin.last s)) (p - j) (conjCoeff (fun i : Fin s => A i.castSucc) B j))
                  (τ - u) *
                ((u ^ (p - j - 1) / (Nat.factorial (p - j - 1) : ℝ)) : 𝔸)) * (τ ^ j : 𝔸) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hpj : 1 ≤ p - j := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt (mem_range.mp hj))
              rw [expSMulConj_taylor (A (Fin.last s))
                (conjCoeff (fun i : Fin s => A i.castSucc) B j) (p - j) τ hpj]
    _ = (∑ m ∈ range p, conjCoeff A B m * (τ ^ m : 𝔸))
        + ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            commutatorRemainderTerm A B τ (Fin.last s) q := by
              simp_rw [add_mul, Finset.sum_add_distrib]
              congr 1
              · exact conjCoeff_sum_of_taylor A B p τ
              · exact taylor_remainder_sum A B p τ

/-- `thm:comm_exp_conj` (theory.tex:222-236): the multi-layer conjugation expands as
`multiConj A B τ = Σ_{j < p} conjCoeff A B j · τ^j + commutatorRemainder A B p τ`,
where the `conjCoeff A B j` are the operators `C_j` independent of `τ`. -/
theorem commutatorExpansion_conj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (hp : 1 ≤ p) :
    multiConj A B τ =
      (∑ j ∈ Finset.range p, conjCoeff A B j * (τ ^ j : 𝔸)) + commutatorRemainder A B p τ := by
  induction s with
  | zero =>
      have hmulti : multiConj A B τ = B := by simp [multiConj]
      have hc0 : conjCoeff A B 0 = B := by
        rw [conjCoeff]
        rw [Finset.sum_eq_single_of_mem (s := finAntidiagonal 0 0) (a := 0)
          (f := fun q => ((∏ i : Fin 0, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A q B)]
        · simp [adSequence]
        · rw [mem_finAntidiagonal]
          simp
        · intro b _ hb
          exfalso
          apply hb
          exact Subsingleton.elim _ _
      have hcj : ∀ j, 0 < j → conjCoeff A B j = 0 := by
        intro j hj
        rw [conjCoeff]
        have hempty : finAntidiagonal 0 j = ∅ := by
          ext q
          rw [mem_finAntidiagonal, show (∑ i : Fin 0, q i) = 0 by simp]
          constructor
          · intro h
            exact False.elim ((ne_of_gt hj) h.symm)
          · intro h
            simp at h
        rw [hempty]
        simp
      have hrem : commutatorRemainder A B p τ = 0 := by simp [commutatorRemainder]
      rw [hmulti, hrem, add_zero]
      rw [Finset.sum_eq_single_of_mem (a := 0) (s := Finset.range p)
        (f := fun j => conjCoeff A B j * (τ ^ j : 𝔸))]
      · simp [hc0]
      · rw [Finset.mem_range]
        exact lt_of_lt_of_le zero_lt_one hp
      · intro j _ hj0
        rw [hcj j (Nat.pos_of_ne_zero hj0), zero_mul]
  | succ s ih =>
      rw [multiConj_succ A B τ, ih (fun i : Fin s => A i.castSucc)]
      have hlin : expSMulConj (A (Fin.last s))
          ((∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) +
            commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ
          = expSMulConj (A (Fin.last s))
              (∑ j ∈ range p, conjCoeff (fun i : Fin s => A i.castSucc) B j * (τ ^ j : 𝔸)) τ +
            expSMulConj (A (Fin.last s))
              (commutatorRemainder (fun i : Fin s => A i.castSucc) B p τ) τ :=
        (expSMulConjLin (A (Fin.last s)) τ).map_add' _ _
      rw [hlin, expSMulConj_taylor_poly A B p τ, commutatorRemainder_succ A B p τ]
      abel

end TrotterError


-- ===== platform entry point =====
open TrotterError

theorem solution : ∀ {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ), ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  exact TrotterError.solution_helper
