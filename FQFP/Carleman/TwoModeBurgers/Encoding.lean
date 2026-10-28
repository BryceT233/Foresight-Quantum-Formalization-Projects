/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.TwoModeBurgers.Obstruction
public import FQFP.Topology.Algebra.MvPolynomial.Identity
public import FQFP.RingTheory.MvPolynomial.Trunc

/-!
# Obstruction to local polynomial encoders

The paper's encoder `Φ` and decoder `Ψ` are families of real multivariate
polynomials. Its affine latent vector field is a family of polynomials of
total degree at most one. The local identities are first promoted from a
nonempty open set to polynomial identities, then a finite-dimensional space
of latent polynomials is pulled back along `Φ`.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

private lemma mkDerivation_aeval (α γ β : ℝ) {m : ℕ}
    (Φ : Fin m → MvPolynomial (Fin 2) ℝ)
    (G : Fin m → MvPolynomial (Fin m) ℝ)
    (hΦ : ∀ i, (mkDerivation ℝ (vectorField α γ β)) (Φ i) = aeval Φ (G i))
    (p : MvPolynomial (Fin m) ℝ) :
    (mkDerivation ℝ (vectorField α γ β)) (aeval Φ p) =
      aeval Φ ((mkDerivation ℝ G) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Derivation.leibniz, aeval_X, mkDerivation_X,
      hp, hΦ]
    simp only [map_add, map_mul, aeval_X, smul_eq_mul]

private lemma mem_truncTotal_range_of_totalDegree_le {m d : ℕ}
    {p : MvPolynomial (Fin m) ℝ} (hp : p.totalDegree ≤ d) :
    p ∈ (truncTotal (Fin m) ℝ (d + 1)).range := by
  refine ⟨p, ?_⟩
  exact (truncTotal_eq_self_iff (d + 1) (by lia) p).2 (by lia)

/-- A polynomial encoder with a polynomial decoder cannot conjugate the
two-mode system to a polynomial vector field of degree at most one. -/
theorem no_polynomial_linear_encoding (α γ β : ℝ) (hβ : β ≠ 0) {m : ℕ}
    (Φ : Fin m → MvPolynomial (Fin 2) ℝ)
    (Ψ : Fin 2 → MvPolynomial (Fin m) ℝ)
    (G : Fin m → MvPolynomial (Fin m) ℝ)
    (hG : ∀ i, (G i).totalDegree ≤ 1)
    (hΦ : ∀ i, (mkDerivation ℝ (vectorField α γ β)) (Φ i) = aeval Φ (G i))
    (hΨ : ∀ i, aeval Φ (Ψ i) = X i) : False := by
  let d := max (Ψ 0).totalDegree (Ψ 1).totalDegree
  let W := (truncTotal (Fin m) ℝ (d + 1)).range
  let V := W.map (aeval Φ).toLinearMap
  have : FiniteDimensional ℝ W := finite_range_truncTotal (d + 1)
  have : FiniteDimensional ℝ V := inferInstance
  have hΨmem (i : Fin 2) : Ψ i ∈ W := by
    apply mem_truncTotal_range_of_totalDegree_le
    fin_cases i <;> simp [d]
  have hcoord (i : Fin 2) : (X i : MvPolynomial (Fin 2) ℝ) ∈ V := by
    rw [← hΨ i]
    exact Submodule.mem_map_of_mem (hΨmem i)
  have hV : ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hp
    have hqdegree : q.totalDegree ≤ d := by
      have hfix := truncTotal_eq_self_of_mem_range (d + 1) hq
      have hlt := (truncTotal_eq_self_iff (d + 1) (by lia) q).1 hfix
      lia
    have hDdegree : ((mkDerivation ℝ G) q).totalDegree ≤ d := by
      have h := totalDegree_mkDerivation_le G 1 hG q
      lia
    change (mkDerivation ℝ (vectorField α γ β)) (aeval Φ q) ∈ V
    rw [mkDerivation_aeval α γ β Φ G hΦ]
    exact Submodule.mem_map_of_mem
      (mem_truncTotal_range_of_totalDegree_le hDdegree)
  exact no_finite_polynomial_closure_first α γ β hβ
    ⟨V, inferInstance, hcoord 0, hV⟩

/-- The same obstruction holds when the polynomial encoder identities are
assumed only on a nonempty open subset of the original state space. -/
theorem no_local_polynomial_linear_encoding (α γ β : ℝ) (hβ : β ≠ 0) {m : ℕ}
    (Φ : Fin m → MvPolynomial (Fin 2) ℝ)
    (Ψ : Fin 2 → MvPolynomial (Fin m) ℝ)
    (G : Fin m → MvPolynomial (Fin m) ℝ)
    (hG : ∀ i, (G i).totalDegree ≤ 1)
    {U : Set (Fin 2 → ℝ)} (hU : IsOpen U) (hUn : U.Nonempty)
    (hΦ : ∀ x ∈ U, ∀ i,
      eval x ((mkDerivation ℝ (vectorField α γ β)) (Φ i)) =
        eval x (aeval Φ (G i)))
    (hΨ : ∀ x ∈ U, ∀ i, eval x (aeval Φ (Ψ i)) = x i) : False := by
  have hΦglobal (i : Fin m) :
      (mkDerivation ℝ (vectorField α γ β)) (Φ i) = aeval Φ (G i) :=
    eq_of_eval_eq_on_isOpen hU hUn (fun x hx => hΦ x hx i)
  have hΨglobal (i : Fin 2) : aeval Φ (Ψ i) = X i := by
    apply eq_of_eval_eq_on_isOpen hU hUn
    intro x hx
    simpa only [eval_X] using hΨ x hx i
  exact no_polynomial_linear_encoding α γ β hβ Φ Ψ G hG hΦglobal hΨglobal

/-- There is no polynomial encoder and polynomial state decoder satisfying
the paper's affine latent dynamics on a nonempty open set. -/
theorem no_local_polynomial_affine_encoding (α γ β : ℝ) (hβ : β ≠ 0) {m : ℕ}
    (Φ : Fin m → MvPolynomial (Fin 2) ℝ)
    (Ψ : Fin 2 → MvPolynomial (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ)
    {U : Set (Fin 2 → ℝ)} (hU : IsOpen U) (hUn : U.Nonempty)
    (hDynamics : ∀ x ∈ U, ∀ i,
      eval x ((mkDerivation ℝ (vectorField α γ β)) (Φ i)) =
        (∑ j, A i j * eval x (Φ j)) + c i)
    (hDecode : ∀ x ∈ U, ∀ i,
      eval (fun j => eval x (Φ j)) (Ψ i) = x i) : False := by
  let G (i : Fin m) : MvPolynomial (Fin m) ℝ :=
    ∑ j, C (A i j) * X j + C (c i)
  have hG (i : Fin m) : (G i).totalDegree ≤ 1 := by
    dsimp [G]
    apply (totalDegree_add _ _).trans
    apply max_le
    · apply totalDegree_finsetSum_le
      intro j hj
      have h := totalDegree_mul (C (A i j)) (X j : MvPolynomial (Fin m) ℝ)
      simp only [totalDegree_C, totalDegree_X] at h
      lia
    · simp
  have hΦ : ∀ x ∈ U, ∀ i,
      eval x ((mkDerivation ℝ (vectorField α γ β)) (Φ i)) =
        eval x (aeval Φ (G i)) := by
    intro x hx i
    rw [hDynamics x hx i]
    simp [G]
  have hΨ : ∀ x ∈ U, ∀ i, eval x (aeval Φ (Ψ i)) = x i := by
    intro x hx i
    change aeval x (aeval Φ (Ψ i)) = x i
    rw [comp_aeval_apply]
    simpa only [aeval_eq_eval] using hDecode x hx i
  exact no_local_polynomial_linear_encoding α γ β hβ Φ Ψ G hG hU hUn hΦ hΨ

end TwoModeBurgers
