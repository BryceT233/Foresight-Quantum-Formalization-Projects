/-
Prove2Me solution for `TrotterError.exp_neg_mul_self`.

Split-node form: the file proves the target and nothing else. No declaration is
re-emitted, so nothing here can collide with a platform node or its `by sorry`
stub, and the target's own platform statement is not imported.

Source: https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects/tree/d6bfac12d15bc59fcc5f90206ac3312da602eb3d
-/
import Mathlib

open NormedSpace

theorem solution : ∀ {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸),
    exp (-x) * exp x = 1 := by
  intro 𝔸 _ _ _ x
  simpa using (exp_add_of_commute (Commute.refl x).neg_left).symm