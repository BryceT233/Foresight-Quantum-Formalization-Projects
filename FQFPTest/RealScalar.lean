/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.Analysis.Normed.Module.RealScalar

/-!
# Real scalar bounds without an algebra structure

The scalar bounds apply to abstract seminormed real vector spaces. The scaled
bound allows negative `u`; it requires only `u ≤ 1`.
-/

section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

example (c : ℝ) (x : E) (hc : |c| ≤ 1) : ‖c • x‖ ≤ ‖x‖ :=
  TrotterError.norm_smul_le_of_abs_le_one c x hc

example (c : ℝ) (x : E) (hc : |c| ≤ 1) (u t : ℝ) (ht : 0 ≤ t) (hu : u ≤ 1) :
    (u * t) * ‖c • x‖ ≤ t * ‖x‖ :=
  TrotterError.norm_smul_exp_arg_le c x hc u t ht hu

end
