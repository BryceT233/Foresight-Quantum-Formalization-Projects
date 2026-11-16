/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Error.Fidelity

/-!
# Fidelity of tensor products

The existing unsquared fidelity is multiplicative under `Density.tensor`.
Positive square roots commute with tensor products, and the trace norm of a
tensor product is the product of trace norms. This is the density-state case of
Watrous, *The Theory of Quantum Information*, Proposition 3.16.
The two state spaces may have different dimensions, and singular operators are allowed.

## Main results

* `Qudit.Operator.traceNorm_tensor`: multiplicativity of the operator trace norm.
* `Qudit.Density.fidelity_tensor`: multiplicativity of unsquared fidelity on independent products.
* `Qudit.Density.fidelity_tensor_right`: appending a common density leaves fidelity unchanged.
-/

@[expose] public section

namespace Qudit

noncomputable section

variable {H K : Qudit}

namespace Operator

/-- The trace norm is multiplicative for arbitrary tensor-product operators. -/
lemma traceNorm_tensor (A : Operator H) (B : Operator K) :
    LinearMap.traceNorm (tensor A B) = LinearMap.traceNorm A * LinearMap.traceNorm B := by
  have hg : (tensor A B).adjoint * tensor A B = tensor (A.adjoint * A) (B.adjoint * B) := by
    change (TensorProduct.map A B).adjoint * TensorProduct.map A B =
      TensorProduct.map (A.adjoint * A) (B.adjoint * B)
    rw [TensorProduct.adjoint_map, ← TensorProduct.map_mul]
  rw [traceNorm_eq_norm_trace_sqrt_adjoint_mul, hg,
    sqrt_tensor (H := H) (K := K) (A.adjoint * A) (B.adjoint * B)
      A.isPositive_adjoint_comp_self B.isPositive_adjoint_comp_self,
    trace_tensor, norm_mul, ← traceNorm_eq_norm_trace_sqrt_adjoint_mul,
    ← traceNorm_eq_norm_trace_sqrt_adjoint_mul]

end Operator

namespace Density

/-- Unsquared mixed-state fidelity is multiplicative under independent tensor products. -/
theorem fidelity_tensor (ρ₁ σ₁ : Density H) (ρ₂ σ₂ : Density K) :
    (ρ₁.tensor ρ₂).fidelity (σ₁.tensor σ₂) = ρ₁.fidelity σ₁ * ρ₂.fidelity σ₂ := by
  rw [fidelity, op_tensor, op_tensor, Operator.sqrt_tensor _ _ ρ₁.positive ρ₂.positive,
    Operator.sqrt_tensor _ _ σ₁.positive σ₂.positive]
  have hm : Operator.tensor ρ₁.op.sqrt ρ₂.op.sqrt * Operator.tensor σ₁.op.sqrt σ₂.op.sqrt =
      Operator.tensor (ρ₁.op.sqrt * σ₁.op.sqrt) (ρ₂.op.sqrt * σ₂.op.sqrt) :=
    (TensorProduct.map_mul _ _ _ _).symm
  rw [hm, Operator.traceNorm_tensor]
  rfl

/-- Appending the same density state to both inputs leaves fidelity unchanged. -/
theorem fidelity_tensor_right (ρ σ : Density H) (τ : Density K) :
    (ρ.tensor τ).fidelity (σ.tensor τ) = ρ.fidelity σ := by
  rw [fidelity_tensor, fidelity_self, mul_one]

/-- Prepending the same density state to both inputs leaves fidelity unchanged. -/
theorem fidelity_tensor_left (ρ σ : Density K) (τ : Density H) :
    (τ.tensor ρ).fidelity (τ.tensor σ) = ρ.fidelity σ := by
  rw [fidelity_tensor, fidelity_self, one_mul]

end Density

end

end Qudit
