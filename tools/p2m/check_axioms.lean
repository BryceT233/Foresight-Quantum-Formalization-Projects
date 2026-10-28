import FQFP
open Lean

/-- The three axioms every Mathlib theorem is allowed to depend on. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Headline + engine theorems of the TrotterError development. -/
def targets : List Name :=
  [ -- MainTheorem: general / anti-Hermitian, additive / multiplicative
    ``TrotterError.trotter_error_bound_comm_scaling,
    ``TrotterError.trotter_error_comm_scaling,
    ``TrotterError.trotter_error_bound_comm_scaling_of_skewAdjoint,
    ``TrotterError.trotter_error_comm_scaling_of_skewAdjoint,
    ``TrotterError.multiplicative_error_bound_comm_scaling,
    ``TrotterError.multiplicative_error_comm_scaling,
    ``TrotterError.multiplicative_error_bound_comm_scaling_of_skewAdjoint,
    ``TrotterError.multiplicative_error_comm_scaling_of_skewAdjoint,
    -- engines
    ``TrotterError.norm_additiveKernel_le,
    ``TrotterError.norm_additiveResidual_le,
    -- OneNormScaling
    ``TrotterError.trotter_error_bound_one_norm_scaling,
    ``TrotterError.trotter_error_one_norm_scaling,
    ``TrotterError.trotter_error_bound_one_norm_scaling_of_skew_adjoint,
    ``TrotterError.trotter_error_one_norm_scaling_of_skew_adjoint,
    ``TrotterError.trotter_number_one_norm_scaling,
    -- structural results
    ``TrotterError.norm_commutatorRemainder_le,
    ``TrotterError.norm_commutatorRemainder_le_of_skewAdjoint,
    ``TrotterError.errorOrderCond_iff,
    ``TrotterError.commutatorExpansion_conj,
    ``TrotterError.secondOrder_bound,
    ``TrotterError.firstOrder_bound ]

run_meta do
  let env ← getEnv
  let mut bad : Nat := 0
  let mut missing : Nat := 0
  for t in targets do
    match env.find? t with
    | none =>
      missing := missing + 1
      IO.println s!"MISSING  {t}"
    | some _ =>
      let axs ← Lean.collectAxioms t
      let extra := axs.filter (fun a => !allowed.contains a)
      if extra.isEmpty then
        IO.println s!"OK       {t}   axioms=[{String.intercalate ", " (axs.toList.map toString)}]"
      else
        bad := bad + 1
        IO.println s!"EXTRA-AXIOM  {t}   extra=[{String.intercalate ", " (extra.toList.map toString)}]"
  IO.println ""
  IO.println s!"checked {targets.length} theorems — extra-axiom: {bad}, missing: {missing}"
