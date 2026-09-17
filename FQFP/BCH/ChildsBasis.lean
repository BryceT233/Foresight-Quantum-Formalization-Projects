/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.Commutator
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Childs four-fold commutator basis

The eight nested commutators `[X₁, [X₂, [X₃, [B, A]]]]` with `Xᵢ ∈ {A, B}` that Childs
enumerates for weight-5 elements of the free Lie algebra on `{A, B}`, used for Suzuki S₄ BCH
bounds, together with the weighted sums of their norms that form the RHS of those bounds.

## Contents

* `childsComm A B i`, `i : Fin 8` — the `i`-th commutator. This is the only definition; it is
  a pattern match, so `childsComm A B i` is the form every call site uses.
* `childsComm_zero … childsComm_seven` — the eight branches, as `@[simp]` rewrite rules giving
  the concrete bracket expression. They are needed because `childsComm` is a pattern match on
  `Fin 8`: `unfold childsComm` leaves a *stuck* `match` on a literal index, and it is these
  lemmas (or `rfl`) that discharge it.
* `bchFourFoldSum A B = Σᵢ ‖childsComm A B i‖` — the unit-coefficient Level-2 RHS.
* `childsPrefactors`, `bchTightPrefactors : Fin 8 → ℝ` — the two prefactor families, each with
  its own `_nonneg` lemma. The weighted sum `Σᵢ γ i · ‖childsComm A B i‖` is written out where
  it is used rather than named.

## Provenance and design

Ported from `Lean-BCH/BCH/ChildsBasis.lean`. That file defined a private helper
`commBr X Y := X * Y - Y * X`, unrolled the eight commutators by hand as eight separate
named `def`s, wrote every sum out as eight explicit terms `‖C₁‖ + ⋯ + ‖C₈‖`, and gave each
prefactor structure eight separate `γᵢ` fields plus eight `nonnegᵢ` proof fields.

None of that is necessary. `commBr` **is** Mathlib's associative-ring Lie bracket `⁅X, Y⁆`
(`Ring.lie_def`), taken from Mathlib here. The eight commutators are one `Fin 8`-indexed
object, so call sites write `childsComm A B i` and there are no numbered aliases to keep in
sync. The sums are `Finset.sum` over `Fin 8`. A prefactor family is a plain function
`Fin 8 → ℝ` with its own `_nonneg` lemma, rather than a structure bundling the two. This file
therefore introduces no new mathematical content — only the choice of which words appear and
which constants are stored.

The **values** are unchanged: `childsPrefactors` and `bchTightPrefactors` carry the same
constants as before. Call sites that projected `γ.γ₁ … γ.γ₈` write `γ 0 … γ 7`.

## Note on overcompleteness

By Witt's formula the degree-5 component of the free Lie algebra on `{A, B}` has dimension
`(1/5)·(2⁵ - 2) = 6`, while the enumeration has `2³ = 8` elements, so it is an over-complete
spanning set admitting two Jacobi relations (between indices `2`/`3` and `6`/`7`). The
eight-element form is retained because it is uniform to enumerate and symmetric under
`A ↔ B`; the overcompleteness costs nothing in bound tightness since the projection used
downstream has `β₃ = β₇ = 0`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open Finset NormedSpace

namespace FQFP.BCH

open TrotterError

-- The associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A`, so that the standard Lie-bracket
-- lemmas are available. `TrotterError` sets this up the same way (`Commutator.lean:58`).
attribute [local instance] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸]

/-! ### The eight commutators -/

/-- The eight Childs four-fold commutators, as a `Fin 8`-indexed family. Branch `i` is the
concrete bracket expression `[X₁,[X₂,[X₃,[B,A]]]]`; see `childsComm_zero` … `childsComm_seven`
for the eight forms. -/
def childsComm (A B : 𝔸) : Fin 8 → 𝔸
  | 0 => ⁅A, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 1 => ⁅A, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 2 => ⁅A, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 3 => ⁅A, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 4 => ⁅B, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 5 => ⁅B, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 6 => ⁅B, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆
  | _ => ⁅B, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆

/-- `childsComm` is a pattern match on `Fin 8`, so `unfold childsComm` leaves a stuck `match` on
a literal index rather than reducing to the bracket expression. These lemmas discharge it. They
are marked `@[simp]` so that a downstream goal mentioning `‖childsComm A B i‖` can be normalised
to the bracket form; the match is stuck for a symbolic `i`, so the rules cannot loop. -/
@[simp] lemma childsComm_zero (A B : 𝔸) : childsComm A B 0 = ⁅A, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_one (A B : 𝔸) : childsComm A B 1 = ⁅A, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_two (A B : 𝔸) : childsComm A B 2 = ⁅A, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_three (A B : 𝔸) : childsComm A B 3 = ⁅A, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_four (A B : 𝔸) : childsComm A B 4 = ⁅B, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_five (A B : 𝔸) : childsComm A B 5 = ⁅B, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_six (A B : 𝔸) : childsComm A B 6 = ⁅B, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma childsComm_seven (A B : 𝔸) : childsComm A B 7 = ⁅B, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl

/-! ### The weighted sums

A prefactor family is just a function `Fin 8 → ℝ` weighting the eight commutator norms; there
is no need to bundle it with its nonnegativity in a structure, nor to name the weighted sum
`∑ i, γ i * ‖childsComm A B i‖` — it is written out where it is used. The two concrete
families are `childsPrefactors` and `bchTightPrefactors`, each with its own nonnegativity
lemma. -/

/-- Sum of the norms of the eight Childs four-fold commutators, with unit coefficients.
This one *is* named, because it is the RHS that the Suzuki bounds quote. -/
def bchFourFoldSum (A B : 𝔸) : ℝ :=
  ∑ i : Fin 8, ‖childsComm A B i‖

lemma bchFourFoldSum_nonneg (A B : 𝔸) : 0 ≤ bchFourFoldSum A B :=
  sum_nonneg fun _ _ => norm_nonneg _

/-- Childs's heuristic prefactors (2021) — balanced-factoring values from the reference
paper. -/
def childsPrefactors : Fin 8 → ℝ :=
  ![0.0047, 0.0057, 0.0046, 0.0074, 0.0097, 0.0097, 0.0173, 0.0284]

lemma childsPrefactors_nonneg (i : Fin 8) : 0 ≤ childsPrefactors i := by
  fin_cases i <;> norm_num [childsPrefactors]

/-- **BCH-derived tight prefactors** — rational ceilings of `|βᵢ(suzukiP)|` at the 1/10⁶ grid,
where `βᵢ(p)` are the degree-2 polynomial coefficients from the CAS pipeline.

At Suzuki `p = 1/(4 − 4^(1/3)) ≈ 0.4144908` the eight numerical `|βᵢ(suzukiP)|` values are
`0.0002595, 0.0006624, 0, 0.0001317, 0.0003757, 0.0011272, 0, 0.0004416`. Ceilings at the
1/10⁶ grid make `γᵢ ≥ |βᵢ(suzukiP)|` rigorous (slack ~10⁻⁷ per coefficient); truncations
would fail the strict inequality for `γ₂` and `γ₆`.

Every ceiling is strictly smaller than Childs's heuristic coefficient (~9× to ~64× tighter
for the non-zero values). The Childs basis is over-complete (two free parameters, since the
weight-5 free Lie algebra is 6-dimensional); the projection here sets both to zero, giving
`γ₃ = γ₇ = 0`. -/
noncomputable def bchTightPrefactors : Fin 8 → ℝ :=
  ![260 / 1000000, 663 / 1000000, 0, 132 / 1000000,
    376 / 1000000, 1128 / 1000000, 0, 442 / 1000000]

lemma bchTightPrefactors_nonneg (i : Fin 8) : 0 ≤ bchTightPrefactors i := by
  fin_cases i <;> norm_num [bchTightPrefactors]

/-! ### The weighted sum

The weighted sum `∑ i, γ i * ‖childsComm A B i‖` is written out where it is used rather than
named. -/

/-- A weighted sum of commutator norms with nonnegative weights is nonnegative. -/
lemma weightedSum_nonneg {γ : Fin 8 → ℝ} (hγ : ∀ i, 0 ≤ γ i) (A B : 𝔸) :
    0 ≤ ∑ i : Fin 8, γ i * ‖childsComm A B i‖ :=
  sum_nonneg fun i _ => mul_nonneg (hγ i) (norm_nonneg _)

/-- The tight prefactors' weighted sum is at most the unit-coefficient `bchFourFoldSum`,
since every `γᵢ ≤ 1` in `bchTightPrefactors` (in fact `γᵢ ≪ 1`). -/
lemma bchTightPrefactors_weightedSum_le_bchFourFoldSum (A B : 𝔸) :
    ∑ i : Fin 8, bchTightPrefactors i * ‖childsComm A B i‖ ≤ bchFourFoldSum A B :=
  sum_le_sum fun i _ => by
    have h1 : bchTightPrefactors i ≤ 1 := by
      fin_cases i <;> norm_num [bchTightPrefactors]
    calc bchTightPrefactors i * ‖childsComm A B i‖
        ≤ 1 * ‖childsComm A B i‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖childsComm A B i‖ := one_mul _

end FQFP.BCH
