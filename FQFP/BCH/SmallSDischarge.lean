/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHTerms
public import FQFP.BCH.WordExpansion

/-!
# The small-`s` discharge: pure cancellation identities

Ported from `Lean-BCH/BCH/SmallSDischarge.lean` (`BCH/SmallSDischarge.lean:37-786`). This file grows
slice by slice; see `artifacts/bch-port.md` §3.3bis for the plan (`P0`…`P4`).

## What these identities are

Write `z = a + b` and let `T_k` be the degree-`k` part of `y = exp a * exp b - 1`. The Dynkin/Ree
form of `log (exp a * exp b)` expresses its degree-`k` part through the `y_j`, and the pure
identities here say that this expression agrees with the explicit word formula of `BCHTerms.lean`:
for degrees 4, 5, 6, 7, 8 respectively

    ½·W + ⅓·y³ - ¼·y⁴ + … - bch*Term a b = 0.

They are the degree-`k` cancellation step behind `pieceB_{sextic,septic,octic,nonic}_decomp`, which
is why they are stated with rational coefficients only: the target's scalar interface is `ℚ`
(`bch*Term` is a `ℚ`-algebra element, not a `𝕂`-one).

## Status

The degree-4 pair and the degree-5 identity are ported, both without a heartbeat bump. (The source's
names are offset by one from the degree they clear: `sextic_pure_identity` is the degree-5 step.)

`bchSexticTerm_expand` is the word-table expansion of `bchSexticTerm`, proved in its own small goal.
The degree-6 identity is not in the file yet. Its pieces are now stated as `private def`s (the
source's `let` chain costs 37.0M heartbeats to elaborate as a *statement*, 185× the default budget;
the same statement with named `def`s costs 344k), and the identity still needs the word-indexed
assembly described in `artifacts/bch-port.md` §3.3quater: a single `noncomm_ring` over the expanded
degree-6 polynomial costs 172M heartbeats and gives up.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace FQFP.BCH

variable {𝔸 : Type*}

/-! ### Degree 4: the cancellation behind `bchQuarticTerm` -/

/-- **The degree-4 pure identity, with the denominators cleared**: 24 times

    Y₄ - ½(Y₁Y₃ + Y₂² + Y₃Y₁) + ⅓(Y₁²Y₂ + Y₁Y₂Y₁ + Y₂Y₁²) - ¼Y₁⁴ + C₄

is zero, where `z = a + b` and `U = 2ab + a² + b² = 2Y₂`. Stated over a bare `Ring` (the scalar is
`Nat`-valued, so no `ℚ` is needed) and proved by `noncomm_ring`. -/
private theorem quintic_pure_identity_cleared [Ring 𝔸] (a b : 𝔸) :
    (a ^ 4 + 4 • (a ^ 3 * b) + 6 • (a ^ 2 * b ^ 2) + 4 • (a * b ^ 3) + b ^ 4) -
    2 • ((a + b) * (a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3) +
         (a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3) * (a + b)) -
    3 • ((2 • (a * b) + a ^ 2 + b ^ 2) * (2 • (a * b) + a ^ 2 + b ^ 2)) +
    4 • ((a + b) ^ 2 * (2 • (a * b) + a ^ 2 + b ^ 2) +
         (a + b) * (2 • (a * b) + a ^ 2 + b ^ 2) * (a + b) +
         (2 • (a * b) + a ^ 2 + b ^ 2) * (a + b) ^ 2) -
    6 • (a + b) ^ 4 +
    (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
     (a * (a * b - b * a) - (a * b - b * a) * a) * b) = 0 := by
  noncomm_ring

/-- **The degree-4 pure identity**, with the `ℚ` scalars of the Dynkin/Ree form: the degree-4 part
of `½y² - ⅓y³ + ¼y⁴` written out in `z` and `T₂`, `T₃`, `T₄`, minus `bchQuarticTerm a b`, is zero.

This is the `ℚ`-scaled companion of `quintic_pure_identity_cleared` (multiply by `24`); the source
needs no heartbeat bump for it, and neither does this port. -/
theorem quintic_pure_identity [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    (24 : ℚ)⁻¹ • a ^ 4 + (24 : ℚ)⁻¹ • b ^ 4 +
    (6 : ℚ)⁻¹ • (a * b ^ 3) + (6 : ℚ)⁻¹ • (a ^ 3 * b) +
    (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2) -
    (2 : ℚ)⁻¹ • ((a + b) * ((6 : ℚ)⁻¹ • a ^ 3 + (6 : ℚ)⁻¹ • b ^ 3 +
        (2 : ℚ)⁻¹ • (a * b ^ 2) + (2 : ℚ)⁻¹ • (a ^ 2 * b)) +
      ((6 : ℚ)⁻¹ • a ^ 3 + (6 : ℚ)⁻¹ • b ^ 3 +
        (2 : ℚ)⁻¹ • (a * b ^ 2) + (2 : ℚ)⁻¹ • (a ^ 2 * b)) * (a + b)) -
    (2 : ℚ)⁻¹ • (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) ^ 2 +
    (3 : ℚ)⁻¹ • ((a + b) ^ 2 * (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) +
      (a + b) * (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) * (a + b) +
      (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) * (a + b) ^ 2) -
    (4 : ℚ)⁻¹ • (a + b) ^ 4 - bchQuarticTerm a b = 0 := by
  unfold bchQuarticTerm
  simp only [pow_succ, pow_zero, one_mul, smul_sub, smul_add, smul_smul,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

/-! ### Degree 5: the cancellation behind `bchQuinticTerm` -/

/-- **The degree-5 pure identity**: the degree-5 part of `½W5 + ⅓y3₅ - ¼y4₅ + ⅕z⁵`, written in
`z = a + b` and the degree-2/3/4 parts `T₂`, `T₃`, `T₄` of `y = exp a * exp b - 1`, minus
`bchQuinticTerm a b`, is zero.

Unlike the source's, the target's `bchQuinticGroup*` are `Finset.sum`s over word data, so the group
sums have to be expanded into monomials between `unfold` and `match_scalars`: without that step
`match_scalars` matches the group coefficients against the *unexpanded* sums and leaves false
residual goals such as `-1 / 720 = 0`. With it, no heartbeat bump is needed. -/
private theorem sextic_pure_identity [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    let z : 𝔸 := a + b
    let T₂ : 𝔸 := a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2
    let T₃ : 𝔸 := (6 : ℚ)⁻¹ • a ^ 3 + (2 : ℚ)⁻¹ • (a ^ 2 * b) +
        (2 : ℚ)⁻¹ • (a * b ^ 2) + (6 : ℚ)⁻¹ • b ^ 3
    let T₄ : 𝔸 := (24 : ℚ)⁻¹ • a ^ 4 + (6 : ℚ)⁻¹ • (a ^ 3 * b) +
        (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2) + (6 : ℚ)⁻¹ • (a * b ^ 3) +
        (24 : ℚ)⁻¹ • b ^ 4
    let W5 : 𝔸 := (60 : ℚ)⁻¹ • a ^ 5 + (60 : ℚ)⁻¹ • b ^ 5 +
        (12 : ℚ)⁻¹ • (a * b ^ 4) + (12 : ℚ)⁻¹ • (a ^ 4 * b) +
        (6 : ℚ)⁻¹ • (a ^ 2 * b ^ 3) + (6 : ℚ)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂)
    let y3_5 : 𝔸 := z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z
    let y4_5 : 𝔸 := z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3
    (2 : ℚ)⁻¹ • W5 + (3 : ℚ)⁻¹ • y3_5 - (4 : ℚ)⁻¹ • y4_5 + (5 : ℚ)⁻¹ • z ^ 5
      - bchQuinticTerm a b = 0 := by
  intro z T₂ T₃ T₄ W5 y3_5 y4_5
  show _ = (0 : 𝔸)
  simp only [show z = a + b from rfl,
    show T₂ = a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2 from rfl,
    show T₃ = (6 : ℚ)⁻¹ • a ^ 3 + (2 : ℚ)⁻¹ • (a ^ 2 * b) +
        (2 : ℚ)⁻¹ • (a * b ^ 2) + (6 : ℚ)⁻¹ • b ^ 3 from rfl,
    show T₄ = (24 : ℚ)⁻¹ • a ^ 4 + (6 : ℚ)⁻¹ • (a ^ 3 * b) +
        (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2) + (6 : ℚ)⁻¹ • (a * b ^ 3) +
        (24 : ℚ)⁻¹ • b ^ 4 from rfl,
    show W5 = (60 : ℚ)⁻¹ • a ^ 5 + (60 : ℚ)⁻¹ • b ^ 5 +
        (12 : ℚ)⁻¹ • (a * b ^ 4) + (12 : ℚ)⁻¹ • (a ^ 4 * b) +
        (6 : ℚ)⁻¹ • (a ^ 2 * b ^ 3) + (6 : ℚ)⁻¹ • (a ^ 3 * b ^ 2) -
        (z * T₄ + T₄ * z) - (T₂ * T₃ + T₃ * T₂) from rfl,
    show y3_5 = z ^ 2 * T₃ + z * T₃ * z + T₃ * z ^ 2 +
        z * T₂ ^ 2 + T₂ * z * T₂ + T₂ ^ 2 * z from rfl,
    show y4_5 = z ^ 3 * T₂ + z ^ 2 * T₂ * z + z * T₂ * z ^ 2 + T₂ * z ^ 3 from rfl]
  unfold bchQuinticTerm bchQuinticGroup1 bchQuinticGroup4
    bchQuinticGroup6 bchQuinticGroup24
  simp only [smul_add, bchQuinticGroup1Words, List.ofFn_succ, wordEval, Fin.isValue,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, mul_ite, ite_mul, Fin.sum_univ_succ,
    Bool.false_eq_true, ↓reduceIte, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const,
    Finset.card_singleton, one_smul, neg_add_rev, bchQuinticGroup4Words, bchQuinticGroup6Words,
    bchQuinticGroup24Words]
  noncomm_ring; module


/-! ### The `y`-degree pieces

The source states the degree-5…8 identities with a `let` chain of abbreviations (`z`, `T₂`, …,
`W6`, `y3_6`, …). In a *statement*, a chain that size costs 37M heartbeats to elaborate — 185× the
default budget — and no proof tactic can recover from that, so the target names the pieces as
`private def`s instead. The mathematical content is unchanged; each body is the source's own
expression, with `z` and `Tₖ` read as the `def`s above it. -/

/-- `z = a + b`: the degree-1 part of `y = exp a * exp b - 1`. -/
private def bchZ {𝔸 : Type*} [Add 𝔸] (a b : 𝔸) : 𝔸 :=
  a + b

/-- `T₂`: the degree-2 part of `y = exp a * exp b - 1`. -/
private def bchT2 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2

/-- `T₃`: the degree-3 part of `y`. -/
private def bchT3 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (6 : ℚ)⁻¹ • a ^ 3 + (2 : ℚ)⁻¹ • (a ^ 2 * b) + (2 : ℚ)⁻¹ • (a * b ^ 2) + (6 : ℚ)⁻¹ • b ^ 3

/-- `T₄`: the degree-4 part of `y`. -/
private def bchT4 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (24 : ℚ)⁻¹ • a ^ 4 + (6 : ℚ)⁻¹ • (a ^ 3 * b) + (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2) +
    (6 : ℚ)⁻¹ • (a * b ^ 3) + (24 : ℚ)⁻¹ • b ^ 4

/-- `T₅`: the degree-5 part of `y`. -/
private def bchT5 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (120 : ℚ)⁻¹ • a ^ 5 + (24 : ℚ)⁻¹ • (a ^ 4 * b) + (12 : ℚ)⁻¹ • (a ^ 3 * b ^ 2) +
    (12 : ℚ)⁻¹ • (a ^ 2 * b ^ 3) + (24 : ℚ)⁻¹ • (a * b ^ 4) + (120 : ℚ)⁻¹ • b ^ 5

/-- `W6 = 2·y_d6 - (y²)_d6`, the degree-6 part of `2y - y²`: the explicit degree-6 words minus the
degree-6 part of `y² = z·T₅ + T₂·T₄ + T₃·T₃ + T₄·T₂ + T₅·z`. -/
private def bchW6 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (360 : ℚ)⁻¹ • a ^ 6 + (60 : ℚ)⁻¹ • (a ^ 5 * b) + (24 : ℚ)⁻¹ • (a ^ 4 * b ^ 2) +
    (18 : ℚ)⁻¹ • (a ^ 3 * b ^ 3) + (24 : ℚ)⁻¹ • (a ^ 2 * b ^ 4) + (60 : ℚ)⁻¹ • (a * b ^ 5) +
    (360 : ℚ)⁻¹ • b ^ 6 -
    (bchZ a b * bchT5 a b + bchT2 a b * bchT4 a b + bchT3 a b * bchT3 a b +
      bchT4 a b * bchT2 a b + bchT5 a b * bchZ a b)

/-- `y3₆ = (y³)_d6`: the ten degree-6 products of three `y`-parts. -/
private def bchY3Deg6 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 2 * bchT4 a b + bchZ a b * bchT4 a b * bchZ a b + bchT4 a b * bchZ a b ^ 2 +
    bchZ a b * bchT2 a b * bchT3 a b + bchZ a b * bchT3 a b * bchT2 a b +
    bchT2 a b * bchZ a b * bchT3 a b + bchT2 a b * bchT3 a b * bchZ a b +
    bchT3 a b * bchZ a b * bchT2 a b + bchT3 a b * bchT2 a b * bchZ a b + bchT2 a b ^ 3

/-- `y4₆ = (y⁴)_d6`: the ten degree-6 products of four `y`-parts. -/
private def bchY4Deg6 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 3 * bchT3 a b + bchZ a b ^ 2 * bchT3 a b * bchZ a b +
    bchZ a b * bchT3 a b * bchZ a b ^ 2 + bchT3 a b * bchZ a b ^ 3 +
    bchZ a b ^ 2 * bchT2 a b ^ 2 + bchZ a b * bchT2 a b * bchZ a b * bchT2 a b +
    bchZ a b * bchT2 a b ^ 2 * bchZ a b + bchT2 a b * bchZ a b ^ 2 * bchT2 a b +
    bchT2 a b * bchZ a b * bchT2 a b * bchZ a b + bchT2 a b ^ 2 * bchZ a b ^ 2

/-- `y5₆ = (y⁵)_d6`: the five degree-6 products of five `y`-parts. -/
private def bchY5Deg6 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 4 * bchT2 a b + bchZ a b ^ 3 * bchT2 a b * bchZ a b +
    bchZ a b ^ 2 * bchT2 a b * bchZ a b ^ 2 + bchZ a b * bchT2 a b * bchZ a b ^ 3 +
    bchT2 a b * bchZ a b ^ 4

/-- `bchSexticTerm` as an explicit monomial chain, for the cancellation identities: proving the
expansion in its own small goal keeps those identities inside the default heartbeat
budget (the `simp only` expansion costs `lemmas × subterms`, so it must not run on the
whole identity). Generated by `scripts/gen_bch_higher_terms.py`. -/
private lemma bchSexticTerm_expand {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    bchSexticTerm a b =
      (-1 / 1440 : ℚ) • (a * a * a * a * b * b) + (4 / 1440 : ℚ) • (a * a * a * b * a * b) +
      (4 / 1440 : ℚ) • (a * a * a * b * b * b) + (-6 / 1440 : ℚ) • (a * a * b * a * a * b) +
      (-6 / 1440 : ℚ) • (a * a * b * a * b * b) + (-6 / 1440 : ℚ) • (a * a * b * b * a * b) +
      (-1 / 1440 : ℚ) • (a * a * b * b * b * b) + (4 / 1440 : ℚ) • (a * b * a * a * a * b) +
      (-6 / 1440 : ℚ) • (a * b * a * a * b * b) + (24 / 1440 : ℚ) • (a * b * a * b * a * b) +
      (4 / 1440 : ℚ) • (a * b * a * b * b * b) + (-6 / 1440 : ℚ) • (a * b * b * a * a * b) +
      (-6 / 1440 : ℚ) • (a * b * b * a * b * b) + (4 / 1440 : ℚ) • (a * b * b * b * a * b) +
      (-4 / 1440 : ℚ) • (b * a * a * a * b * a) + (6 / 1440 : ℚ) • (b * a * a * b * a * a) +
      (6 / 1440 : ℚ) • (b * a * a * b * b * a) + (-4 / 1440 : ℚ) • (b * a * b * a * a * a) +
      (-24 / 1440 : ℚ) • (b * a * b * a * b * a) + (6 / 1440 : ℚ) • (b * a * b * b * a * a) +
      (-4 / 1440 : ℚ) • (b * a * b * b * b * a) + (1 / 1440 : ℚ) • (b * b * a * a * a * a) +
      (6 / 1440 : ℚ) • (b * b * a * a * b * a) + (6 / 1440 : ℚ) • (b * b * a * b * a * a) +
      (6 / 1440 : ℚ) • (b * b * a * b * b * a) + (-4 / 1440 : ℚ) • (b * b * b * a * a * a) +
      (-4 / 1440 : ℚ) • (b * b * b * a * b * a) + (1 / 1440 : ℚ) • (b * b * b * b * a * a)
  := by
  unfold bchSexticTerm
  simp only [one_smul, bchSexticTermCoeffs, bchSexticTermWords, List.ofFn_succ, List.ofFn_zero,
    wordEval, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_succ, List.prod_cons, List.prod_nil, mul_one, mul_ite, ite_mul,
    Fin.sum_univ_succ, Bool.false_eq_true, ↓reduceIte, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_const, Finset.card_singleton]
  noncomm_ring

end FQFP.BCH
