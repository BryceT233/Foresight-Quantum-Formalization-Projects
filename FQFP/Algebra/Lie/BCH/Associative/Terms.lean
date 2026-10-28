/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.Basic
public import FQFP.Algebra.Word.Table
public import Mathlib.Algebra.Module.Rat

/-!
# Homogeneous BCH polynomials

The degree-three through degree-eight BCH polynomials and their algebraic identities.
The coefficients are rational, and no topology or norm is used. Noncommutative words
are evaluated with `List.prod`; integer coefficient tables certify the higher-degree
identities without changing the rational polynomials they represent.

## Main definitions

* `bchCubicTerm`, `bchQuarticTerm`, `bchQuinticTerm`: the low-degree polynomials.
* `bchSexticTerm`, `bchSepticTerm`, `bchOcticTerm`: evaluation of integer word tables.

## Main results

* The `bchCubicTerm_smul`, `bchQuarticTerm_smul`, and `bchQuinticTerm_smul`
  homogeneity identities.
* The cubic and quartic linear/quadratic decompositions in the first argument.
* `bchCubicTerm_residual_eq`, `bchCommutator_residual_eq`: exact residual identities for
  arbitrary approximations to the exponentials.
-/

@[expose] public section

namespace FQFP.BCH

open WordTable

variable {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸]

/-- The denominator scale for the degree-three through degree-eight BCH certificates.
Its prime factors clear the rational coefficients at these degrees. -/
def coefficientScale : ℚ := 210

noncomputable section

/-- The degree-3 BCH term: `(1/12)([a,[a,b]] + [b,[b,a]])` with `[x,y] = x * y - y * x`.

This is the leading cubic correction to the BCH element,
`bch a b = a + b + ½[a,b] + bchCubicTerm a b + O(s⁴)`. -/
noncomputable def bchCubicTerm {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (12 : ℚ)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a) +
  (12 : ℚ)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)

/-- **Homogeneity of `bchCubicTerm`**: `C₃(c·a, c·b) = c³·C₃(a,b)`.

This is the property that lets the Suzuki condition `4p³ + (1-4p)³ = 0` kill the cubic term. -/
theorem bchCubicTerm_smul {R : Type*} [CommSemiring R] [Algebra R 𝔸] (a b : 𝔸) (c : R) :
    bchCubicTerm (c • a) (c • b) = c ^ 3 • bchCubicTerm a b := by
  have triple : ∀ x y z : 𝔸, (c • x) * ((c • y) * (c • z)) = c ^ 3 • (x * (y * z)) := by
    intro x y z
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1; ring
  have triple' : ∀ x y z : 𝔸, ((c • x) * (c • y)) * (c • z) = c ^ 3 • (x * y * z) := by
    intro x y z
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1; ring
  unfold bchCubicTerm
  simp only [mul_sub, sub_mul, triple, triple', ← smul_sub, smul_comm (c ^ 3) ((12 : ℚ)⁻¹),
    ← smul_add]
/-- **`C₃` decomposition along `x ↦ x + W`**: the difference `C₃(x+W,y) - C₃(x,y)` is
`(1/12)·`(a part linear in `W`) plus `(1/12)·`(a part quadratic in `W`).

This refines the telescoping identity behind `norm_bchCubicTerm_diff_le`, which only sees the
collapsed form. When `x, y = O(s)` and `W = O(s²)`, the linear part is `O(s⁴)`
and the quadratic part is `O(s⁵)`. -/
theorem bchCubicTerm_LQ_decomp (x W y : 𝔸) :
    bchCubicTerm (x + W) y - bchCubicTerm x y =
      (12 : ℚ)⁻¹ • (
        x * W * y + W * x * y - x * y * W - x * y * W - W * y * x - W * y * x +
        y * x * W + y * W * x + y * y * W - y * W * y - y * W * y + W * y * y) +
      (12 : ℚ)⁻¹ • (
        W * W * y - W * y * W - W * y * W + y * W * W) := by
  unfold bchCubicTerm
  simp only [smul_sub, smul_add, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

/-! ### The degree-4 term -/

/-- The degree-4 BCH term: `-(1/24) [b,[a,[a,b]]]`, the quartic correction in
`bch a b = a + b + ½[a,b] + C₃(a,b) + C₄(a,b) + O(s⁵)`.

In the free Lie algebra `[b,[a,[a,b]]] + [a,[b,[b,a]]] = 0`, so this single triple bracket also
equals `(1/24)[a,[b,[b,a]]]`; the sign convention is the one that makes the expansion of
`bch a b` come out right. -/
noncomputable def bchQuarticTerm {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  -((24 : ℚ)⁻¹ • (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
    (a * (a * b - b * a) - (a * b - b * a) * a) * b))

/-- **Homogeneity of `bchQuarticTerm`**: `C₄(c·a, c·b) = c⁴·C₄(a,b)`.

The inner double bracket is cubic in `(a,b)`, and the outer one adds one more factor of `c`. The
proof is the source's: push the scalars outwards, then split the resulting scalar equalities. -/
theorem bchQuarticTerm_smul {R : Type*} [CommSemiring R] [Algebra R 𝔸] (a b : 𝔸) (c : R) :
    bchQuarticTerm (c • a) (c • b) = c ^ 4 • bchQuarticTerm a b := by
  unfold bchQuarticTerm
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, mul_sub, sub_mul, smul_smul,
    smul_neg, neg_inj]
  ring_nf
  simp only [smul_comm (1 / 24 : ℚ) (c ^ 4)]

/-- **`C₄` decomposition along `x ↦ x + W`**: the difference `C₄(x+W,y) - C₄(x,y)` is
`(1/24)·`(a part linear in `W`) plus `(1/24)·`(a part quadratic in `W`).

The degree-4 analogue of `bchCubicTerm_LQ_decomp`. It extracts the degree-5 (linear in `W` when
`W = O(s²)`) and degree-6 (quadratic in `W`) leading parts of the quartic difference. -/
theorem bchQuarticTerm_LQ_decomp (x W y : 𝔸) :
    bchQuarticTerm (x + W) y - bchQuarticTerm x y =
      (24 : ℚ)⁻¹ • (
        x * W * y * y + W * x * y * y - x * y * W * y - x * y * W * y -
        W * y * x * y - W * y * x * y +
        y * W * y * x + y * W * y * x + y * x * y * W + y * x * y * W -
        y * y * x * W - y * y * W * x) +
      (24 : ℚ)⁻¹ • (
        W * W * y * y - W * y * W * y - W * y * W * y +
        y * W * y * W + y * W * y * W - y * y * W * W) := by
  unfold bchQuarticTerm
  simp only [smul_sub, smul_add, mul_add, add_mul, mul_sub, sub_mul, sub_neg_eq_add,
    ← mul_assoc]
  match_scalars <;> ring

/-! ### The degree-5 term

The four groups are sums over an explicit list of **word patterns** (`0` is the letter `a`),
in the form consumed by `norm_sum_wordEval_le_of_pos`: the word data is a
`Fin m → Fin 5 → Fin 2`, so the norm bound of a group is one application of the group lemma rather
than one estimate per word. -/

/-- The four word patterns of `bchQuinticGroup1`: the "almost pure" words `AAAAB`, `ABBBB`, `BAAAA`,
`BBBBA`. -/
def bchQuinticGroup1Words : Fin 4 → Fin 5 → Fin 2 :=
  ![![0, 0, 0, 0, 1], ![0, 1, 1, 1, 1],
    ![1, 0, 0, 0, 0], ![1, 1, 1, 1, 0]]

/-- The ten word patterns of `bchQuinticGroup4`. -/
def bchQuinticGroup4Words : Fin 10 → Fin 5 → Fin 2 :=
  ![![0, 0, 0, 1, 0], ![0, 0, 0, 1, 1],
    ![0, 0, 1, 1, 1], ![0, 1, 0, 0, 0],
    ![0, 1, 1, 1, 0], ![1, 0, 0, 0, 1],
    ![1, 0, 1, 1, 1], ![1, 1, 0, 0, 0],
    ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 1]]

/-- The fourteen word patterns of `bchQuinticGroup6`. -/
def bchQuinticGroup6Words : Fin 14 → Fin 5 → Fin 2 :=
  ![![0, 0, 1, 0, 0], ![0, 0, 1, 0, 1],
    ![0, 0, 1, 1, 0], ![0, 1, 0, 0, 1],
    ![0, 1, 0, 1, 1], ![0, 1, 1, 0, 0],
    ![0, 1, 1, 0, 1], ![1, 0, 0, 1, 0],
    ![1, 0, 0, 1, 1], ![1, 0, 1, 0, 0],
    ![1, 0, 1, 1, 0], ![1, 1, 0, 0, 1],
    ![1, 1, 0, 1, 0], ![1, 1, 0, 1, 1]]

/-- The two palindromic word patterns of `bchQuinticGroup24`. -/
def bchQuinticGroup24Words : Fin 2 → Fin 5 → Fin 2 :=
  ![![0, 1, 0, 1, 0], ![1, 0, 1, 0, 1]]

/-- **Coefficient-1 group** of `bchQuinticTerm`: the four 5-letter words whose coefficient has
absolute value 1. -/
noncomputable def bchQuinticGroup1 {𝔸 : Type*} [Semiring 𝔸] (a b : 𝔸) : 𝔸 :=
  ∑ i, wordEval ![a, b] (bchQuinticGroup1Words i)

/-- **Coefficient-4 group** of `bchQuinticTerm`: the ten 5-letter words whose coefficient has
absolute value 4. -/
noncomputable def bchQuinticGroup4 {𝔸 : Type*} [Semiring 𝔸] (a b : 𝔸) : 𝔸 :=
  ∑ i, wordEval ![a, b] (bchQuinticGroup4Words i)

/-- **Coefficient-6 group** of `bchQuinticTerm`: the fourteen 5-letter words whose coefficient has
absolute value 6. -/
noncomputable def bchQuinticGroup6 {𝔸 : Type*} [Semiring 𝔸] (a b : 𝔸) : 𝔸 :=
  ∑ i, wordEval ![a, b] (bchQuinticGroup6Words i)

/-- **Coefficient-24 group** of `bchQuinticTerm`: the two palindromic 5-letter words whose
coefficient has absolute value 24. -/
noncomputable def bchQuinticGroup24 {𝔸 : Type*} [Semiring 𝔸] (a b : 𝔸) : 𝔸 :=
  ∑ i, wordEval ![a, b] (bchQuinticGroup24Words i)

/-- The degree-5 BCH term: the degree-5 part of `bch a b = log (exp a * exp b)`.

It involves 30 of the 32 five-letter words on `{a, b}`: the pure words `aaaaa` and `bbbbb` are
absent, since `bch a 0 = a` and `bch 0 b = b` have no quintic correction. The common denominator is
`720`. The words are collected into four groups by the absolute value of their coefficient (`1`,
`4`, `6`, `24`), which keeps the homogeneity and norm bookkeeping uniform. -/
noncomputable def bchQuinticTerm {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (720 : ℚ)⁻¹ • (
    -bchQuinticGroup1 a b + (4 : ℚ) • bchQuinticGroup4 a b -
      (6 : ℚ) • bchQuinticGroup6 a b + (24 : ℚ) • bchQuinticGroup24 a b)

/-- The degree-five certificate, derived from the same four word families as
`bchQuinticTerm`. Each integer coefficient is the rational coefficient multiplied by
`coefficientScale ^ 5`. -/
def bchQuinticTermTable : WordTable.Table (Fin 2) :=
  (List.ofFn fun i => (List.ofFn (bchQuinticGroup1Words i), -567236250)) ++
    (List.ofFn fun i => (List.ofFn (bchQuinticGroup4Words i), 2268945000)) ++
    (List.ofFn fun i => (List.ofFn (bchQuinticGroup6Words i), -3403417500)) ++
    (List.ofFn fun i => (List.ofFn (bchQuinticGroup24Words i), 13613670000))

/-- Evaluation of the degree-five certificate is the quintic BCH polynomial. -/
lemma eval_bchQuinticTermTable {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] bchQuinticTermTable = bchQuinticTerm a b := by
  simp only [bchQuinticTermTable, eval_append, eval_ofFn, bchQuinticTerm,
    bchQuinticGroup1, bchQuinticGroup4, bchQuinticGroup6, bchQuinticGroup24, wordEval]
  norm_num [coefficientScale]
  module

/-! #### Homogeneity of the degree-5 term -/

theorem bchQuinticGroup1_smul {R 𝔸 : Type*} [CommSemiring R] [Semiring 𝔸] [Algebra R 𝔸]
    (a b : 𝔸) (c : R) : bchQuinticGroup1 (c • a) (c • b) = c ^ 5 • bchQuinticGroup1 a b := by
  unfold bchQuinticGroup1
  exact sum_prod_map_smul (![a, b] : Fin 2 → 𝔸) bchQuinticGroup1Words c

theorem bchQuinticGroup4_smul {R 𝔸 : Type*} [CommSemiring R] [Semiring 𝔸] [Algebra R 𝔸]
    (a b : 𝔸) (c : R) : bchQuinticGroup4 (c • a) (c • b) = c ^ 5 • bchQuinticGroup4 a b := by
  unfold bchQuinticGroup4
  exact sum_prod_map_smul (![a, b] : Fin 2 → 𝔸) bchQuinticGroup4Words c

theorem bchQuinticGroup6_smul {R 𝔸 : Type*} [CommSemiring R] [Semiring 𝔸] [Algebra R 𝔸]
    (a b : 𝔸) (c : R) : bchQuinticGroup6 (c • a) (c • b) = c ^ 5 • bchQuinticGroup6 a b := by
  unfold bchQuinticGroup6
  exact sum_prod_map_smul (![a, b] : Fin 2 → 𝔸) bchQuinticGroup6Words c

theorem bchQuinticGroup24_smul {R 𝔸 : Type*} [CommSemiring R] [Semiring 𝔸] [Algebra R 𝔸]
    (a b : 𝔸) (c : R) : bchQuinticGroup24 (c • a) (c • b) = c ^ 5 • bchQuinticGroup24 a b := by
  unfold bchQuinticGroup24
  exact sum_prod_map_smul (![a, b] : Fin 2 → 𝔸) bchQuinticGroup24Words c

/-- **Homogeneity of `bchQuinticTerm`**: `C₅(c·a, c·b) = c⁵·C₅(a,b)`. -/
theorem bchQuinticTerm_smul {R : Type*} [CommSemiring R] [Algebra R 𝔸] (a b : 𝔸) (c : R) :
    bchQuinticTerm (c • a) (c • b) = c ^ 5 • bchQuinticTerm a b := by
  unfold bchQuinticTerm
  rw [bchQuinticGroup1_smul, bchQuinticGroup4_smul, bchQuinticGroup6_smul,
    bchQuinticGroup24_smul]
  -- Pull `c ^ 5` out of each scaled group, then out of the outer `(720)⁻¹` scaling.
  rw [smul_comm ((4 : ℚ)) (c ^ 5), smul_comm ((6 : ℚ)) (c ^ 5),
    smul_comm ((24 : ℚ)) (c ^ 5),
    ← smul_neg, ← smul_add, ← smul_sub, ← smul_add,
    smul_comm ((720 : ℚ)⁻¹) (c ^ 5)]

/-! ### The degree-6, -7 and -8 terms

`bchSexticTerm` / `bchSepticTerm` / `bchOcticTerm` are the degree-6/7/8 parts of
`bch a b = log (exp a * exp b)`, the next three after `bchQuinticTerm`.

The degree-6, degree-7 and degree-8 terms are stated over their **tables**: a `List` of
`(word, coefficient)` rows, which is the single object that the word and coefficient arrays of the
source present as two projections. Their coefficients are the paper's rationals cleared by
`coefficientScale ^ d`,
the integer presentation of `FQFP.Algebra.Word.Table`.

Denominators and the constants behind the `s ^ k` bounds: `28 · 24/1440 = 7/15`,
`126 · 216/30240 = 9/10` and `124 · 432/120960 = 31/70`, all `≤ 1`.

The cancellation identities through degree eight are proved in `DynkinReeSextic`,
`DynkinReeSeptic`, and `DynkinReeOctic`. The norm bounds are in `BCHTerms`. -/

/-- **The degree-6 table**: the 28 monomials of the source's `bch_sextic_term`, in the source's
order (`0` is the letter `a`).

The paper's coefficients are the rationals `±1/1440`, `±1/360`, `±1/240`, `±1/60`; the table stores
them cleared by `coefficientScale ^ 6` (`coefficientScale = 210`, so `coefficientScale ^ 6 =
85766121000000`), which is the integer
presentation used to certify the cancellation identities. `WordTable.eval` interprets
each integer coefficient at its rational scale.

This replaces a `Fin 28 → Fin 6 → Fin 2` word array paired with a `Fin 28 → ℚ` coefficient
array: the two are one object — an element of the free word algebra — and pairing them by index
is what a table says directly. -/
def bchSexticTermTable : WordTable.Table (Fin 2) :=
  [([0, 0, 0, 0, 1, 1], -59559806250),
    ([0, 0, 0, 1, 0, 1], 238239225000),
    ([0, 0, 0, 1, 1, 1], 238239225000),
    ([0, 0, 1, 0, 0, 1], -357358837500),
    ([0, 0, 1, 0, 1, 1], -357358837500),
    ([0, 0, 1, 1, 0, 1], -357358837500),
    ([0, 0, 1, 1, 1, 1], -59559806250),
    ([0, 1, 0, 0, 0, 1], 238239225000),
    ([0, 1, 0, 0, 1, 1], -357358837500),
    ([0, 1, 0, 1, 0, 1], 1429435350000),
    ([0, 1, 0, 1, 1, 1], 238239225000),
    ([0, 1, 1, 0, 0, 1], -357358837500),
    ([0, 1, 1, 0, 1, 1], -357358837500),
    ([0, 1, 1, 1, 0, 1], 238239225000),
    ([1, 0, 0, 0, 1, 0], -238239225000),
    ([1, 0, 0, 1, 0, 0], 357358837500),
    ([1, 0, 0, 1, 1, 0], 357358837500),
    ([1, 0, 1, 0, 0, 0], -238239225000),
    ([1, 0, 1, 0, 1, 0], -1429435350000),
    ([1, 0, 1, 1, 0, 0], 357358837500),
    ([1, 0, 1, 1, 1, 0], -238239225000),
    ([1, 1, 0, 0, 0, 0], 59559806250),
    ([1, 1, 0, 0, 1, 0], 357358837500),
    ([1, 1, 0, 1, 0, 0], 357358837500),
    ([1, 1, 0, 1, 1, 0], 357358837500),
    ([1, 1, 1, 0, 0, 0], -238239225000),
    ([1, 1, 1, 0, 1, 0], -238239225000),
    ([1, 1, 1, 1, 0, 0], 59559806250)]

/-- **The degree-7 table**: the 126 monomials of the source's `bch_septic_term`, in the
source's order (`0` is the letter `a`).

The paper's coefficients are the rationals `k/30240` of the source's `bch_septic_term`,
cleared by `coefficientScale ^ 7` (`coefficientScale = 210`, so `coefficientScale ^ 7 =
18010885410000000`); the rational data is
interpreted at its rational scale by `WordTable.eval`.

This replaces a `Fin 126 → Fin 7 → Fin 2` word array paired with a `Fin 126 → ℚ`
coefficient array, exactly as `bchSexticTermTable` replaced the degree-6 pair: the two are
one object, and the single list is what the cancellation identity computes with. -/
def bchSepticTermTable : WordTable.Table (Fin 2) :=
  [
    ([0, 0, 0, 0, 0, 0, 1], 595598062500),
    ([0, 0, 0, 0, 0, 1, 0], -3573588375000),
    ([0, 0, 0, 0, 0, 1, 1], -3573588375000),
    ([0, 0, 0, 0, 1, 0, 0], 8933970937500),
    ([0, 0, 0, 0, 1, 0, 1], 8933970937500),
    ([0, 0, 0, 0, 1, 1, 0], 8933970937500),
    ([0, 0, 0, 0, 1, 1, 1], 4764784500000),
    ([0, 0, 0, 1, 0, 0, 0], -11911961250000),
    ([0, 0, 0, 1, 0, 0, 1], -3573588375000),
    ([0, 0, 0, 1, 0, 1, 0], -28588707000000),
    ([0, 0, 0, 1, 0, 1, 1], -3573588375000),
    ([0, 0, 0, 1, 1, 0, 0], -3573588375000),
    ([0, 0, 0, 1, 1, 0, 1], -3573588375000),
    ([0, 0, 0, 1, 1, 1, 0], -11911961250000),
    ([0, 0, 0, 1, 1, 1, 1], 4764784500000),
    ([0, 0, 1, 0, 0, 0, 0], 8933970937500),
    ([0, 0, 1, 0, 0, 0, 1], -3573588375000),
    ([0, 0, 1, 0, 0, 1, 0], 21441530250000),
    ([0, 0, 1, 0, 0, 1, 1], -16081147687500),
    ([0, 0, 1, 0, 1, 0, 0], 21441530250000),
    ([0, 0, 1, 0, 1, 0, 1], 21441530250000),
    ([0, 0, 1, 0, 1, 1, 0], 21441530250000),
    ([0, 0, 1, 0, 1, 1, 1], -3573588375000),
    ([0, 0, 1, 1, 0, 0, 0], -3573588375000),
    ([0, 0, 1, 1, 0, 0, 1], -16081147687500),
    ([0, 0, 1, 1, 0, 1, 0], 21441530250000),
    ([0, 0, 1, 1, 0, 1, 1], -16081147687500),
    ([0, 0, 1, 1, 1, 0, 0], -3573588375000),
    ([0, 0, 1, 1, 1, 0, 1], -3573588375000),
    ([0, 0, 1, 1, 1, 1, 0], 8933970937500),
    ([0, 0, 1, 1, 1, 1, 1], -3573588375000),
    ([0, 1, 0, 0, 0, 0, 0], -3573588375000),
    ([0, 1, 0, 0, 0, 0, 1], 8933970937500),
    ([0, 1, 0, 0, 0, 1, 0], -28588707000000),
    ([0, 1, 0, 0, 0, 1, 1], -3573588375000),
    ([0, 1, 0, 0, 1, 0, 0], 21441530250000),
    ([0, 1, 0, 0, 1, 0, 1], 21441530250000),
    ([0, 1, 0, 0, 1, 1, 0], 21441530250000),
    ([0, 1, 0, 0, 1, 1, 1], -3573588375000),
    ([0, 1, 0, 1, 0, 0, 0], -28588707000000),
    ([0, 1, 0, 1, 0, 0, 1], 21441530250000),
    ([0, 1, 0, 1, 0, 1, 0], -128649181500000),
    ([0, 1, 0, 1, 0, 1, 1], 21441530250000),
    ([0, 1, 0, 1, 1, 0, 0], 21441530250000),
    ([0, 1, 0, 1, 1, 0, 1], 21441530250000),
    ([0, 1, 0, 1, 1, 1, 0], -28588707000000),
    ([0, 1, 0, 1, 1, 1, 1], 8933970937500),
    ([0, 1, 1, 0, 0, 0, 0], 8933970937500),
    ([0, 1, 1, 0, 0, 0, 1], -3573588375000),
    ([0, 1, 1, 0, 0, 1, 0], 21441530250000),
    ([0, 1, 1, 0, 0, 1, 1], -16081147687500),
    ([0, 1, 1, 0, 1, 0, 0], 21441530250000),
    ([0, 1, 1, 0, 1, 0, 1], 21441530250000),
    ([0, 1, 1, 0, 1, 1, 0], 21441530250000),
    ([0, 1, 1, 0, 1, 1, 1], -3573588375000),
    ([0, 1, 1, 1, 0, 0, 0], -11911961250000),
    ([0, 1, 1, 1, 0, 0, 1], -3573588375000),
    ([0, 1, 1, 1, 0, 1, 0], -28588707000000),
    ([0, 1, 1, 1, 0, 1, 1], -3573588375000),
    ([0, 1, 1, 1, 1, 0, 0], 8933970937500),
    ([0, 1, 1, 1, 1, 0, 1], 8933970937500),
    ([0, 1, 1, 1, 1, 1, 0], -3573588375000),
    ([0, 1, 1, 1, 1, 1, 1], 595598062500),
    ([1, 0, 0, 0, 0, 0, 0], 595598062500),
    ([1, 0, 0, 0, 0, 0, 1], -3573588375000),
    ([1, 0, 0, 0, 0, 1, 0], 8933970937500),
    ([1, 0, 0, 0, 0, 1, 1], 8933970937500),
    ([1, 0, 0, 0, 1, 0, 0], -3573588375000),
    ([1, 0, 0, 0, 1, 0, 1], -28588707000000),
    ([1, 0, 0, 0, 1, 1, 0], -3573588375000),
    ([1, 0, 0, 0, 1, 1, 1], -11911961250000),
    ([1, 0, 0, 1, 0, 0, 0], -3573588375000),
    ([1, 0, 0, 1, 0, 0, 1], 21441530250000),
    ([1, 0, 0, 1, 0, 1, 0], 21441530250000),
    ([1, 0, 0, 1, 0, 1, 1], 21441530250000),
    ([1, 0, 0, 1, 1, 0, 0], -16081147687500),
    ([1, 0, 0, 1, 1, 0, 1], 21441530250000),
    ([1, 0, 0, 1, 1, 1, 0], -3573588375000),
    ([1, 0, 0, 1, 1, 1, 1], 8933970937500),
    ([1, 0, 1, 0, 0, 0, 0], 8933970937500),
    ([1, 0, 1, 0, 0, 0, 1], -28588707000000),
    ([1, 0, 1, 0, 0, 1, 0], 21441530250000),
    ([1, 0, 1, 0, 0, 1, 1], 21441530250000),
    ([1, 0, 1, 0, 1, 0, 0], 21441530250000),
    ([1, 0, 1, 0, 1, 0, 1], -128649181500000),
    ([1, 0, 1, 0, 1, 1, 0], 21441530250000),
    ([1, 0, 1, 0, 1, 1, 1], -28588707000000),
    ([1, 0, 1, 1, 0, 0, 0], -3573588375000),
    ([1, 0, 1, 1, 0, 0, 1], 21441530250000),
    ([1, 0, 1, 1, 0, 1, 0], 21441530250000),
    ([1, 0, 1, 1, 0, 1, 1], 21441530250000),
    ([1, 0, 1, 1, 1, 0, 0], -3573588375000),
    ([1, 0, 1, 1, 1, 0, 1], -28588707000000),
    ([1, 0, 1, 1, 1, 1, 0], 8933970937500),
    ([1, 0, 1, 1, 1, 1, 1], -3573588375000),
    ([1, 1, 0, 0, 0, 0, 0], -3573588375000),
    ([1, 1, 0, 0, 0, 0, 1], 8933970937500),
    ([1, 1, 0, 0, 0, 1, 0], -3573588375000),
    ([1, 1, 0, 0, 0, 1, 1], -3573588375000),
    ([1, 1, 0, 0, 1, 0, 0], -16081147687500),
    ([1, 1, 0, 0, 1, 0, 1], 21441530250000),
    ([1, 1, 0, 0, 1, 1, 0], -16081147687500),
    ([1, 1, 0, 0, 1, 1, 1], -3573588375000),
    ([1, 1, 0, 1, 0, 0, 0], -3573588375000),
    ([1, 1, 0, 1, 0, 0, 1], 21441530250000),
    ([1, 1, 0, 1, 0, 1, 0], 21441530250000),
    ([1, 1, 0, 1, 0, 1, 1], 21441530250000),
    ([1, 1, 0, 1, 1, 0, 0], -16081147687500),
    ([1, 1, 0, 1, 1, 0, 1], 21441530250000),
    ([1, 1, 0, 1, 1, 1, 0], -3573588375000),
    ([1, 1, 0, 1, 1, 1, 1], 8933970937500),
    ([1, 1, 1, 0, 0, 0, 0], 4764784500000),
    ([1, 1, 1, 0, 0, 0, 1], -11911961250000),
    ([1, 1, 1, 0, 0, 1, 0], -3573588375000),
    ([1, 1, 1, 0, 0, 1, 1], -3573588375000),
    ([1, 1, 1, 0, 1, 0, 0], -3573588375000),
    ([1, 1, 1, 0, 1, 0, 1], -28588707000000),
    ([1, 1, 1, 0, 1, 1, 0], -3573588375000),
    ([1, 1, 1, 0, 1, 1, 1], -11911961250000),
    ([1, 1, 1, 1, 0, 0, 0], 4764784500000),
    ([1, 1, 1, 1, 0, 0, 1], 8933970937500),
    ([1, 1, 1, 1, 0, 1, 0], 8933970937500),
    ([1, 1, 1, 1, 0, 1, 1], 8933970937500),
    ([1, 1, 1, 1, 1, 0, 0], -3573588375000),
    ([1, 1, 1, 1, 1, 0, 1], -3573588375000),
    ([1, 1, 1, 1, 1, 1, 0], 595598062500)]

/-- **Degree-6 term** `C₆(a,b)`: the degree-6 part of `bch a b`, evaluated from its table.

The table is the term: `eval coefficientScale ![a, b]` multiplies out each row's word and weights
it by the row's
coefficient over `coefficientScale ^ 6`, so the definition *is* the word data. -/
noncomputable def bchSexticTerm {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  eval coefficientScale ![a, b] bchSexticTermTable
/-- **Degree-7 term** `C₇(a,b)`: the degree-7 part of `bch a b`, evaluated from its table.

The table is the term: `eval coefficientScale ![a, b]` multiplies out each row's word and weights
it by the row's
coefficient over `coefficientScale ^ 7`, so the definition *is* the word data. -/
noncomputable def bchSepticTerm {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  eval coefficientScale ![a, b] bchSepticTermTable
/-- **The degree-8 table**: the 124 monomials of the source's `bch_octic_term`, in the source's
order (`0` is the letter `a`).

The paper's coefficients are the rationals `k/120960` of the source's `bch_octic_term`, cleared by
`coefficientScale ^ 8` (`coefficientScale = 210`, so `coefficientScale ^ 8 =
3782285936100000000`); `WordTable.eval` interprets the rational coefficients,
which is what the norm bound below consumes.

This replaces a `Fin 124 → Fin 8 → Fin 2` word array paired with a `Fin 124 → ℚ` coefficient array,
exactly as `bchSexticTermTable` and `bchSepticTermTable` replaced the degree-6 and degree-7 pairs:
the two are one object, and the single list is what the cancellation identity computes with. -/
def bchOcticTermTable : WordTable.Table (Fin 2) :=
  [([0, 0, 0, 0, 0, 0, 1, 1], 62537796562500),
    ([0, 0, 0, 0, 0, 1, 0, 1], -375226779375000),
    ([0, 0, 0, 0, 0, 1, 1, 1], -375226779375000),
    ([0, 0, 0, 0, 1, 0, 0, 1], 938066948437500),
    ([0, 0, 0, 0, 1, 0, 1, 1], 938066948437500),
    ([0, 0, 0, 0, 1, 1, 0, 1], 938066948437500),
    ([0, 0, 0, 0, 1, 1, 1, 1], 719184660468750),
    ([0, 0, 0, 1, 0, 0, 0, 1], -1250755931250000),
    ([0, 0, 0, 1, 0, 0, 1, 1], -375226779375000),
    ([0, 0, 0, 1, 0, 1, 0, 1], -3001814235000000),
    ([0, 0, 0, 1, 0, 1, 1, 1], -1250755931250000),
    ([0, 0, 0, 1, 1, 0, 0, 1], -375226779375000),
    ([0, 0, 0, 1, 1, 0, 1, 1], -375226779375000),
    ([0, 0, 0, 1, 1, 1, 0, 1], -1250755931250000),
    ([0, 0, 0, 1, 1, 1, 1, 1], -375226779375000),
    ([0, 0, 1, 0, 0, 0, 0, 1], 938066948437500),
    ([0, 0, 1, 0, 0, 0, 1, 1], -375226779375000),
    ([0, 0, 1, 0, 0, 1, 0, 1], 2251360676250000),
    ([0, 0, 1, 0, 0, 1, 1, 1], -375226779375000),
    ([0, 0, 1, 0, 1, 0, 0, 1], 2251360676250000),
    ([0, 0, 1, 0, 1, 0, 1, 1], 2251360676250000),
    ([0, 0, 1, 0, 1, 1, 0, 1], 2251360676250000),
    ([0, 0, 1, 0, 1, 1, 1, 1], 938066948437500),
    ([0, 0, 1, 1, 0, 0, 0, 1], -375226779375000),
    ([0, 0, 1, 1, 0, 0, 1, 1], -1688520507187500),
    ([0, 0, 1, 1, 0, 1, 0, 1], 2251360676250000),
    ([0, 0, 1, 1, 0, 1, 1, 1], -375226779375000),
    ([0, 0, 1, 1, 1, 0, 0, 1], -375226779375000),
    ([0, 0, 1, 1, 1, 0, 1, 1], -375226779375000),
    ([0, 0, 1, 1, 1, 1, 0, 1], 938066948437500),
    ([0, 0, 1, 1, 1, 1, 1, 1], 62537796562500),
    ([0, 1, 0, 0, 0, 0, 0, 1], -375226779375000),
    ([0, 1, 0, 0, 0, 0, 1, 1], 938066948437500),
    ([0, 1, 0, 0, 0, 1, 0, 1], -3001814235000000),
    ([0, 1, 0, 0, 0, 1, 1, 1], -1250755931250000),
    ([0, 1, 0, 0, 1, 0, 0, 1], 2251360676250000),
    ([0, 1, 0, 0, 1, 0, 1, 1], 2251360676250000),
    ([0, 1, 0, 0, 1, 1, 0, 1], 2251360676250000),
    ([0, 1, 0, 0, 1, 1, 1, 1], 938066948437500),
    ([0, 1, 0, 1, 0, 0, 0, 1], -3001814235000000),
    ([0, 1, 0, 1, 0, 0, 1, 1], 2251360676250000),
    ([0, 1, 0, 1, 0, 1, 0, 1], -13508164057500000),
    ([0, 1, 0, 1, 0, 1, 1, 1], -3001814235000000),
    ([0, 1, 0, 1, 1, 0, 0, 1], 2251360676250000),
    ([0, 1, 0, 1, 1, 0, 1, 1], 2251360676250000),
    ([0, 1, 0, 1, 1, 1, 0, 1], -3001814235000000),
    ([0, 1, 0, 1, 1, 1, 1, 1], -375226779375000),
    ([0, 1, 1, 0, 0, 0, 0, 1], 938066948437500),
    ([0, 1, 1, 0, 0, 0, 1, 1], -375226779375000),
    ([0, 1, 1, 0, 0, 1, 0, 1], 2251360676250000),
    ([0, 1, 1, 0, 0, 1, 1, 1], -375226779375000),
    ([0, 1, 1, 0, 1, 0, 0, 1], 2251360676250000),
    ([0, 1, 1, 0, 1, 0, 1, 1], 2251360676250000),
    ([0, 1, 1, 0, 1, 1, 0, 1], 2251360676250000),
    ([0, 1, 1, 0, 1, 1, 1, 1], 938066948437500),
    ([0, 1, 1, 1, 0, 0, 0, 1], -1250755931250000),
    ([0, 1, 1, 1, 0, 0, 1, 1], -375226779375000),
    ([0, 1, 1, 1, 0, 1, 0, 1], -3001814235000000),
    ([0, 1, 1, 1, 0, 1, 1, 1], -1250755931250000),
    ([0, 1, 1, 1, 1, 0, 0, 1], 938066948437500),
    ([0, 1, 1, 1, 1, 0, 1, 1], 938066948437500),
    ([0, 1, 1, 1, 1, 1, 0, 1], -375226779375000),
    ([1, 0, 0, 0, 0, 0, 1, 0], 375226779375000),
    ([1, 0, 0, 0, 0, 1, 0, 0], -938066948437500),
    ([1, 0, 0, 0, 0, 1, 1, 0], -938066948437500),
    ([1, 0, 0, 0, 1, 0, 0, 0], 1250755931250000),
    ([1, 0, 0, 0, 1, 0, 1, 0], 3001814235000000),
    ([1, 0, 0, 0, 1, 1, 0, 0], 375226779375000),
    ([1, 0, 0, 0, 1, 1, 1, 0], 1250755931250000),
    ([1, 0, 0, 1, 0, 0, 0, 0], -938066948437500),
    ([1, 0, 0, 1, 0, 0, 1, 0], -2251360676250000),
    ([1, 0, 0, 1, 0, 1, 0, 0], -2251360676250000),
    ([1, 0, 0, 1, 0, 1, 1, 0], -2251360676250000),
    ([1, 0, 0, 1, 1, 0, 0, 0], 375226779375000),
    ([1, 0, 0, 1, 1, 0, 1, 0], -2251360676250000),
    ([1, 0, 0, 1, 1, 1, 0, 0], 375226779375000),
    ([1, 0, 0, 1, 1, 1, 1, 0], -938066948437500),
    ([1, 0, 1, 0, 0, 0, 0, 0], 375226779375000),
    ([1, 0, 1, 0, 0, 0, 1, 0], 3001814235000000),
    ([1, 0, 1, 0, 0, 1, 0, 0], -2251360676250000),
    ([1, 0, 1, 0, 0, 1, 1, 0], -2251360676250000),
    ([1, 0, 1, 0, 1, 0, 0, 0], 3001814235000000),
    ([1, 0, 1, 0, 1, 0, 1, 0], 13508164057500000),
    ([1, 0, 1, 0, 1, 1, 0, 0], -2251360676250000),
    ([1, 0, 1, 0, 1, 1, 1, 0], 3001814235000000),
    ([1, 0, 1, 1, 0, 0, 0, 0], -938066948437500),
    ([1, 0, 1, 1, 0, 0, 1, 0], -2251360676250000),
    ([1, 0, 1, 1, 0, 1, 0, 0], -2251360676250000),
    ([1, 0, 1, 1, 0, 1, 1, 0], -2251360676250000),
    ([1, 0, 1, 1, 1, 0, 0, 0], 1250755931250000),
    ([1, 0, 1, 1, 1, 0, 1, 0], 3001814235000000),
    ([1, 0, 1, 1, 1, 1, 0, 0], -938066948437500),
    ([1, 0, 1, 1, 1, 1, 1, 0], 375226779375000),
    ([1, 1, 0, 0, 0, 0, 0, 0], -62537796562500),
    ([1, 1, 0, 0, 0, 0, 1, 0], -938066948437500),
    ([1, 1, 0, 0, 0, 1, 0, 0], 375226779375000),
    ([1, 1, 0, 0, 0, 1, 1, 0], 375226779375000),
    ([1, 1, 0, 0, 1, 0, 0, 0], 375226779375000),
    ([1, 1, 0, 0, 1, 0, 1, 0], -2251360676250000),
    ([1, 1, 0, 0, 1, 1, 0, 0], 1688520507187500),
    ([1, 1, 0, 0, 1, 1, 1, 0], 375226779375000),
    ([1, 1, 0, 1, 0, 0, 0, 0], -938066948437500),
    ([1, 1, 0, 1, 0, 0, 1, 0], -2251360676250000),
    ([1, 1, 0, 1, 0, 1, 0, 0], -2251360676250000),
    ([1, 1, 0, 1, 0, 1, 1, 0], -2251360676250000),
    ([1, 1, 0, 1, 1, 0, 0, 0], 375226779375000),
    ([1, 1, 0, 1, 1, 0, 1, 0], -2251360676250000),
    ([1, 1, 0, 1, 1, 1, 0, 0], 375226779375000),
    ([1, 1, 0, 1, 1, 1, 1, 0], -938066948437500),
    ([1, 1, 1, 0, 0, 0, 0, 0], 375226779375000),
    ([1, 1, 1, 0, 0, 0, 1, 0], 1250755931250000),
    ([1, 1, 1, 0, 0, 1, 0, 0], 375226779375000),
    ([1, 1, 1, 0, 0, 1, 1, 0], 375226779375000),
    ([1, 1, 1, 0, 1, 0, 0, 0], 1250755931250000),
    ([1, 1, 1, 0, 1, 0, 1, 0], 3001814235000000),
    ([1, 1, 1, 0, 1, 1, 0, 0], 375226779375000),
    ([1, 1, 1, 0, 1, 1, 1, 0], 1250755931250000),
    ([1, 1, 1, 1, 0, 0, 0, 0], -719184660468750),
    ([1, 1, 1, 1, 0, 0, 1, 0], -938066948437500),
    ([1, 1, 1, 1, 0, 1, 0, 0], -938066948437500),
    ([1, 1, 1, 1, 0, 1, 1, 0], -938066948437500),
    ([1, 1, 1, 1, 1, 0, 0, 0], 375226779375000),
    ([1, 1, 1, 1, 1, 0, 1, 0], 375226779375000),
    ([1, 1, 1, 1, 1, 1, 0, 0], -62537796562500)]

/-- **Degree-8 term** `C₈(a,b)`: the degree-8 part of `bch a b`, evaluated from its table.

The table is the term: `eval coefficientScale ![a, b]` multiplies out each row's word and weights
it by the row's
coefficient over `coefficientScale ^ 8`, so the definition *is* the word data. -/
noncomputable def bchOcticTerm {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  eval coefficientScale ![a, b] bchOcticTermTable

end

/-! ### Exact low-degree residuals -/

/-- Exact cubic cancellation with arbitrary approximations to the two exponentials. -/
theorem bchCubicTerm_residual_eq {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (ea eb a b : 𝔸) :
    let D₁ := ea - 1 - a
    let D₂ := eb - 1 - b
    let P := ea * eb - 1 - (a + b)
    let E₁ := D₁ - (2 : ℚ)⁻¹ • a ^ 2
    let E₂ := D₂ - (2 : ℚ)⁻¹ • b ^ 2
    let Q := a * D₂ + D₁ * b + D₁ * D₂
    let F₁ := E₁ - (6 : ℚ)⁻¹ • a ^ 3
    let F₂ := E₂ - (6 : ℚ)⁻¹ • b ^ 3
    (2 : ℚ)⁻¹ • ((2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
          (a + b) * P - P * (a + b) - P ^ 2) +
        (3 : ℚ)⁻¹ • (a + b) ^ 3 - bchCubicTerm a b =
    F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
    (2 : ℚ)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)) -
    (2 : ℚ)⁻¹ • P ^ 2 := by
  dsimp only
  unfold bchCubicTerm
  simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, add_mul, mul_sub, sub_mul,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_add, smul_sub, smul_smul,
    ← mul_assoc]
  module

/-- Exact commutator extraction with arbitrary approximations to the exponentials. -/
theorem bchCommutator_residual_eq {A : Type*} [Ring A] [Algebra ℚ A]
    (ea eb a b : A) :
    let y := ea * eb - 1
    let D₁ := ea - 1 - a
    let D₂ := eb - 1 - b
    let E₁ := D₁ - (2 : ℚ)⁻¹ • a ^ 2
    let E₂ := D₂ - (2 : ℚ)⁻¹ • b ^ 2
    let P := y - (a + b)
    y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) - (2 : ℚ)⁻¹ • y ^ 2 =
      (2 : ℚ)⁻¹ • ((2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
        (a + b) * P - P * (a + b) - P ^ 2) := by
  dsimp only
  simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, add_mul, mul_sub, sub_mul,
    smul_add, smul_sub, smul_smul,
    ← mul_assoc]
  module

end FQFP.BCH
