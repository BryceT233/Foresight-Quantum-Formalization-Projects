#!/usr/bin/env python3
"""Generate the arity-free Lean rendering of the quintic Taylor machinery.

Ported from `Lean-BCH/scripts/gen_bch_quintic_term_taylor2.py`. That script emits the two
definitions as explicit `+`-chains of 75 and 105 monomials in `{x, V, y}`, which then forces the
downstream bound to be proved monomial by monomial (about 1200 lines in `Basic.lean`, plus 2V/3V/4V
scaffolding).

Here the same words are emitted as *data* — the pattern as a `List (Fin 3)` and the coefficient as a
numerator over `720` — and each definition is the corresponding `∑` of `wordProdList` terms. That is
the shape the arity-free norm API consumes: `WordExpansion.norm_sum_smul_wordProdList_le` bounds a
whole group in one application.

The remainder is split by the number of `V` letters (2, 3, 4) *in the definition*, so that the split
identity is `rfl` and each piece has a uniform letter profile — which is what pins the bound constant
to the source's `(1680 + 720 + 30)/720 = 2430/720`.

Usage:  python scripts/gen_bch_quintic_taylor2.py
Writes: FQFP/BCH/QuinticTaylor2.lean
"""

import math
import pathlib
from collections import defaultdict
from itertools import combinations

from fractions import Fraction

TARGET = pathlib.Path(__file__).resolve().parent.parent / "FQFP" / "BCH" / "QuinticTaylor2.lean"

DENOM = 720
X, V, Y = 0, 1, 2  # 0 = x, 1 = V, 2 = y
BINDERS = "{𝔸 : Type*} [Ring 𝔸] [SMul ℚ 𝔸]"


# ---- noncommutative polynomials in {a, b} ----

def ncpoly_zero():
    return defaultdict(lambda: Fraction(0))


def ncpoly_from_scalar(c):
    r = ncpoly_zero()
    c = Fraction(c)
    if c != 0:
        r[()] = c
    return r


def ncpoly_atom(i):
    r = ncpoly_zero()
    r[(i,)] = Fraction(1)
    return r


def ncpoly_add(p, q):
    r = ncpoly_zero()
    for w, c in p.items():
        r[w] += c
    for w, c in q.items():
        r[w] += c
    return defaultdict(lambda: Fraction(0), {w: c for w, c in r.items() if c != 0})


def ncpoly_scale(p, c):
    c = Fraction(c)
    if c == 0:
        return ncpoly_zero()
    return defaultdict(lambda: Fraction(0), {w: c * v for w, v in p.items()})


def ncpoly_mul(p, q):
    r = ncpoly_zero()
    for wp, cp in p.items():
        for wq, cq in q.items():
            r[wp + wq] += cp * cq
    return defaultdict(lambda: Fraction(0), {w: c for w, c in r.items() if c != 0})


def ncpoly_truncate(p, mx):
    return defaultdict(lambda: Fraction(0), {w: c for w, c in p.items() if len(w) <= mx})


def ncpoly_exp(x, mx):
    r = ncpoly_from_scalar(1)
    xp = ncpoly_from_scalar(1)
    for k in range(1, mx + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), mx)
        r = ncpoly_add(r, ncpoly_scale(xp, Fraction(1, math.factorial(k))))
    return r


def ncpoly_log_one_plus(x, mx):
    r = ncpoly_zero()
    xp = ncpoly_from_scalar(1)
    for k in range(1, mx + 1):
        xp = ncpoly_truncate(ncpoly_mul(xp, x), mx)
        sign = Fraction(1) if k % 2 == 1 else Fraction(-1)
        r = ncpoly_add(r, ncpoly_scale(xp, sign / k))
    return r


def bch_degree_five():
    """The degree-5 part of `log (exp a * exp b)`, atoms 0 = a, 1 = b."""
    pd = ncpoly_truncate(ncpoly_mul(ncpoly_exp(ncpoly_atom(0), 5), ncpoly_exp(ncpoly_atom(1), 5)), 5)
    m1 = defaultdict(lambda: Fraction(0), {w: c for w, c in pd.items() if w != ()})
    full = ncpoly_log_one_plus(m1, 5)
    return {w: c for w, c in full.items() if len(w) == 5}


def substitute(w, positions, replacement):
    out = list(w)
    for i in positions:
        out[i] = replacement
    return tuple(out)


def taylor_pieces():
    """`lin_diff` (one `V`), and the remainder split by the number of `V` letters."""
    lin = ncpoly_zero()
    by_vcount = {2: ncpoly_zero(), 3: ncpoly_zero(), 4: ncpoly_zero()}
    for w, c in bch_degree_five().items():
        if c == 0:
            continue
        base = tuple(X if atom == 0 else Y for atom in w)  # a -> x, b -> y
        x_positions = [i for i, atom in enumerate(base) if atom == X]
        for i in x_positions:
            lin[substitute(base, [i], V)] += c
        for k in range(2, len(x_positions) + 1):
            for subset in combinations(x_positions, k):
                by_vcount[k][substitute(base, subset, V)] += c
    clean = lambda p: sorted(((w, c) for w, c in p.items() if c != 0), key=lambda kv: kv[0])
    return clean(lin), {k: clean(p) for k, p in by_vcount.items()}


# ---- Lean emission ----

def wrap(entries, indent, width=94):
    """Format `entries` as a `![...]` vector, wrapped by character budget so lines stay short."""
    lines, cur = [], None
    for entry in entries:
        if cur is None:
            cur = entry
        elif indent + len(cur) + 2 + len(entry) <= width:
            cur += ", " + entry
        else:
            lines.append(cur)
            cur = entry
    if cur is not None:
        lines.append(cur)
    return "![" + (",\n" + " " * indent).join(lines) + "]"


def emit_data(kind, name, items, doc):
    """A `Fin m → List (Fin 3)` word vector or a `Fin m → ℚ` coefficient vector."""
    if kind == "words":
        entries = ["[" + ", ".join(str(a) for a in w) + "]" for w, _ in items]
        ty = "List (Fin 3)"
    else:
        entries = []
        for _, c in items:
            num = int(c * DENOM)
            entries.append(f"{num} / {DENOM}" if abs(num) != 1 else
                           ("1 / " + str(DENOM) if num == 1 else "-1 / " + str(DENOM)))
        ty = "ℚ"
    return f"/-- {doc} -/\ndef {name} : Fin {len(items)} → {ty} :=\n  {wrap(entries, 4)}\n\n"

HELPERS = """section Budget

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- **Coefficient budget**: the total of the absolute values of a coefficient vector is at most its
length times its largest absolute value. This is what turns a generated piece's bound constant into
`(number of words) * (largest coefficient)`, without expanding the sum term by term. -/
lemma sum_abs_le_card_mul_sup' {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → ℚ) :
    (∑ i, |(c i : ℝ)|)
      ≤ (Fintype.card ι : ℝ) * (Finset.univ.sup' Finset.univ_nonempty fun i => |(c i : ℝ)|) := by
  calc (∑ i, |(c i : ℝ)|)
      ≤ ∑ _i : ι, (Finset.univ.sup' Finset.univ_nonempty fun i => |(c i : ℝ)|) :=
        Finset.sum_le_sum fun i _ =>
          Finset.le_sup' (fun i => |(c i : ℝ)|) (Finset.mem_univ i)
    _ = (Fintype.card ι : ℝ) * (Finset.univ.sup' Finset.univ_nonempty fun i => |(c i : ℝ)|) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Exponent arithmetic: `M ^ (5 - (j + 2)) * Vn ^ (j + 2) = M ^ (3 - j) * Vn ^ j * Vn ^ 2`. -/
private lemma pow_sub_profile (M Vn : ℝ) (j : ℕ) :
    M ^ (5 - (j + 2)) * Vn ^ (j + 2) = M ^ (3 - j) * Vn ^ j * Vn ^ 2 := by
  have hM : 5 - (j + 2) = 3 - j := by omega
  rw [hM, pow_add]
  ring

/-- **Letter-profile relaxation**: a word with `k ≥ 2` letters `V` and `5 - k` letters from `{x, y}`
has profile `M ^ (5 - k) * Vn ^ k`, which is at most `M ^ 3 * Vn ^ 2` because `Vn ≤ M`. This is what
lets each piece of the remainder be bounded at the source's constant, which uses `M³‖V‖²`. -/
lemma profile_le (M Vn : ℝ) (hM0 : 0 ≤ M) (hVn0 : 0 ≤ Vn) (hVnM : Vn ≤ M) {k : ℕ}
    (hk : 2 ≤ k) (hk5 : k ≤ 5) : M ^ (5 - k) * Vn ^ k ≤ M ^ 3 * Vn ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [pow_sub_profile]
  calc M ^ (3 - j) * Vn ^ j * Vn ^ 2
      = M ^ (3 - j) * (Vn ^ j * Vn ^ 2) := by ring
    _ ≤ M ^ (3 - j) * (M ^ j * Vn ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hVn0 hVnM j) (pow_nonneg hVn0 2))
          (pow_nonneg hM0 (3 - j))
    _ = M ^ 3 * Vn ^ 2 := by
        have hj3 : j ≤ 3 := by omega
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj3]

end Budget"""


def emit_bounds(pieces):
    """The norm bounds for the three pieces.

    The constants are the source's: the number of words of the piece times its largest absolute
    coefficient, over `720` (`Basic.lean:4254/4664/4774`, and `4797` for the assembled bound). One
    `Finset.sum` triangle inequality bounds the whole piece at once, because every word of a piece
    has the same letter profile `M ^ (5 - k) * Vn ^ k`; that profile then relaxes to `M ^ 3 * Vn ^ 2`
    by cancelling `Vn ^ 2` and using `Vn ≤ M` on the remaining `k - 2` powers. The coefficient budget
    `hA` is `sum_abs_le_card_mul_sup'` plus a `fin_cases` check of the piece's largest coefficient, so
    it does not expand the piece term by term."""
    out = []
    for k in (2, 3, 4):
        tag = f"{k}V"
        profile = f"M ^ {5 - k} * Vn ^ {k}"
        coeffs = f"bchQuinticTermTaylor2Remainder{tag}Coeffs"
        words = f"bchQuinticTermTaylor2Remainder{tag}Words"
        items = pieces[k]
        count = len(items)
        maxabs = max(abs(int(c * DENOM)) for _, c in items)
        const = count * maxabs
        # The letter-profile step evaluates the concrete word by `fin_cases`. For the `4V` piece the
        # last word leaves `simp` with a disjunction (`mul_eq_mul_left_iff` cancels the common `M ^ 1`),
        # which the trailing `try simp` discharges. The `;` (not `<;>`) is what `lint-style` wants.
        profile_script = f"fin_cases i <;> simp [{words}] <;> ring_nf ;try simp"
        out.append(f"""/-- Norm bound for the `{tag}` piece: `≤ ({const}/720) M³‖V‖²` with `M = ‖x‖ + ‖V‖ + ‖y‖`.

The constant is the source's: the `{count}` words of the piece times its largest absolute coefficient
`{maxabs}/720`. Every word of the piece has the same letter profile — `{5 - k}` letters from `{{x, y}}`
and `{k}` letters `V` — so each of the `{count}` terms is bounded by `({maxabs}/720) * ({profile})`,
which relaxes to `({maxabs}/720) * (M³‖V‖²)` because `‖V‖ ≤ M`. -/
theorem norm_bchQuinticTermTaylor2Remainder{tag}_le {{𝔸 : Type*}}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder{tag} x V y‖
      ≤ ({const} / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) := by
  set M := ‖x‖ + ‖V‖ + ‖y‖ with hM
  set Vn := ‖V‖ with hVn
  -- Local names for the piece's data and its summand, so the bound proof stays inside 100 columns.
  set c : Fin {count} → ℚ := {coeffs} with hc
  set w : Fin {count} → List (Fin 3) := {words} with hwdef
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hVn0 : 0 ≤ Vn := norm_nonneg _
  have hx : ‖x‖ ≤ M := by rw [hM]; linarith [norm_nonneg V, norm_nonneg y]
  have hV : ‖V‖ ≤ Vn := le_refl _
  have hy : ‖y‖ ≤ M := by rw [hM]; linarith [norm_nonneg x, norm_nonneg V]
  have hVnM : Vn ≤ M := by rw [hM]; linarith [norm_nonneg x, norm_nonneg y]
  have hw : ∀ i, ‖wordProdList ![x, V, y] (w i)‖ ≤ {profile} := by
    intro i
    calc ‖wordProdList ![x, V, y] (w i)‖
        ≤ ((w i).map ![M, Vn, M]).prod :=
          norm_wordProdList_le (letters := ![x, V, y]) (b := ![M, Vn, M])
            (fun j => by fin_cases j <;> simp [hx, hV, hy]) (w i)
      _ = {profile} := by
          rw [hwdef]
          {profile_script}
  have hsup : (Finset.univ.sup' Finset.univ_nonempty fun i : Fin {count} =>
      |(c i : ℝ)|) ≤ ({maxabs} / 720 : ℝ) := by
    refine Finset.sup'_le _ _ fun i _ => ?_
    rw [hc]
    fin_cases i <;> norm_num [{coeffs}]
  have hA : (∑ i : Fin {count}, |(c i : ℝ)|) ≤ ({const} / 720 : ℝ) := by
    have hcard : (Fintype.card (Fin {count}) : ℝ) = ({count} : ℝ) := by norm_num
    calc (∑ i : Fin {count}, |(c i : ℝ)|)
        ≤ (Fintype.card (Fin {count}) : ℝ) *
            (Finset.univ.sup' Finset.univ_nonempty fun i : Fin {count} => |(c i : ℝ)|) :=
          sum_abs_le_card_mul_sup' c
      _ ≤ ({count} : ℝ) * ({maxabs} / 720 : ℝ) := by
          rw [hcard]
          exact mul_le_mul_of_nonneg_left hsup (by norm_num)
      _ = ({const} / 720 : ℝ) := by norm_num
  unfold bchQuinticTermTaylor2Remainder{tag} bchWordSum
  -- One triangle inequality bounds the whole piece; the profile relaxation below is the only
  -- place where `Vn ≤ M` enters.
  calc ‖∑ i, c i • wordProdList ![x, V, y] (w i)‖
      ≤ ∑ i : Fin {count}, |(c i : ℝ)| * ({profile}) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
        calc ‖c i • wordProdList ![x, V, y] (w i)‖
            ≤ ‖c i‖ * ‖wordProdList ![x, V, y] (w i)‖ := norm_smul_le _ _
          _ = |(c i : ℝ)| * ‖wordProdList ![x, V, y] (w i)‖ := by
              rw [← Rat.norm_cast_real, Real.norm_eq_abs]
          _ ≤ |(c i : ℝ)| * ({profile}) :=
              mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
    _ = (∑ i : Fin {count}, |(c i : ℝ)|) * ({profile}) := by rw [Finset.sum_mul]
    _ ≤ ({const} / 720 : ℝ) * ({profile}) :=
        mul_le_mul_of_nonneg_right hA
          (mul_nonneg (pow_nonneg hM0 {5 - k}) (pow_nonneg hVn0 {k}))
    _ ≤ ({const} / 720 : ℝ) * (M ^ 3 * Vn ^ 2) :=
        mul_le_mul_of_nonneg_left
          (profile_le M Vn hM0 hVn0 hVnM (k := {k}) (by norm_num) (by norm_num))
          (by norm_num)
""")
    return out


def main():
    lin, pieces = taylor_pieces()
    for label, items in [("lin_diff", lin)] + [(f"{k}V", pieces[k]) for k in (2, 3, 4)]:
        total = sum(abs(int(c * DENOM)) for _, c in items)
        print(f"# {label}: {len(items)} words, sum|c| over {DENOM} = {total}", flush=True)

    L, R = [], []
    L.append("""/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHTerms

/-!
# The Taylor expansion of the degree-5 term

`bchQuinticTerm (x + V) y - bchQuinticTerm x y` splits into its directional derivative
(`bchQuinticTerm_lin_diff`, linear in `V`) and a second-order remainder, and the remainder splits
further by the number of `V` letters (`bchQuinticTerm_taylor2_remainder_{2V,3V,4V}`).

The remainder is *defined* as the sum of those three pieces, so the split identity is `rfl`, and
each piece has a uniform letter profile: every word of the `kV` piece has exactly `k` letters `V`
and `5 - k` letters from `{x, y}`. That uniformity is what lets the bound constant come out as the
source's `(1680 + 720 + 30)/720 = 2430/720`.

## Provenance

Generated by `scripts/gen_bch_quintic_taylor2.py`, which ports the word lists of
`Lean-BCH/scripts/gen_bch_quintic_term_taylor2.py`. That script emits the same words as explicit
`+`-chains and then proves the norm bound one monomial at a time (`Basic.lean:3461-4830`, about
1200 lines, including 2V/3V/4V bound lemmas that nothing outside `Basic.lean` uses). Here the words
are data and each definition is a `∑` over `wordProdList`, which the arity-free norm API bounds in
a single application.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace FQFP.BCH

noncomputable section

/-! ### Word data

Patterns are `List (Fin 3)`: `0` is `x`, `1` is `V`, `2` is `y`. Coefficients are `ℚ`-valued, with
numerator over the common denominator `720`, matching the source's `(-1/720) • (…)` chains. -/

""")
    L.append(emit_data("words", "bchQuinticTermLinDiffWords", lin,
                       f"The {len(lin)} word patterns of `bchQuinticTerm_lin_diff`: one `V` at \
each `x`-position."))
    L.append(emit_data("coeffs", "bchQuinticTermLinDiffCoeffs", lin,
                       "The coefficients of `bchQuinticTerm_lin_diff`, over `720`."))
    data = {}
    for k in (2, 3, 4):
        items = pieces[k]
        data[k] = (f"bchQuinticTermTaylor2Remainder{k}VCoeffs",
                   f"bchQuinticTermTaylor2Remainder{k}VWords")
        L.append(emit_data("words", data[k][1], items,
                           f"The {len(items)} word patterns of the `{k}V` piece, exactly `{k}` \
letters `V`."))
        L.append(emit_data("coeffs", data[k][0], items,
                           f"The coefficients of the `{k}V` piece, over `720`."))
    L.append("\n")

    R.append("""/-! ### The definitions -/

/-- The weighted sum of the words named by `words` with the coefficients `coeffs`. -/
noncomputable def bchWordSum {𝔸 : Type*} [Ring 𝔸] [SMul ℚ 𝔸] {m : ℕ}
    (coeffs : Fin m → ℚ) (words : Fin m → List (Fin 3)) (x V y : 𝔸) : 𝔸 :=
  ∑ i, coeffs i • wordProdList ![x, V, y] (words i)

/-- **First-order directional difference** of `bchQuinticTerm` in its first argument: one `V` at
each `x`-position of each degree-5 word. -/
noncomputable def bchQuinticTermLinDiff {𝔸 : Type*} [Ring 𝔸] [SMul ℚ 𝔸] (x V y : 𝔸) : 𝔸 :=
  bchWordSum bchQuinticTermLinDiffCoeffs bchQuinticTermLinDiffWords x V y

""")
    for k, blurb in ((2, "exactly two letters `V`"),
                     (3, "exactly three letters `V`"),
                     (4, "exactly four letters `V`")):
        R.append(f"""/-- The `{k}V` piece of the second-order Taylor remainder: {blurb}. -/
noncomputable def bchQuinticTermTaylor2Remainder{k}V {{𝔸 : Type*}} [Ring 𝔸] [SMul ℚ 𝔸]
    (x V y : 𝔸) : 𝔸 :=
  bchWordSum {data[k][0]} {data[k][1]} x V y

""")
    R.append("""/-- **Second-order Taylor remainder** of `bchQuinticTerm` in its first argument, split by the
number of `V` letters. The split is part of the definition, so the split identity is `rfl`. -/
noncomputable def bchQuinticTermTaylor2Remainder {𝔸 : Type*} [Ring 𝔸] [SMul ℚ 𝔸]
    (x V y : 𝔸) : 𝔸 :=
  bchQuinticTermTaylor2Remainder2V x V y + bchQuinticTermTaylor2Remainder3V x V y +
    bchQuinticTermTaylor2Remainder4V x V y

/-! ### The norm bounds

Each piece of the remainder has a uniform letter profile, so one `fin_cases` script per piece
evaluates every word of the piece at once, and the piece's coefficient budget is one
`sum_abs_le_card_mul_sup'` plus a `fin_cases` check of its largest coefficient. The constants are
the source's `Basic.lean:4254/4664/4774/4797`. -/

""")
    R.append(HELPERS + "\n\n")
    R.extend(emit_bounds(pieces))
    R.append("""/-- **Norm bound for the second-order Taylor remainder**:
`‖C₅(x+V,y) - C₅(x,y) - linDiff‖ ≤ (2430/720) M³‖V‖²` with `M = ‖x‖ + ‖V‖ + ‖y‖`.

`(1680 + 720 + 30)/720 = 2430/720` is the sum of the three pieces' constants. -/
theorem norm_bchQuinticTermTaylor2Remainder_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormOneClass 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder x V y‖ ≤
      (2430 / 720 : ℝ) * (‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2 := by
  have h2 := norm_bchQuinticTermTaylor2Remainder2V_le x V y
  have h3 := norm_bchQuinticTermTaylor2Remainder3V_le x V y
  have h4 := norm_bchQuinticTermTaylor2Remainder4V_le x V y
  have s1 := norm_add_le (bchQuinticTermTaylor2Remainder2V x V y +
    bchQuinticTermTaylor2Remainder3V x V y) (bchQuinticTermTaylor2Remainder4V x V y)
  have s2 := norm_add_le (bchQuinticTermTaylor2Remainder2V x V y)
    (bchQuinticTermTaylor2Remainder3V x V y)
  have hsum : (2430 / 720 : ℝ) = 1680 / 720 + 720 / 720 + 30 / 720 := by norm_num
  unfold bchQuinticTermTaylor2Remainder
  rw [hsum]
  linarith only [s1, s2, h2, h3, h4]

end

end FQFP.BCH
""")

    TARGET.write_text("".join(L) + "".join(R), encoding="utf-8", newline="\n")
    print(f"# wrote {TARGET}", flush=True)


if __name__ == "__main__":
    main()
