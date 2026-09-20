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
    """A `Fin m → List (Fin 3)` word vector or a `Fin m → ℤ` coefficient vector."""
    if kind == "words":
        entries = ["[" + ", ".join(str(a) for a in w) + "]" for w, _ in items]
        ty = "List (Fin 3)"
    else:
        entries = [str(int(c * DENOM)) for _, c in items]
        ty = "ℤ"
    return f"/-- {doc} -/\ndef {name} : Fin {len(items)} → {ty} :=\n  {wrap(entries, 4)}\n\n"


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

Patterns are `List (Fin 3)`: `0` is `x`, `1` is `V`, `2` is `y`. Coefficients are numerators over
`720`, matching `BCHTerms.norm_sevenTwenty_rat` (`‖(720 : ℚ)‖ = 720`). -/

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

    R.append("""/-! ### The definitions -/

/-- The weighted sum of the words named by `words` with the numerators `coeffs`, over `720`. -/
noncomputable def bchWordSum {𝔸 : Type*} [Ring 𝔸] [SMul ℚ 𝔸] {m : ℕ}
    (coeffs : Fin m → ℤ) (words : Fin m → List (Fin 3)) (x V y : 𝔸) : 𝔸 :=
  (720 : ℚ)⁻¹ • ∑ i, (coeffs i : ℚ) • wordProdList ![x, V, y] (words i)

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

end

end FQFP.BCH
""")

    TARGET.write_text("".join(L) + "".join(R), encoding="utf-8", newline="\n")
    print(f"# wrote {TARGET}", flush=True)


if __name__ == "__main__":
    main()
