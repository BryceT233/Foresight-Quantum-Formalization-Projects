#!/usr/bin/env python3
"""Verify that the degree-6 Dynkin/Ree cancellation identity holds as a *table* identity.

The pure identity of `SmallSDischarge.lean` is

    ½·W6 + ⅓·y3₆ - ¼·y4₆ + ⅕·y5₆ - ⅙·z⁶ - bchSexticTerm = 0

with `z = a + b`, `T_k` the degree-`k` part of `y = exp a * exp b - 1`, `W6 = 2·y_d6 - (y²)_d6`,
and `yᵐ_dk` the degree-`k` part of `yᵐ`.

A table is a list of `(word, coefficient)` pairs, where a word is a list of letters (`0` = `a`,
`1` = `b`). Tables multiply by cartesian product: concatenate the words, multiply the coefficients.
`T_k` is the table of `a^n b^(k-n) / (n! (k-n)!)` over `n = 0..k`.

The `k`-th power of `y` has degree-`k` part `Σ_{positive compositions (i₁,…,i_k) of k} T_{i₁} ⋯
T_{i_k}`; this script generates those compositions, computes both sides, and compares them
coefficient-wise. Agreement means the corresponding Lean statement is a pure data identity — no
`noncomm_ring` needed.

Usage:
    python scripts/check_sextic_free_identity.py
"""

from __future__ import annotations

import re
import sys
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BCH_TERMS = ROOT / "FQFP" / "BCH" / "BCHTerms.lean"

Tab = list[tuple[tuple[int, ...], Fraction]]
Map = dict[tuple[int, ...], Fraction]

DEG = 6


def w(a: int, b: int) -> tuple[int, ...]:
    """The word with `a` copies of `0` and `b` copies of `1`."""
    return (0,) * a + (1,) * b


def mul(s: Tab, t: Tab) -> Tab:
    return [(u + v, c * d) for u, c in s for v, d in t]


def add(*ts: Tab) -> Tab:
    return [row for t in ts for row in t]


def scale(c: Fraction, t) -> Tab:
    rows = list(t.items()) if isinstance(t, dict) else t
    return [(u, c * d) for u, d in rows]


def product_of(ts: list[Tab]) -> Tab:
    out: Tab = [((), Fraction(1))]
    for t in ts:
        out = mul(out, t)
    return out


def collapse(t: Tab) -> Map:
    out: dict[tuple[int, ...], Fraction] = defaultdict(Fraction)
    for u, c in t:
        out[u] += c
    return {u: c for u, c in out.items() if c != 0}


def comps(total: int, parts: int, prefix: tuple[int, ...] = ()) -> list[tuple[int, ...]]:
    """The positive compositions of `total` into `parts` parts."""
    if parts == 0:
        return [prefix] if total == 0 else []
    return [c for first in range(1, total - parts + 2)
            for c in comps(total - first, parts - 1, prefix + (first,))]


# ── T_k: the degree-k part of `y = exp a * exp b - 1` ────────────────────────────────────────────
def T(k: int) -> Tab:
    return [(w(n, k - n), Fraction(1, factorial(n) * factorial(k - n))) for n in range(k + 1)]


Z = T(1)  # = a + b


def y_power(p: int) -> Map:
    """The degree-`DEG` part of `y^p`."""
    out: Tab = []
    for c in comps(DEG, p):
        out += product_of([T(i) for i in c])
    return {u: v for u, v in collapse(out).items() if len(u) == DEG}


Y2, Y3, Y4, Y5 = (y_power(p) for p in (2, 3, 4, 5))
Z6 = collapse(product_of([Z] * DEG))

# sanity: the degree-6 part of `y` itself must be the degree-6 part of `exp a * exp b - 1`
Y1 = collapse(add(*[T(i) for i in range(1, DEG + 1)]))
Y1 = {u: v for u, v in Y1.items() if len(u) == DEG}
assert Y1[w(6, 0)] == Fraction(1, 720), Y1[w(6, 0)]
assert Y1[w(5, 1)] == Fraction(1, 120), Y1[w(5, 1)]

W6 = collapse(scale(2, Y1) + scale(-1, Y2))

LHS = collapse(add(scale(Fraction(1, 2), W6),
                   scale(Fraction(1, 3), Y3),
                   scale(Fraction(-1, 4), Y4),
                   scale(Fraction(1, 5), Y5),
                   scale(Fraction(-1, 6), Z6)))


def strip_comments(text: str) -> str:
    """Drop Lean block comments, keeping the line structure."""
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(text):
        if depth == 0 and text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def definition_body(text: str, name: str) -> str:
    """The right-hand side of `def <name> ... := <body>`, up to the next top-level `def`."""
    m = re.search(rf"^def\s+{name}\s[^\n]*:=\s*", text, re.MULTILINE)
    if not m:
        raise SystemExit(f"definition `{name}` not found")
    rest = text[m.end():]
    end = re.search(r"^def\s", rest, re.MULTILINE)
    return rest[: end.start()] if end else rest


def parse_bch_table() -> Map:
    """`bchSexticTermWords` / `bchSexticTermCoeffs` as a table."""
    text = strip_comments(BCH_TERMS.read_text(encoding="utf-8"))
    words = [tuple(int(x) for x in row.replace(" ", "").split(","))
             for row in re.findall(r"!\[([01](?:\s*,\s*[01])*)\]",
                                   definition_body(text, "bchSexticTermWords"))]
    coeffs = [Fraction(c.replace(" ", ""))
              for c in definition_body(text, "bchSexticTermCoeffs")
              .replace("![", "").replace("]", "").split(",") if c.strip()]
    if len(words) != len(coeffs):
        raise SystemExit(f"{len(words)} words vs {len(coeffs)} coefficients")
    return collapse(list(zip(words, coeffs)))


def emit(tab: Map, name: str) -> str:
    """Emit a Lean table definition, rows sorted by word."""
    lines = [f"def {name} : Tab :="]
    for k, (u, c) in enumerate(sorted(tab.items())):
        letters = ", ".join(str(x) for x in u)
        comma = "," if k + 1 < len(tab) else ""
        lines.append(f"  [([{letters}], {c.numerator} / {c.denominator})]{comma}")
    return "\n".join(lines)


def main() -> int:
    if "--emit" in sys.argv:
        print(emit(LHS, "bchSexticDynkinTable"))
        return 0

    rhs = parse_bch_table()
    print(f"# Dynkin side has {len(LHS)} words, bchSexticTerm has {len(rhs)}", file=sys.stderr)
    keys = sorted(set(LHS) | set(rhs))
    bad = [(u, LHS.get(u, Fraction(0)), rhs.get(u, Fraction(0))) for u in keys
           if LHS.get(u, Fraction(0)) != rhs.get(u, Fraction(0))]
    if bad:
        print(f"# MISMATCH on {len(bad)} of {len(keys)} words", file=sys.stderr)
        for u, x, y in bad[:20]:
            print(f"  {u}: dynkin {x} vs bch {y}", file=sys.stderr)
        return 1
    print(f"# tables agree on all {len(keys)} words", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
