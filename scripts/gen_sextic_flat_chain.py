"""Compute the degree-6 taylor pieces as flat monomial chains, as an independent check.

The identity behind `septic_pure_identity` is checked here in the free `ℚ`-algebra on two generators
`a`, `b`: every piece is a `dict[monomial, Fraction]`, the two sides are compared, and a Lean probe
is emitted so that the cost of `noncomm_ring` on a *flat* degree-6 identity can be measured. Flat
means no products are left, so `noncomm_ring` only has to collect like monomials.

Usage: python scripts/gen_sextic_flat_chain.py [--emit FILE]
"""

import argparse
import re
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TERMS = ROOT / "FQFP" / "BCH" / "BCHTerms.lean"

Poly = dict


def mul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for u, cu in p.items():
        for v, cv in q.items():
            w = u + v
            out[w] = out.get(w, F(0)) + cu * cv
    return {k: v for k, v in out.items() if v}


def add(*ps: Poly) -> Poly:
    out: Poly = {}
    for p in ps:
        for u, cu in p.items():
            out[u] = out.get(u, F(0)) + cu
    return {k: v for k, v in out.items() if v}


def smul(c: F, p: Poly) -> Poly:
    return {u: c * cu for u, cu in p.items() if c * cu}


def neg(p: Poly) -> Poly:
    return smul(F(-1), p)


def pw(p: Poly, n: int) -> Poly:
    out: Poly = {(): F(1)}
    for _ in range(n):
        out = mul(out, p)
    return out


def mono(*letters: str) -> Poly:
    return {tuple(letters): F(1)}


A, B = mono("a"), mono("b")
Z = add(A, B)
T2 = add(mul(A, B), smul(F(1, 2), pw(A, 2)), smul(F(1, 2), pw(B, 2)))
T3 = add(smul(F(1, 6), pw(A, 3)), smul(F(1, 2), mul(pw(A, 2), B)),
         smul(F(1, 2), mul(A, pw(B, 2))), smul(F(1, 6), pw(B, 3)))
T4 = add(smul(F(1, 24), pw(A, 4)), smul(F(1, 6), mul(pw(A, 3), B)),
         smul(F(1, 4), mul(pw(A, 2), pw(B, 2))), smul(F(1, 6), mul(A, pw(B, 3))),
         smul(F(1, 24), pw(B, 4)))
T5 = add(smul(F(1, 120), pw(A, 5)), smul(F(1, 24), mul(pw(A, 4), B)),
         smul(F(1, 12), mul(pw(A, 3), pw(B, 2))), smul(F(1, 12), mul(pw(A, 2), pw(B, 3))),
         smul(F(1, 24), mul(A, pw(B, 4))), smul(F(1, 120), pw(B, 5)))

W6 = add(
    smul(F(1, 360), pw(A, 6)), smul(F(1, 60), mul(pw(A, 5), B)),
    smul(F(1, 24), mul(pw(A, 4), pw(B, 2))), smul(F(1, 18), mul(pw(A, 3), pw(B, 3))),
    smul(F(1, 24), mul(pw(A, 2), pw(B, 4))), smul(F(1, 60), mul(A, pw(B, 5))),
    smul(F(1, 360), pw(B, 6)),
    neg(add(mul(Z, T5), mul(T2, T4), mul(T3, T3), mul(T4, T2), mul(T5, Z))))

Y3 = add(mul(pw(Z, 2), T4), mul(mul(Z, T4), Z), mul(T4, pw(Z, 2)),
         mul(mul(Z, T2), T3), mul(mul(Z, T3), T2), mul(mul(T2, Z), T3),
         mul(mul(T2, T3), Z), mul(mul(T3, Z), T2), mul(mul(T3, T2), Z), pw(T2, 3))
Y4 = add(mul(pw(Z, 3), T3), mul(mul(pw(Z, 2), T3), Z), mul(mul(Z, T3), pw(Z, 2)),
         mul(T3, pw(Z, 3)), mul(pw(Z, 2), pw(T2, 2)), mul(mul(mul(Z, T2), Z), T2),
         mul(mul(Z, pw(T2, 2)), Z), mul(mul(T2, pw(Z, 2)), T2),
         mul(mul(mul(T2, Z), T2), Z), mul(pw(T2, 2), pw(Z, 2)))
Y5 = add(mul(pw(Z, 4), T2), mul(mul(pw(Z, 3), T2), Z), mul(mul(pw(Z, 2), T2), pw(Z, 2)),
         mul(mul(Z, T2), pw(Z, 3)), mul(T2, pw(Z, 4)))

TAYLOR = add(smul(F(1, 2), W6), smul(F(1, 3), Y3), neg(smul(F(1, 4), Y4)),
             smul(F(1, 5), Y5), neg(smul(F(1, 6), pw(Z, 6))))


def sextic() -> Poly:
    """`bchSexticTerm` read off the target's own word/coefficient tables."""
    text = TERMS.read_text(encoding="utf-8")

    def rows(name: str) -> str:
        m = re.search(rf"def {name}\b.*?:=[ \t]*\n(?P<b>.*?)\n\n", text, re.S)
        if m is None:
            raise SystemExit(f"table {name} not found")
        return m.group("b")

    words = [tuple(w == "true" for w in re.findall(r"true|false", row))
             for row in re.findall(r"!\[([^\]]*)\]", rows("bchSexticTermWords"))]
    coeffs = [F(int(n), int(d)) for n, d in re.findall(r"(-?\d+)\s*/\s*(\d+)",
                                                       rows("bchSexticTermCoeffs"))]
    if len(words) != len(coeffs):
        raise SystemExit("word/coefficient length mismatch")
    return add(*[smul(c, {tuple("a" if x else "b" for x in w): F(1)})
                 for w, c in zip(words, coeffs)])


def render(p: Poly) -> str:
    """The chain as a Lean sum, wrapped at term boundaries to stay under 100 columns."""
    items = ["(%s : ℚ) • (%s)" % (
        c if c.denominator == 1 else "%d / %d" % (c.numerator, c.denominator),
        " * ".join(w)) for w, c in sorted(p.items(), key=lambda kv: (len(kv[0]), kv[0]))]
    lines, cur = [], "      "
    for it in items:
        piece = ("" if cur.strip() == "" else " + ") + it
        if len(cur) + len(piece) + 2 > 98:
            lines.append(cur + " +")
            cur = "      " + it
        else:
            cur += piece
    lines.append(cur)
    return "\n".join(lines)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit", metavar="FILE", help="write the Lean probe here")
    args = ap.parse_args()

    S = sextic()
    print("sextic terms:      %d" % len(S))
    for name, p in (("W6", W6), ("Y3", Y3), ("Y4", Y4), ("Y5", Y5), ("Z^6", pw(Z, 6))):
        print("%-18s %d terms, degree %d" % (name, len(p), max(map(len, p))))
    print("taylor terms:      %d" % len(TAYLOR))
    print("taylor - sextic:   %d terms" % len(add(TAYLOR, neg(S))))
    print("RESULT: %s" % ("identical" if not add(TAYLOR, neg(S)) else "DIFFERENT"))

    if not args.emit:
        return
    parts = [render(smul(F(1, 2), W6)), render(smul(F(1, 3), Y3)), render(smul(F(1, 4), Y4)),
             render(smul(F(1, 5), Y5)), render(smul(F(1, 6), pw(Z, 6)))]
    probe = "\n".join([
        "/- Flat degree-6 probe: how expensive is `noncomm_ring` when nothing is left to expand? -/",
        "import FQFP.BCH.BCHTerms",
        "",
        "namespace FQFP.BCH",
        "",
        "variable {𝔸 : Type*}",
        "",
        "set_option trace.profiler true in",
        "set_option trace.profiler.useHeartbeats true in",
        "set_option trace.profiler.threshold 2000 in",
        "private theorem probe_collected [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :",
        "      " + render(TAYLOR) + " =",
        "      " + render(S) + " := by",
        "  noncomm_ring",
        "",
        "set_option trace.profiler true in",
        "set_option trace.profiler.useHeartbeats true in",
        "set_option trace.profiler.threshold 2000 in",
        "private theorem probe_uncollected [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :",
        "      (" + parts[0] + ") +\n      (" + parts[1] + ") -\n      (" + parts[2] + ") +\n      (" +
        parts[3] + ") -\n      (" + parts[4] + ") -\n      (" + render(S) + ") = 0 := by",
        "  noncomm_ring",
        "",
        "end FQFP.BCH",
        ""])
    Path(args.emit).write_text(probe, encoding="utf-8")
    print("wrote %s (%d lines)" % (args.emit, probe.count("\n")))


if __name__ == "__main__":
    main()
