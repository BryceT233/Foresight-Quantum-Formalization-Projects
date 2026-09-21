"""Diagnose a pure cancellation identity by expanding both sides over the free algebra on {a, b}.

Noncommutative polynomials are `{word: Fraction}` maps (a word is a tuple of `0` = `a` / `1` = `b`).
The `bch*Term` side is read from the target's `bchQuinticGroup*Words` tables in
`FQFP/BCH/BCHTerms.lean`; the Dynkin/Ree side is transcribed from the source statement.

Run from the repository root:

    python scripts/check_pure_identity.py --degree 5
"""

import argparse
import itertools
import re
import sys
from fractions import Fraction as F

A, B = (0,), (1,)
ONE = {(): F(1)}


def add(*ps):
    out = {}
    for p in ps:
        for w, c in p.items():
            out[w] = out.get(w, F(0)) + c
    return {w: c for w, c in out.items() if c}


def sub(p, q):
    return add(p, {w: -c for w, c in q.items()})


def mul(*ps):
    out = ONE
    for p in ps:
        new = {}
        for w1, c1 in out.items():
            for w2, c2 in p.items():
                w = w1 + w2
                new[w] = new.get(w, F(0)) + c1 * c2
        out = {w: c for w, c in new.items() if c}
    return out


def smul(c, p):
    return {w: c * v for w, v in p.items() if c * v}


def pow_(p, n):
    out = ONE
    for _ in range(n):
        out = mul(out, p)
    return out


def monomial(letters, coeff=F(1)):
    word = ()
    for l in letters:
        word += (l,)
    return {word: coeff}


def a(n=1):
    return {A * n: F(1)}


def b(n=1):
    return {B * n: F(1)}


def group_words(text, name):
    """`[(word, coefficient numerator)]` from a `bchQuinticGroup*Words` table."""
    body = re.search(r"^def %s\b.*?:=\s*$(.*?)(?=\n\n)" % re.escape(name), text, re.M | re.S)
    if body is None:
        raise SystemExit("could not find %s" % name)
    out = []
    for row in re.findall(r"!\[([^\]]*)\]", body.group(1)):
        letters = [0 if x == "true" else 1 for x in re.findall(r"true|false", row)]
        out.append(tuple(letters))
    return out


def bch_quintic_term(text):
    """`bchQuinticTerm = (1/720) • (-G1 + 4•G4 - 6•G6 + 24•G24)` over the target's tables."""
    tables = [("bchQuinticGroup1Words", F(-1)), ("bchQuinticGroup4Words", F(4)),
              ("bchQuinticGroup6Words", F(-6)), ("bchQuinticGroup24Words", F(24))]
    out = {}
    for name, coeff in tables:
        for w in group_words(text, name):
            out = add(out, smul(coeff / 720, {w: F(1)}))
    return out


def dynkin_side(degree):
    z = add(a(), b())
    if degree == 4:
        raise SystemExit("degree 4 is stated differently; only 5..8 are handled here")
    T = [None, None]
    # T_k = degree-k part of exp(a)exp(b) - 1 = sum_{i+j=k} a^i/i! * b^j/j!
    import math
    for k in range(2, degree + 1):
        acc = {}
        for i in range(k + 1):
            j = k - i
            acc = add(acc, smul(F(1, math.factorial(i) * math.factorial(j)),
                                mul(a(i) if i else ONE, b(j) if j else ONE)))
        T.append(acc)
    # y_j = T_j for j >= 2, y_1 = z
    y = [None, z] + T[2:]
    # leading term: sum_{k>=1} (-1)^(k+1)/k * (y^k)_d(degree)
    total = {}
    for k in range(1, degree + 1):
        yk = ONE
        for _ in range(k):
            yk = mul(yk, z if k == 1 else y[k] if k < len(y) else ONE)
        total = add(total, smul(F((-1) ** (k + 1), k), yk))
    return total


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--degree", type=int, required=True)
    ap.add_argument("--bchterms", default="FQFP/BCH/BCHTerms.lean")
    args = ap.parse_args()
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    text = open(args.bchterms, encoding="utf-8").read().replace("\r\n", "\n")

    if args.degree == 5:
        z = add(a(), b())
        T2 = add(monomial([0, 1]), smul(F(1, 2), pow_(a(), 2)), smul(F(1, 2), pow_(b(), 2)))
        T3 = add(smul(F(1, 6), pow_(a(), 3)), smul(F(1, 2), mul(a(), b(), b())),
                 smul(F(1, 2), mul(a(2), b())), smul(F(1, 6), pow_(b(), 3)))
        T4 = add(smul(F(1, 24), pow_(a(), 4)), smul(F(1, 6), mul(a(3), b())),
                 smul(F(1, 4), mul(a(2), b(2))), smul(F(1, 6), mul(a(), b(3))),
                 smul(F(1, 24), pow_(b(), 4)))
        W5 = sub(add(smul(F(1, 60), pow_(a(), 5)), smul(F(1, 60), pow_(b(), 5)),
                     smul(F(1, 12), mul(a(), b(4))), smul(F(1, 12), mul(a(4), b())),
                     smul(F(1, 6), mul(a(2), b(3))), smul(F(1, 6), mul(a(3), b(2)))),
                 add(mul(z, T4), mul(T4, z), mul(T2, T3), mul(T3, T2)))
        y3 = add(mul(pow_(z, 2), T3), mul(z, T3, z), mul(T3, pow_(z, 2)),
                 mul(z, pow_(T2, 2)), mul(T2, z, T2), mul(pow_(T2, 2), z))
        y4 = add(mul(pow_(z, 3), T2), mul(pow_(z, 2), T2, z), mul(z, T2, pow_(z, 2)),
                 mul(T2, pow_(z, 3)))
        lhs = add(smul(F(1, 2), W5), smul(F(1, 3), y3), smul(-F(1, 4), y4),
                  smul(F(1, 5), pow_(z, 5)))
    else:
        lhs = dynkin_side(args.degree)

    rhs = bch_quintic_term(text) if args.degree == 5 else None
    if rhs is None:
        raise SystemExit("only degree 5 wired up so far")
    diff = sub(lhs, rhs)
    print("degree %d: LHS has %d words, RHS has %d, difference has %d"
          % (args.degree, len(lhs), len(rhs), len(diff)))
    if not diff:
        print("RESULT: identical")
        return 0
    print("RESULT: %d differing words (first 12 below)" % len(diff))
    for w in sorted(diff, key=lambda x: (len(x), x))[:12]:
        print("   %s : %s" % ("".join("ab"[x] for x in w), diff[w]))
    return 1


if __name__ == "__main__":
    sys.exit(main())
