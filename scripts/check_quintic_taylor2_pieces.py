"""Independent cross-check of the degree-5 Taylor pieces.

This script does NOT read the Lean definitions of the pieces. It rebuilds them from scratch out
of data parsed from two Lean source files:

* the four `bchQuinticGroup{1,4,6,24}Words` tables of `FQFP/BCH/BCHTerms.lean`
  (the group structure of `bchQuinticTerm`, itself ported from `Lean-BCH/BCH/Basic.lean`), and
* the *old* flat tables `bchQuinticTermLinDiff{,Words}` and
  `bchQuinticTermTaylor2Remainder{2V,3V,4V}{,Words}`, which were verified word-by-word and
  coefficient-by-coefficient against the source before this rewrite (see
  `artifacts/quintic-taylor2-route.md`).

From the four groups it enumerates, for every word and every nonempty subset of size `k` of its
`a`-positions, the word obtained by substituting `V` there, and collects `(word, coefficient)`
pairs. It then asserts that for `k = 1, 2, 3, 4` the resulting multiset is exactly the old table's.

Run from the repository root:

    git show ab05359:FQFP/BCH/QuinticTaylor2.lean > old_qt2.lean
    python scripts/check_quintic_taylor2_pieces.py old_qt2.lean

`ab05359` is the last commit before the rewrite — the flat `Fin 75/70/30/5` tables were removed
*by* the rewrite, so they only exist in the history. Relocate with
`git log --oneline -- FQFP/BCH/QuinticTaylor2.lean`.

Exit status 0 means the new pieces agree with the verified old tables.
"""

import itertools
import re
import sys
from collections import Counter
from fractions import Fraction

GROUPS = [
    # `bchQuinticTerm = (1/720) • (-G1 + 4•G4 - 6•G6 + 24•G24)`, so the signed coefficients are
    # -1, 4, -6, 24.
    ("bchQuinticGroup1Words", -1),
    ("bchQuinticGroup4Words", 4),
    ("bchQuinticGroup6Words", -6),
    ("bchQuinticGroup24Words", 24),
]

OLD = {
    1: ("bchQuinticTermLinDiffWords", "bchQuinticTermLinDiffCoeffs"),
    2: ("bchQuinticTermTaylor2Remainder2VWords", "bchQuinticTermTaylor2Remainder2VCoeffs"),
    3: ("bchQuinticTermTaylor2Remainder3VWords", "bchQuinticTermTaylor2Remainder3VCoeffs"),
    4: ("bchQuinticTermTaylor2Remainder4VWords", "bchQuinticTermTaylor2Remainder4VCoeffs"),
}


def def_body(text, name):
    """The `:= ...` body of `def <name>`, up to the next blank line."""
    m = re.search(r"^def %s\b.*?:=\s*$(.*?)(?=\n\n)" % re.escape(name), text, re.M | re.S)
    if m is None:
        raise SystemExit("could not find the definition of %s" % name)
    return m.group(1)


def bool_words(text, name):
    """Parse `Fin n -> Fin 5 -> Bool` as a list of tuples of bools."""
    body = def_body(text, name)
    return [tuple(w == "true" for w in re.findall(r"true|false", inner))
            for inner in re.findall(r"!\[([^\]]*)\]", body)]


def int_words(text, name):
    """Parse `Fin n -> List (Fin 3)` as a list of tuples of ints."""
    body = def_body(text, name)
    return [tuple(int(x) for x in re.findall(r"\d+", inner))
            for inner in re.findall(r"\[([^\]]*)\]", body)]


def coeffs(text, name):
    """Parse `Fin n -> Q` written as `c / 720` chains."""
    body = def_body(text, name)
    found = re.findall(r"(-?\d+)\s*/\s*(\d+)", body)
    if not found:
        raise SystemExit("could not parse the coefficients of %s" % name)
    return [Fraction(int(n), int(d)) for n, d in found]


def new_pieces(bchterms):
    """`{k: Counter[(word, coefficient)]}` rebuilt from the four groups."""
    pieces = {k: Counter() for k in range(1, 6)}
    for name, coeff in GROUPS:
        for w in bool_words(bchterms, name):
            apos = [i for i, is_a in enumerate(w) if is_a]
            for k in range(1, len(apos) + 1):
                for s in itertools.combinations(apos, k):
                    s = set(s)
                    word = tuple(1 if i in s else (0 if w[i] else 2) for i in range(5))
                    pieces[k][(word, Fraction(coeff, 720))] += 1
    return pieces


def read_text(path):
    """Read a text file, tolerating the UTF-8 / UTF-16 BOMs a shell redirect may add."""
    with open(path, "rb") as fh:
        raw = fh.read()
    for enc in ("utf-8-sig", "utf-16", "utf-8"):
        try:
            return raw.decode(enc).replace("\r\n", "\n")
        except UnicodeDecodeError:
            continue
    raise SystemExit("could not decode %s" % path)


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    bchterms = read_text("FQFP/BCH/BCHTerms.lean")
    old_text = read_text(sys.argv[1])

    pieces = new_pieces(bchterms)
    ok = True

    print("rebuilt piece sizes (number of (word, coefficient) terms):")
    for k in sorted(OLD):
        print("  k = %d : %d" % (k, sum(pieces[k].values())))

    for k, (wname, cname) in sorted(OLD.items()):
        words = int_words(old_text, wname)
        cs = coeffs(old_text, cname)
        if len(words) != len(cs):
            print("!! k = %d : old table has %d words but %d coefficients"
                  % (k, len(words), len(cs)))
            ok = False
            continue
        old = Counter(zip(words, cs))
        if old == pieces[k]:
            print("k = %d : OK (%d terms, %d distinct words)"
                  % (k, sum(old.values()), len(old)))
        else:
            ok = False
            print("k = %d : MISMATCH" % k)
            for key in sorted(set(old) | set(pieces[k]), key=str):
                if old[key] != pieces[k][key]:
                    print("   %s : old %d, new %d" % (key, old[key], pieces[k][key]))

    total = sum(sum(pieces[k].values()) for k in (1, 2, 3, 4))
    print("total terms k = 1..4 : %d" % total)
    print("RESULT:", "OK" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
