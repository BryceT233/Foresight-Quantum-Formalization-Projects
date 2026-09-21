"""Extract the degree-6/7/8 BCH terms from `Lean-BCH/BCH/Basic.lean` as word data.

The source writes `bch_sextic_term` / `bch_septic_term` / `bch_octic_term` as explicit
`+`-chains of monomials (28, 126 and 124 terms). The target represents a degree-`k` term as a
`Fin m → Fin k → Bool` word table plus a `Fin m → ℚ` coefficient table over the source's common
denominator, so that `WordExpansion.norm_sum_wordEval_le` bounds it in one application.

This script is the *generator*; `--check` re-parses the source and compares against a target file
so that the two stay in step. Run from the repository root:

    python scripts/gen_bch_higher_terms.py
    python scripts/gen_bch_higher_terms.py --check FQFP/BCH/BCHTerms.lean

`--check` is the independent half: it reads the target's `![true, false, ...]` word rows and
`![-1 / 1440, ...]` coefficient rows and asserts they are exactly the source's monomial chain, in
the source's order and over the source's denominator.
"""

import argparse
import re
import sys
from fractions import Fraction
from math import lcm

TERMS = [
    # (target stem, source definition name, degree)
    ("bchSexticTerm", "bch_sextic_term", 6),
    ("bchSepticTerm", "bch_septic_term", 7),
    ("bchOcticTerm", "bch_octic_term", 8),
]


def def_body(text, name):
    m = re.search(r"^noncomputable def %s\b.*?:=\s*$(.*?)(?=\n\n)" % re.escape(name),
                  text, re.M | re.S)
    if m is None:
        raise SystemExit("could not find the definition of %s" % name)
    return m.group(1)


def parse_source(text, name, degree):
    """[(word, (numerator, denominator))] with `word` a tuple of `bool` (`True` is `a`)."""
    terms = []
    for line in def_body(text, name).splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.match(r"^[+-]?\s*\((-?\d+)\s*/\s*(\d+)\s*:\s*[^)]*\)\s*•\s*\((.*)\)\s*$", line)
        if m is None:
            raise SystemExit("unparsed line of %s: %r" % (name, line))
        num, den, prod = int(m.group(1)), int(m.group(2)), m.group(3)
        letters = re.findall(r"[ab]", prod)
        if len(letters) != degree or re.sub(r"[ab*\s]", "", prod):
            raise SystemExit("bad product in %s: %r" % (name, prod))
        terms.append((tuple(c == "a" for c in letters), (num, den)))
    return terms


def read_text(path):
    with open(path, "rb") as fh:
        raw = fh.read()
    for enc in ("utf-8-sig", "utf-16", "utf-8"):
        try:
            return raw.decode(enc).replace("\r\n", "\n")
        except UnicodeDecodeError:
            continue
    raise SystemExit("could not decode %s" % path)


def parse_target(text, stem):
    """The target's word and coefficient rows, in the order they are written."""
    words = re.search(r"^def %sWords\b.*?:=\s*$(.*?)(?=\n\n)" % stem, text, re.M | re.S)
    coeffs = re.search(r"^def %sCoeffs\b.*?:=\s*$(.*?)(?=\n\n)" % stem, text, re.M | re.S)
    if words is None or coeffs is None:
        raise SystemExit("could not find %sWords / %sCoeffs" % (stem, stem))
    table = [tuple(w == "true" for w in re.findall(r"true|false", row))
             for row in re.findall(r"!\[([^\]]*)\]", words.group(1))]
    nums = [(int(n), int(d)) for n, d in re.findall(r"(-?\d+)\s*/\s*(\d+)", coeffs.group(1))]
    if len(table) != len(nums):
        raise SystemExit("%s: %d word rows but %d coefficients" % (stem, len(table), len(nums)))
    return list(zip(table, nums))


def emit_table(def_line, items, width=96):
    """`def ... := ![item, item, ...]`, wrapped at item boundaries to stay under 100 columns."""
    out = [def_line]
    cur = "  ![" + items[0]
    for it in items[1:]:
        piece = ", " + it
        if len(cur) + len(piece) + 1 > width:
            out.append(cur + ",")
            cur = "    " + it
        else:
            cur += piece
    out.append(cur + "]")
    return out


def render(terms, stem, degree, common):
    rows = ["![" + ", ".join("true" if c else "false" for c in word) + "]" for word, _ in terms]
    coeffs = ["%d / %d" % (n * (common // d), common) for _, (n, d) in terms]
    out = ["/-- The word patterns of `%s`: the %d %d-letter monomials of the source's" % (
               stem, len(terms), degree),
           "`bch_%s_term`, in the source's order (`true` is the letter `a`). -/" % stem[3:-4].lower()]
    out += emit_table("def %sWords : Fin %d → Fin %d → Bool :=" % (stem, len(terms), degree), rows)
    out += ["",
            "/-- The coefficients of `%s`, in the source's order, over the common" % stem,
            "denominator %d. -/" % common]
    out += emit_table("def %sCoeffs : Fin %d → ℚ :=" % (stem, len(terms)), coeffs)
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", default="D:/project/Lean-BCH/BCH/Basic.lean")
    ap.add_argument("--check", metavar="TARGET")
    ap.add_argument("--emit", action="store_true", help="print a summary and the target tables")
    ap.add_argument("--lean-only", action="store_true",
                    help="print only the target tables, for splicing into BCHTerms.lean")
    args = ap.parse_args()
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    source = read_text(args.source)
    parsed = {stem: parse_source(source, name, deg) for stem, name, deg in TERMS}
    commons = {stem: lcm(*[d for _, (_, d) in terms]) for stem, terms in parsed.items()}

    if args.lean_only:
        print("\n\n".join(render(parsed[stem], stem, deg, commons[stem])
                          for stem, _, deg in TERMS))
        return 0

    if args.check:
        target = read_text(args.check)
        ok = True
        for stem, name, deg in TERMS:
            want, common = parsed[stem], commons[stem]
            want = [(w, (n * (common // d), common)) for w, (n, d) in want]
            got = parse_target(target, stem)
            if want == got:
                print("%s: OK (%d terms, denominator %d)" % (stem, len(want), common))
            else:
                ok = False
                print("%s: MISMATCH" % stem)
                if len(want) != len(got):
                    print("   length: source %d, target %d" % (len(want), len(got)))
                for i, (a, b) in enumerate(zip(want, got)):
                    if a != b:
                        print("   row %d: source %s, target %s" % (i, a, b))
        print("RESULT:", "OK" if ok else "MISMATCH")
        return 0 if ok else 1

    for stem, name, deg in TERMS:
        terms, common = parsed[stem], commons[stem]
        print("=== %s (source `%s`, degree %d) ===" % (stem, name, deg))
        print("  terms             : %d" % len(terms))
        print("  common denominator: %d" % common)
        print("  distinct words    : %d" % len({w for w, _ in terms}))
        print("  signed sum        : %s (must be 0: the degree-%d part is a Lie element)"
              % (sum(Fraction(n, d) for _, (n, d) in terms), deg))
        print("  sum |coefficient| : %s" % sum(abs(Fraction(n, d)) for _, (n, d) in terms))
        print("  numerator values  : %s"
              % sorted({n * (common // d) for _, (n, d) in terms}))
        if args.emit:
            print()
            print(render(terms, stem, deg, common))
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
