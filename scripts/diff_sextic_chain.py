"""Compare a generated monomial chain against the word/coefficient table it came from.

Usage: python scripts/diff_sextic_chain.py <STEM> <chain-file>

Parses `def <STEM>Coeffs` / `def <STEM>Words` out of `FQFP/BCH/BCHTerms.lean` and the
`(c : ℚ) • (m)` chain emitted by `scripts/gen_bch_higher_terms.py --expand`, then reports
the word/coefficient difference under both letter conventions (forward and reversed).
"""

import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TERMS = ROOT / "FQFP" / "BCH" / "BCHTerms.lean"


def table(text: str, name: str) -> list[str]:
    m = re.search(rf"def {name}\b.*?:=[ \t]*\n(?P<body>.*?)\n\n", text, re.S)
    if m is None:
        raise SystemExit(f"table {name} not found")
    return re.findall(r"!?\[([^\[\]]*)\]", m.group("body"))


def words(stem: str) -> list[tuple[bool, ...]]:
    out = []
    for entry in table(TERMS.read_text(encoding="utf-8"), f"{stem}Words"):
        out.append(tuple(part.strip() == "true" for part in entry.split(",")))
    return out


def coeffs(stem: str) -> list[Fraction]:
    text = TERMS.read_text(encoding="utf-8")
    m = re.search(rf"def {stem}Coeffs\b.*?:=[ \t]*\n(?P<body>.*?)\n\n", text, re.S)
    if m is None:
        raise SystemExit(f"table {stem}Coeffs not found")
    return [Fraction(int(n), int(d)) for n, d in re.findall(r"(-?\d+)\s*/\s*(\d+)", m.group("body"))]


def read_text(path: str) -> str:
    """PowerShell redirection writes UTF-16, so accept a BOM here."""
    raw = Path(path).read_bytes()
    for enc in ("utf-8-sig", "utf-16", "utf-8"):
        try:
            return raw.decode(enc).replace("\r\n", "\n")
        except UnicodeDecodeError:
            continue
    raise SystemExit(f"could not decode {path}")


def chain(path: str) -> list[tuple[Fraction, tuple[bool, ...]]]:
    text = read_text(path)
    text = text[: text.index(":= by")]
    out = []
    for c, mono in re.findall(r"\(([^()]*: ℚ)\) • \(([^()]*)\)", text):
        letters = [part.strip() for part in mono.split("*")]
        out.append((Fraction(c.split(":")[0].replace(" ", "")), tuple(x == "a" for x in letters)))
    return out


def main() -> None:
    stem, path = sys.argv[1], sys.argv[2]
    ws, cs = words(stem), coeffs(stem)
    print(f"{stem}: table has {len(ws)} words / {len(cs)} coeffs")
    ch = chain(path)
    print(f"chain has {len(ch)} terms")
    for label, key in (("forward", lambda w: w), ("reversed", lambda w: tuple(reversed(w)))):
        want = {key(w): c for w, c in zip(ws, cs)}
        got: dict[tuple[bool, ...], Fraction] = {}
        for c, w in ch:
            got[w] = got.get(w, Fraction(0)) + c
        keys = set(want) | set(got)
        diff = {k: (want.get(k, Fraction(0)), got.get(k, Fraction(0))) for k in keys}
        bad = {k: v for k, v in diff.items() if v[0] != v[1]}
        print(f"{label}: {len(bad)} differing words")
        for k, (a, b) in sorted(bad.items(), key=lambda kv: (kv[1][0] - kv[1][1])):
            print(f"    {'a' if k[0] else 'b'}... table={a} chain={b}")


if __name__ == "__main__":
    main()
