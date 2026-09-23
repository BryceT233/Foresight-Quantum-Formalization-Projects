#!/usr/bin/env python3
"""Verify that the degree-6 Dynkin/Ree cancellation identity holds as a *table* identity.

The pure identity of `SmallSDischarge.lean` is

    ½·W6 + ⅓·y3₆ - ¼·y4₆ + ⅕·y5₆ - ⅙·z⁶ - bchSexticTerm = 0

with `z = a + b`, `T_k` the degree-`k` part of `y = exp a * exp b - 1`, `W6 = 2·y_d6 - (y²)_d6`,
and `yᵐ_dk` the degree-`k` part of `yᵐ`.

A table is a list of `(word, coefficient)` pairs, where a word is a list of letters (`0` = `a`,
`1` = `b`). Tables multiply by cartesian product: concatenate the words, multiply the coefficients.
`T_k` is the table of `a^n b^(k-n) / (n! (k-n)!)` over `n = 0..k`.

`SmallSDischarge.lean` stores the coefficients as **integers**, cleared by `K ^ 6` with
`K = 210` (`WordAlgebra.lean`); the tables read out of it are therefore integer-valued, and the
Dynkin/Ree scalars `1/2 … 1/6` appear there already cleared by `60`.

The check runs twice, from two independent models:

* **compositions** — the mathematics: the degree-6 part of `y^p` is the sum over the positive
  compositions of 6 into `p` parts of the product of the corresponding `T_i`, and the rational form
  of `bchSexticTerm` is recovered from the Lean table by dividing out `K ^ 6`.
* **pieces** — the code: the six degree-6 piece tables `w6Tab`, `y36Tab`, `y46Tab`, `y56Tab`,
  `z6Tab` are read out of `SmallSDischarge.lean` and evaluated with the same
  `mulKTab`/`powKTab`/`smulKTab` algebra that Lean uses.  A change to the Lean expressions is
  therefore picked up automatically.

It also prints the 64 coefficients that `SmallSDischarge.lean` asserts to vanish, in the word order of
the `2 ^ 6` six-letter words.

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
SMALL_S_DISCHARGE = ROOT / "FQFP" / "BCH" / "SmallSDischarge.lean"

Tab = list[tuple[tuple[int, ...], Fraction]]
Map = dict[tuple[int, ...], Fraction]

DEG = 6
K = 210
WORDS: list[tuple[int, ...]] = list(product((0, 1), repeat=DEG))


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


def degrees(tab: Tab, k: int) -> Map:
    return {u: c for u, c in collapse(tab).items() if len(u) == k}


# ── Model 1 (mathematics): compositions ─────────────────────────────────────────────────────────


def T(k: int) -> Tab:
    return [(w(n, k - n), Fraction(1, factorial(n) * factorial(k - n))) for n in range(k + 1)]


Z = T(1)  # = a + b


def y_power(p: int) -> Map:
    """The degree-`DEG` part of `y^p`, by positive compositions."""
    out: Tab = []
    for c in comps(DEG, p):
        out += product_of([T(i) for i in c])
    return degrees(out, DEG)


Y2, Y3, Y4, Y5 = (y_power(p) for p in (2, 3, 4, 5))
Z6 = collapse(product_of([Z] * DEG))

# sanity: the degree-6 part of `y` itself must be the degree-6 part of `exp a * exp b - 1`
Y1 = degrees(add(*[T(i) for i in range(1, DEG + 1)]), DEG)
assert Y1[w(6, 0)] == Fraction(1, 720), Y1[w(6, 0)]
assert Y1[w(5, 1)] == Fraction(1, 120), Y1[w(5, 1)]

W6 = collapse(scale(2, Y1) + scale(-1, Y2))

LHS = collapse(add(scale(Fraction(1, 2), W6),
                   scale(Fraction(1, 3), Y3),
                   scale(Fraction(-1, 4), Y4),
                   scale(Fraction(1, 5), Y5),
                   scale(Fraction(-1, 6), Z6)))


# ── Model 2 (code): the piece tables read out of `SmallSDischarge.lean` ─────────────────────────────


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
    """The `def <name> ...` chunk, up to the next top-level declaration.

    The chunk is returned whole (signature included) rather than as the part after `:=`: a
    definition written with the equation compiler (`def T : (k : Nat) -> Tab` followed by
    `| 0 => ...` branches) has no `:=` at all, so splitting on `:=` would run past it into the next
    declaration."""
    m = re.search(rf"^def\s+{name}\b", text, re.MULTILINE)
    if not m:
        raise SystemExit(f"definition `{name}` not found")
    rest = text[m.start():]
    end = re.search(r"^(def|theorem|lemma|abbrev|instance)\s", rest[1:], re.MULTILINE)
    return rest[: end.start() + 1] if end else rest


def definition_rhs(text: str, name: str) -> str:
    """The part of `def <name> ...` after its `:=`."""
    chunk = definition_body(text, name)
    m = re.search(r":=\s*", chunk)
    if not m:
        raise SystemExit(f"definition `{name}` has no `:=`")
    return chunk[m.end():]


def parse_bch_table() -> Map:
    """`bchSexticTermTable : KTab` as a coefficient map, cleared by `K ^ 6`."""
    text = strip_comments(BCH_TERMS.read_text(encoding="utf-8"))
    body = definition_rhs(text, "bchSexticTermTable")
    rows = parse_rows(body)
    if len(rows) != 28:
        raise SystemExit(f"bchSexticTermTable: expected 28 rows, parsed {len(rows)}")
    return collapse(rows)


def uncleared(tab: Map) -> Map:
    """The rational table a `K ^ 6`-cleared table denotes."""
    return {u: c / K ** DEG for u, c in tab.items()}


def parse_rows(chunk: str) -> Tab:
    """Every `([a, b, ..], coeff)` row of a table chunk."""
    rows: Tab = []
    for u, c in re.findall(r"\(\[([0-9,\s]*)\],\s*\(?([^)]+?)\)?\s*\)", chunk):
        word = tuple(int(x) for x in u.split(",") if x.strip())
        rows.append((word, parse_rat(c)))
    return rows


def parse_rat(text: str) -> Fraction:
    text = text.strip().strip("()").strip()
    m = re.fullmatch(r"(-?\d+)\s*/\s*(\d+)", text)
    return Fraction(int(m.group(1)), int(m.group(2))) if m else Fraction(int(text))


def parse_t_tables() -> dict[int, Tab]:
    """The literal branches of the degree-`k` table `T`."""
    text = strip_comments(SMALL_S_DISCHARGE.read_text(encoding="utf-8"))
    body = definition_body(text, "bchTTable")
    branches = list(re.finditer(r"\n\s*\|\s*(\d+)\s*=>", body))
    out: dict[int, Tab] = {}
    for i, b in enumerate(branches):
        end = branches[i + 1].start() if i + 1 < len(branches) else len(body)
        out[int(b.group(1))] = parse_rows(body[b.end():end])
    for k in range(1, DEG + 1):
        if len(out[k]) != k + 1:
            raise SystemExit(f"T {k}: expected {k + 1} rows, parsed {len(out[k])}")
    return out


def piece_tables() -> dict[str, Map]:
    """Evaluate the six degree-6 piece definitions with the `WordAlgebra` table algebra.

    The bodies are read out of `SmallSDischarge.lean` and parsed, not rewritten: Lean and Python agree
    on the syntax of this fragment (`f a b` application, `++`/`+`, `*`, parentheses) except for
    precedence — Lean's application binds tighter than Python's `-` — so a small recursive-descent
    parser is used instead of `eval`."""
    text = strip_comments(SMALL_S_DISCHARGE.read_text(encoding="utf-8"))
    t = parse_t_tables()
    env = {
        "bchTTable": t,
        "mulTab": mul,
        "powTab": lambda s, n: product_of([s] * n),
        "smulTab": scale,
        "mulKTab": mul,
        "powKTab": lambda s, n: product_of([s] * n),
        "smulKTab": scale,
    }
    out: dict[str, Map] = {}
    for name in ("w6Tab", "y36Tab", "y46Tab", "y56Tab", "z6Tab"):
        out[name] = collapse(eval_table_expr(t, env, definition_rhs(text, name)))
    return out


def eval_table_expr(t: dict[int, Tab], env: dict[str, object], body: str) -> Tab:
    """Evaluate a table expression written in the Lean syntax of `WordAlgebra`."""
    tokens = tokenize(body)
    value, pos = parse_sum(t, env, tokens, 0)
    if pos != len(tokens):
        raise SystemExit(f"trailing tokens in table expression: {tokens[pos:]}")
    return value


def tokenize(body: str) -> list[str]:
    """Split a table expression into `++`, name, number, rational literal and table literal tokens."""
    tokens: list[str] = []
    i = 0
    patterns = (
        ("op", re.compile(r"\+\+")),
        ("rat", re.compile(r"\(\s*(-?\d+)\s*:\s*ℚ\s*\)\s*(⁻¹)?")),
        ("num", re.compile(r"-?\d+")),
        ("name", re.compile(r"[A-Za-z_][A-Za-z0-9_]*")),
        ("lpar", re.compile(r"\(")),
        ("rpar", re.compile(r"\)")),
    )
    while i < len(body):
        if body[i].isspace():
            i += 1
            continue
        if body[i] == "[":
            end = find_matching(body, i, "[", "]")
            tokens.append(body[i:end + 1])
            i = end + 1
            continue
        for kind, pat in patterns:
            m = pat.match(body, i)
            if m:
                tokens.append(m.group(0))
                i = m.end()
                break
        else:
            raise SystemExit(f"cannot tokenize {body[i:i + 20]!r}")
    return tokens


def find_matching(text: str, start: int, open_ch: str, close_ch: str) -> int:
    depth = 0
    for i in range(start, len(text)):
        if text[i] == open_ch:
            depth += 1
        elif text[i] == close_ch:
            depth -= 1
            if depth == 0:
                return i
    raise SystemExit(f"unbalanced {open_ch}{close_ch} in {text[start:start + 40]!r}")


def parse_sum(t: dict[int, Tab], env: dict[str, object], tokens: list[str], pos: int):
    """`s ++ t ++ ...` — left-associated table concatenation."""
    value, pos = parse_app(t, env, tokens, pos)
    while pos < len(tokens) and tokens[pos] == "++":
        rhs, pos = parse_app(t, env, tokens, pos + 1)
        value = value + rhs
    return value, pos


def parse_app(t: dict[int, Tab], env: dict[str, object], tokens: list[str], pos: int):
    """`f a b ...` — left-associated application of a function to its arguments."""
    head, pos = parse_atom(t, env, tokens, pos)
    args: list[object] = []
    while pos < len(tokens) and tokens[pos] not in ("++", ")"):
        arg, pos = parse_atom(t, env, tokens, pos)
        args.append(arg)
    if isinstance(head, str):
        if head not in env:
            raise SystemExit(f"unknown table name `{head}`")
        head = env[head]
    return head(*args) if args else head, pos


def parse_atom(t: dict[int, Tab], env: dict[str, object], tokens: list[str], pos: int):
    if pos >= len(tokens):
        raise SystemExit("unexpected end of table expression")
    tok = tokens[pos]
    if tok == "(":
        value, pos = parse_sum(t, env, tokens, pos + 1)
        if pos >= len(tokens) or tokens[pos] != ")":
            raise SystemExit("missing `)` in table expression")
        return value, pos + 1
    if tok.startswith("["):
        rows = parse_rows(tok)
        if not rows:
            raise SystemExit(f"empty table literal {tok[:40]!r}")
        return rows, pos + 1
    m = re.fullmatch(r"\(\s*(-?\d+)\s*:\s*ℚ\s*\)\s*(⁻¹)?", tok)
    if m:
        c = Fraction(int(m.group(1)))
        return (1 / c if m.group(2) else c), pos + 1
    if re.fullmatch(r"-?\d+", tok):
        return int(tok), pos + 1
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", tok):
        if tok == "bchTTable":
            nxt = tokens[pos + 1] if pos + 1 < len(tokens) else ""
            if re.fullmatch(r"\d+", nxt):
                return t[int(nxt)], pos + 2
            return lambda k: t[k], pos + 1
        return tok, pos + 1
    raise SystemExit(f"unexpected token {tok!r}")


def main() -> int:
    rhs = parse_bch_table()
    rhs_rat = uncleared(rhs)
    pieces = piece_tables()

    # The scalars are the Dynkin/Ree ones cleared by `lcm(1, …, 6) = 60`, exactly as `dynkin6Tab`
    # writes them: 60/2, 60/3, -60/4, 60/5, -60/6, -60.
    dynkin = collapse(add(scale(Fraction(30), pieces["w6Tab"]),
                          scale(Fraction(20), pieces["y36Tab"]),
                          scale(Fraction(-15), pieces["y46Tab"]),
                          scale(Fraction(12), pieces["y56Tab"]),
                          scale(Fraction(-10), pieces["z6Tab"]),
                          scale(Fraction(-60), rhs)))

    problems: list[str] = []

    print(f"# piece rows: " + " ".join(f"{k}={len(v)}" for k, v in pieces.items()),
          file=sys.stderr)
    print(f"# Dynkin side has {len(LHS)} words, bchSexticTerm has {len(rhs_rat)}", file=sys.stderr)
    keys = sorted(set(LHS) | set(rhs_rat))
    bad = [(u, LHS.get(u, Fraction(0)), rhs_rat.get(u, Fraction(0))) for u in keys
           if LHS.get(u, Fraction(0)) != rhs_rat.get(u, Fraction(0))]
    if bad:
        problems.append(f"compositions vs bchSexticTerm: {len(bad)} mismatched words")
        for u, x, y in bad[:20]:
            print(f"  {u}: dynkin {x} vs bch {y}", file=sys.stderr)
    else:
        print(f"# compositions agree with bchSexticTerm on all {len(keys)} words",
              file=sys.stderr)

    nonzero = {u: c for u, c in dynkin.items() if c != 0}
    if nonzero:
        problems.append(f"pieces model: {len(nonzero)} words survive, expected 0")
        for u, c in sorted(nonzero.items())[:20]:
            print(f"  pieces model: {u} -> {c}", file=sys.stderr)
    else:
        print("# pieces model: all 64 six-letter words cancel", file=sys.stderr)

    print("# the 64 coefficients of dynkin6Tab, over the six-letter words:", file=sys.stderr)
    for i, u in enumerate(WORDS):
        print(f"#   {i:2d} [{'|'.join(str(x) for x in u)}] -> "
              f"{dynkin.get(u, Fraction(0))}", file=sys.stderr)

    if problems:
        for p in problems:
            print(f"# FAIL: {p}", file=sys.stderr)
        return 1
    print("# OK", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
