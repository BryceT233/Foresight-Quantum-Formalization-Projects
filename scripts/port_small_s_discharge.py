"""Port the pure cancellation identities of `Lean-BCH/BCH/SmallSDischarge.lean` to the target style.

The source states each identity with `𝕂 : Type*` scalars (`[RCLike 𝕂]`) and proves it with one giant
`unfold … ; simp only […] ; match_scalars <;> ring`, under a `maxHeartbeats` bump. The target's
scalar interface is `ℚ` (see `artifacts/bch-port.md` §4.2), so the mechanical part of the port is:

* drop the `𝕂` parameter and `[RCLike 𝕂] [NormedAlgebra 𝕂 𝔸]`, keep `[NormedRing 𝔸]`;
* `(n : 𝕂)⁻¹` → `(n : ℚ)⁻¹`;
* `bch_quartic_term 𝕂` / `bch_quintic_term 𝕂` / `bch_sextic_term 𝕂` / `bch_septic_term 𝕂` /
  `bch_octic_term 𝕂` → `bchQuarticTerm` / `bchQuinticTerm` / `bchSexticTerm` / `bchSepticTerm` /
  `bchOcticTerm`;
* `bch_quintic_group_N` → `bchQuinticGroupN`;
* drop the `omit […] in` and `set_option maxHeartbeats … in` lines (the target bans `omit` and
  heartbeat bumps).

What is *not* mechanical is the proof: the target's `bch*Term` are `Finset.sum`s over word data, so
between `unfold` and `match_scalars` the group sums have to be expanded into monomials. That edit is
left to the caller — the script marks the spot with a `-- TODO(port): expand the group sums` line.

Usage (from the repository root):

    python scripts/port_small_s_discharge.py --list
    python scripts/port_small_s_discharge.py --emit sextic_pure_identity
    python scripts/port_small_s_discharge.py --emit sextic_pure_identity --check FQFP/BCH/SmallSDischarge.lean
"""

import argparse
import re
import sys

DEFAULT_SOURCE = "D:/project/Lean-BCH/BCH/SmallSDischarge.lean"

# (source name, target Lean type argument, degree of the identity)
TERM_RENAME = [
    ("bch_quartic_term", "bchQuarticTerm"),
    ("bch_quintic_term", "bchQuinticTerm"),
    ("bch_sextic_term", "bchSexticTerm"),
    ("bch_septic_term", "bchSepticTerm"),
    ("bch_octic_term", "bchOcticTerm"),
    ("bch_quintic_group_", "bchQuinticGroup"),
]


def read_text(path):
    with open(path, "rb") as fh:
        raw = fh.read()
    for enc in ("utf-8-sig", "utf-16", "utf-8"):
        try:
            return raw.decode(enc).replace("\r\n", "\n")
        except UnicodeDecodeError:
            continue
    raise SystemExit("could not decode %s" % path)


def declarations(text):
    """[(name, first_line_index, end_index)] for every top-level declaration."""
    lines = text.split("\n")
    starts = [i for i, l in enumerate(lines)
              if re.match(r"^(private |noncomputable )*(theorem|lemma|def)\s", l)]
    out = []
    for idx, i in enumerate(starts):
        m = re.match(r"^(?:private |noncomputable )*(?:theorem|lemma|def)\s+([A-Za-z0-9_]+)", lines[i])
        end = starts[idx + 1] if idx + 1 < len(starts) else len(lines)
        out.append((m.group(1), i, end))
    return lines, out


def transform(body):
    """Rewrite a source declaration into the target's scalar convention."""
    out = []
    for line in body.split("\n"):
        stripped = line.strip()
        if re.match(r"^omit \[", stripped) or re.match(r"^set_option maxHeartbeats", stripped):
            continue
        out.append(line)
    body = "\n".join(out)

    body = re.sub(
        r"theorem (\w+) \(𝕂 : Type\*\) \[RCLike 𝕂\] \{𝔸 : Type\*\}\s*\n\s*"
        r"\[NormedRing 𝔸\] \[NormedAlgebra 𝕂 𝔸\] \(a b : 𝔸\) :",
        r"theorem \1 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :",
        body)
    if "RCLike" in body or "[NormedAlgebra 𝕂 𝔸]" in body:
        raise SystemExit("header was not rewritten; check the source's shape:\n"
                         + body.split("\n")[0])
    body = re.sub(r"\((\d+) : 𝕂\)", r"(\1 : ℚ)", body)
    for old, new in TERM_RENAME:
        body = body.replace(old + " 𝕂 a b", new + " a b")
        body = body.replace(old, new)
    body = body.replace("(0 : 𝔸) := by", "(0 : 𝔸) := by", 1)
    # `unfold`-only lines get the TODO marker, since the group sums still need expanding.
    body = re.sub(r"^(\s*)unfold ((?:bchQuintic(?:Term|Group\d+)\s*)+)$",
                  r"\1unfold \2\n\1-- TODO(port): expand the group sums into monomials before match_scalars",
                  body, flags=re.M)
    # Drop the trailing comment block that belongs to the *next* declaration in the source.
    lines = body.split("\n")
    end = None
    for j, l in enumerate(lines):
        if l.strip() in ("match_scalars <;> ring", "noncomm_ring"):
            end = j
    if end is None:
        raise SystemExit("could not find the end of the proof")
    return "\n".join(lines[:end + 1]).rstrip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--source", default=DEFAULT_SOURCE)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--emit", metavar="NAME")
    ap.add_argument("--check", metavar="TARGET", help="verify the emitted text is in TARGET")
    args = ap.parse_args()
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    text = read_text(args.source)
    lines, decls = declarations(text)
    identities = [(n, i, e) for n, i, e in decls if "pure_identity" in n]
    if not identities:
        raise SystemExit("no pure identities found")

    if args.list:
        for name, i, e in identities:
            body = "\n".join(lines[i:e])
            print("%-26s source lines %5d-%-5d  %3d lines  %s"
                  % (name, i + 1, e, e - i, "bump" if "maxHeartbeats" in body else "no bump"))
        return 0

    if not args.emit:
        raise SystemExit("pass --list or --emit NAME")
    match = [x for x in identities if x[0] == args.emit]
    if not match:
        raise SystemExit("unknown identity %s" % args.emit)
    name, i, e = match[0]
    body = transform("\n".join(lines[i:e]))

    if args.check:
        target = read_text(args.check)
        missing = [l for l in body.split("\n")
                   if l.strip() and l.strip() not in target]
        if missing:
            print("NOT IN %s:" % args.check)
            for l in missing[:10]:
                print("   " + l)
            return 1
        print("%s: OK (all %d lines present in %s)" % (name, len(body.split("\n")), args.check))
        return 0

    print(body)
    return 0


if __name__ == "__main__":
    sys.exit(main())
