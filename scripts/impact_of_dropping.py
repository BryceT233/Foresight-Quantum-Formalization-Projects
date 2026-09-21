"""Reverse-dependency closure of a source declaration, to size the impact of dropping it.

Parses every `BCH/*.lean` declaration (name + body), then walks *upwards*: which declarations
mention the seed, which mention those, and so on. The declarations left without any consumer are
the public results that a drop would actually cost.

Usage (from the repository root, with `--root` pointing at the source tree):

    python scripts/impact_of_dropping.py --root D:/project/Lean-BCH/BCH --seed octic_pure_identity
"""

import argparse
import os
import re
import sys

DECL = re.compile(r"^(?:private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


def read(path):
    with open(path, "rb") as fh:
        raw = fh.read()
    for enc in ("utf-8-sig", "utf-16", "utf-8"):
        try:
            return raw.decode(enc).replace("\r\n", "\n")
        except UnicodeDecodeError:
            continue
    raise SystemExit("could not decode %s" % path)


def strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", " ", text)


def declarations(root):
    """{name: (file, body)} over every source file."""
    out = {}
    for fn in sorted(os.listdir(root)):
        if not fn.endswith(".lean"):
            continue
        text = strip_comments(read(os.path.join(root, fn)))
        lines = text.split("\n")
        starts = [(i, m) for i, l in enumerate(lines) if (m := DECL.match(l))]
        for idx, (i, m) in enumerate(starts):
            end = starts[idx + 1][0] if idx + 1 < len(starts) else len(lines)
            out.setdefault(m.group(2), (fn, "\n".join(lines[i:end])))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="D:/project/Lean-BCH/BCH")
    ap.add_argument("--seed", action="append", required=True)
    args = ap.parse_args()
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

    decls = declarations(args.root)
    # reverse edges: name -> declarations whose body mentions it
    consumers = {n: set() for n in decls}
    for name, (fn, body) in decls.items():
        for other in set(IDENT.findall(body)):
            if other in decls and other != name:
                consumers[other].add(name)

    seen, frontier = set(), [s for s in args.seed if s in decls]
    missing = [s for s in args.seed if s not in decls]
    while frontier:
        n = frontier.pop()
        if n in seen:
            continue
        seen.add(n)
        frontier.extend(consumers[n] - seen)

    print("seeds: %s" % ", ".join(args.seed))
    if missing:
        print("NOT FOUND: %s" % ", ".join(missing))
    print("transitively affected declarations: %d" % len(seen))
    by_file = {}
    for n in seen:
        by_file.setdefault(decls[n][0], []).append(n)
    for fn in sorted(by_file):
        print("  %-30s %3d" % (fn, len(by_file[fn])))

    roots = [n for n in seen if not consumers[n]]
    print("\nunconsumed (top-level) declarations in the closure: %d" % len(roots))
    for n in sorted(roots):
        print("  %-34s %s" % (n, decls[n][0]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
