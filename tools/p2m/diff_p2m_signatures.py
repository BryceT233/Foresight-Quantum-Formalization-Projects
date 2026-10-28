#!/usr/bin/env python3
"""Cross-check that the merged source still reproduces the prove2.me upload's signatures.

D:\\p2m-v4331\\artifacts\\cqm-signatures.jsonl is the frozen record from which the platform's
`formal_statement` and `preamble` payloads were generated. Re-collecting signatures from the
post-merge source and requiring exact equality proves the refactor touched no published
statement — the same guarantee diff_types.py enforces for the transplant, applied here to the
merge.

Run:  python tools/p2m/diff_p2m_signatures.py
"""
import json
import sys
from pathlib import Path

FROZEN = Path(r"D:\p2m-v4331\artifacts\cqm-signatures.jsonl")
FRESH = Path(r"D:\project\CQM1\artifacts\cqm-signatures.jsonl")


def load(path):
    out = {}
    with path.open(encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            if rec.get("missing"):
                print(f"MISSING from environment: {rec['name']}")
                continue
            out[rec["name"]] = rec
    return out


def main():
    frozen = load(FROZEN)
    fresh = load(FRESH)
    bad = 0
    for n in sorted(set(frozen) | set(fresh)):
        f, g = frozen.get(n), fresh.get(n)
        if f is None:
            print(f"ONLY IN FRESH  {n}")
            bad += 1
            continue
        if g is None:
            print(f"ONLY IN FROZEN {n}")
            bad += 1
            continue
        if f["binders"] == g["binders"] and f["body"] == g["body"]:
            print(f"OK  {n}")
            continue
        bad += 1
        print(f"DIFF {n}")
        for field in ("binders", "body"):
            if f[field] != g[field]:
                print(f"    [{field}] frozen: {f[field]}")
                print(f"    [{field}] fresh : {g[field]}")

    print()
    print(f"frozen signatures compared : {len(frozen)}")
    print(f"fresh  signatures collected: {len(fresh)}")
    print(f"MISMATCHES                 : {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
