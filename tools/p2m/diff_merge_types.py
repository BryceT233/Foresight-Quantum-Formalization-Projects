#!/usr/bin/env python3
"""Verify that moving declarations from MonoidalCategory.lean into Measurement.lean did not
change a single declaration type.

Compares artifacts/cqm-merge-types-before.jsonl against -after.jsonl, keyed by each
declaration's user-facing name. Private constants are renamed by the module move
(`_private.<module>.<idx>.<user>`), so their mangled name cannot serve as a key; the collector
already emitted `key` = user name for exactly this reason.

Unlike diff_types.py this comparison is STRICT — no universe-name folding. Nothing is
renumbered here: the same declarations are re-elaborated in a new file, from the same section
variables, so any textual difference at all is a real difference and must be justified.

Run:  python tools/p2m/diff_merge_types.py
"""
import json
import sys
from pathlib import Path

ART = Path(r"D:\project\CQM1\artifacts")


def load(path):
    out = {}
    with path.open(encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            if rec.get("missing"):
                print(f"MISSING in environment: {rec['name']}")
                continue
            out[rec["key"]] = rec
    return out


def short(module):
    return module.rsplit(".", 1)[-1]


def main():
    before = load(ART / "cqm-merge-types-before.jsonl")
    after = load(ART / "cqm-merge-types-after.jsonl")

    bad = 0
    removed = sorted(set(before) - set(after))
    added = sorted(set(after) - set(before))
    for k in removed:
        print(f"REMOVED  {k}")
        bad += 1
    for k in added:
        print(f"ADDED    {k}")
        bad += 1

    moved_count = 0
    for k in sorted(set(before) & set(after)):
        b, a = before[k], after[k]
        diffs = []
        for field in ("binders", "body", "isPrivate"):
            if b[field] != a[field]:
                diffs.append((field, b[field], a[field]))
        # A public declaration must keep its fully-qualified name; only the *module* it is
        # attributed to may change, and that is reported separately below.
        if not b["isPrivate"] and b["const"] != a["const"]:
            diffs.append(("const", b["const"], a["const"]))
        if diffs:
            bad += 1
            print(f"DIFF     {k}")
            for field, x, y in diffs:
                print(f"    [{field}] before: {x}")
                print(f"    [{field}] after : {y}")
        else:
            if b["module"] != a["module"]:
                moved_count += 1
                print(f"OK  moved  {short(b['module'])} -> {short(a['module'])}   {k}")
            else:
                print(f"OK  stays  {short(a['module'])}   {k}")

    print()
    print(f"shared declarations compared : {len(set(before) & set(after))}")
    print(f"  of which relocated         : {moved_count}")
    print(f"removed / added              : {len(removed)} / {len(added)}")
    print(f"before total / after total   : {len(before)} / {len(after)}")
    print(f"STRICT TYPE MISMATCHES       : {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
