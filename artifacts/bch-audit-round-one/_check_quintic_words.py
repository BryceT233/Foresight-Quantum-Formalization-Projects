#!/usr/bin/env python3
"""Fidelity check for the arity-free rewrite of the quintic groups.

`bch-term-fidelity-check.py` parses the *textual bodies* of the group definitions, which the
arity-free rewrite replaced by `Finset.sum`s over `Fin m → Fin 5 → Bool` pattern vectors. This
script redoes exactly that comparison for the new shape: it extracts the words from

  * the source `bch_quintic_group_*` in `Lean-BCH/BCH/Basic.lean`, written as explicit products of
    the letters `a` and `b`, and
  * the target `bchQuinticGroup*Words` in `FQFP/BCH/BCHTerms.lean`, written as `![true, …]` patterns
    where `true` is the letter `a`,

and compares the two multisets. A mismatch means the rewrite changed the mathematical content.

Run with:  python artifacts/bch-audit-round-one/_check_quintic_words.py
"""

import pathlib
import re
import sys

SRC = pathlib.Path(r"D:\project\Lean-BCH\BCH\Basic.lean")
TGT = pathlib.Path(r"D:\project\CQM1\FQFP\BCH\BCHTerms.lean")

GROUPS = [("bch_quintic_group_1", "bchQuinticGroup1", 4),
          ("bch_quintic_group_4", "bchQuinticGroup4", 10),
          ("bch_quintic_group_6", "bchQuinticGroup6", 14),
          ("bch_quintic_group_24", "bchQuinticGroup24", 2)]


def body_after(text, needle):
    """The definition body: everything after the first `:=` up to the next blank line."""
    chunk = text.split(needle, 1)[1].split("\n\n", 1)[0]
    return chunk.split(":=", 1)[1]


def source_words(text, name):
    """The words of `name`, one 5-letter string per summand, read off the explicit product."""
    words = []
    for term in body_after(text, f"def {name} ").replace("\n", " ").split("+"):
        letters = re.findall(r"[ab]", term)
        if letters:
            words.append("".join(letters))
    return words


def target_words(text, name):
    """The words of `name`Words, read off the `![true, …]` pattern vectors."""
    body = body_after(text, f"def {name}Words")
    patterns = re.findall(r"!\[([^][]*)\]", body)
    words = []
    for pat in patterns:
        entries = [t.strip() for t in pat.split(",")]
        assert all(t in ("true", "false") for t in entries), entries
        words.append("".join("a" if t == "true" else "b" for t in entries))
    return words


def main():
    src_text = SRC.read_text(encoding="utf-8")
    tgt_text = TGT.read_text(encoding="utf-8")
    ok = True
    for src_name, tgt_name, expected in GROUPS:
        want = source_words(src_text, src_name)
        got = target_words(tgt_text, tgt_name)
        counts = f"source {len(want)}, target {len(got)}, expected {expected}"
        if len(want) != expected or len(got) != expected:
            print(f"MISMATCH {tgt_name}: wrong number of words ({counts})")
            ok = False
            continue
        if sorted(want) != sorted(got):
            only_src = sorted(set(want) - set(got))
            only_tgt = sorted(set(got) - set(want))
            print(f"MISMATCH {tgt_name}: only in source {only_src}, only in target {only_tgt}")
            ok = False
            continue
        # multiplicities
        if sorted(want) != sorted(got):
            ok = False
        print(f"MATCH {tgt_name}: {len(got)} words ({counts})")
    print("all groups match the source" if ok else "FIDELITY FAILURE")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
