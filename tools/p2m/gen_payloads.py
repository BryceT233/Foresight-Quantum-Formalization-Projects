#!/usr/bin/env python3
"""
Emit Prove2Me theorem payloads (preamble + formal_statement) for the mission's
milestone nodes, sliced verbatim out of the v4.33.1 sources.

Writes one JSON file per target into <out-dir>/payload/, plus a manifest listing
them in dependency order. Milestones whose Lean theorem already exists as a
published platform node are marked `published` so the caller can add them as
`reference` items instead of drafts.

Usage:
    python gen_payloads.py <targets-file> <out-dir>
"""
import json
import os
import re
import sys

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

SRC_ROOT = r"D:\p2m-v4331"
GRAPH = r"D:\project\CQM1\decl_graph.jsonl"
SKETCH_DIR = r"D:\project\CQM1\tools\p2m\sketch"
SHA = "d6bfac12d15bc59fcc5f90206ac3312da602eb3d"
REPO = "https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects"
# already-published platform nodes: theorem user-name -> platform id
PUBLISHED = {
    "TrotterError.norm_commutatorRemainder_le": "f7c88b3b-41df-498e-af3e-2d9fbb8a5dd8",
    "TrotterError.exp_neg_mul_self": "ac8829e4-2dcc-4f19-80a7-2397990e6641",
}


def load():
    rows = []
    with open(GRAPH, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return {r["userName"]: r for r in rows}


def sketch(module):
    base = module.rsplit(".", 1)[-1]
    path = os.path.join(SKETCH_DIR, f"sketch_info.{base}.jsonl")
    out = []
    if os.path.exists(path):
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    o = json.loads(line)
                    if o.get("kind") == "decl":
                        out.append(o)
    return out


def prelude(path):
    """open / open scoped / attribute / set_option / variable lines the payload needs."""
    with open(path, encoding="utf-8", newline="") as fh:
        lines = fh.read().replace("\r\n", "\n").split("\n")
    keep, in_comment = [], False
    decl_re = re.compile(
        r"^(theorem|lemma|def|abbrev|noncomputable\s+def|protected\s+|private\s+|"
        r"instance|structure|inductive|class|example|@\[|mutual)\b")
    for ln in lines:
        s = ln.strip()
        if in_comment:
            if "-/" in s:
                in_comment = False
            continue
        if s.startswith("/-"):
            if s.startswith("/--") and not s.startswith("/-!"):
                break
            if "-/" not in s:
                in_comment = True
            continue
        if s in ("module",) or s.startswith("@[expose] public section") or s == "@[expose]":
            continue
        if s.startswith("import ") or s.startswith("public import "):
            continue
        if s.startswith("namespace ") or s == "section" or s == "end":
            continue
        if decl_re.match(s):
            break
        if s:
            keep.append(s)
    return keep


def main():
    targets_file, out_dir = sys.argv[1], sys.argv[2]
    pdir = os.path.join(out_dir, "payload")
    os.makedirs(pdir, exist_ok=True)
    with open(targets_file, encoding="utf-8") as fh:
        targets = []
        for l in fh:
            l = l.split("#", 1)[0].strip()      # allow trailing `# comment`
            if l:
                targets.append(l)

    by_user = load()
    manifest = []
    for t in targets:
        r = by_user.get(t)
        if r is None:
            print(f"!! not in graph: {t}")
            continue
        facts = sketch(r["module"])
        cand = [o for o in facts if o["declStart"]["line"] == r["startLine"]]
        if not cand:
            print(f"!! no sketch fact for {t} (startLine {r['startLine']})")
            continue
        d = cand[0]
        vs = d.get("valStart")
        if vs is None:
            print(f"!! no valStart for {t}")
            continue
        src_path = os.path.join(SRC_ROOT, r["module"].replace(".", os.sep) + ".lean")
        with open(src_path, encoding="utf-8", newline="") as fh:
            text = fh.read().replace("\r\n", "\n")
        data = text.encode("utf-8")
        a, b = d["declStart"]["offset"], vs["offset"]
        ds = d.get("docstring")
        if ds and ds["start"]["offset"] >= a:
            stmt_b = data[a: ds["start"]["offset"]] + data[ds["end"]["offset"]: b]
        else:
            stmt_b = data[a:b]
        stmt = stmt_b.decode("utf-8").rstrip()
        short = t.rsplit(".", 1)[-1]
        stmt = re.sub(r"\s*(theorem|lemma)\s+" + re.escape(short) + r"\b",
                      f"theorem {t}", stmt, count=1).strip()

        pl = prelude(src_path)
        # The platform compiles `preamble` + `formal_statement` on its own, and the
        # project's own definitions are NOT in scope unless they are imported. They
        # are published as the `TrotterError` definition bundle, which the server
        # resolves as `Definitions.Def_TrotterError`.
        preamble = "\n".join(["import Mathlib",
                              "import Definitions.Def_TrotterErrorMilestones"] + pl)
        payload = {
            "theorem_name": t,
            "preamble": preamble,
            "formal_statement": stmt + " := by sorry",
            "source": (f"{REPO}/blob/{SHA}/{r['module'].replace('.', '/')}.lean"
                       f"#L{r['startLine']}-L{r['endLine']}"),
            "lean_module": r["module"],
            "lean_span": [r["startLine"], r["endLine"]],
            "published_id": PUBLISHED.get(t),
        }
        fn = os.path.join(pdir, short + ".json")
        with open(fn, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=1, ensure_ascii=False)
        manifest.append({"target": t, "file": os.path.basename(fn),
                         "published_id": PUBLISHED.get(t),
                         "module": r["module"], "span": [r["startLine"], r["endLine"]]})
        tag = "PUBLISHED" if PUBLISHED.get(t) else "draft"
        print(f"  {tag:<9} {t}")

    with open(os.path.join(out_dir, "payload_manifest.json"), "w", encoding="utf-8") as fh:
        json.dump(manifest, fh, indent=1, ensure_ascii=False)
    print(f"\nwrote {len(manifest)} payloads to {pdir}")


if __name__ == "__main__":
    main()
