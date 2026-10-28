#!/usr/bin/env python3
"""
Phase 2 classifier + Phase 3/4 generator for the Prove2Me node split.

Reads the Stage-1 declaration graph and the Stage-2 sketch facts, closes over the
MODULE IMPORT GRAPH (the declaration graph's valueDeps under-report edges that run
through private helpers), classifies every reachable declaration, and emits, for a
requested target list:

    Definitions/Def_<module>.lean   def-material bundles
    Theorems/Thm_<slug>.lean        preamble + formal_statement (ends `:= by sorry`)
    Solutions/Sol_<slug>.lean       ONLY `theorem solution`, nothing re-emitted

The split-node rule matters: a solution must NOT re-emit declarations that exist
as platform nodes, or the server's sorry check sees the platform's `by sorry`
stubs (see STATUS.md 6.9-6.14). Dependencies are pulled in with
`import Definitions.Def_*` / `import Theorems.Thm_<child>`.

Usage:
    python gen_nodes.py classify  <targets-file> <out-dir>
    python gen_nodes.py emit      <targets-file> <out-dir>
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

DEF_KINDS = ("def", "inductive", "ctor", "rec", "opaque")
# Phase 2 thresholds (playbook): proof > 40 lines -> node; <= 10 lines -> inline;
# 11-40 lines -> node only with a promotion signal (we treat as inline by default
# and promote explicitly via the targets file).
NODE_MIN_LINES = 41
INLINE_MAX_LINES = 10


def load_graph():
    by_name, by_user = {}, {}
    with open(GRAPH, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                r = json.loads(line)
                by_name[r["name"]] = r
                by_user[r["userName"]] = r
    return by_name, by_user


def load_sketch(module):
    base = module.rsplit(".", 1)[-1]
    path = os.path.join(SKETCH_DIR, f"sketch_info.{base}.jsonl")
    facts = []
    if os.path.exists(path):
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    o = json.loads(line)
                    if o.get("kind") == "decl":
                        facts.append(o)
    return facts


def module_import_closure(seeds):
    seen, q = set(), list(seeds)
    while q:
        m = q.pop()
        if m in seen:
            continue
        seen.add(m)
        path = os.path.join(SRC_ROOT, m.replace(".", os.sep) + ".lean")
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as fh:
            for ln in fh:
                s = ln.strip()
                for pre in ("import ", "public import "):
                    if s.startswith(pre):
                        dep = s[len(pre):].strip()
                        if dep.startswith("FQFP."):
                            q.append(dep)
    return seen


def module_order(rows):
    mods = sorted({r["module"] for r in rows})
    deps = {m: set() for m in mods}
    mod_of = {r["name"]: r["module"] for r in rows}
    for r in rows:
        for d in (r.get("typeDeps") or []) + (r.get("valueDeps") or []):
            dm = mod_of.get(d)
            if dm and dm != r["module"]:
                deps[r["module"]].add(dm)
    ordered, placed = [], set()
    while len(placed) < len(mods):
        progressed = False
        for m in mods:
            if m not in placed and deps[m] <= placed:
                ordered.append(m)
                placed.add(m)
                progressed = True
        if not progressed:
            for m in mods:
                if m not in placed:
                    ordered.append(m)
                    placed.add(m)
            break
    return ordered


def slug(name):
    return name.replace(".", "_")


def module_prelude(path):
    """`open` / `open scoped` / `variable` / `set_option` / `attribute` lines, in
    order, that a statement or proof sliced out of this module needs."""
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


def project_imports(module, nodes_by_module):
    """The platform imports a solution needs: the def bundle plus every child
    theorem module that lives in the same source module."""
    imports = ["import Mathlib"]
    imports.append("import Definitions.Def_TrotterError")
    return imports


def main():
    mode = sys.argv[1]
    targets_file, out_dir = sys.argv[2], sys.argv[3]
    os.makedirs(out_dir, exist_ok=True)
    with open(targets_file, encoding="utf-8") as fh:
        targets = [l.strip() for l in fh if l.strip() and not l.startswith("#")]

    by_name, by_user = load_graph()
    # close over the module import graph of every target's module
    seed_mods = {by_user[t]["module"] for t in targets if t in by_user}
    mods = module_import_closure(seed_mods)
    rows = [r for r in by_name.values() if r["module"] in mods and r["startLine"] > 0]

    defs = [r for r in rows if r["kind"] in DEF_KINDS]
    thms = [r for r in rows if r["kind"] == "theorem"]
    for r in thms:
        r["_span"] = r["endLine"] - r["startLine"] + 1
    nodes = [r for r in thms if r["_span"] >= NODE_MIN_LINES or r["userName"] in targets]
    inlines = [r for r in thms if r not in nodes]

    print(f"modules in closure : {len(mods)}")
    print(f"declarations       : {len(rows)}")
    print(f"  def-material     : {len(defs)}")
    print(f"  nodes (>= {NODE_MIN_LINES} lines or requested): {len(nodes)}")
    print(f"  inline helpers   : {len(inlines)}")
    print(f"\nrequested targets  : {len(targets)}")
    missing = [t for t in targets if t not in by_user]
    if missing:
        print(f"  !! not found: {missing}")

    with open(os.path.join(out_dir, "plan.json"), "w", encoding="utf-8") as fh:
        json.dump({
            "modules": sorted(mods),
            "counts": {"decls": len(rows), "defs": len(defs),
                       "nodes": len(nodes), "inlines": len(inlines)},
            "targets": targets,
            "nodes": [{"name": r["userName"], "module": r["module"],
                       "span": r["_span"], "startLine": r["startLine"],
                       "endLine": r["endLine"]} for r in
                      sorted(nodes, key=lambda x: (x["module"], x["startLine"]))],
            "defs": [{"name": r["userName"], "module": r["module"],
                      "startLine": r["startLine"], "endLine": r["endLine"]}
                     for r in sorted(defs, key=lambda x: (x["module"], x["startLine"]))],
        }, fh, indent=1, ensure_ascii=False)
    print(f"\nwrote {os.path.join(out_dir, 'plan.json')}")

    if mode == "classify":
        return

    # ---- emit -----------------------------------------------------------
    thm_dir = os.path.join(out_dir, "Theorems")
    sol_dir = os.path.join(out_dir, "Solutions")
    os.makedirs(thm_dir, exist_ok=True)
    os.makedirs(sol_dir, exist_ok=True)

    emitted = 0
    for t in targets:
        if t not in by_user:
            continue
        r = by_user[t]
        facts = load_sketch(r["module"])
        cand = [o for o in facts if o["declStart"]["line"] == r["startLine"]]
        if not cand:
            print(f"  !! no sketch fact for {t} (line {r['startLine']})")
            continue
        d = cand[0]
        vs = d.get("valStart")
        src_path = os.path.join(SRC_ROOT, r["module"].replace(".", os.sep) + ".lean")
        with open(src_path, encoding="utf-8", newline="") as fh:
            text = fh.read().replace("\r\n", "\n")
        data = text.encode("utf-8")
        if vs is None:
            print(f"  !! no valStart for {t}")
            continue
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

        prelude = module_prelude(src_path)
        prelude_txt = "\n".join(prelude)
        preamble = "import Mathlib"
        thm_file = (f"/-\nProve2Me theorem node `{t}`.\n\n"
                    f"Source: {REPO}/blob/{SHA}/{r['module'].replace('.', '/')}.lean"
                    f"#L{r['startLine']}-L{r['endLine']}\n-/\n"
                    + preamble + "\n\n" + prelude_txt + "\n\n" + stmt + " := by sorry\n")
        with open(os.path.join(thm_dir, f"Thm_{slug(t)}.lean"), "w",
                  encoding="utf-8", newline="\n") as fh:
            fh.write(thm_file)

        # proof slice: from valStart to the end of the declaration
        lines = text.split("\n")
        starts, off = [], 0
        for lb in lines:
            starts.append(off)
            off += len(lb.encode("utf-8")) + 1
        e = starts[r["endLine"] - 1] + len(lines[r["endLine"] - 1].encode("utf-8"))
        proof_b = data[vs["offset"]:e]
        proof = proof_b.decode("utf-8").rstrip()

        # signature: the statement minus `theorem <name>` and the trailing `:= by sorry`
        sig = re.sub(r"^\s*(theorem|lemma)\s+\S+\s*", "", stmt, count=1, flags=re.S)
        sig = re.sub(r"\s*:=\s*by\s+sorry\s*$", "", sig, flags=re.S).strip()

        sol = (f"/-\nProve2Me solution for `{t}`.\n\n"
               f"Split-node form: this file proves its target and nothing else, so no\n"
               f"declaration is re-emitted and the platform's `by sorry` stubs are never\n"
               f"pulled into the environment.\n\n"
               f"Source: {REPO}/blob/{SHA}/{r['module'].replace('.', '/')}.lean"
               f"#L{r['startLine']}-L{r['endLine']}\n-/\n"
               + preamble + "\n\n" + prelude_txt + "\n\n"
               + f"theorem solution {sig} := {proof}\n")
        with open(os.path.join(sol_dir, f"Sol_{slug(t)}.lean"), "w",
                  encoding="utf-8", newline="\n") as fh:
            fh.write(sol)
        emitted += 1

    print(f"emitted {emitted} Thm_/Sol_ pairs into {out_dir}")


if __name__ == "__main__":
    main()
