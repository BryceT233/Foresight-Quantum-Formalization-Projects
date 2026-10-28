#!/usr/bin/env python3
"""
Generate a Prove2Me submission for one target theorem of the TrotterError
development, by skeleton subtraction from the source modules.

Pilot mode: emits ONE platform theorem stub (formal_statement) plus ONE
solution file containing every reachable declaration, re-emitted in
module-dependency order. Used to validate the platform pipeline end to end
before scaling to the full node-split decomposition.

Usage:
    python gen_pilot.py <target user-name> <out-dir>
"""
import json
import os
import re
import sys
from collections import deque

# Windows consoles default to GBK here; Lean source is full of Unicode.
try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

SRC_ROOT = r"D:\p2m-v4331"                       # v4.33.1 branch checkout
GRAPH = r"D:\project\CQM1\decl_graph.jsonl"
SKETCH_DIR = r"D:\project\CQM1\tools\p2m\sketch"
SHA = "d6bfac12d15bc59fcc5f90206ac3312da602eb3d"
REPO = "https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects"


def load_graph():
    by_name, by_user = {}, {}
    with open(GRAPH, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            by_name[r["name"]] = r
            by_user[r["userName"]] = r
    return by_name, by_user


def load_sketch(module):
    """module like 'FQFP.TrotterError.Calculus' -> dict name -> decl fact"""
    base = module.rsplit(".", 1)[-1]
    path = os.path.join(SKETCH_DIR, f"sketch_info.{base}.jsonl")
    facts = {}
    if not os.path.exists(path):
        return facts
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            o = json.loads(line)
            if o.get("kind") == "decl":
                # facts are namespaced implicitly; key by the short name tail
                facts.setdefault("__list__", []).append(o)
    return facts


def closure(by_name, by_user, root_user):
    if root_user not in by_user:
        raise SystemExit(f"target not found: {root_user}")
    seen, q = set(), deque([by_user[root_user]["name"]])
    while q:
        cur = q.popleft()
        if cur in seen or cur not in by_name:
            continue
        seen.add(cur)
        row = by_name[cur]
        for d in list(row.get("typeDeps") or []) + list(row.get("valueDeps") or []):
            if d in by_name:
                q.append(d)
    kept = [by_name[n] for n in seen]
    return [r for r in kept if r["startLine"] > 0]


def module_order(rows):
    """Order modules so that a module's dependencies come first."""
    mods = sorted({r["module"] for r in rows})
    deps = {m: set() for m in mods}
    mod_of = {}
    for r in rows:
        mod_of[r["name"]] = r["module"]
    for r in rows:
        for d in list(r.get("typeDeps") or []) + list(r.get("valueDeps") or []):
            dm = mod_of.get(d)
            if dm and dm != r["module"]:
                deps[r["module"]].add(dm)
    ordered, placed = [], set()
    while len(placed) < len(mods):
        progressed = False
        for m in mods:
            if m in placed:
                continue
            if deps[m] <= placed:
                ordered.append(m)
                placed.add(m)
                progressed = True
        if not progressed:                       # cycle: fall back to lexical
            for m in mods:
                if m not in placed:
                    ordered.append(m)
                    placed.add(m)
            break
    return ordered


STRIP_LINE_PATTERNS = [
    re.compile(r"^module\s*$"),
    re.compile(r"^import\s"),
    re.compile(r"^public\s+import\s"),
    re.compile(r"^public\s+section\s*$"),
    re.compile(r"^@\[expose\]\s+public\s+section\s*$"),
    re.compile(r"^@\[expose\]\s*$"),
    re.compile(r"^section\s*$"),
    re.compile(r"^end\s*$"),
]


def split_signature(sig):
    """Split `(x : T) {y : U} [C] : conclusion` into (binders, conclusion, lam_args).

    Binders are matched as balanced groups over ()/{}/().  Only a colon at depth
    zero separates the binders from the conclusion, so type annotations like
    `{𝔸 : Type*}` are not mistaken for it.  Consecutive bracket groups that share
    a type form one `fun (a b : T) =>` argument, mirroring Lean's binder grouping.
    """
    openers = {"(": ")", "{": "}", "⦃": "⦄", "[": "]"}
    closers = {v: k for k, v in openers.items()}
    groups, stack, start = [], [], 0
    i = 0
    while i < len(sig):
        ch = sig[i]
        if ch in openers:
            if not stack:
                start = i
            stack.append(ch)
        elif ch in closers:
            if stack and stack[-1] == closers[ch]:
                stack.pop()
                if not stack:
                    groups.append(sig[start: i + 1])
        elif ch == ":" and not stack:
            break
        i += 1
    binders = " ".join(groups)
    concl = sig[i + 1:].strip() if i < len(sig) else sig
    lam_args, explicit = [], []
    for g in groups:
        inner = g[1:-1]
        if ":" not in inner:
            # Bare binder: `{s}` (implicit), `[Foo]` (instance), `⦃s⦄`.
            # Keep implicit binders NAMED — `_` would not bind `s`, and later
            # occurrences such as `Fin s → 𝔸` would then be unbound.
            if g[0] in "⦃{":
                lam_args.append(g)
            else:
                lam_args.append("_")
            continue
        names, typ = inner.split(":", 1)
        names, typ = names.split(), typ.strip()
        if not names or g[0] == "[":
            # unnamed binder, or an instance binder — Lean names these itself
            lam_args.append("_")
        elif g[0] == "{":
            lam_args.append("{" + " ".join(names) + " : " + typ + "}")
        else:
            lam_args.append("(" + " ".join(names) + " : " + typ + ")")
            explicit.extend(names)
    lam = " ".join(lam_args)
    args = " ".join(explicit)
    return binders, concl, lam, args


def module_import_closure(seeds):
    """Transitive closure over `import FQFP.…` lines, read from the source files."""
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


def clean_module_source(path, rename=None):
    """Strip module-system machinery and section wrappers; keep namespace blocks.

    `rename` is an optional (local_line, old_short, new_short) triple used to give
    the target declaration a name that does not collide with the platform's own
    `by sorry` stub of it.
    """
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    out, imports = [], []
    for idx, ln in enumerate(lines, start=1):
        s = ln.strip()
        if s.startswith("import "):
            imports.append(s)
            continue
        if s.startswith("public import "):
            imports.append("import " + s[len("public import "):])
            continue
        if s in ("module",) or s.startswith("@[expose] public section") or s == "@[expose]":
            continue
        if rename:
            rl, old, new = rename
            if abs(idx - rl) <= 2:
                # only the declaration head carries `theorem`/`lemma` <name>
                ln2 = re.sub(r"\b(theorem|lemma)\s+" + re.escape(old) + r"\b",
                             lambda m: f"{m.group(1)} {new}", ln)
                ln = ln2
        out.append(ln)
    return "\n".join(out), imports


def main():
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    target, out_dir = sys.argv[1], sys.argv[2]
    os.makedirs(out_dir, exist_ok=True)

    by_name, by_user = load_graph()
    rows = closure(by_name, by_user, target)
    # Family-B lesson: the Stage-1 graph's valueDeps under-report edges that run
    # through private helpers, so neither declaration-level closure nor
    # module-level closure is complete. Close over the MODULE IMPORT GRAPH
    # instead (read from the sources), then emit those modules whole. The
    # TrotterError subtree is closed under imports and never reaches BCH/CQM.
    mods = module_import_closure({r["module"] for r in rows})
    rows = [r for r in by_name.values()
            if r["module"] in mods and r["startLine"] > 0]
    mods = module_order(rows) if rows else sorted(mods)

    print(f"target           : {target}")
    print(f"reachable decls  : {len(rows)}")
    print(f"modules (ordered): {len(mods)}")
    for m in mods:
        n = sum(1 for r in rows if r["module"] == m)
        print(f"   {m:<45} {n:4}")

    # ---- formal_statement: the target's statement, cut at valStart ------
    target_short = target.rsplit(".", 1)[-1]
    ns, _, _ = target.rpartition(".")
    trow = by_user[target]
    facts = load_sketch(trow["module"])
    src_path = os.path.join(SRC_ROOT, trow["module"].replace(".", os.sep) + ".lean")
    with open(src_path, encoding="utf-8", newline="") as fh:
        text = fh.read().replace("\r\n", "\n")
    # Stage 2's `offset` is a UTF-8 *byte* offset (Lean's String.Pos), not a
    # character index, so all slicing below works on the encoded form.
    data = text.encode("utf-8")
    lines = text.split("\n")
    line_start = trow["startLine"]                    # 1-based, authoritative
    line_end = trow["endLine"]
    head = lines[line_start - 1] if line_start - 1 < len(lines) else ""
    print(f"\ntarget decl spans lines {line_start}-{line_end}")
    print(f"head: {head[:100]}")

    # pick the Stage-2 decl fact that STARTS on the graph's start line. Names may
    # repeat (a target lemma and a private helper can share a short name), so the
    # line is the only reliable join key.
    all_facts = facts.get("__list__", [])
    cand = [o for o in all_facts if o["declStart"]["line"] == line_start]
    if not cand:
        cand = [o for o in all_facts
                if o.get("nameText") == target_short
                and o["declStart"]["line"] <= line_start <= o["declEnd"]["line"]]
    print(f"decl facts in module: {len(all_facts)}; candidates on line {line_start}: {len(cand)}")
    for o in cand:
        print(f"   nameText={o.get('nameText')} lines {o['declStart']['line']}-{o['declEnd']['line']}"
              f" valStart={'-' if o.get('valStart') is None else o['valStart']['line']}")
    if not cand:
        print("!! no matching decl fact; emitting the graph span")
        stmt_text = "\n".join(lines[line_start - 1: line_end]).strip()
    else:
        d = cand[0]
        vs = d.get("valStart")
        if vs is None:
            print("!! decl fact has no valStart; using the graph span")
            stmt_text = "\n".join(lines[line_start - 1: line_end]).strip()
        else:
            a, b = d["declStart"]["offset"], vs["offset"]
            ds = d.get("docstring")
            if ds and ds["start"]["offset"] >= a:
                stmt_bytes = data[a: ds["start"]["offset"]] + data[ds["end"]["offset"]: b]
            else:
                stmt_bytes = data[a:b]
            stmt_text = stmt_bytes.decode("utf-8").rstrip()
    stmt_text = re.sub(r"\s*theorem\s+" + re.escape(target_short) + r"\b",
                       f"theorem {target}", stmt_text, count=1).strip()
    formal = stmt_text + " := by sorry"
    # the part after the declaration name is the signature `{sig} : <type>`
    sig = re.sub(r"^\s*theorem\s+\S+\s*", "", stmt_text, count=1).strip()
    sig = re.sub(r"\s*:=\s*by\s+sorry\s*$", "", sig).strip()
    binders, concl, lam, args = split_signature(sig)

    # ---- assemble the solution body -------------------------------------
    # The target's declaration is renamed to `solution_helper`: the platform holds
    # its own `by sorry` stub of the target's statement, and re-emitting the same
    # name would put `sorryAx` into the environment the verifier inspects.
    trow = by_user[target]
    rename = (trow["startLine"], target_short, "solution_helper")
    all_imports, bodies = [], []
    for m in mods:
        rel = m.replace(".", os.sep) + ".lean"
        path = os.path.join(SRC_ROOT, rel)
        src, imps = clean_module_source(path, rename if m == trow["module"] else None)
        all_imports.extend(imps)
        bodies.append(f"\n-- ===== from {m} =====\n" + src)

    # dedupe imports; drop in-project imports (their content is re-emitted below)
    seen_imp, imports = set(), []
    for i in sorted(set(all_imports)):
        if i.startswith("import FQFP"):
            continue
        if i not in seen_imp:
            seen_imp.add(i)
            imports.append(i)
    imports.sort(key=lambda s: (0 if "Mathlib" in s else 1, s))

    header = (
        "/-\n"
        f"Prove2Me solution for `{target}`.\n\n"
        "Generated from the FQFP TrotterError development by skeleton subtraction:\n"
        "every declaration reachable from the target is re-emitted, module-system\n"
        "machinery removed, in module-dependency order.\n\n"
        f"Source: {REPO}/tree/{SHA}\n"
        "-/\n"
    )
    body = header + "\n".join(imports) + "\n" + "\n".join(bodies) + "\n"

    # the platform requires a top-level `theorem solution` whose type is exactly
    # the target's. Lean has no `theorem x := term`, so the type is restated and
    # discharged by the already-proved target.
    # The entry point restates the target's type and discharges it with `exact`,
    # letting Lean infer every implicit and instance binder from the goal type.
    # `TrotterError.<target>` is the copy re-emitted above, so the file uses no
    # platform import beyond the ones already at its head. (In the full split
    # pipeline this becomes a helper node imported as Theorems.Thm_<slug>.)
    # ---- entry point -----------------------------------------------------
    # The platform requires a top-level `theorem solution` whose type is exactly
    # the target's. The target's own platform statement is stored as `by sorry`,
    # so it must not be cited — and re-emitting a declaration under the target's
    # name would collide with that stub. The target is therefore proved here
    # under a DISTINCT helper name, and `solution` is discharged from it.
    helper = f"{ns}.solution_helper"
    src = os.environ.get("P2M_SOLUTION_SOURCE") or helper
    # `∀ …` (not bare binders) so that instance binders are resolved from the
    # goal type rather than left as metavariables.
    body += ("\n-- ===== platform entry point =====\n"
             "open TrotterError\n\n"
             f"theorem solution : ∀ {binders}, {concl} := by\n"
             f"  exact {src}\n")

    sol_path = os.path.join(out_dir, f"Sol_{target_short}.lean")
    with open(sol_path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(body)
    print(f"\nwrote {sol_path}  ({len(body.splitlines())} lines)")

    stmt_path = os.path.join(out_dir, f"Stmt_{target_short}.txt")
    with open(stmt_path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(formal + "\n")
    print(f"wrote {stmt_path}")

    # ---- the theorem's preamble -------------------------------------------
    # The platform compiles `preamble` + `formal_statement` with no local defs
    # allowed, so the definition layer must come from Definitions.Def_*. Mirrors
    # the server's module layout: Theorems/Thm_<slug>.lean imports
    # Definitions/Def_TrotterError.lean.
    preamble = "import Mathlib\nimport Definitions.Def_TrotterError"
    p_path = os.path.join(out_dir, f"Preamble_{target_short}.txt")
    with open(p_path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(preamble + "\n")
    # stage a local mirror so the exact payload can be compiled before upload
    mirror_dir = os.path.join(out_dir, "mirror", "Theorems")
    os.makedirs(mirror_dir, exist_ok=True)
    with open(os.path.join(mirror_dir, f"Thm_{target_short}.lean"),
              "w", encoding="utf-8", newline="\n") as fh:
        fh.write(preamble + "\n\n" + formal + "\n")
    print(f"wrote {p_path}  (preamble: {preamble!r})")
    print("\n--- formal_statement ---")
    print(formal)


if __name__ == "__main__":
    main()
