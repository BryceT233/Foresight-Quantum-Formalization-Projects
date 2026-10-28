#!/usr/bin/env python3
"""
Generate a Prove2Me Definitions bundle: the def/structure/instance layer the
target's `formal_statement` needs, so the statement compiles on its own.

The platform compiles a theorem's `preamble` + `formal_statement` in isolation,
and contributes.md forbids local `def`s in the preamble. Definitions must be
published first via POST /submit-definition and imported as
`import Definitions.Def_<definition_name>`.

`definition_name` must match [a-zA-Z_][a-zA-Z0-9_]*, so the bundle lives in the
namespace `TrotterError` and is registered as `Def_TrotterError`; the module then
resolves to `Definitions.Def_TrotterError`.

Usage:
    python gen_defs.py <target user-name> <out-dir>
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
SHA = "d6bfac12d15bc59fcc5f90206ac3312da602eb3d"
REPO = "https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects"

DEF_KINDS = ("def", "inductive", "ctor", "rec", "opaque")


def module_import_closure(seeds):
    """Transitive closure over `import FQFP.…` lines, read from the sources."""
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


def closure(by_name, start):
    seen, q = set(), [start]
    while q:
        cur = q.pop()
        if cur in seen or cur not in by_name:
            continue
        seen.add(cur)
        r = by_name[cur]
        for d in (r.get("typeDeps") or []) + (r.get("valueDeps") or []):
            if d in by_name:
                q.append(d)
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
        for m in mods:
            if m not in placed and deps[m] <= placed:
                ordered.append(m)
                placed.add(m)
        if len(placed) < len(mods) and all(m in placed for m in mods):
            break
        if not any(m not in placed for m in mods):
            break
        # guard against cycles stalling the loop
        before = len(placed)
        for m in mods:
            if m not in placed and deps[m] <= placed:
                ordered.append(m)
                placed.add(m)
        if len(placed) == before:
            for m in mods:
                if m not in placed:
                    ordered.append(m)
                    placed.add(m)
    return ordered


def all_subtree_imports():
    """Union of every Mathlib import used anywhere in the TrotterError subtree.

    The project's modules import only a handful of Mathlib modules directly and
    rely on FQFP-internal imports for the rest, so the project-internal ones are
    dropped when the bundle is assembled. Taking the union of the whole subtree
    restores that transitive surface; extra imports are harmless, missing ones
    cascade into `unknown namespace` / `unknown identifier` errors.
    """
    root = os.path.join(SRC_ROOT, "FQFP", "TrotterError")
    out = set()
    for name in os.listdir(root):
        if not name.endswith(".lean"):
            continue
        with open(os.path.join(root, name), encoding="utf-8") as fh:
            for ln in fh:
                s = ln.strip()
                for pre in ("import ", "public import "):
                    if s.startswith(pre):
                        dep = s[len(pre):].strip()
                        if dep.startswith("Mathlib."):
                            out.add("import " + dep)
    return out


def module_header(path):
    """The declaration-free prelude of a module: imports, `variable`, `open`,
    `open scoped`, `local notation`, `set_option`, `attribute`, and the
    `namespace`/`section` lines — everything up to the first declaration.
    Extracted declarations are emitted verbatim, so they need exactly this
    context to elaborate (binders, `open`s and notations in particular).

    In this project `open`/`variable` sit *after* `namespace TrotterError`, so
    the namespace line itself must be kept: loop until a real declaration.
    """
    with open(path, encoding="utf-8", newline="") as fh:
        lines = fh.read().replace("\r\n", "\n").split("\n")
    keep = []
    decl_re = re.compile(
        r"^(theorem|lemma|def|abbrev|noncomputable\s+def|protected\s+|private\s+|"
        r"instance|structure|inductive|class|example|@\[|mutual)\b")
    in_comment = False
    for ln in lines:
        s = ln.strip()
        if in_comment:
            # inside a block comment: consume it, drop it from the prelude, and
            # only leave the comment once the closer is seen
            if "-/" in s:
                in_comment = False
            continue
        if s.startswith("/-"):
            # A `/--` docstring directly above a declaration belongs to that
            # declaration (which is emitted separately), so it marks the end of
            # the prelude. `/-!` section headers and plain `/-` block comments are
            # context: drop them and keep collecting.
            if s.startswith("/--") and not s.startswith("/-!"):
                break
            if "-/" not in s:
                in_comment = True
            continue
        if s in ("module",) or s.startswith("@[expose] public section") or s == "@[expose]":
            continue
        if s.startswith("import ") or s.startswith("public import "):
            continue                       # collected separately, deduped
        if s.startswith("namespace ") or s == "section":
            continue                       # bodies are wrapped once, below
        if s == "end":
            continue                       # closes the stripped section/namespace
        if decl_re.match(s):
            break                          # first real declaration ends the prelude
        keep.append(ln)
    while keep and not keep[-1].strip():
        keep.pop()
    return "\n".join(keep)


def main():
    target, out_dir = sys.argv[1], sys.argv[2]
    os.makedirs(out_dir, exist_ok=True)
    by_name, by_user = load_graph()
    # A targets file lists many targets; union their closures so one bundle serves
    # the whole upload. A bare name is treated as a single target.
    if os.path.exists(target):
        with open(target, encoding="utf-8") as fh:
            targets = []
            for l in fh:
                l = l.split("#", 1)[0].strip()     # allow trailing `# comment`
                if l:
                    targets.append(l)
        label = f"{len(targets)} targets"
    else:
        targets, label = [target], target
    seen = set()
    for t in targets:
        if t in by_user:
            seen |= closure(by_name, by_user[t]["name"])

    # every definition-like declaration the targets' statements need
    seeds = [by_name[n] for n in seen
             if by_name[n]["startLine"] > 0 and by_name[n]["kind"] in DEF_KINDS]
    # The bundle must be SELF-CONTAINED: a def body may cite helper theorems
    # (a structure whose fields carry proofs, a definition whose value uses a
    # lemma), and those must ship with it or the server cannot compile it.
    # Close over the declaration graph and keep every non-private declaration.
    work = [s["name"] for s in seeds]
    keep_names, visited = set(), set()
    while work:
        nm = work.pop()
        if nm in visited or nm not in by_name:
            continue
        visited.add(nm)
        r = by_name[nm]
        if r["startLine"] <= 0 or r.get("isPrivate"):
            continue
        if r["kind"] in ("ctor", "rec"):
            continue                       # ship with their parent structure
        keep_names.add(nm)
        for d in (r.get("typeDeps") or []) + (r.get("valueDeps") or []):
            if d in by_name and d not in visited:
                work.append(d)
    defs = [by_name[n] for n in keep_names]
    print(f"  (closure expanded from {len(seeds)} defs to {len(defs)} declarations)")
    # The Stage-1 graph reports a structure's FIELDS as separate `def` rows that sit
    # inside the structure's span. Emitting them on their own produces duplicate
    # field declarations, so drop any row whose span is contained in another
    # emitted declaration's span (in the same module).
    spans = {}
    for d in defs:
        spans.setdefault(d["module"], []).append((d["startLine"], d["endLine"], d["name"]))
    keep = []
    for d in defs:
        contained = False
        for (s, e, nm) in spans[d["module"]]:
            if nm == d["name"]:
                continue
            if s <= d["startLine"] and d["endLine"] <= e:
                contained = True
                break
        if not contained:
            keep.append(d)
    print(f"  (dropped {len(defs) - len(keep)} fields/nested rows inside other spans)")
    defs = keep
    # A structure/inductive must be declared BEFORE the `variable` line that
    # mentions it, and other modules' bodies rely on `open ProductFormulaData`
    # being in effect (it sits inside `namespace TrotterError` in the sources), so
    # re-establish it right after the structure is declared.
    structs = [d for d in defs if d["kind"] == "inductive"]
    others = [d for d in defs if d["kind"] != "inductive"]
    struct_names = [d["name"].split(".")[-1] for d in structs]
    def render(d, text, data, starts, line_bytes):
        a = starts[d["startLine"] - 1]
        b = starts[d["endLine"] - 1] + len(line_bytes[d["endLine"] - 1].encode("utf-8"))
        return data[a:b].decode("utf-8").rstrip()

    head_structs = []
    for d in structs:
        path = os.path.join(SRC_ROOT, d["module"].replace(".", os.sep) + ".lean")
        with open(path, encoding="utf-8", newline="") as fh:
            _t = fh.read().replace("\r\n", "\n")
        _lb = _t.split("\n")
        _st, _off = [], 0
        for x in _lb:
            _st.append(_off)
            _off += len(x.encode("utf-8")) + 1
        head_structs.append(f"\n-- {d['name']}\n" + render(d, _t, _t.encode("utf-8"), _st, _lb))
    defs = others
    by_parent = {}
    for d in defs:
        nm = d["name"]
        # `X.mk` / `X.rec` belong to the structure/inductive `X`
        parent = nm
        for suf in (".mk", ".rec", ".recOn", ".casesOn", ".noConfusion", ".below", ".brecOn"):
            if nm.endswith(suf):
                parent = nm[: -len(suf)]
                break
        prev = by_parent.get(parent)
        # prefer the row that actually declares the type (inductive/def/structure)
        rank = {"inductive": 0, "def": 1, "opaque": 2, "ctor": 3, "rec": 4}
        if prev is None or rank.get(d["kind"], 5) < rank.get(prev["kind"], 5):
            by_parent[parent] = d
    defs = list(by_parent.values())

    mods = module_order(defs)
    # Dependency-directed hoisting: a module that defines a STRUCTURE must be
    # emitted before any module whose declarations use it, or the structure is
    # still an unresolved identifier at that point. `module_order` only knows the
    # edges it can see, so hoist defining modules explicitly.
    definers = {}
    for d in defs:
        if d["kind"] == "inductive":
            definers[d["name"].split(".")[-1]] = d["module"]
    def hoist_rank(m):
        # ProductFormula defines `ProductFormulaData`; keep it first.
        return 0 if "ProductFormula" in m and m.endswith("ProductFormula") else 1
    mods = sorted(mods, key=lambda m: (hoist_rank(m), mods.index(m)))
    print(f"target: {label}")
    print(f"definition-like declarations: {len(defs)}")
    for m in mods:
        n = sum(1 for d in defs if d["module"] == m)
        print(f"   {m:<45} {n:4}")

    # ---- emit the definition bodies, module by module --------------------
    chunks, imports, opens, variables = [], [], [], []
    for m in mods:
        path = os.path.join(SRC_ROOT, m.replace(".", os.sep) + ".lean")
        with open(path, encoding="utf-8", newline="") as fh:
            text = fh.read().replace("\r\n", "\n")
        data = text.encode("utf-8")
        # a per-line byte index: offsets must all be byte-based (Lean's String.Pos
        # is a UTF-8 byte offset, and mixing in character counts slices wrongly)
        line_bytes = text.split("\n")
        starts, off = [], 0
        for lb in line_bytes:
            starts.append(off)
            off += len(lb.encode("utf-8")) + 1            # +1 for the newline

        for ln in line_bytes:
            s = ln.strip()
            if s.startswith("variable "):
                # `variable` lines bind the module's type parameters with their
                # typeclass assumptions. Extracted def bodies rely on them (e.g.
                # `dysonTerm` needs `NormOneClass 𝔸` to elaborate the numeral `1`),
                # so they must ship with the bundle.
                variables.append(s)
            elif s.startswith("import "):
                imports.append(s)
            elif s.startswith("public import "):
                imports.append("import " + s[len("public import "):])
            elif s.startswith("open ") or s.startswith("open scoped "):
                # Only keep `open`s of Mathlib namespaces. An `open` of a
                # PROJECT-owned namespace (`ProductFormulaData`, `TrotterError…`)
                # would be emitted before the bundle reopens that namespace, and
                # fails with `unknown namespace`; the bodies below are re-emitted
                # in their original relative context, so they do not need it.
                if re.search(r"\b(ProductFormulaData|TrotterError)\b", s):
                    continue
                opens.append(s)
            elif s.startswith("attribute ") or s.startswith("set_option "):
                # module-local elaboration context the extracted bodies rely on
                # (e.g. `attribute [local instance] LieRing.ofAssociativeRing`)
                opens.append(s)

        chunks.append(f"\n/-! #### from {m} -/\n")
        open_ns = None
        for d in sorted([x for x in defs if x["module"] == m],
                        key=lambda x: x["startLine"]):
            # A declaration whose fully-qualified name is `TrotterError.<X>.…` was
            # written inside `namespace <X>`; slicing it out loses that context, so
            # reopen the nested namespace around the run of such declarations.
            parts = d["name"].split(".")
            want = parts[1] if len(parts) >= 3 and parts[0] == "TrotterError" else None
            if want != open_ns:
                if open_ns is not None:
                    chunks.append(f"end {open_ns}\n")
                if want is not None:
                    chunks.append(f"namespace {want}\n")
                open_ns = want
            a = starts[d["startLine"] - 1]
            b = starts[d["endLine"] - 1] + len(line_bytes[d["endLine"] - 1].encode("utf-8"))
            body = data[a:b].decode("utf-8").rstrip()
            chunks.append(f"\n-- {d['name']}\n{body}")
        if open_ns is not None:
            chunks.append(f"end {open_ns}\n")

    seen_imp, imps = set(), []
    for i in sorted(set(imports) | all_subtree_imports()):
        if i.startswith("import FQFP") or i in seen_imp:
            continue
        seen_imp.add(i)
        imps.append(i)
    imps.sort(key=lambda s: (0 if "Mathlib" in s else 1, s))

    # All `open`s go in one block AFTER every import, so each one resolves. An
    # `open` naming a namespace this bundle does not define (e.g.
    # `TrotterError.List`, which lives in a different module) is skipped.
    seen_open, open_lines = set(), []
    for o in opens:
        if o in seen_open:
            continue
        seen_open.add(o)
        open_lines.append(o)
    open_lines = [o for o in open_lines if not o.startswith("open TrotterError.List")]

    header = (
        "/-\n"
        f"Prove2Me definition bundle for `{target}`.\n\n"
        "The def/structure layer needed by the target's formal_statement, so that\n"
        "the statement compiles standalone. Generated from the FQFP TrotterError\n"
        "development; source spans are taken verbatim.\n\n"
        f"Source: {REPO}/tree/{SHA}\n"
        "-/\n"
    )
    seen_var, var_lines = set(), []
    for v in variables:
        if v not in seen_var:
            seen_var.add(v)
            var_lines.append(v)
    # `variable` and `open` of project namespaces must sit INSIDE
    # `namespace TrotterError` so that names like `ProductFormulaData` resolve.
    out = (header + "\n".join(imps)
           + "\n\nnamespace TrotterError\n"
           + "\n".join(head_structs)
           + "".join(f"\nopen {n}\n" for n in struct_names)
           + "\n" + "\n".join(var_lines) + "\n"
           + "\n".join(open_lines) + "\n"
           + "\n".join(chunks)
           + "\n\nend TrotterError\n")

    out_path = os.path.join(out_dir, "Def_TrotterError.lean")
    with open(out_path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(out)
    print(f"\nwrote {out_path}  ({len(out.splitlines())} lines)")


if __name__ == "__main__":
    main()
