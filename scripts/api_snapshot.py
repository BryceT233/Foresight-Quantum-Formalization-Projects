"""Export or compare Lean API snapshots; see scripts/API_SNAPSHOTS.md."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def normalize_expression(text, parameters, remap):
    # Preserve string literals and escaped identifiers. Formatting and module moves
    # must never rewrite literal contents or collapse whitespace inside them.
    result = []
    quoted = re.compile(r'("(?:[^"\\]|\\.)*")')
    tokens = re.compile(r'`(?:«[^»]*»|[^\s()\[\],«»])+|\s+|[^\s`]+')
    for index, part in enumerate(quoted.split(text)):
        if index % 2:
            result.append(part)
            continue
        for match in tokens.finditer(part):
            token = match[0]
            if token.isspace():
                continue
            if token.startswith("`"):
                name = token[1:]
                if result and result[-1].endswith("Lean.Level.param"):
                    name = parameters.get(name, name)
                else:
                    name = remap(name)
                token = "`" + name
            result.append(token)
    return "".join(result)


def load_snapshot(path, migrations):
    records = {}
    module_map = migrations.get("modules", {})
    declaration_map = migrations.get("declarations", {})
    for row in iter_records(path):
        key = row["key"]
        # Only module-qualified private identities are remapped. Public names stay stable.
        replacements = {
            "__private." + old + ".": "__private." + new + "."
            for old, new in module_map.items()
        }
        replacements.update(declaration_map)

        alternatives = [re.escape(old) + ("" if old.endswith(".") else r"(?![\w.])")
                        for old in sorted(replacements, key=len, reverse=True)]
        rename = re.compile("|".join(alternatives)) if alternatives else None

        def remap(text):
            return rename.sub(lambda m: replacements[m[0]], text) if rename else text

        key = remap(key)
        if key in records:
            raise ValueError(f"Identity collision after migration: {key}")
        parameters = {n: f"level_{i}" for i, n in enumerate(row["levels"])}
        for field in ("type", "value"):
            value = normalize_expression(row[field], parameters, remap)
            row[field] = hashlib.sha256(value.encode("utf-8")).hexdigest()
        row["levels"] = len(parameters)
        records[key] = row
    return records


def iter_records(path):
    with path.open(encoding="utf-8") as stream:
        for line in stream:
            if line.strip():
                yield json.loads(line)


def compare(args):
    migrations = json.loads(args.migrations.read_text(encoding="utf-8")) if args.migrations else {}
    before = load_snapshot(args.before, migrations)
    after = load_snapshot(args.after, {})
    fields = ("kind", "levels", "type", "value", "private", "internal", "instance_priority",
              "instance_kind", "simp_forms", "reducibility")
    changed = {
        n: [field for field in fields if before[n][field] != after[n][field]]
        for n in before.keys() & after.keys()
    }
    changed = {n: changes for n, changes in changed.items() if changes}
    missing = sorted(before.keys() - after.keys())
    added = sorted(after.keys() - before.keys())
    result = {"before": len(before), "after": len(after), "missing": missing,
              "changed": changed, "added": added,
              "scope": "public, private and generated project constants; global registrations"}
    serialized = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(serialized, encoding="utf-8")
    print(serialized, end="")
    return int(bool(missing or changed or (args.exact and added)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    export = commands.add_parser("export")
    export.add_argument("output", type=Path)
    export.add_argument("--module", action="append", default=[])
    export.add_argument("--prefix", default="FQFP")
    diff = commands.add_parser("compare")
    diff.add_argument("before", type=Path)
    diff.add_argument("after", type=Path)
    diff.add_argument("--migrations", type=Path)
    diff.add_argument("--report", type=Path)
    diff.add_argument("--exact", action="store_true", help="Also reject added declarations")
    args = parser.parse_args()
    if args.command == "compare":
        return compare(args)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    partial = args.output.resolve().with_suffix(args.output.suffix + ".partial")
    result = subprocess.call(
        ["lake", "env", "lean", "--run", "scripts/ApiSnapshot.lean",
         str(partial), args.prefix, *(args.module or ["FQFP"])], cwd=ROOT
    )
    if result == 0:
        partial.replace(args.output.resolve())
    return result


if __name__ == "__main__":
    sys.exit(main())
