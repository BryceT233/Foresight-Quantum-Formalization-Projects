"""Regression tests for identity, registration and fail-closed snapshot comparison."""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from types import SimpleNamespace

from api_snapshot import compare, load_snapshot


def record(key="__private.FQFP.Left.helper", module="FQFP.Left", **changes):
    row = dict(key=key, name=key, module=module, private=True, internal=True,
               kind="definition", levels=["u_1"], type="Lean.Level.param `u_1",
               value="Lean.Expr.const `__private.FQFP.Left.helper []",
               instance_priority=None, instance_kind="none", simp_forms=[False]*5,
               reducibility="regular")
    row.update(changes)
    return row


class SnapshotComparisonTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def write(self, name, rows):
        path = self.root / name
        path.write_text("".join(json.dumps(r) + "\n" for r in rows), encoding="utf-8")
        return path

    def result(self, before, after, **options):
        args = SimpleNamespace(before=self.write("before", before), after=self.write("after", after),
                               migrations=None, exact=False, report=None, **options)
        with contextlib.redirect_stdout(io.StringIO()):
            return compare(args)

    def test_private_names_in_different_modules_remain_distinct(self):
        path = self.write("records", [record(), record("__private.FQFP.Right.helper", "FQFP.Right")])
        self.assertEqual(len(load_snapshot(path, {})), 2)

    def test_explicit_module_move_maps_private_references(self):
        before = self.write("before", [record()])
        after = self.write("after", [record("__private.FQFP.Right.helper", "FQFP.Right",
                           value="Lean.Expr.const `__private.FQFP.Right.helper []")])
        left = load_snapshot(before, {"modules": {"FQFP.Left": "FQFP.Right"}})
        right = load_snapshot(after, {})
        self.assertEqual(left.keys(), right.keys())
        self.assertEqual(next(iter(left.values()))["value"], next(iter(right.values()))["value"])

    def test_migration_collision_is_an_error(self):
        path = self.write("records", [record(), record("__private.FQFP.Right.helper", "FQFP.Right")])
        with self.assertRaisesRegex(ValueError, "collision"):
            load_snapshot(path, {"modules": {"FQFP.Left": "FQFP.Right"}})

    def test_priority_simp_type_body_and_missing_changes_fail(self):
        for field, value in [("instance_priority", 100), ("simp_forms", [True]*5),
                             ("type", "DifferentType"), ("value", "DifferentBody")]:
            with self.subTest(field=field):
                self.assertEqual(self.result([record()], [record(**{field:value})]), 1)
        self.assertEqual(self.result([record()], []), 1)

    def test_universe_binder_renaming_is_allowed(self):
        self.assertEqual(self.result([record()], [record(levels=["v"], type="Lean.Level.param `v")]), 0)

    def test_added_declarations_can_be_checked_strictly(self):
        before, after = self.write("before", []), self.write("after", [record()])
        args = SimpleNamespace(before=before, after=after, migrations=None, exact=True, report=None)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(compare(args), 1)

    def test_private_rename_does_not_rename_a_longer_identifier(self):
        row = record(value="Lean.Expr.const `__private.FQFP.Left.helperExtra []")
        path = self.write("records", [row])
        unchanged = load_snapshot(path, {})
        renamed = load_snapshot(path, {"declarations": {"__private.FQFP.Left.helper": "other"}})
        self.assertEqual(next(iter(unchanged.values()))["value"],
                         next(iter(renamed.values()))["value"])

    def test_formatting_is_ignored_but_literal_spaces_are_preserved(self):
        self.assertEqual(self.result([record(value='Lean.Expr.lit "two  spaces"')],
                                     [record(value='Lean.Expr.lit\n  "two  spaces"')]), 0)
        self.assertEqual(self.result([record(value='Lean.Expr.lit "two  spaces"')],
                                     [record(value='Lean.Expr.lit "two spaces"')]), 1)

    def test_module_move_does_not_rewrite_a_string_literal(self):
        path = self.write("records", [record(value='Lean.Expr.lit "__private.FQFP.Left.helper"')])
        original = load_snapshot(path, {})
        renamed = load_snapshot(path, {"modules": {"FQFP.Left":"FQFP.Right"}})
        self.assertEqual(next(iter(original.values()))["value"],
                         next(iter(renamed.values()))["value"])


if __name__ == "__main__":
    unittest.main()
