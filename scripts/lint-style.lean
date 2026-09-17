/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
import Mathlib.Tactic.Linter.TextBased
import Cli.Basic
import Lean.Elab.ParseImportsFast

/-!
# `lake exe lint-style`

Runs Mathlib's text-based style linters (line length, trailing whitespace, tabs, unicode,
adaptation notes, ...) over the modules of this project.

This is the local counterpart of `lake exe runLinter` (which is the declaration linter). The
linters themselves live in `Mathlib.Tactic.Linter.TextBased`; this file only supplies the
project's linter options and the list of modules, so that `lake exe lint-style` lints this
project rather than Mathlib.

`scripts/nolints-style.txt` holds per-file exceptions in Mathlib's format.
-/

-- The `Cli` macro separates the blocks of its `FLAGS:`/`ARGS:` sections by blank lines; that is
-- the macro's layout, not a style slip, so the `emptyLine` linter is off for this file.
set_option linter.style.emptyLine false

open Cli Lean.Linter Mathlib.Linter.TextBased System.FilePath

/-- The Lean options that `lakefile.toml` sets, in the shape the linters consume. `weak.`-prefixed
names are stripped, exactly as Lean does when reading command line arguments. -/
def projectOptions : Lean.Options :=
  let raw : Lean.LeanOptions := .ofArray #[
    ⟨`pp.unicode.fun, .ofBool true⟩,
    ⟨`relaxedAutoImplicit, .ofBool false⟩,
    ⟨`weak.linter.mathlibStandardSet, .ofBool true⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩]
  raw.values.foldl (fun acc name value =>
    let name : Lean.Name :=
      if name.getRoot == `weak then name.replacePrefix `weak .anonymous else name
    acc.insert name value.toDataValue) Lean.Options.empty

/-- Every Lean module under `dir`, recursively, named as `pre.path`. -/
partial def modulesUnder (dir : System.FilePath) (pre : Lean.Name) :
    IO (Array Lean.Name) := do
  let mut mods : Array Lean.Name := #[]
  for entry in (← dir.readDir) do
    if ← entry.path.isDir then
      mods := mods ++ (← modulesUnder entry.path (pre ++ entry.fileName.toName))
    else if entry.path.extension == some "lean" then
      mods := mods.push (pre ++ (entry.fileName.dropEnd 5).toName)
  return mods

/-- Every Lean module of the project, derived from the source directories. -/
def projectModules : IO (Array Lean.Name) := do
  let mut mods : Array Lean.Name := #[]
  for dir in ["FQFP", "_spike"] do
    if ← (dir : System.FilePath).pathExists then
      mods := mods ++ (← modulesUnder dir dir.toName)
  return mods

/-- Implementation of the `lint-style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let opts : LinterOptions := {
    toOptions := projectOptions
    linterSets := (linterSetsExt.getState (← Lean.importModules #[] {} 0)).merged }
  let style : ErrorFormat :=
    if args.hasFlag "github" then .github
    else if args.hasFlag "exceptionsFile" then .exceptionsFile
    else .humanReadable
  let fix := args.hasFlag "fix"
  let mods ← match args.variableArgsAs! String with
    | #[] => projectModules
    | given => pure <| given.map (·.toName)
  if mods.isEmpty then
    throw <| IO.userError "lint-style: no modules to lint"
  let filename : System.FilePath := "scripts" / "nolints-style.txt"
  let nolints ← try
      IO.FS.lines filename
    catch _ =>
      IO.eprintln s!"warning: nolints file could not be read; treating as empty: {filename}"
      pure #[]
  let numberErrors := (← lintModules opts nolints mods style fix)
    + (← modulesNotUpperCamelCase opts mods).toUInt32
    + (← modulesOSForbidden opts mods).toUInt32
  if fix then return 0 else return min numberErrors 125

/-- Setting up command line options and help text for `lake exe lint-style`. -/
def lintStyle : Cmd := `[Cli|
  «lint-style» VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in specified modules.
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    exceptionsFile; "Print errors in the format of the `nolints-style.txt` exceptions file"
    fix;        "Automatically fix the style error, if possible"

  ARGS:
    ...modules : String; "Which modules will be linted.\n\
                          If no modules are specified, every module of this project is linted."
]

/-- The entry point to the `lake exe lint-style` command. -/
def main (args : List String) : IO UInt32 := do lintStyle.validate args
