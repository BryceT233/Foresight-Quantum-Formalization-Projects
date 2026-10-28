/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
import Lean

/-!
# Runtime API snapshot exporter

Invoked by `scripts/api_snapshot.py`. Runtime imports avoid inheriting project
notations while parsing this tool. Private keys include their source module.
-/

open Lean Meta

/-- Module-qualified identity for a private constant; public names are unchanged. -/
def snapshotName (env : Environment) (n : Name) : Name := Id.run do
  let some user := privateToUserName? n | return n
  let some idx := env.getModuleIdxFor? n | return n
  return `__private ++ env.header.moduleNames[idx.toNat]! ++ user

/-- Normalize binder names and metadata while retaining unambiguous constant identities. -/
partial def snapshotExpr (env : Environment) : Expr → Expr
  | .const n ls => .const (snapshotName env n) ls
  | .app f a => .app (snapshotExpr env f) (snapshotExpr env a)
  | .lam _ t b i => .lam .anonymous (snapshotExpr env t) (snapshotExpr env b) i
  | .forallE _ t b i => .forallE .anonymous (snapshotExpr env t) (snapshotExpr env b) i
  | .letE _ t v b nd => .letE .anonymous (snapshotExpr env t) (snapshotExpr env v)
      (snapshotExpr env b) nd
  | .mdata _ e => snapshotExpr env e
  | .proj s i e => .proj (snapshotName env s) i (snapshotExpr env e)
  | e => e

/-- Write the constants and their global API registrations in the imported environment. -/
def exportSnapshot (output : System.FilePath) (modulePrefix : Name) : CoreM Unit := do
  let env ← getEnv
  let simp ← getSimpTheorems
  let stream ← IO.FS.Handle.mk output .write
  let constants := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let mut count := 0
  let mut keys : Std.HashSet String := {}
  for (n, ci) in constants do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless modulePrefix.isPrefixOf m do continue
    let key := (snapshotName env n).toString
    if keys.contains key then throwError "Ambiguous private identity: {key}"
    keys := keys.insert key
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let value := match ci with
      | .defnInfo d => reprStr (snapshotExpr env d.value)
      | .opaqueInfo o => reprStr (snapshotExpr env o.value)
      | _ => ""
    let priority ← getInstancePriority? n
    let instanceKind ← getInstanceAttrKind? n
    let instanceKind := match instanceKind with
      | none => "none"
      | some .global => "global"
      | some .local => "local"
      | some .scoped => "scoped"
    let simpForms := #[simp.isLemma (.decl n true false), simp.isLemma (.decl n false false),
      simp.isLemma (.decl n true true), simp.isLemma (.decl n false true), simp.isDeclToUnfold n]
    let row := Json.mkObj [
      ("key", toJson key), ("name", toJson n.toString), ("module", toJson m.toString),
      ("private", toJson (privateToUserName? n).isSome), ("internal", toJson n.isInternal),
      ("kind", toJson kind), ("levels", toJson (ci.levelParams.map toString)),
      ("type", toJson (reprStr (snapshotExpr env ci.type))), ("value", toJson value),
      ("instance_priority", toJson priority), ("instance_kind", toJson instanceKind),
      ("simp_forms", toJson simpForms),
      ("reducibility", toJson (reprStr (getReducibilityStatusCore env n)))]
    stream.putStrLn row.compress
    count := count + 1
  IO.println s!"Exported {count} constants to {output}"

/-- Export one environment: OUTPUT PREFIX MODULE..., without rebuilding dependencies. -/
unsafe def main (args : List String) : IO UInt32 := do
  let output :: modulePrefix :: modules := args | throw <| IO.userError "Expected OUTPUT PREFIX MODULE..."
  if modules.isEmpty then throw <| IO.userError "At least one import module is required"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := modules.toArray.map fun m => ({ module := m.toName } : Import)
  let env ← importModules imports {} 0 (loadExts := true)
  let _ ← (exportSnapshot output modulePrefix.toName).toIO
    { fileName := "ApiSnapshot", fileMap := default } { env }
  return 0
