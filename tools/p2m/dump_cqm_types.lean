/-
Before/after type dump for the `MonoidalCategory` -> `Measurement` merge.

Emits one JSON line per declaration originating in the target modules, with the type split
into `binders` / `body` exactly the way `collect_signatures.lean` does (same `forallTelescope`
+ `pp.funBinderTypes` treatment, same reasons). The two runs are then compared by
`tools/p2m/diff_merge_types.py`: moving a declaration between files must not change its type,
otherwise the merge silently altered a statement.

Deliberately imports only `FQFP.CQM.Category.Measurement`, not `FQFP` — the BCH subtree is
unrelated to this merge and importing it would couple the check to its build state.

Run:  lake env lean --run tools/p2m/dump_cqm_types.lean
      (writes artifacts/data/cqm-merge-types.jsonl; rename per side before the next run)
-/
import FQFP.CQM.Category.Measurement
open Lean Meta

/-- Modules whose declarations are compared across the merge. -/
def targetModules : List Name :=
  [ `FQFP.CQM.Category.MonoidalCategory,
    `FQFP.CQM.Category.Measurement ]

run_meta do
  let env ← getEnv
  let modNames := env.header.moduleNames
  let getMod : Name → Option Name := fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modNames[idx.toNat]?
    | none => none
  -- Same private-declaration treatment as extract_decl_graph.lean: `_private.…` names are
  -- isInternal, but dropping them would hide the three reassoc lemmas the merge must move.
  let keep : Name → Bool := fun n => !n.isInternal || (privateToUserName? n).isSome
  let mut ns : Array (Name × Name) := #[]   -- (key, actual constant name)
  for (n, _) in env.constants.toList do
    unless keep n do continue
    let some m := getMod n | continue
    unless targetModules.contains m do continue
    -- Private constants are renamed by the module move (`_private.<module>.<idx>.<user>`),
    -- so key them by their user name; public ones keep their full name.
    let key := (privateToUserName? n).getD n
    ns := ns.push (key, n)
  ns := ns.qsort (fun a b => a.1.toString < b.1.toString)
  let mut lines : Array String := #[]
  for (key, n) in ns do
    let some ci := env.find? n | continue
    let modS := ((getMod n).getD Name.anonymous).toString
    let (binds, bodyS) ← forallTelescope ci.type fun xs body => do
      let mut bs : Array String := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        let tyS ← withOptions (fun o => o.setBool `pp.funBinderTypes true) (ppExpr d.type)
        let nmS := d.userName.toString
        let hygienic := nmS.contains "_hyg" || nmS.contains "_@." || nmS.contains "✝"
        if d.binderInfo == .instImplicit then
          bs := bs.push s!"[{tyS}]"
        else
          let (l, r) := match d.binderInfo with
            | .implicit => ("{", "}")
            | .strictImplicit => ("⦃", "⦄")
            | _ => ("(", ")")
          let nm := if hygienic then "_" else nmS
          bs := bs.push s!"{l}{nm} : {tyS}{r}"
      let b ← withOptions (fun o => o.setBool `pp.funBinderTypes true) (ppExpr body)
      return (bs, s!"{b}")
    lines := lines.push (Json.mkObj
      [("key", Json.str key.toString),
       ("const", Json.str n.toString),
       ("module", Json.str modS),
       ("isPrivate", Json.bool (privateToUserName? n).isSome),
       ("binders", Json.str (String.intercalate " " binds.toList)),
       ("body", Json.str bodyS)]).compress
  IO.FS.writeFile "artifacts/data/cqm-merge-types.jsonl"
    (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"wrote {lines.size} declarations to artifacts/data/cqm-merge-types.jsonl"
