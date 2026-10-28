/-
Signature collector for the CQM upload: prints `@@<full name>\t<pp type>` for every
declaration the platform files need an explicit signature for.

The pp form of a theorem's type already spells out every type variable and instance
binder, which is exactly what the platform's `formal_statement` requires
(`autoImplicit false` on the server). Running the whole set through one collector keeps
the stub signature and the solution signature textually identical.

Run:  lake env lean --run tools/p2m/collect_signatures.lean > artifacts/data/cqm-signatures.tsv
-/
import FQFP.CQM.Category.Measurement
open Lean Meta

/-- The 7 targets plus every inline helper the solutions will need. -/
def wanted : List Name :=
  [ -- targets
    ``CategoryTheory.DaggerCategory.dagger_entry,
    ``CategoryTheory.DaggerCategory.dagger_biproduct_matrix,
    ``CategoryTheory.DaggerCategory.dagger_add,
    ``CategoryTheory.MonoidalCategory.Effect.disjoint_iff_isIsometry_dagger,
    ``CategoryTheory.MonoidalCategory.Effect.complete_iff_kernel_iota_eq_zero,
    ``CategoryTheory.MonoidalCategory.Effect.isUnitary_lift_of_complete_disjoint,
    ``CategoryTheory.MonoidalCategory.Effect.sum_probability_eq_one,
    -- inline helpers (DaggerBiproduct)
    ``CategoryTheory.DaggerCategory.IsDaggerBiproduct.dagger_π,
    ``CategoryTheory.DaggerCategory.IsDaggerBinaryBiproduct.dagger_fst,
    ``CategoryTheory.DaggerCategory.IsDaggerBinaryBiproduct.dagger_snd,
    ``CategoryTheory.DaggerCategory.IsDaggerBinaryBiproduct.dagger_desc,
    ``CategoryTheory.DaggerCategory.IsDaggerBinaryBiproduct.dagger_lift,
    -- inline helpers (Measurement)
    ``CategoryTheory.MonoidalCategory.Effect.iota_lift_dagger,
    ``CategoryTheory.MonoidalCategory.Effect.lift_comp_dagger_eq_sum ]

run_meta do
  let mut lines : Array String := #[]
  for n in wanted do
    match (← getEnv).find? n with
    | none =>
      lines := lines.push (Json.mkObj [("name", Json.str n.toString),
        ("missing", Json.bool true)]).compress
    | some ci =>
      -- Rebuild the binder list from the local declarations, not from the printed type.
      -- `ppExpr` renders a *non-dependent* binder as an anonymous arrow, so a signature
      -- taken from its output silently drops the hypothesis names — `(hx : P) (hxd : Q) :
      -- R` prints as `P → Q → R` — and the copied proof body then fails with
      -- "Unknown identifier `hx`". `forallTelescope` keeps each binder's `userName` and
      -- `binderInfo`, which is what a re-elaboratable signature needs.
      --
      -- `pp.funBinderTypes` is still needed for the types: without it the printer writes
      -- `fun x => …` for `fun _ : ι → 𝟙_ C`, the index type is lost, and instance
      -- synthesis gets stuck on `HasBiproduct` ("the first and fifth type arguments
      -- contain metavariables").
      let (binds, bodyS) ← forallTelescope ci.type fun xs body => do
        let mut bs : Array String := #[]
        for x in xs do
          let d ← x.fvarId!.getDecl
          let tyS ← withOptions (fun o => o.setBool `pp.funBinderTypes true) (ppExpr d.type)
          let nmS := d.userName.toString
          -- Fvar names produced by elaboration are hygienic (`inst._@.Foo._hyg.3`), which
          -- is not a usable identifier. Instance binders are resolved by synthesis rather
          -- than by name, so emit them anonymously; anything else hygienic becomes `_`.
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
        [("name", Json.str n.toString),
         ("binders", Json.str (String.intercalate " " binds.toList)),
         ("body", Json.str bodyS)]).compress
  -- Written directly rather than piped through a shell: structured, multi-line-bearing
  -- output does not survive a line-oriented shell round-trip intact.
  IO.FS.writeFile "artifacts/data/cqm-signatures.jsonl" (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"wrote {lines.size} signatures to artifacts/data/cqm-signatures.jsonl"
