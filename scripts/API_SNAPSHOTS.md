# API snapshots and project checks

Run `python scripts/check.py` from a configured Lean environment. The same command
runs in CI: it builds the sole umbrella entrypoint `FQFP`, runs declaration
and style lint, tests the snapshot comparator, and runs every `.lean` regression
under `FQFPTest/`. The default style command now scans that directory too.
Fetch Mathlib's cache first if it is absent (`lake exe cache get`).

## Export and compare

Build the modules before exporting. Snapshots import their compiled environments;
the exporter deliberately does not rebuild them implicitly.

```text
python scripts/api_snapshot.py export scratch/before.jsonl
# Make and build the proposed changes, then:
python scripts/api_snapshot.py export scratch/after.jsonl
python scripts/api_snapshot.py compare scratch/before.jsonl scratch/after.jsonl --report scratch/api-diff.json
```

By default the exporter imports `FQFP` and records constants whose defining module
starts with `FQFP`. Select a narrower environment with repeated `--module` flags;
`--prefix` controls the defining-module filter. Use the same import set on both
sides. `--exact` additionally rejects newly added declarations. A nonzero exit
means a missing declaration, changed recorded field, or a malformed/colliding
identity; a successful comparison does not require the module locations to match.

## Identity and coverage

The snapshot records public, private and generated project constants. A private
identity contains **both its source module and full user name**, so same-named
helpers in different modules stay distinct. The exporter rejects collisions
instead of silently overwriting records. Universe binder names, local binder
names and expression metadata are normalized; binder order and implicitness are
preserved. Definition and opaque values are compared; theorem proof bodies are
not. Raw snapshots can be large and belong in `scratch/`, not in Git.

Recorded global API state includes instance priority and registration kind,
four simp membership forms (pre/post, forward/reverse), simp unfolding membership,
and reducibility status. This is **not** a snapshot of local proof-context
instances, simp theorem priorities, every custom attribute, proof performance,
or the complete theorem-axiom dependency graph. Source review, kernel builds,
regressions and, where needed, an axiom audit remain separate checks.

The tools do not recover historical private data that older exporters omitted.
New snapshots must be taken before and after a change to establish that coverage.
The earlier public-only snapshots remain useful within their documented scope.

## Explicit migrations

```text
python scripts/api_snapshot.py compare scratch/before.jsonl scratch/after.jsonl --migrations scripts/api_migrations.json
```

`api_migrations.json` records the original 109 file relocations, the five
generic category modules moved out of `CQM`, and fourteen Carleman module moves. Its `modules`
dictionary remaps only module-qualified private identities and references;
public declaration namespaces are not automatically renamed. `declarations`
supports explicit identity moves for split modules. A custom map must identify
the actual private destination when one old module splits into several files:
the recorded primary destination is not a claim that every helper moved there.
The checked-in declaration map also records the four generated proof helpers
moved when generic polynomial degree bounds were split out of the Lie module.
The original private support-bound theorem stays in the Lie module as a wrapper;
its identity is deliberately not mapped to the new public theorem.
The dagger-category split maps its generated `HasKernels` proof helper explicitly
to `CategoryTheory.Dagger.Kernels`; other private helpers remain in the primary
destinations. Monoidal, braided, scalar and state declarations retain their
public names, independently of their new module locations.
Two generated macro/unexpander declarations for the dagger notation also have
explicit name moves, since Lean embeds their source module in their names.
The Carleman split has twelve explicit helper moves: three for monomial-basis
coordinates, one for augmentation-ideal membership, one for the polynomial
derivative example, and seven for the scalar Grönwall budget. Helpers belonging
to retained approximant/error declarations keep their original module identities.
The actual private flat-function construction moves with the infinite-coordinate
nonuniqueness theorem, via the `Carleman.Counterexamples` module mapping.
The remaining-structure pass adds ten relation/RelCat module moves and sixteen
exact helper moves for split polynomial, subset-sum, Taylor, asymptotic, ODE and
bicone declarations. Sixteen older helper identities also map directly to their
final destinations; this preserves the comparator's one-pass rename semantics
when a declaration has moved in more than one refactoring round.
Overlapping rename rules are applied once, longest match first; identity
collisions fail closed. Review every reported removal or registration change.

## Regression tests for the tools

```text
python -m unittest discover -s scripts -p test_api_snapshot.py
```

These tests cover private identity separation and collisions, explicit moves,
changed types/bodies/registrations, universe binder renaming and strict additions.
The real before/after exports test integration with Lean; synthetic records only
test the comparator's failure modes.
