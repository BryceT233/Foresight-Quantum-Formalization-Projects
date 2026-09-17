# Upstream `NormedSpace.log` (mathlib4 PR #43670) vs. `FQFP/BCH/LogOnePlus.lean`

Decision note. Question from the author: should `FQFP/BCH/LogOnePlus.lean` be refactored to align
with the newly merged `NormedSpace.log`?

**Answer: yes — but as an interface migration, not a rewrite of the analytic content.** The
reasons, the overlap map and the concrete plan are below.

## 1. Availability (verified locally)

The file is **not** in this project's pinned Mathlib. `lakefile.toml` pins `rev = "v4.33.0"`, and
the checkout at `.lake/packages/mathlib` is

```
HEAD db584cd6d4  2026-08-10  (tag: v4.33.0, tag: master-2026-08-10, origin/stable)
```

- `Mathlib/Analysis/Normed/Algebra/` has no `Logarithm.lean` (only `Basic`, `DualNumber`,
  `GelfandMazur`, `MatrixExponential`, `QuaternionExponential`, `Spectrum`, `Ultra`, `Unitization`,
  `UnitizationL1`, `Exponential`, `GelfandFormula`, `TrivSqZeroExt`).
- A whole-tree search for `logSeries`, `NormedSpace.log`, `log_eq_tsum`, `star_log`, `log_mem`
  returns **zero** hits.

So none of the upstream names can be referred to today without moving the pin. The PR is
[#43670 "feat: add NormedSpace.log"](https://github.com/leanprover-community/mathlib4/pull/43670),
merged after 2026-08-10. (Its file path is not verifiable from here — github.com is blocked by this
environment's network policy — but the imports `Mathlib.Algebra.Algebra.TransferInstance`,
`Mathlib.Algebra.Star.Module`, `Mathlib.Analysis.Analytic.OfScalars` are all present locally, so
nothing in it needs new dependencies.)

## 2. What the two files actually are

They are **two halves of the same project**, and upstream says so explicitly:

> This file only contains the definition and its immediate algebraic properties; convergence of the
> series and the relation to `NormedSpace.exp` are left to later files.

| layer | upstream PR #43670 | `FQFP/BCH/LogOnePlus.lean` |
|---|---|---|
| series definition | `NormedSpace.logSeries` | `logOnePlusSeries` |
| the function | `NormedSpace.log x = ∑ cₙ (x-1)ⁿ` | `logOnePlus x = ∑ cₙ xⁿ` |
| junk value | `0` | `0` |
| algebraic | `log_one`, `log_op`, `star_log`, `log_mem`, `Commute.log*` | `logOnePlus_zero`; M3/M5 still `pending` |
| convergence, radius | **deferred to later files** | `logOnePlusSeries_radius_eq_one` ✔ |
| summability | deferred | M1 ✔ |
| `HasFPowerSeriesOnBall`, `AnalyticAt`, `ContinuousOn` | deferred (named on the TODO list) | M2 ✔ |
| `exp ∘ log` relation | deferred (on the TODO list) | declared in the module docstring, not yet proved |

Overlap with the mirror plan in `artifacts/abstractions/LogOnePlus.md`: upstream `log_mem` is my
**M3**, upstream `Commute.log_right/log_left/log` is my **M5** verbatim, and upstream
`log_one`/`logSeries_apply_zero` covers what `logOnePlus_zero`/`logOnePlusSeries_apply_zero` do
today. Upstream's TODO list names "`HasFPowerSeriesOnBall log (logSeries 𝕂 𝔸) 1 (logSeries 𝕂 𝔸).radius`
and its consequences, mirroring `NormedSpace.analyticAt_exp_of_mem_ball`" — i.e. **M2** — and
"`exp (log x) = x` and `log (exp x) = x` whenever both series converge" — i.e. the file's declared
but unproved `exp_logOnePlus`.

Consequence: writing M3/M5 for `logOnePlus` now means writing them a second time for `log` on the
next Mathlib bump, and the analytic layer is exactly the complement upstream is asking for.

## 3. Two substantive reasons to align (not cosmetic)

**(a) Centring.** `log x = ∑ cₙ (x-1)ⁿ` is the standard logarithm: it agrees with `Real.log` /
`Complex.log`, and the BCH target is `log (exp X * exp Y)`. The current object forces
`logOnePlus (exp X * exp Y - 1)` in every statement, and its natural identity reads
`exp (logOnePlus x) = 1 + x` instead of `exp (log x) = x`.

This is not free of mathematical consequence — it is visible in the hypotheses. Upstream's
`log_mem` needs `[SubringClass S 𝔸]`, whereas `exp_mem` (and my planned `logOnePlus_mem`, M3) needs
only `[SubsemiringClass S 𝔸]`: subtracting `1` (upstream's proof is
`pow_mem (sub_mem h (one_mem s)) _`) is what forces closure under negation. So the centring choice
changes theorem statements, not just notation.

**(b) Abstraction level of the definition.** Upstream defines

```lean
def logSeries (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
    [IsTopologicalRing 𝔸] : FormalMultilinearSeries 𝕂 𝔸 𝔸

noncomputable irreducible_def log (x : 𝔸) : 𝔸 := …
```

i.e. **no norm in the definition**, matching `NormedSpace.exp`'s deliberate design ("we do not
require this in the definition in order to make `NormedSpace.exp` independent of a particular choice
of norm"). The current `logOnePlusSeries` / `logOnePlus` require `[SeminormedRing 𝔸]` /
`[NormedRing 𝔸]`, baking a norm into the definition.

This is the open question recorded as §5.2 of `artifacts/abstractions/LogOnePlus.md` ("the
`NormedRing` binder on `logOnePlus`"), where the tentative conclusion was that the norm is intrinsic
because the series only converges on a ball. Upstream's file settles it: the norm is intrinsic to
the **convergence** results only; the definition and the whole algebraic layer need just
`IsTopologicalRing`. The narrowing is therefore a real interface defect, not a necessary one.

## 4. Plan

Do it as a retargeting of the interface, reusing the existing proofs. Keep every new name in
`FQFP.*` — **do not** use the `NormedSpace` namespace: as soon as the pin moves past #43670,
`NormedSpace.log`/`logSeries` would be a hard "already declared" clash, whereas `FQFP.log` merely
becomes redundant.

1. **Rename** `FQFP/BCH/LogOnePlus.lean` → `FQFP/BCH/Logarithm.lean`, and update `FQFP.lean` and
   `FQFP/BCH/ScratchProbe.lean` (the only call sites).
2. **Series.** `logSeries 𝕂 𝔸` at upstream's binders, but keep the current file's definition style:
   `ofScalars 𝔸 fun n => ((-1 : 𝕂) ^ (n + 1) / n)`. This is *better* than both `expSeries` and
   upstream's `logSeries`, which are defined by hand via `ContinuousMultilinearMap.mkPiAlgebraFin`
   and only afterwards proved to be `ofScalars`; defining as `ofScalars` is what lets
   `logOnePlusSeries_radius_eq_one` go straight through `ofScalars_radius_eq_of_tendsto`. Do not
   regress to `mkPiAlgebraFin` to "match" upstream.
   Adopt upstream's *proof technique* for the scalar-tower lemma (§5 below).
3. **Function.** `log x = ∑ cₙ (x-1)ⁿ` with junk `0`, at upstream's binders; then
   `log_eq_logSeries_sum`, `log_eq_tsum`, `log_one`, `log_op`, `star_log`, `log_mem`
   (`SubringClass`), `Commute.log_right/log_left/log` — the algebraic layer, own proofs, docstrings
   citing PR #43670.
4. **Analytic layer, retargeted to centre `1`.** Same proofs, different centre:
   - `logSeries_radius_eq_one` (unchanged statement);
   - M1 summability family, unchanged except the series name;
   - `logSeries_hasSum_log_of_mem_ball` and `_of_mem_ball'`;
   - `mem_eball_logSeries_radius : ‖x - 1‖ < 1 → x ∈ Metric.eball 1 (logSeries ℚ 𝔸).radius`;
   - `log_hasFPowerSeriesOnBall : HasFPowerSeriesOnBall log (logSeries ℚ 𝔸) 1 1`. Note this is
     *easier* than the current version: the `hasSum` obligation is
     `log (1 + y) = (logSeries ℚ 𝔸).sum y`, and the left-hand side unfolds to
     `(logSeries ℚ 𝔸).sum ((1 + y) - 1)`, so `one_add_sub` closes it definitionally.
   - `log_hasFPowerSeriesAt_one`, `continuousOn_log`, `analyticAt_log_of_mem_ball`;
   - `hasStrictFDerivAt_log_one` / `hasFDerivAt_log_one` — derivative the identity **at `1`**;
   - the composition material, now with the natural centre condition `log 1 = 0` (= `log_one`) for
     `HasFPowerSeriesAt.comp` against `exp`.
5. **Keep a thin `logOnePlus` shim** if the BCH layer wants the near-`0` form:
   `logOnePlus x := log (1 + x)`, with `logOnePlusSeries := logSeries`, `logOnePlus_zero` and
   `mem_eball ...` as one-liners. This is a *definition*, not duplicated content, so it does not
   violate the one-home rule; drop it if unused.
   *Not adopted:* the shim was tried and then deleted — see §7. Statements near `0` are written
   as `log (1 + x)` directly.
6. **On the next Mathlib bump:** delete the whole vendored algebraic layer and the series
   definition, keep the analytic layer, and rename `FQFP.log` → `NormedSpace.log` — mechanical, not
   a rewrite. That is the main payoff of aligning the names now.

## 5. Things to take from upstream regardless of the decision

* **A cleaner scalar-tower proof.** Upstream's two private lemmas
  `neg_one_pow_div_natCast_eq_inv_intCast` and `neg_one_pow_div_natCast_smul_eq` reduce
  `((-1)^k/n : R) • x = ((-1)^k/n : S) • x` via `inv_intCast_smul_eq`, so
  `logSeries_eq_logSeries_rat` is `ext c; simp [logSeries, neg_one_pow_div_natCast_smul_eq 𝕂 ℚ]` —
  no unfolding of `mkPiAlgebraFin`, hence no `_root_.smul_apply` and no `simp only` workaround.
  It is also **field-general** (`𝕂` vs `𝕂'`), where `logOnePlusCoeff_eq_algebraMap` targets `ℚ`.
  This is strictly better than the version landed here on 2026-08-10
  (`logOnePlusSeries_eq_logOnePlusSeries_rat`, see `LogOnePlus.md` §7.1); worth adopting even under
  the "do nothing" option. (The `_root_.smul_apply` deprecation note in
  `artifacts/simp_debugging.md` remains relevant for other lemmas, but not for this one.)
* **`logSeries_apply_zero` is a different statement from `logOnePlusSeries_apply_zero`.** Upstream
  states "every term vanishes at `x = 0`" (`logSeries 𝕂 𝔸 n (fun _ ↦ 0) = 0`, the literal mirror of
  `expSeries_apply_zero`), which is what gives `log_one` through `tsum_zero`. The current file
  states "the constant term vanishes for every `x`" (`logOnePlusSeries 𝕜 𝔸 0 fun _ => x = 0`), which
  is what gives `logOnePlus_zero`. The two are different and both are useful; keep both after the
  migration rather than choosing.
* **Upstream's TODO list is a map of the remaining work**, and it commits to the ultrametric
  (`p`-adic) case: for a complete ultrametric normed field of characteristic zero the series
  converges on all of `‖x - 1‖ < 1`, with `‖n‖ = ‖p‖ ^ padicValNat p n`; plus Iwasawa's formula and
  `log (x * y) = log x + log y` on that disc. This is the same obstruction recorded in §5.1 of
  `LogOnePlus.md`: the radius-`1` result here is proved over `ℚ` only, and for a general
  `NontriviallyNormedField` the ratio test needs `‖(n : 𝕜)‖ = n`, which fails `p`-adically. So the
  ℚ restriction is correct, and any *upstreamable* version of this analytic layer must state an
  archimedean hypothesis explicitly. Worth deciding now whether the analytic layer is intended as an
  upstream contribution (in which case state it for a general field with that hypothesis) or as
  internal project infrastructure (in which case `ℚ` is fine).

## 6. Provenance

Upstream #43670 is Apache-2.0, © Kevin Buzzard; this project's files are Apache-2.0 too
(`FQFP/BCH/LogOnePlus.lean` header: "Copyright (c) 2026 Foresight Quantum"). Two acceptable routes:

* **Adopt the interface, write our own proofs**, and cite `mathlib4#43670` in the docstring of each
  aligned declaration. The analytic half and the `ofScalars` definition style are independent work
  anyway; the algebraic half is a handful of lines each. Cleanest for a paper artifact: no verbatim
  upstream code to account for.
* **Vendor** upstream's file verbatim with its copyright header plus a provenance note. Faster, but
  puts a third-party file in the project's artifact and must be explained in the paper.

Recommendation: the first.

## 7. Landed (option A + re-derive)

`FQFP/BCH/LogOnePlus.lean` was renamed to `FQFP/BCH/Logarithm.lean` (518 lines) and retargeted to
`log` centred at `1` with upstream's `IsTopologicalRing` binders. `FQFP.lean` and
`FQFP/BCH/ScratchProbe.lean` were updated; the old file was deleted. Verified with
`lake build FQFP` ✔, `lake exe runLinter` ✔, `lake exe lint-style` ✔.

**What is in the file now** (all names `FQFP.*`, except the `Commute` lemmas — see below):

| group | declarations |
|---|---|
| series | `logSeries`, `logSeries_eq_ofScalars`, `_apply_eq`, `_apply_eq'`, `_apply_zero`, `_apply_one`, `_apply_two`, `_sum_eq`, `_sum_eq_rat`, `_eq_logSeries_rat`, `_eq_logSeries` |
| function | `log`, `log_of_isEmpty_algebra_rat`, `log_eq_logSeries_sum`, `log_eq_tsum`, `log_one`, `log_op`, `star_log`, `log_mem` |
| `Commute` | `_root_.Commute.log_right`, `_root_.Commute.log_left`, `_root_.Commute.log` |
| radius | `norm_logSeries_coeff`, `tendsto_norm_logSeries_coeff_ratio`, `logSeries_radius_eq_one` |
| summability | `norm_logSeries_summable_of_mem_ball`, `…'`, `logSeries_summable_of_mem_ball`, `…'` |
| ball | `logSeries_hasSum_log_one_add_of_mem_ball`, `…'`, `mem_eball_logSeries_radius`, `log_hasFPowerSeriesOnBall`, `log_hasFPowerSeriesAt_one`, `continuousOn_log`, `analyticAt_log_of_mem_ball` |
| derivative | `continuousMultilinearCurryFin1_logSeries_apply_one`, `logSeries_apply_one_const`, `hasStrictFDerivAt_log_one`, `hasFDerivAt_log_one` |

**Naming rule used.** The *analytic* declarations are `FQFP.*`. The `Commute` lemmas are
`_root_.Commute.log_right/left/log` — deliberately upstream's exact names and namespace, because
that block is straight algebraic-layer content which Mathlib will provide, so on the next pin bump
it is a pure deletion rather than a rename. (Consequence, accepted: the bump will then produce a
hard "already declared" error there instead of a redundant lemma. `FQFP.log`/`FQFP.logSeries`
themselves merely become redundant.) One further post-bump hazard: this file does
`open NormedSpace`, so once `NormedSpace.log` exists, bare `log` inside the file becomes ambiguous
and will need qualifying or the `open` dropping.

**Adopted from upstream, and it is a real improvement:**

* The private `neg_one_pow_div_natCast_eq_inv_intCast` /
  `neg_one_pow_div_natCast_smul_eq` pair (via `inv_intCast_smul_eq`) replaced the earlier
  `logOnePlusCoeff_eq_algebraMap` + `algebraMap_smul` route. Consequences: `logSeries_sum_eq_rat`
  now needs only `[Algebra ℚ 𝔸]` (matching `expSeries_sum_eq_rat`, which is what makes
  `log_eq_logSeries_sum` mirror `exp_eq_expSeries_sum` exactly), the scalar-tower lemma is
  field-general rather than `ℚ`-targeted, and the `simp only [… _root_.smul_apply …]` workaround
  recorded in `simp_debugging.md` is gone — `simp [logSeries, ofScalars,
  neg_one_pow_div_natCast_smul_eq 𝕂 ℚ]` closes it with no recursion loop.
* `logSeries_eq_logSeries` (the Exp:684 mirror that `LogOnePlus.md` §4 listed as still open) is now
  two lines instead of "not a two-line mirror", because the scalar-independence is field-general.
* `log_mem` with `[SubringClass S 𝔸]`, as predicted in §3(a) — the `SubsemiringClass` of `exp_mem`
  no longer suffices once the centre is `1`.
* `logSeries_apply_zero` in upstream's form ("every term vanishes at `x = 0`") instead of the old
  "constant term vanishes for every `x`". The latter is dropped: `log_one` follows from the former
  through `tsum_zero`, so keeping both would be two homes for one fact.

**Deviations forced by this Mathlib, none mathematical:**

* `logSeries` is still defined as `ofScalars 𝔸 (fun n => …)` (per §4 step 2), so every
  `ofScalars`-API lemma applies directly and `logSeries_radius_eq_one` goes straight through
  `ofScalars_radius_eq_of_tendsto`. Upstream defines via `mkPiAlgebraFin` and then proves
  `logSeries_eq_ofScalars`; that is *not* adopted.
* `log_one` needed care. Upstream's one-liner is `simp [log, logSeries_sum_eq, ← logSeries_apply_eq,
  logSeries_apply_zero, tsum_zero]`; here the `Logarithm.lean` version is
  `rw [log]; split_ifs with h` plus an explicit `let inst : Algebra ℚ 𝔸 := h.some` and
  `change (logSeries ℚ 𝔸).sum (1 - 1) = 0`. Reason: the `letI` inside `log`'s own body does not
  make the instance available to typeclass search in the resulting subgoal, so
  `Algebra ℚ 𝔸` cannot be synthesized. Note the fix uses `let`, not `letI`: `Mathlib.Tactic.Linter.HaveILetI`
  flags `letI`/`haveI` whenever the main goal is a `Prop` (and its docstring records that Lean 4's
  `let`/`have` already register local instances), so `let` is both the lint-clean and the working
  form. The same linter rejects `show` for a goal change — use `change`.
* `log_eq_tsum` is stated at function level (`log = fun x => …`), as upstream has it, so the
  analytic lemma that needs the pointwise form goes through
  `congrFun (log_eq_tsum ℚ) (1 + x)`.
* `log_hasFPowerSeriesOnBall` is at centre `1` with radius `1`. Its `hasSum` obligation is
  `log (1 + y) = …`, and the analytic workhorse is therefore stated as
  `logSeries_hasSum_log_one_add_of_mem_ball` (about `log (1 + x)`), which makes the structure
  literal a plain `exact` with no recentring arithmetic. As predicted in §4 step 4, this is
  *easier* than the old centre-`0` version.
* **No origin-centred alias.** `logOnePlus` (and the `logOnePlus_zero` /
  `logOnePlus_hasFPowerSeriesOnBall` pair) was written first and then **deleted**: it is a pure
  renaming of `log (1 + x)`, so statements near `0` are phrased directly as `log (1 + x)`. Nothing
  is lost — `logSeries_hasSum_log_one_add_of_mem_ball` is already stated in that form, and where a
  recentred `HasFPowerSeriesOnBall` is wanted it is three fields of `log_hasFPowerSeriesOnBall`
  (see `ScratchProbe.lean`). Note for that transcription: the `r_le`/`r_pos` fields need the
  `(𝔸 := 𝔸)` annotation on `log_hasFPowerSeriesOnBall`, because its radius is the literal `1` and so
  does not pin `𝔸` for instance synthesis, and the `hasSum` obligation is
  `HasSum … (f (0 + y))`, so `simpa only [zero_add]` is needed against a lemma stated at `y`.
  `logOnePlusSeries` was likewise never kept: the series is literally `logSeries`, and a second name
  would be two homes for one definition.

**Pre-existing breakage found in `FQFP/BCH/ScratchProbe.lean`.** It did not compile before this
migration and nobody had noticed, because it is not in the import closure of `FQFP.lean`, so
`lake build FQFP` never built it. Three independent defects: the last theorem's statement said the
derivative of `s ↦ logOnePlus (s • x)` is `t • x` at `t`, while its own docstring said the constant
`x` — and `fderiv_zero` proves the value at `0` is `x`, so the statement was simply wrong;
`HasFDerivAt.comp_hasDerivAt hfd t hshift` used an old signature (now
`hfd.comp_hasDerivAt hshift`); and a `simpa` tried to bridge `DifferentiableAt logOnePlus 0` to the
*composite* `DifferentiableAt (fun s => logOnePlus (s • x)) 0`.

The file was rewritten around `log (1 + x)` and now **builds cleanly** (including
`lake build FQFP.BCH.ScratchProbe`, which the old version never did). Two judgement calls there,
both reversible:

* the broken statement was repaired to the form its docstring described, i.e. the derivative at the
  origin: `hasDerivAt_log_one_add_smul (x : 𝔸) : HasDerivAt (fun s : ℚ => log (1 + s • x)) x 0`.
  The old `(t : ℚ)` binder and `t • x` derivative cannot be right, since by `fderiv_zero` the
  derivative at `0` is `x`, not `0 • x`. (The true derivative at a general `t` is
  `(1 + t • x)⁻¹ * x`, which needs invertibility of `1 + t • x` and is a different theorem.)
* the two declarations lost their `private`, which is what the module-level
  `linter.privateModule` warning was about (`@[expose] public section` with only private contents).

The file's own header still says "Delete when done".

Still outstanding from the original mirror plan: **M4**, i.e. the `log`-centred analogue of
`map_exp_of_mem_ball` (`map_log_of_mem_ball : f (log x) = log (f x)` for a continuous ring hom `f`
and `x` in the ball), and the `Prod.fst`/`Pi.coe`/`Function.update` projections.

`exp_log` (`exp (log x) = x` for `‖x - 1‖ < 1`) is now scaffolded rather than merely declared: the
final section `/-! ### The exponential of the logarithm` of `Logarithm.lean` records the ODE plan
(the curve `t ↦ exp (-(log (1 + t • x))) * (1 + t • x)` is constant) and proves its centre case.
The plan's general step needs the derivative of `log` at an *arbitrary* point of the ball, which is
not available yet.

That section was originally pasted in from an older draft and has been corrected twice. First pass:
it referred to the deleted `logOnePlus`/`logOnePlusSeries`, carried a duplicate `ℝ`-valued `fderiv`
theorem whose proof was an unfinished `by have := …` stub, and had two theorems under one and the
same docstring. Second pass (author's request): the ℚ statement of `fderiv_log_one_add_smul_zero`
was replaced by the **ℝ** one, since the ODE parameter is real. (Superseded by §8: the general step
is now proved, and the centre chain — including that ℝ `fderiv` theorem — was deleted as unused.)

### The `ℝ` layer added for that

Getting the ℝ statement needed more than a scalar-field substitution, because the only radius result
in the file was `logSeries_radius_eq_one`, over `ℚ` (the field `log` is defined with). New:

| declaration | why |
|---|---|
| `norm_logSeries_coeff_real` | the `ℝ` coefficient norm `‖(-1)^(n+1)/n‖ = 1/n`; the only genuinely new computation |
| `tendsto_norm_logSeries_coeff_ratio_real` | the `ℝ` ratio test — obtained from the `ℚ` one by `simpa only [norm_logSeries_coeff, norm_logSeries_coeff_real]`, since both coefficient norms are the same function |
| `logSeries_radius_eq_one_real` | `(logSeries ℝ 𝔸).radius = 1`, mirroring the `ℚ` proof through `ofScalars_radius_eq_of_tendsto` |
| `mem_eball_logSeries_radius_real` | `‖x‖ < 1 → x ∈ eball 0 (logSeries ℝ 𝔸).radius` |
| `logSeries_hasSum_log_one_add_of_mem_ball_real` | the `HasSum` for the ℝ series; the sum is identified with `log (1 + x)` through `logSeries_sum_eq_rat` and `log_eq_logSeries_sum` |
| `hasFPowerSeriesOnBall_log_one_add_real` | `HasFPowerSeriesOnBall (fun y => log (1 + y)) (logSeries ℝ 𝔸) 0 1` |

then, in `section ExpLog`, all private: `hasFPowerSeriesAt_log_one_add_smul` (the composite's power
series, by `compContinuousLinearMap`), `fderiv_log_one_add_smul_zero` (the requested statement, now
over `ℝ`), `hasFDerivAt_log_one_add_smul`, and `hasDerivAt_log_one_add_smul` — the last being the
form the ODE argument actually consumes.

**Rejected alternative, recorded because it will come up again.** `HasFDerivAt` over `ℚ` does *not*
transfer to `ℝ` by `simpa`, even though the little-o condition is a statement about the norm only:
the bound is `1 : 𝔸 →L[𝕜] 𝔸`, whose underlying function is `1 • ·`, and `1 •[ℚ] h = 1 •[ℝ] h` is
`one_smul`, not `rfl`. The tool for this is
`hasFDerivAt_of_restrictScalars` (`Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean`):
`HasFDerivAt f g' x → f'.restrictScalars 𝕜 = g' → HasFDerivAt f f' x`, i.e. the reverse of
`HasFDerivAt.restrictScalars`. It works here — `hasFDerivAt_log_one_real : HasFDerivAt log (1 : 𝔸
→L[ℝ] 𝔸) 1` follows in one line — but it needs `IsScalarTower ℚ ℝ 𝔸`, and it cannot handle the
*composite* `t ↦ log (1 + t • x)` at all, because that changes the domain (`ℚ → 𝔸` vs `ℝ → 𝔸`) and
`restrictScalars` keeps `E` fixed. So the ℝ power series is the right foundation, and it is also what
the general-point derivative will be read off (the series of `log` at `1`, recentred by
`changeOrigin`, differentiated term by term until the geometric series appears). `hasFDerivAt_of_restrictScalars`
remains the cheaper tool for any *same-domain* ℚ→ℝ transfer.

### Two pieces of debt this leaves

1. **The radius trio is now duplicated** (`norm_logSeries_coeff` / `…_real` and friends). Two clean
   fixes, both cheap, recorded for when it matters: state the trio once over a general `𝕜` with an
   archimedean hypothesis (`∀ n : ℕ, ‖(n : 𝕜)‖ = (n : ℝ)`, which is what the ratio test actually
   uses and which fails `p`-adically — see §5.1 of `LogOnePlus.md`), or add a generic
   `FormalMultilinearSeries.radius_congr` for series with equal coefficient norms, which is possible
   because `radius` is defined as an `iSup` over the single quantity `‖p n‖ * r ^ n` and therefore
   depends on nothing else. The second would give `logSeries_radius_eq_one_real` in two lines from
   the `ℚ` statement.
2. **`ScratchProbe.lean` is now fully subsumed** (it has public `hasFPowerSeriesOnBall_log_one_add`,
   `differentiableAt_log_one_add_smul`, `fderiv_zero`, `hasDerivAt_log_one_add_smul` covering the
   same ground over `ℚ`), and `Logarithm.lean` no longer needs it. Its header already says "Delete
   when done"; it was left in place rather than deleted, since it is untracked and unrecoverable.
   *Resolved in §8: deleted, with the author's consent.*

## 8. The ODE port, and the final section/variable layout

The ODE route is no longer a plan: `exp_log_one_add` and `exp_log` are proved, ported from the
verified `D:\project\Lean-BCH\BCH\LogSeries.lean` (`exp_logOnePlus`, line 742) and restated in this
file's own vocabulary (`log (1 + x)`, `logSeries ℝ 𝔸`). `lake build FQFP`, `lake exe runLinter` and
`lake exe lint-style` all pass with no warnings.

Two things were dropped while landing it, both by the author's decision:

* the **centre chain** (`hasFPowerSeriesAt_log_one_add_smul` → `fderiv_log_one_add_smul_zero` →
  `hasFDerivAt_log_one_add_smul` → `hasDerivAt_log_one_add_smul`, four private lemmas) is dead once
  the general-point derivative exists: the main theorem consumes
  `hasDerivAt_log_one_add_smul_tsum`, which is stated at arbitrary `t` and specialises to the centre
  case. Keeping it would have been four private lemmas that no proof calls and no consumer can see.
* `FQFP/BCH/ScratchProbe.lean` (untracked) was deleted.

### Splitting by hypothesis instead of `omit`

The file previously carried a dozen `omit … in` prefixes, all of the same shape: a section variable
that one lemma in the section does not use. Per the project rule ("fix the boundary, not the
proof"), each such lemma was given a section whose variable block is exactly its hypothesis set, and
every `omit` disappeared — the file now contains no `omit`, no `include` and no `set_option`. The
final blocks are:

| section | variables |
|---|---|
| `Series`, `Log`, `Commute` | `[Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]` (`General` adds `[Field 𝕂] [Algebra 𝕂 𝔸]`) |
| `CoeffNorm` | none — the coefficient norms and ratio tests are about `ℚ`/`ℝ` only |
| `Radius` / `RadiusReal` | `[NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸]` / the same over `ℝ` |
| `Summable` (+ nested `CompleteAlgebra`) | `[NontriviallyNormedField 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]`, plus `[CompleteSpace 𝔸]` in the nested block |
| `BallHasSum`, `BallRadius`, `Ball` | `[NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]`; `CompleteSpace` for `BallHasSum`/`Ball`, `NormOneClass` for `BallRadius`/`Ball` |
| `BallRealHasSum`, `BallRealRadius`, `BallReal` | the `ℝ` counterparts, with `BallRealHasSum`/`BallReal` adding the `ℚ` algebra too |
| `Deriv` (+ nested `DerivAtOne`) | `[NormedAlgebra ℚ 𝔸]`, plus `[CompleteSpace 𝔸] [NormOneClass 𝔸]` for the differential at `1` |
| `ExpLogBound` | `[NormedRing 𝔸]` only |
| `ExpLogCurve` | `+ [NormedAlgebra ℝ 𝔸]` |
| `ExpLogTermBound` | `+ [NormOneClass 𝔸]` (the uniform bound goes through `norm_pow_le`) |
| `ExpLogDerivative` | `+ [CompleteSpace 𝔸]` (differentiating the `tsum`) |
| `ExpLogExp` | the `ℝ` and `ℚ` algebras and `CompleteSpace`, but *not* `NormOneClass` |
| `ExpLogMain` | all five |

Two facts made the `ExpLog` half of this possible, and are worth remembering: `norm_pow_le` needs
`[NormOneClass 𝔸]` (so the term-wise bound needs it while the term-wise *summands* do not), and the
chain rule for `exp` along a commuting increment needs the `ℚ`-scalar action to build `exp` but not
the `ℝ` one. The file-level prose now states this split explicitly, so a later reader can tell that
the section boundaries are semantic rather than accidental.
