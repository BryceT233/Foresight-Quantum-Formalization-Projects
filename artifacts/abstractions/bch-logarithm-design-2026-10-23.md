# BCH logarithm: abstraction audit (2026-10-23)

The initial sections record a read-only design audit of the working-tree `FQFP/BCH/Logarithm.lean`,
after the first Mathlib deduplication and before this round of optimization. It follows
`artifacts/abstraction-agent-prompt-v3.md`, `artifacts/have_lessons.md`, and the two Markdown files
under `.claude/`. Proposed signatures below are sketches, not compilation evidence. No build was
run by the design reviewer. The implementation and validation results are recorded at the end.

## Mathematical content

The logarithm is Mathlib's function defined by the series
`log (1 + x) = Σₙ ((-1)^(n+1)/n) • xⁿ`. Its constant coefficient is zero. The same diagonal
terms make sense over any two scalar fields acting on the ring and agree, even without a
specified rational-algebra structure. This scalar independence is an algebraic fact and must
remain separate from analytic assumptions.

Convergence and analytic expansion at a point are naturally parametrized by the scalar field
and the actual convergence radius. Computing that radius as `1` is a second fact valid for the
ordinary rational and real norms. The coefficient norm identity `‖cₙ‖ = 1/n` does not hold over an
arbitrary normed field of characteristic zero (consider a p-adic field).

For partial sums, the mathematical object is a finite rational polynomial evaluated in a ring.
It does not need a norm or completeness. Bounds require a norm and rational norm compatibility;
identifying the limiting sum additionally requires completeness. The zero coefficient is why
the coarse geometric bound remains valid without the `NormOneClass` assumption.

The final identity `exp (log (1 + x)) = 1 + x` uses a real one-parameter curve in a complete
rational normed algebra. The existing `RealScalar` construction supplies the real structure.
No change to that mathematical hypothesis is proposed.

## Clean design

```text
Mathlib.logSeries K A and Mathlib.log
  ├─ field-independent diagonal coefficients (pure topological algebra)
  ├─ arbitrary-radius HasSum and power-series facts (normed K, CharZero K, complete A)
  │    ├─ rational unit-radius specialization
  │    └─ real unit-radius specialization
  ├─ rational finite polynomial / partial sums (Ring A, Algebra Q A)
  │    ├─ one coefficient-times-power bound (normed A)
  │    └─ geometric remainder and summability (complete A where needed)
  └─ real-curve derivative + commutative exponential chain rule
       └─ exp_log_one_add and exp_log
```

The Mathlib objects remain the unique definitions of the infinite series and logarithm. There
is no reason to create a new `logOnePlus`, coefficient structure, convergence class, or subtype
of small elements.

## Proposed changes, in priority order

### 1. Share the coefficient-times-power bound

Current code proves the same inequality separately in `norm_logSeries_tail_le` and
`summable_logCoeff_smul`, including a separate zero-index case in both. Extract the actual common
mathematical statement:

```lean
theorem norm_logCoeff_smul_pow_le
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] (x : A) (i : ℕ) :
    ‖logCoeff i • x ^ i‖ ≤ ‖x‖ ^ i
```

It needs neither completeness, `NormOneClass`, nor the small-norm hypothesis. Prove `i = 0`
using `logCoeff_zero`, and the positive case with `norm_smul`, `norm_logCoeff_le_one`, and
`norm_pow_le'`. The summability proof then applies `Summable.of_norm_bounded` to this inequality;
the tail proof applies it at `k + n` and rewrites `pow_add`. This removes duplicated reasoning
rather than shortening each copy independently.

Evidence: Mathlib `Analysis/Normed/Ring/Basic.lean:412` is precisely
`norm_pow_le' (a) (h : 0 < n) : ‖a ^ n‖ ≤ ‖a‖ ^ n`. Its unprimed companion at line 417 requires
`NormOneClass`; using that companion would accidentally strengthen the remainder theorem.

Scope: one new lemma and two proof bodies, all in the same file. Low cost and highest priority.

### 2. Give partial sums their natural algebraic interface and recurrence

Current definition:

```lean
noncomputable def logPartialSum (A : Type*) [NormedRing A] [NormedAlgebra ℚ A]
    (n : ℕ) (x : A) : A := ∑ i ∈ Finset.range n, logCoeff i • x ^ i
```

Proposed interface:

```lean
def logPartialSum (A : Type*) [Ring A] [Algebra ℚ A] (n : ℕ) (x : A) : A

theorem logPartialSum_succ
    {A : Type*} [Ring A] [Algebra ℚ A] (x : A) (n : ℕ) :
    logPartialSum A (n + 1) x = logPartialSum A n x + logCoeff n • x ^ n
```

The current finite-sum implementation already works at this level. `logCoeff` is a computable
rational expression, so its `noncomputable` annotation is also unnecessary. The zero through
fourth partial-sum identities belong under the same weak algebraic assumptions; they should use
the recurrence and the preceding partial-sum identity, replacing repeated full expansions of
`Finset.sum_range_succ`.

Keep the current argument order, name, and finite-sum representation for caller compatibility.
Consider adding the equality to the standard series partial sum:

```lean
theorem logPartialSum_eq_partialSum
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] (n : ℕ) (x : A) :
    logPartialSum A n x = (logSeries ℚ A).partialSum n x
```

This equality makes the standard analytic approximation API usable without replacing the
project's pure algebraic finite polynomial by a topologically constrained definition.

Evidence: `Analysis/Analytic/ConvergenceRadius.lean:86` defines
`FormalMultilinearSeries.partialSum p n x := ∑ k ∈ range n, p k (fun _ ↦ x)`. Mathlib
`Analysis/Analytic/Basic.lean:593` proves `HasFPowerSeriesOnBall.tendsto_partialSum`, and line 771
provides `HasFPowerSeriesAt.isBigO_sub_partialSum_pow`. The connection lemma is an equality of
existing mathematical objects, not a new conversion function or duplicate definition.

Scope: definition context, five explicit identities, one recurrence; optional connection lemma.
Low cost. Do not add new simp attributes without checking the actual normal form in a real proof.

### 3. Separate arbitrary-radius analytics from unit-radius calculations

Current rational statement:

```lean
theorem logSeries_hasSum_log_one_add_of_mem_ball
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]
    (x : A) (hx : x ∈ Metric.eball 0 (logSeries ℚ A).radius) :
    HasSum (fun n ↦ logSeries ℚ A n (fun _ ↦ x)) (log (1 + x))
```

Current real counterpart repeats it and carries both `[NormedAlgebra ℚ A]` and
`[NormedAlgebra ℝ A]`. The natural common statement is:

```lean
theorem logSeries_hasSum_log_one_add_of_mem_ball
    {K A : Type*} [NontriviallyNormedField K] [CharZero K]
    [NormedRing A] [NormedAlgebra K A] [CompleteSpace A]
    (x : A) (hx : x ∈ Metric.eball 0 (logSeries K A).radius) :
    HasSum (fun n ↦ logSeries K A n (fun _ ↦ x)) (log (1 + x))

theorem hasFPowerSeriesOnBall_log_of_radius_pos
    {K A : Type*} [NontriviallyNormedField K] [CharZero K]
    [NormedRing A] [NormedAlgebra K A] [CompleteSpace A]
    (h : 0 < (logSeries K A).radius) :
    HasFPowerSeriesOnBall log (logSeries K A) 1 (logSeries K A).radius
```

Mathlib `log_eq_logSeries_sum K` already handles the internally chosen rational structure, so
the generic statement needs no separate `[NormedAlgebra ℚ A]`. One can construct its `hasSum`
field directly from the generic `HasSum` theorem at `1 + y`. The rational unit-ball theorem is
then a radius rewrite; the current real theorem remains a specialization. Preserve old real
names and all previously available hypotheses, even if the generic result needs fewer.

The origin-centered real statement can be constructed directly from that same generic `HasSum`
theorem and the real radius computation. It does not need to re-extract `‖y‖ < 1` from membership
in a ball of radius `1` and then reconstruct membership in an equal ball. Rewrite the radius in
the membership proof instead.

Mathlib precedents checked (same file, nearest analogous implementation):

- `expSeries_hasSum_exp_of_mem_ball`, `Exponential.lean:302`;
- `expSeries_hasSum_exp_of_mem_ball'`, line 308;
- `hasFPowerSeriesOnBall_exp_of_radius_pos`, line 314;
- `hasFPowerSeriesAt_exp_zero_of_radius_pos`, line 319;
- `continuousOn_exp`, line 324;
- `analyticAt_exp_of_mem_ball`, line 329;
- `exp_hasFPowerSeriesOnBall`, line 493;
- `hasFPowerSeriesAt_exp_zero`, line 496.

Evidence also comes from Mathlib `Logarithm.lean`: `log_eq_logSeries_sum` accepts a general
characteristic-zero field; its TODO explicitly proposes the actual-radius power-series theorem.
`FormalMultilinearSeries.hasSum` supplies the convergence theorem for arbitrary normed fields.

Scope: existing rational/real HasSum and ball-series proofs, optional general lemma. Moderate
cost; avoid expanding this pass into a broad API rename.

### 4. Optional: unify radius proofs only with a correct norm-compatibility assumption

The rational and real radius proofs have identical skeletons. A natural shared helper can accept
the coefficient norm identity explicitly:

```lean
private theorem logSeries_radius_eq_one_of_norm_coeff
    {K A : Type*} [NontriviallyNormedField K]
    [NormedRing A] [NormedAlgebra K A] [NormOneClass A]
    (hcoeff : ∀ n : ℕ, ‖((-1 : K) ^ (n + 1) / n)‖ = (n : ℝ)⁻¹) :
    (logSeries K A).radius = 1
```

Alternatively, rational norm compatibility `[NormedAlgebra ℚ K]` yields a public generic radius
theorem through `norm_algebraMap'`, with rational and real versions as wrappers. The explicit
coefficient identity is simpler if no generic public scalar-field API is desired.

Do not replace it by a claim for arbitrary characteristic-zero normed fields. Do not force a
real scalar structure on the rational-radius theorem just to share a proof.

Evidence: `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto`,
`Analysis/Analytic/OfScalars.lean:233`; `norm_algebraMap'`,
`Analysis/Normed/Module/Basic.lean:300`. Both existing ratio limits rewrite to the same scalar-free
sequence `n⁻¹ / (n+1)⁻¹`; a common limit theorem for that sequence is sufficient if the radius
helper is not introduced.

Scope: two coefficient/radius sections. Medium cost, lower priority than the concrete duplicate
term bound and partial-sum recurrence.

## Existing choices to preserve

- `logSeries_eq_logSeries` is stronger than Mathlib's rational-comparison theorem: its two scalar
  fields may have no rational-algebra structure. Its private signed-integer coefficient proof
  must remain unless replaced by an equally general proof. Routing it through
  `logSeries_eq_logSeries_rat` would strengthen its assumptions.
- The coarse remainder theorem has no `NormOneClass` assumption. The zero coefficient and
  positive-exponent norm estimate are essential to this interface.
- The project partial sum is indexed by the first omitted degree; retain this convention and
  the existing formulas. No shifted reindexing API is needed.
- `logSeries_apply_one_const` currently duplicates the conclusion of the more general
  `logSeries_apply_one`. Keep its public compatibility name, but its proof can simply be the
  general lemma at `K := ℚ`; no curry/uncurry round trip is necessary.
- Do not expose termwise derivative scaffolding solely because it was extracted from a long
  proof. A helper deserves a public name only when its mathematical statement is useful alone.
- Do not create a separate `logTail` definition for a single norm-bound application; a term bound
  plus the existing infinite sum is enough.

## Documentation corrections

The initial deduplication already removed the incorrect boundary-divergence claim. Preserve
that correction: the real series at `x = 2` is the alternating harmonic series and converges.

There is another inaccurate implementation description in the exponential section: it says the
real derivative is read off `hasFPowerSeriesOnBall_log_one_add_real`, but the actual proof uses
`hasDerivAt_tsum_of_isPreconnected` and explicit termwise derivatives. Proposed replacement:

> Since the curve parameter is real, its series and termwise derivatives are expressed over
> `ℝ`. The scalar-independence theorem identifies this sum with Mathlib's logarithm.

The paragraph claiming the derivative is `(1 + t • x)⁻¹ * x` should also be phrased in terms of
the geometric-series multiplier, because the ambient type is only a normed ring and has no
inverse operation. Proposed text:

> Its derivative is the geometric-series multiplier `Σₙ (-(t • x))ⁿ * x`; multiplying it on the
> right by `1 + t • x` gives `x`.

This matches both the hypotheses and the current cancellation proof without suggesting a
division-ring assumption.

## Cost and validation boundary

Items 1 and 2 are small structural improvements; item 3 fixes the main duplicated analytic
interface; item 4 is optional. All fit inside `Logarithm.lean`. Existing public names can remain,
with more general implementations or small specialization wrappers. No file split or commit is
part of this plan. Verification must run `lake build FQFP`, the declaration linter, and style
linter in the repository-prescribed order after using the cache workflow.

## Implemented changes

The implementation stays in `FQFP/BCH/Logarithm.lean`; no other Lean file was changed in this
round. All baseline public declaration names remain. The file decreases from 843 to 801 lines
against `scratch/bch-logarithm-opt-baseline-2026-10-23.lean`, the snapshot taken at the start of
this request, including the user's intervening documentation edits.

### Convergence and power-series interface

The existing HasSum theorem and its explicit-coefficient form now accept any characteristic-zero
normed scalar field, retaining their names. Their shared boundary is:

```lean
variable {𝔸 𝕂 : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂]
  [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

theorem logSeries_hasSum_log_one_add_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    HasSum (fun n => logSeries 𝕂 𝔸 n fun _ => x) (log (1 + x))

theorem log_hasFPowerSeriesOnBall_of_radius_pos
    (h : 0 < (logSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall log (logSeries 𝕂 𝔸) 1 (logSeries 𝕂 𝔸).radius
```

The second theorem is new. It uses Mathlib's power series for the sum, followed by translation.
The rational unit-ball theorem and the real origin-centered theorem are specializations of this
interface. The real HasSum/power-series statements no longer require an unrelated explicit
`NormedAlgebra ℚ 𝔸` assumption. Their section boundaries were corrected instead of adding
`omit` directives or suppressing unused-argument warnings.

The rational and real radius calculations remain separate. A new coefficient-norm compatibility
interface would add machinery for two short specializations, and arbitrary characteristic zero
does not justify that norm identity. The rational coefficient-ratio proof instead reduces directly
to `tendsto_natCast_div_add_atTop` and `Tendsto.inv₀`. Norms are rewritten before successor casts:
combining those phases into one simp call destroys the coefficient-pattern match.

### Pure algebraic partial sums and the common norm estimate

`logCoeff` and `logPartialSum` are computable definitions. The latter and its explicit low-degree
formulas now require only `[Ring 𝔸] [Algebra ℚ 𝔸]`. Two new public lemmas supply the missing API:

```lean
-- [Ring 𝔸] [Algebra ℚ 𝔸]
theorem logPartialSum_succ (n : ℕ) (x : 𝔸) :
    logPartialSum 𝔸 (n + 1) x = logPartialSum 𝔸 n x + logCoeff n • x ^ n

-- [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
theorem norm_logCoeff_smul_pow_le (x : 𝔸) (i : ℕ) :
    ‖logCoeff i • x ^ i‖ ≤ ‖x‖ ^ i
```

The recurrence derives the degree-two, three, and four formulas successively. It deliberately
has no simp attribute, avoiding automatic recursive expansion of arbitrary partial sums.
The term bound handles the zero coefficient once and uses `norm_pow_le'` for positive degrees.
Both summability and the geometric tail now call this bound; neither gains `NormOneClass`.
The low-order remainder estimates use the general estimate and additive-group normalization,
without one-use `have` equations.

### ODE proof and documentation

The geometric-series cancellation identity is now a private mathematical lemma independent of
the rational scalar structure and `NormOneClass`:

```lean
-- [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
private lemma log_one_add_smul_deriv_mul (x : 𝔸) (t : ℝ) (ht : |t| * ‖x‖ < 1) :
    (∑' n : ℕ, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)) * (1 + t • x) = x
```

The main theorem uses `constant_of_has_deriv_right_zero` on `[0,1]`. This covers `x = 0` directly
and removes the reciprocal-radius interval and nonzero case split. The final exponential
cancellation uses `isUnit_exp` and `IsUnit.mul_left_cancel`. A larger local radius for termwise
differentiation is obtained through `exists_pos_mul_lt`, removing its separate norm-zero branch.
The positive-degree derivative bound also drops `NormOneClass` by using `norm_pow_le'`.

The arbitrary-two-field comparison theorem and its private coefficient helpers are unchanged.
The public `exp_log_one_add` and `exp_log` keep their original assumptions. Real scalar
construction remains internal. No heartbeat-limit changes, profiler settings, axioms, or `sorry`
were introduced.

The documentation now describes the geometric-series derivative and its cancellation identity,
rather than an inverse unavailable in a general normed ring. It no longer claims that the ODE
proof uses the real `HasFPowerSeriesOnBall` theorem. The remainder discussion correctly states a
term norm inequality, and the generic convergence theorem is described using its actual radius.

## Validation results

Mathlib oleans were already cached and dependencies were unchanged, so cache retrieval was
skipped as permitted by `AGENTS.md`. The environment has no Lean LSP diagnostics tools; each
implementation batch was checked with `lake env lean FQFP/BCH/Logarithm.lean` instead. The first
generic-interface batch exposed unused rational scalar section assumptions on two real results;
those assumptions were removed at their section boundaries, and subsequent checks were clean.

The final build and both linters were run in the prescribed order:

| Check | Result | Evidence |
| --- | --- | --- |
| `lake build FQFP` | Passed, 9133 jobs; no warnings | `scratch/logs/bch-logarithm-opt-build-2026-10-23.log` |
| `lake exe runLinter` | `Linting passed for FQFP` | `scratch/logs/bch-logarithm-opt-declaration-lint-2026-10-23.log` |
| `lake exe lint-style` | Exit code 0; no style errors or new warnings | `scratch/logs/bch-logarithm-opt-style-lint-2026-10-23.log` |
| `.claude/skills/improve/check_patterns.py` | No findings | `scratch/logs/bch-logarithm-opt-patterns-2026-10-23.log` |
| `git diff --check` | Passed for the modified source and this note | Reproducible from the working tree |

The style runner replays its existing warning about `scripts/lint-style.lean` importing a
module-system file; the same warning was present before this round. No warning was suppressed.
The pattern checker was run with the bundled Python runtime and UTF-8 output because the system
Python shim was unavailable and the default console encoding could not print Lean symbols.

The final independent mathematical/API review confirmed that public names were retained, the
cross-field theorem was unchanged, the noncommutative multiplication order was respected, and
the interval argument included the zero and endpoint cases. No files were split and no commit
was created. Other pre-existing workspace edits were left untouched.

## Final variable and section cleanup

The final pass consolidates the namespace's type parameters into `variable {𝔸 𝕂 : Type*}`.
Typeclass assumptions remain local to mathematical layers and are introduced only when needed.
Single-declaration assumptions use `variable ... in`. Shared convergence, partial-sum, and ODE
blocks reuse their common assumptions, while the nested termwise-derivative scope is retained
to prevent `NormOneClass` from reaching the exponential chain rule.

The public inverse theorem remains in a separate rational-algebra scope: the real scalar
structure is still constructed inside the proof, rather than becoming an extra public argument.
The finite polynomial formulas now sit together with the pure algebraic partial-sum definitions;
the real power-series specialization sits with the other real-scalar results. These are moves
within the existing file, with no mathematical or proof changes.

Against `scratch/bch-logarithm-variable-baseline-2026-10-23.lean`, this pass reduces the file from
801 to 735 lines and its named sections from 26 to 11. The source comparison script confirms
that all 65 declaration statements and proof bodies are unchanged, ignoring whitespace and the
surrounding scope commands. An independent Lean metaprogram inventories the elaborated typeclass
assumptions of all 51 public declarations; the sorted inventories before and after are identical.

The probe and source-comparison programs live in `scratch/`. The elaborated inventories are
`scratch/logs/bch-logarithm-variable-api-before-2026-10-23.log` and
`scratch/logs/bch-logarithm-variable-api-after-2026-10-23.log`.

Final pre-commit validation, in order (cached Mathlib oleans were reused):

| Check | Result | Evidence |
| --- | --- | --- |
| `lake build FQFP` | Passed, 9133 jobs; no warnings | `scratch/logs/bch-logarithm-variable-build-2026-10-23.log` |
| `lake exe runLinter` | `Linting passed for FQFP` | `scratch/logs/bch-logarithm-variable-declaration-lint-2026-10-23.log` |
| `lake exe lint-style` | Exit code 0; no new warnings | `scratch/logs/bch-logarithm-variable-style-lint-2026-10-23.log` |
| Pattern checker | No findings | `scratch/logs/bch-logarithm-variable-patterns-2026-10-23.log` |

The style command still replays the existing module-system warning from the checker script.
The commit scope is the two logarithm-related Lean files and the two audit/design notes produced
in this conversation; unrelated working-tree changes are excluded.
