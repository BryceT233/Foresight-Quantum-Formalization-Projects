# Mirroring `Mathlib/Analysis/Normed/Algebra/Exponential.lean` into `FQFP/BCH/LogOnePlus.lean`

> **Superseded 2026-08-11.** `FQFP/BCH/LogOnePlus.lean` no longer exists: it was renamed to
> `FQFP/BCH/Logarithm.lean` and retargeted to `log x = ∑ cₙ (x-1)ⁿ` (centre `1`, no norm in the
> definition), to align with `NormedSpace.log` from
> [mathlib4#43670](https://github.com/leanprover-community/mathlib4/pull/43670). The decision
> record and the outcome are in `artifacts/log-upstream-alignment.md`. What survives of this note:
> the exp→log mirror survey of §1–§3 (still a valid inventory of what is mirrorable and what is
> not), §4's inventory of non-mirrors, and the observation in §3 that the *algebraic* half is
> upstream's while the *analytic* half is this project's. Names in the text below refer to the old
> `logOnePlus*` spellings; the new spellings are `log*`/`logSeries*`. §8 of that same record
> supersedes the `omit`-based advice in §5 below: every hypothesis mismatch is now handled by
> section boundaries, and the file contains no `omit` at all.

Scope: `FQFP/BCH/LogOnePlus.lean` (309 lines) vs. `Mathlib.Analysis.Normed.Algebra.Exponential`
(695 lines). Question asked: which results of the exponential file can be mirrored to the
Banach-algebra logarithm, and which five should be mirrored next?

Status of this note: design/investigation only. No build command was run (per
`artifacts/abstraction-agent-prompt-v3.md`); the signatures below are checked against the Mathlib
API by reading the sources, not by elaboration.

---

## 1. The mathematics, in plain language

Both files build a function out of a *scalar-coefficient* formal power series, i.e. an
`ofScalars` series `∑ cₙ · (∏ xᵢ)`:

| | coefficient `cₙ` | series | radius | sum |
|---|---|---|---|---|
| exp | `(n!)⁻¹` | `expSeries 𝕂 𝔸` | `∞` (`expSeries_radius_eq_top`) | `exp x = ∑ₙ (n!)⁻¹ • xⁿ` |
| log | `(-1)^(n+1) / n` | `logOnePlusSeries 𝕜 𝔸` | `1` (`logOnePlusSeries_radius_eq_one`) | `logOnePlus x = ∑ₙ ((-1)^(n+1)/n) • xⁿ` |

`logOnePlus` is the germ of `log (1 + x)` at `0`: the constant coefficient of `log(1+t)` is `0`,
which is exactly why `1` is absent from the definition. Mathematically the two functions are
inverse to each other near `0` (`exp (log (1+x)) = 1 + x` for `‖x‖ < 1`), and this is the
declared-but-not-yet-proved main result of the file (module docstring line 40).

**The transfer principle.** A result of `Exponential.lean` mirrors to `LogOnePlus.lean` iff its
proof uses only

1. the `ofScalars`/diagonal-term interface (`ofScalars_apply_eq`, `ofScalars_radius_*`),
2. the definitional shape `∑' n, cₙ • xⁿ` and the *generic* Banach-algebra lemmas about `tsum`
   (`HasSum`, `Summable`, `tsum_congr`, `Commute.tsum_*`, `tsum_mem`), and
3. the *value of the radius* (`∞` resp. `1`),

but **not** the arithmetic identities satisfied by the specific coefficients. Two consequences:

- Everything that exp can do because its radius is `∞` (global `exp_add`, global continuity,
  global `map_exp`, global summability) has **no** log counterpart: the log file can only ever
  claim those statements on `Metric.eball 0 (logOnePlusSeries ℚ 𝔸).radius`, or equivalently on the
  open unit ball via `mem_eball_logOnePlusSeries_radius`.
- The hard core of the exp file (`exp_add_of_commute_of_mem_ball`, the Cauchy-product/antidiagonal
  computation with `Nat.cast_add_choose`) is **not** a mirror at all. The corresponding
  mathematical statement for log is the multiplicative-to-additive law
  `logOnePlus (x + y + x*y) = logOnePlus x + logOnePlus y`, whose proof needs a *different*
  coefficient identity. Mirroring the analytic shell of `Exponential.lean` does not give the group
  law; see §4.

## 2. Existing coverage (what the file already mirrors)

`logOnePlusSeries_eq_ofScalars`, `_apply_eq`, `_apply_eq'`, `_apply_zero`, `_apply_one`,
`_apply_two`, `_sum_eq`, `_sum_eq_rat`, `_eq_logOnePlusSeries_rat`, `logOnePlus_of_isEmpty_algebra_rat`,
`logOnePlus_eq_tsum`, `logOnePlus_eq_logOnePlusSeries_sum`,
`logOnePlus_zero`, `norm_logOnePlusSeries_coeff`,
`tendsto_norm_logOnePlusSeries_coeff_ratio`, `logOnePlusSeries_radius_eq_one`,
`norm_logOnePlusSeries_summable_of_mem_ball`, `_summable_of_mem_ball'`,
`logOnePlusSeries_summable_of_mem_ball`, `logOnePlusSeries_summable_of_mem_ball'`,
`logOnePlusSeries_hasSum_logOnePlus_of_mem_ball`, `_of_mem_ball'`,
`mem_eball_logOnePlusSeries_radius`, `logOnePlus_hasFPowerSeriesOnBall`,
`logOnePlus_hasFPowerSeriesAt_zero`, `continuousOn_logOnePlus`,
`analyticAt_logOnePlus_of_mem_ball`,
`continuousMultilinearCurryFin1_logOnePlusSeries_apply_one`,
`logOnePlusSeries_apply_one_const`, `hasStrictFDerivAt_logOnePlus_zero`,
`hasFDerivAt_logOnePlus_zero`.

M1 (§3) and M2 (§3) have landed; the two remaining gaps from the list below are M3/M5/M4.

Notable *gaps* (exp has the result, log does not, and the mirror is legitimate):

- ~~the whole summability layer (`expSeries_*_summable_of_mem_ball`, Exp:275–299)~~ — **landed (M1)**,
- ~~the `'`-form of the `HasSum` statement (`expSeries_hasSum_exp_of_mem_ball'`, Exp:307)~~ —
  **landed (M2)**,
- ~~`HasFPowerSeriesAt`, `AnalyticAt`, `ContinuousOn` (Exp:318–333)~~ — **landed (M2)**,
- the closure lemma `exp_mem` (Exp:212) — M3,
- the ring-homomorphism lemma `map_exp_of_mem_ball` (Exp:383) — M4,
- the `Commute.*` family (Exp:228–241) — M5,
- the projection lemmas `Prod.fst_exp` / `Pi.coe_exp` / `Function.update_exp` (Exp:594–622).

## 3. The five recommended mirrors

All five are literal mirrors: same hypothesis shape modulo the ball/radius substitution
`∞ ↦ 1`, same proof route, no new coefficient identity. Ordering is by value for the BCH
roadmap (`exp_logOnePlus` and then the product law), not by difficulty.

### M1. The summability layer on the ball

Source: `norm_expSeries_summable_of_mem_ball`, `norm_expSeries_summable_of_mem_ball'`,
`expSeries_summable_of_mem_ball`, `expSeries_summable_of_mem_ball'` (Exp:275–299).

```lean
theorem norm_logOnePlusSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logOnePlusSeries ℚ 𝔸).radius) :
    Summable fun n => ‖logOnePlusSeries ℚ 𝔸 n fun _ => x‖ :=
  (logOnePlusSeries ℚ 𝔸).summable_norm_apply hx

theorem norm_logOnePlusSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logOnePlusSeries ℚ 𝔸).radius) :
    Summable fun n => ‖((-1 : ℚ) ^ (n + 1) / n) • x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← logOnePlusSeries_apply_eq']
  exact norm_logOnePlusSeries_summable_of_mem_ball x hx

-- these two need [CompleteSpace 𝔸]
theorem logOnePlusSeries_summable_of_mem_ball (x : 𝔸) (hx : …) :
    Summable fun n => logOnePlusSeries ℚ 𝔸 n fun _ => x :=
  (norm_logOnePlusSeries_summable_of_mem_ball x hx).of_norm

theorem logOnePlusSeries_summable_of_mem_ball' (x : 𝔸) (hx : …) :
    Summable fun n => ((-1 : ℚ) ^ (n + 1) / n) • x ^ n :=
  (norm_logOnePlusSeries_summable_of_mem_ball' x hx).of_norm
```

Why first: the file jumps straight from `logOnePlusSeries_radius_eq_one` to
`logOnePlusSeries_hasSum_logOnePlus_of_mem_ball`. Every downstream step that multiplies two
series — i.e. every step towards `exp_logOnePlus` and the product law — consumes a `Summable`
hypothesis (`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`, `HasSum.map`,
`Summable.tsum_mul_*`), and there is currently nothing to feed it.

Cost: ~15 lines, four docstrings. Effort **S**. Risk: none; purely `FormalMultilinearSeries`
API (`summable_norm_apply`, ConvergenceRadius.lean:247) plus the existing `…_apply_eq'`.

### M2. `HasFPowerSeriesAt`, `AnalyticAt`, `ContinuousOn`, and the `sum` identification

Source: `expSeries_hasSum_exp_of_mem_ball'` (Exp:307), `hasFPowerSeriesAt_exp_zero_of_radius_pos`
(Exp:318), `continuousOn_exp` (Exp:323), `analyticAt_exp_of_mem_ball` (Exp:328), and
`exp_eq_expSeries_sum` (Exp:158).

```lean
/-- The `'`-form of the existing `HasSum` lemma. -/
theorem logOnePlusSeries_hasSum_logOnePlus_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logOnePlusSeries ℚ 𝔸).radius) :
    HasSum (fun n => ((-1 : ℚ) ^ (n + 1) / n) • x ^ n) (logOnePlus x) := by
  rw [← logOnePlusSeries_apply_eq']
  exact logOnePlusSeries_hasSum_logOnePlus_of_mem_ball x hx

theorem logOnePlus_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt logOnePlus (logOnePlusSeries ℚ 𝔸) 0 :=
  logOnePlus_hasFPowerSeriesOnBall.hasFPowerSeriesAt

/-- `logOnePlus` is the sum of its own series (visible form of the `dif`-definition). -/
theorem logOnePlus_eq_logOnePlusSeries_sum [Algebra ℚ 𝔸] :
    logOnePlus = (logOnePlusSeries ℚ 𝔸).sum := by
  ext x
  rw [logOnePlus_eq_tsum x, logOnePlusSeries_sum_eq x]

theorem continuousOn_logOnePlus :
    ContinuousOn (logOnePlus : 𝔸 → 𝔸) (Metric.eball 0 (logOnePlusSeries ℚ 𝔸).radius) :=
  (FormalMultilinearSeries.continuousOn (p := logOnePlusSeries ℚ 𝔸)).congr
    fun x _ => by rw [logOnePlusSeries_sum_eq x, ← logOnePlus_eq_tsum x]

theorem analyticAt_logOnePlus_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logOnePlusSeries ℚ 𝔸).radius) :
    AnalyticAt ℚ logOnePlus x :=
  logOnePlus_hasFPowerSeriesOnBall.analyticAt_of_mem
    (by rwa [logOnePlusSeries_radius_eq_one] at hx)
```

Two structural notes. (a) The exp version of the analyticity lemma needs a
`by_cases h : radius = 0` split (`analyticAt_exp_of_mem_ball`, Exp:328) because `exp`'s radius is
only known to be positive in that generality; the log version does not, since
`logOnePlusSeries_radius_eq_one` is unconditional and the ball is *fixed*, not a parameter. This is
one place where the mirror is **simpler** than the source. (b) The exp file has no analogue of
`continuousOn_exp` at fixed radius: `continuousOn_exp` is stated on
`Metric.eball 0 (expSeries 𝕂 𝔸).radius`, which is the whole space only because of
`expSeries_radius_eq_top`; for log the same statement is exactly the unit ball, so the mirror is
the *honest* form of the result and `exp_continuous` (Exp:507, global) has no log counterpart.

Cost: ~20 lines, five docstrings. Effort **S–M**. Risk: low. Uses
`FormalMultilinearSeries.continuousOn` (Analytic/Basic.lean:1090, needs `[CompleteSpace 𝔸]`),
`HasFPowerSeriesOnBall.analyticAt_of_mem` (Analytic/ChangeOrigin.lean:355). This is the block that
`exp_logOnePlus` will need on the exp-composition side.

### M3. `logOnePlus_mem` — closure under a closed sub-semiring

Source: `exp_mem` (Exp:212).

```lean
theorem logOnePlus_mem
    {R S : Type*} [Monoid R] [SMul ℚ R] [MulAction R 𝔸] [IsScalarTower ℚ R 𝔸]
    [SetLike S 𝔸] [SubsemiringClass S 𝔸] [SMulMemClass S R 𝔸] {s : S}
    (h_closed : IsClosed (s : Set 𝔸)) {x : 𝔸} (h : x ∈ s) :
    logOnePlus x ∈ s := by
  have := SMulMemClass.ofIsScalarTower S ℚ R 𝔸
  rw [logOnePlus_eq_tsum ℚ]
  exact tsum_mem h_closed fun n => SMulMemClass.smul_mem _ <| pow_mem h n
```

This is a **verbatim** mirror: the hypothesis block of `exp_mem` carries over unchanged, and so
does the proof (`tsum_mem` handles the non-summable case through the junk value, and the junk
value `0` of `logOnePlus` is in `s` by `AddSubmonoidClass.zero_mem`, which
`SubsemiringClass` supplies — `SubsemiringClass extends SubmonoidClass, AddSubmonoidClass`,
`Algebra/Ring/Subsemiring/Defs.lean:57`). No ball hypothesis is needed: the lemma is about the
`tsum`, not about convergence.

One honest interface difference: `exp_mem` sits in the `TopologicalAlgebra` section and requires
only `[Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]`, because `NormedSpace.exp` was
deliberately defined without a norm instance. `logOnePlus` is defined under `[NormedRing 𝔸]`, so
this mirror inherits `[NormedRing 𝔸]`. That is intrinsic rather than accidental: the log series
only converges on a ball, so *every* statement about it needs the norm, whereas `exp` converges
everywhere and can be norm-independent. (See §5 for the residual design question.)

Cost: ~10 lines, one docstring. Effort **S**. Value: every "stay inside the subalgebra / real
subalgebra / C*-subalgebra" argument in the BCH development gets its log half for free.

### M4. `map_logOnePlus_of_mem_ball` — continuous ring homomorphisms commute with log

Source: `map_exp_of_mem_ball` (Exp:383); corollary mirror of `algebraMap_exp_comm_of_mem_ball`
(Exp:393).

```lean
variable {𝔸 𝔹 : Type*} [NormedRing 𝔸] [NormedRing 𝔹] [NormedAlgebra ℚ 𝔸] [Algebra ℚ 𝔹]
  [CompleteSpace 𝔸]

theorem map_logOnePlus_of_mem_ball {F} [FunLike F 𝔸 𝔹] [RingHomClass F 𝔸 𝔹]
    (f : F) (hf : Continuous f) (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logOnePlusSeries ℚ 𝔸).radius) :
    f (logOnePlus x) = logOnePlus (f x) := by
  rw [logOnePlus_eq_tsum (𝔸 := 𝔸) x, logOnePlus_eq_tsum (𝔸 := 𝔹) (f x)]
  refine (((logOnePlusSeries_summable_of_mem_ball' x hx).hasSum.map f hf).tsum_eq).trans ?_
  refine tsum_congr fun n => ?_
  rw [map_ratCast_smul f ℚ ℚ, map_pow]
```

This one is worth stating precisely because it *looks* like it needs a stronger hypothesis than
the exp version and does not. Because `logOnePlus` is a `tsum` and `tsum` is a total function, the
right-hand side `logOnePlus (f x)` unfolds to `∑' n, cₙ • (f x)ⁿ` **unconditionally**; summability
is needed only on the left, where `HasSum.map` is applied — i.e. only `hx`. So the hypothesis list
is identical to `map_exp_of_mem_ball`'s, with the radius substitution. No norm bound on `f` is
required (contrast `exp_smul`/`exp_units_conj`, Exp:584–592, which are global only because
`exp`'s radius is `∞`; their log analogues *would* need `‖g • x‖ < 1` and therefore are not
literal mirrors).

Cost: ~15 lines, one docstring. Effort **S–M**. Risk: low–medium — `map_ratCast_smul`
(`Algebra/Module/Rat.lean:29`) needs `[AddMonoidHomClass F 𝔸 𝔹]` for the *unital* ring hom
`f`, which `RingHomClass` supplies; the exp sibling uses the same route via
`map_inv_natCast_smul`. Corollary worth adding in the same pass:
`algebraMap_logOnePlus_comm_of_mem_ball : algebraMap ℚ 𝔸 (logOnePlus x) = logOnePlus (algebraMap ℚ 𝔸 x)`
for `x : ℚ`, `‖x‖ < 1` (mirror of `algebraMap_exp_comm_of_mem_ball`).

### M5. The `Commute` family

Source: `Commute.exp_right`, `Commute.exp_left`, `Commute.exp` (Exp:228–241).

```lean
variable {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℚ 𝔸] [T2Space 𝔸]

theorem _root_.Commute.logOnePlus_right {x y : 𝔸} (h : Commute x y) :
    Commute x (logOnePlus y) := by
  rw [logOnePlus_eq_tsum ℚ]
  exact Commute.tsum_right x fun n => (h.pow_right n).smul_right _

theorem _root_.Commute.logOnePlus_left {x y : 𝔸} (h : Commute x y) :
    Commute (logOnePlus x) y :=
  h.symm.logOnePlus_right.symm

theorem _root_.Commute.logOnePlus {x y : 𝔸} (h : Commute x y) :
    Commute (logOnePlus x) (logOnePlus y) :=
  h.logOnePlus_left.logOnePlus_right
```

Another verbatim mirror, and again with **no** ball hypothesis: `Commute.tsum_right`
(`Topology/Algebra/InfiniteSum/Ring.lean:78`) is proved by `by_cases` on summability and is
correct with the junk value. `Commute.smul_right`
(`Algebra/Group/Action/Defs.lean:398`) applies because `Algebra ℚ 𝔸` gives
`SMulCommClass ℚ 𝔸 𝔸` and `IsScalarTower ℚ 𝔸 𝔸`. `[T2Space 𝔸]` is inherited from the source
lemma's `[T2Space α]` hypothesis, exactly as in the exp version.

Cost: ~10 lines, three docstrings. Effort **S**. Value: this is the "log is a limit of polynomials
in `y`" API; it is the lemma one reaches for when manipulating the product law inside a
noncommutative Banach algebra, and it is currently missing.

## 4. What is *not* a mirror (and why this matters)

Do not schedule these as "mirrors"; they are new mathematics with different content.

- `exp_add_of_commute_of_mem_ball` (Exp:338) and `exp_add_of_mem_ball` (Exp:437). The log-side
  statement is `logOnePlus (x + y + x*y) = logOnePlus x + logOnePlus y`. The exp proof is
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` followed by
  `Nat.cast_add_choose` — i.e. it is exactly Vandermonde, which is what makes `exp` a
  homomorphism. The log identity comes instead from `exp (L x + L y) = (1+x)(1+y)` plus
  injectivity of `exp` near `0`, or from a genuinely different coefficient identity. Budget it as
  its own project, and note that M1 is its prerequisite.
- `exp_neg_of_mem_ball`, `invertibleExpOfMemBall`, `isUnit_exp_of_mem_ball`, `invOf_exp_of_mem_ball`
  (Exp:354–380), `isUnit_exp`/`invOf_exp`/`Ring.inverse_exp` (Exp:529–537). `logOnePlus` is not a
  unit and has no inverse story; the log-side content is `1 + x` invertible, which is a statement
  about `1 + x`, not about `logOnePlus`.
- Everything that consumes `expSeries_radius_eq_top`: `norm_expSeries_summable`,
  `expSeries_summable`, `expSeries_hasSum_exp`, `exp_hasFPowerSeriesOnBall`,
  `exp_hasFPowerSeriesAt_zero`, `exp_analytic`, `exp_continuous`, `exp_add`, `exp_add_of_commute`,
  `exp_sum_of_commute`, `exp_sum`, `exp_nsmul`, `exp_zsmul`, `map_exp`, `exp_smul`,
  `exp_units_conj`, `exp_conj`, `Prod.fst_exp`, `Pi.coe_exp`, `Function.update_exp`. The global
  statements have no log counterpart, because the log series diverges at `x = 1`.
  - Exception worth doing later: `Prod.fst_exp`/`Pi.coe_exp`/`Function.update_exp` **do** have
    ball-restricted mirrors, because the projections are norm-nonincreasing
    (`‖x.fst‖ ≤ ‖x‖`, `‖x i‖ ≤ ‖x‖`), so `hx : ‖x‖ < 1` descends to the component:
    `(logOnePlus x).fst = logOnePlus x.fst` etc. These are cheap and directly useful if the BCH
    development works with `Fin Γ → 𝔸`. `exp_smul`/`exp_units_conj` do *not* descend this way
    (a general action is not isometric) — they need an explicit `‖g • x‖ < 1`, which is why they
    are not in the five.
- The division-ring rephrasings `expSeries_apply_eq_div` / `expSeries_sum_eq_div` /
  `exp_eq_tsum_div` (Exp:250–264) and `norm_expSeries_div_summable` / `expSeries_div_summable` /
  `expSeries_div_hasSum_exp` (Exp:630–640). The log coefficients do not have the factorial shape,
  so the `xⁿ / n!` rephrasing becomes `(-1)^(n+1) * (xⁿ / n)` under extra `CharZero`/invertibility
  bookkeeping. Genuinely mirrorable but low value; skip.

Two more items in the "cheap, do while you are there" bucket:

- `logOnePlusSeries_radius_pos : 0 < (logOnePlusSeries ℚ 𝔸).radius` (mirror of
  `expSeries_radius_pos`, Exp:462) — one line from `logOnePlusSeries_radius_eq_one`; removes a
  `by rw [logOnePlusSeries_radius_eq_one]; norm_num` from call sites such as
  `FQFP/BCH/ScratchProbe.lean:50`.
- The scalar-tower pair. `Exponential.lean` has *two* different theorems here and they are not the
  same statement:
  - `expSeries_eq_expSeries_rat [Algebra ℚ 𝔸] (n : ℕ) : ⇑(expSeries 𝕂 𝔸 n) = expSeries ℚ 𝔸 n`
    (Exp:152) — function-level, coefficientwise, from a general `𝕂` down to `ℚ`. **Landed**, see §7.
  - `expSeries_eq_expSeries (n : ℕ) (x : 𝔸) : (expSeries 𝕂 𝔸 n fun _ => x) = expSeries 𝕂' 𝔸 n fun _ => x`
    (Exp:684) — pointwise in `x`, between two *arbitrary* fields. Still open on the log side; it is
    the strictly more general statement (no `ℚ` in sight) and would let `logOnePlusSeries_apply_eq`
    be reused across scalar fields.
  (An earlier revision of this note conflated the two; Exp:684 is not the source of the landed
  lemma.)
- `logOnePlus_eq_ofScalarsSum` (mirror of `exp_eq_ofScalarsSum`, Exp:173), once M2's
  `logOnePlus_eq_logOnePlusSeries_sum` exists:
  `logOnePlus = ofScalarsSum (E := 𝔸) fun n => (-1 : ℚ) ^ (n + 1) / n`.

## 5. Residual design notes (phase 3/4 deltas)

1. **Field generality of the radius.** `expSeries_radius_eq_top` is stated for a general
   `NontriviallyNormedField 𝕂` with `[CharZero 𝕂] [ContinuousSMul ℚ 𝕂]` (Exp:446, 451);
   `logOnePlusSeries_radius_eq_one` is proved only for `ℚ`. The mirror would need
   `‖(n : 𝕜)‖ = n` (the log ratio test computes `((n:ℝ)+1)/(n:ℝ)`), which holds for `ℝ`/`ℂ`/`RCLike`
   but *not* for a general nontrivially normed field of characteristic zero — a `p`-adic field has
   `‖p‖ < 1`, so `‖(n+1)‖/‖n‖` does not tend to `1` and the radius is genuinely different. So the
   restriction to `ℚ` is correct, not an oversight; if a wider statement is wanted it should be
   stated for `𝕜` with an archimedean norm. This is worth a sentence in the file's docstring
   because the coefficient `norm_logOnePlusSeries_coeff` reads at first glance like a
   general-`𝕜` lemma.
2. **The `NormedRing` binder on `logOnePlus`.** `NormedSpace.exp` is defined under
   `[Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]` explicitly so that it is independent of
   the chosen norm; `logOnePlus` is defined under `[NormedRing 𝔸]`. Since the log series converges
   only on the ball, the norm is intrinsic to the mathematics here and the narrowing is the right
   call — the only visible cost is that M3's hypothesis block carries `[NormedRing 𝔸]` where
   `exp_mem` carries `[Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]`. No change recommended;
   recorded so that a future reader does not "fix" it.
3. **`logOnePlus_eq_tsum` is the single bridge.** Every mirror above routes through
   `logOnePlus_eq_tsum`, which contains the `Subsingleton.elim` on `Algebra ℚ 𝔸` that the exp file
   spreads over `exp_eq_expSeries_sum` / `exp_eq_tsum` / `exp_eq_tsum_rat`. Adding M2's
   `logOnePlus_eq_logOnePlusSeries_sum` (a `funext`, no `dif` reasoning) gives downstream call
   sites a friction-free form and is a prerequisite for `ofScalarsSum`-based statements. It is the
   one item in this report that is interface rather than content.

## 6. Scope and cost

| # | mirrors | new decls | effort | risk |
|---|---|---|---|---|
| M1 | Exp:275–299 | 4 | S | none |
| M2 | Exp:158, 307, 318, 323, 328 | 5 | S–M | low |
| M3 | Exp:212 | 1 | S | none |
| M4 | Exp:383 (+393 corollary) | 2 | S–M | low–med |
| M5 | Exp:228–241 | 3 | S | none |
|    | *while-you-are-there* (§4 tail) | 3 | S | none |

Total ≈ 15 public declarations, all in `FQFP/BCH/LogOnePlus.lean`, ~70–90 lines including
docstrings. Every declaration needs a `/-- … --/` docstring and a `Counterpart of …` cross
reference to its exponential sibling, to match the file's existing convention; lines must stay
within the style limit checked by `lake exe lint-style`, and `lake exe runLinter` must be clean
(no unused `[NormOneClass 𝔸]`/`[CompleteSpace 𝔸]` binders — note that M1's first two lemmas and
M5 do **not** use `[CompleteSpace 𝔸]`, so they must either be `omit`-ed out of the section
variables or placed outside the complete-space section, exactly as
`logOnePlusSeries_hasSum_logOnePlus_of_mem_ball` and `mem_eball_logOnePlusSeries_radius` already
are).

Suggested landing order: M1 → M2 → M3 → M5 → M4. M1/M2 unblock `exp_logOnePlus`; M3/M5 are
independent and cheap; M4 is the tool for transporting results between the abstract Banach algebra
and concrete models.

Prerequisite for the *next* thing after these: the product law (§4) still needs a coefficient
identity that has no counterpart in `Exponential.lean` at all — mirroring cannot supply it.

## 7. Landed

All of the below verified with `lake build FQFP` ✔, `lake exe runLinter` ✔, `lake exe lint-style` ✔
(clean, no warnings).

### 7.1 `logOnePlusSeries_eq_logOnePlusSeries_rat`

Mirror of `expSeries_eq_expSeries_rat` (Exp:152), immediately after `logOnePlusSeries_sum_eq_rat`.

```lean
theorem logOnePlusSeries_eq_logOnePlusSeries_rat [Algebra ℚ 𝕜] [Algebra ℚ 𝔸] (n : ℕ) :
    ⇑(logOnePlusSeries 𝕜 𝔸 n) = logOnePlusSeries ℚ 𝔸 n := by
  ext c
  simp only [logOnePlusSeries, ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, logOnePlusCoeff_eq_algebraMap (𝕜 := 𝕜) n,
    algebraMap_smul]
```

Two deviations from the literal mirror, both forced by API drift rather than mathematics:

- The exp proof is a one-liner `simp [expSeries, inv_natCast_smul_eq 𝕂 ℚ]`. Here `simp [...]` on
  `[logOnePlusSeries, ofScalars, logOnePlusCoeff_eq_algebraMap …, algebraMap_smul]` dies with
  `maximum recursion depth has been reached` — a rewrite loop, not a heartbeat problem, so the fix
  is a targeted `simp only` (AGENTS.md: no `maxHeartbeats` bumps, no `maxRecDepth` bumps). The
  residual after unfolding is `(c1 • mkPiAlgebraFin 𝕜 n 𝔸) c = (c2 • mkPiAlgebraFin ℚ n 𝔸) c`,
  which `smul_apply` + `mkPiAlgebraFin_apply` + `algebraMap_smul` closes. The log coefficients do
  not have the `n⁻¹` shape that `inv_natCast_smul_eq` targets, which is why
  `logOnePlusCoeff_eq_algebraMap` replaces it.
- `ContinuousMultilinearMap.smul_apply` is deprecated (since 2026-06-10) in favour of
  `_root_.smul_apply`, and bare `smul_apply` is **ambiguous** in this file because
  `FormalMultilinearSeries.smul_apply` is also in scope. Use `_root_.smul_apply`. This applies to
  M1/M2 as well: any mirror that goes through `FormalMultilinearSeries`'s `SMul` instances will hit
  the same ambiguity.

Cost came in at ~10 lines including docstring, as estimated (S).

### 7.2 M1 — the summability layer

Four declarations mirroring Exp:275–299, in a new `section Summable` between `end Radius` and the
`### The power series` block:

* `norm_logOnePlusSeries_summable_of_mem_ball` — `(logOnePlusSeries 𝕜 𝔸).summable_norm_apply hx`;
* `norm_logOnePlusSeries_summable_of_mem_ball'` — via `logOnePlusSeries_apply_eq'`;
* `logOnePlusSeries_summable_of_mem_ball` and `…'` — the `.of_norm` forms, under `[CompleteSpace 𝔸]`.

Stated for a general `𝕜` (`[NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]`), the
literal mirror of exp's general-`𝕂` block; the ball is `(logOnePlusSeries 𝕜 𝔸).radius`, so a `ℚ`
caller instantiates `𝕜 := ℚ` and the argument is inferred from the ball itself.

**Two fixes were needed, both about `variable` scope rather than about proof:**

1. *The file had a file-wide `variable`.* `variable {𝔸 𝕜} [Field 𝕜] [SeminormedRing 𝔸] [Algebra 𝕜 𝔸]`
   sat at the top level of `namespace FQFP`, not inside a section, so every later section inherited
   it. Adding `[NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]` then put *two*
   `Field 𝕜`, two `SeminormedRing 𝔸` and two `Algebra 𝕜 𝔸` instances in scope, and any statement
   mentioning `𝕜` failed to elaborate with `failed to synthesize HPow 𝕜 𝕜 ?m` /
   `HPow 𝔸 𝕜 ?m` — `n + 1` and `n` were elaborated at type `𝕜` instead of `ℕ`, the `HPow`
   metavariable never having been pinned. Fix: wrap that first block in `section Series … end Series`.
   This is the AGENTS.md "fix the boundary, not the proof" case; no proof was touched. Sections
   `Sum`, `Radius`, `Ball` and `Deriv` already re-declare their own variables, so nothing else moved.
2. *`n`'s type needs an anchor.* The exp diagonal statement
   `Summable fun n => ‖(n !⁻¹ : 𝕂) • x ^ n‖` pins `n : ℕ` through `n !`. The log coefficient
   `((-1)^(n+1)/n)` contains no such anchor, so `Summable fun n => …` leaves `n`'s type ambiguous.
   The binder must be written `Summable fun n : ℕ => …` — the same explicitness the file already uses
   in `logOnePlusSeries_apply_eq'`.

No hypothesis drift: the ball hypothesis has the same shape as the exp side modulo the radius
substitution.

### 7.3 M2 — `HasFPowerSeriesAt`, `ContinuousOn`, `AnalyticAt`, and the `sum` bridge

Five declarations:

* `logOnePlus_eq_logOnePlusSeries_sum` (in `section Sum`; mirror of `exp_eq_expSeries_sum`, Exp:158)
  — `ext x; rw [logOnePlus_eq_tsum x, logOnePlusSeries_sum_eq x]`; gives callers a `dif`-free form.
* `logOnePlusSeries_hasSum_logOnePlus_of_mem_ball'` (mirror of Exp:307) — `rw [← …_apply_eq']` then
  the existing `HasSum` lemma; carries `omit [NormOneClass 𝔸] in` like its unprimed sibling.
* `logOnePlus_hasFPowerSeriesAt_zero` (mirror of Exp:318) — one line from
  `logOnePlus_hasFPowerSeriesOnBall.hasFPowerSeriesAt`.
* `continuousOn_logOnePlus` (mirror of Exp:323) —
  `(FormalMultilinearSeries.continuousOn (p := …)).congr`, the pointwise identification
  `logOnePlus x = (logOnePlusSeries ℚ 𝔸).sum x` being supplied by `logOnePlus_eq_tsum` together with
  `logOnePlusSeries_sum_eq`.
* `analyticAt_logOnePlus_of_mem_ball` (mirror of Exp:328) — `…analyticAt_of_mem` after rewriting the
  ball with `logOnePlusSeries_radius_eq_one`.

Simpler than the source in one place: exp's analyticity lemma needs a `by_cases h : radius = 0` split
(Exp:330–333) because its radius is only known to be positive there; here
`logOnePlusSeries_radius_eq_one` is unconditional, so the rewrite is total.

One linter iteration: `continuousOn_logOnePlus` tripped `linter.unusedSectionVars` for
`[NormOneClass 𝔸]` — the section variable was auto-included but unused, since the lemma needs
neither `NormOneClass` nor the known value of the radius. Fixed with `omit [NormOneClass 𝔸] in`,
which is exactly what the linter's message prescribes.

**Lesson for M3/M5:** any lemma placed in `section Ball` inherits `[NormOneClass 𝔸]` and must
`omit` it unless it really uses it, i.e. unless it goes through `logOnePlusSeries_radius_eq_one`.

Remaining: M3 (`logOnePlus_mem`), M5 (`Commute.*`), M4 (`map_logOnePlus_of_mem_ball`).
