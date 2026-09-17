# Real scalars on a complete normed `ℚ`-algebra

**Status: done.** The construction is in `FQFP/BCH/RealScalar.lean` (120 lines), which builds with
no `sorry`, and passes `lake exe runLinter` and `lake exe lint-style`.

**Statement.** A complete normed ring `𝔸` with a `NormedAlgebra ℚ 𝔸` structure is a
`NormedAlgebra ℝ 𝔸`, and that structure is unique. No extra hypothesis is needed — in particular
`NormOneClass 𝔸` is not assumed; `‖(1 : 𝔸)‖ = 1` follows from the `ℚ`-algebra structure.

## Contents

| declaration | statement |
|---|---|
| `normedAlgebraReal` | the `NormedAlgebra ℝ 𝔸` structure (`abbrev`, `@[no_expose]`) |
| `realNormedAlgebraUnique` | `Unique (NormedAlgebra ℝ 𝔸)`, global instance |
| `NormedAlgebra.coe_rat_smul` | `(q : ℝ) • a = q • a`, `@[simp]` |

Plus one private helper, `uniformContinuous_algebraMap : UniformContinuous (algebraMap ℚ 𝔸)`,
proved by rewriting `algebraMap ℚ 𝔸` as the continuous linear map
`ContinuousLinearMap.smulRight (id ℚ ℚ) 1`.

## Proof outline

1. `algebraMap ℚ 𝔸` is uniformly continuous (the private helper above).
2. `IsDenseInducing.extendRingHom (i := Rat.castHom ℝ) …` extends it along the dense inclusion
   `ℚ → ℝ` to a ring homomorphism `ℝ →+* 𝔸`: `ℚ` is dense (`Rat.denseRange_cast`) and the
   inclusion is a uniform embedding (`Rat.isUniformEmbedding_coe_real`), so the uniformly
   continuous extension exists and is a ring hom.
3. `RingHom.toAlgebra'` turns that into an `Algebra ℝ 𝔸`; the centrality obligation is discharged
   by density — `Rat.denseRange_cast` induction, closedness by `isClosed_eq` (both sides
   continuous), the rational case by `Algebra.commutes'`.
4. `norm_smul_le` is the same density reduction: at rational `r` it is `norm_smul_le` for the
   existing `ℚ`-action, after `Rat.norm_cast_real` and `extend_eq`. This is where the absence of a
   `NormOneClass` hypothesis is cashed in — nothing beyond the `ℚ`-action is used.
5. `realNormedAlgebraUnique`: given any `NormedAlgebra ℝ 𝔸` structure `P`, compare the two
   algebra maps. `algebraMap ℝ 𝔸` is continuous (`fun_prop`), so both sides are continuous in `r`
   and agree at rationals (`IsScalarTower.rat.algebraMap_apply`, i.e. both are
   `algebraMap ℚ 𝔸` there); `Rat.denseRange_cast` + `isClosed_eq` closes it.

## API notes worth recording

* **`RingHom.toAlgebra` vs `RingHom.toAlgebra'`.** In this Mathlib (`v4.33.0`),
  `RingHom.toAlgebra` requires `[CommSemiring S]`, i.e. `CommSemiring 𝔸`, which a `NormedRing`
  does not provide (noncommutative rings are allowed). The applicable constructor is
  ```lean
  RingHom.toAlgebra' (i : R →+* S) (h : ∀ c x, i c * x = x * i c) : Algebra R S
  ```
  whose second argument is precisely the centrality supplied by step 3.
* **Avoiding `Module ℝ 𝔸`.** An earlier version built `SMul ℝ 𝔸`, then `Module ℝ 𝔸` via
  `LinearMap`, and assembled the algebra with `Algebra.ofModule'`. That route forces a `mul_smul`
  proof, i.e. `realAction a (r * s) = realAction (realAction a s) r`, which is awkward with the
  available lemmas. Going through `RingHom.toAlgebra'` removes the `Module` instance (and hence
  that obligation) entirely: the scalar action is defined as
  `r • x = algebraMap ℝ 𝔸 r * x`, with `algebraMap ℝ 𝔸 r` the extension of `algebraMap ℚ 𝔸`.
* **Naming.** The `Unique` instance must be named explicitly. Left anonymous, Lean generates
  `instUniqueNormedAlgebraRealOfCompleteSpace_fQFP`, whose underscore trips the `defsWithUnderscore`
  environment linter (reported as an **error** by `lake exe runLinter`). Hence
  `realNormedAlgebraUnique` — any explicit spelling is fine as long as it contains no underscore.

## Scope of the instances

`normedAlgebraReal` is registered only as a `local instance` (`attribute [local instance]`, line 114),
never globally: the surrounding `FQFP.TrotterError.*` files take `[NormedAlgebra ℝ 𝔸]` as an
explicit hypothesis, and a global instance would compete with it. The `Unique` instance *is*
global, which is what makes the two routes compatible — a caller holding any
`NormedAlgebra ℝ 𝔸]` instance can identify it with `normedAlgebraReal` by `Subsingleton.elim`.

**Caveat on `NormedAlgebra.coe_rat_smul`.** Because `normedAlgebraReal` is only a local instance,
the instance argument of this lemma is *fixed* to `normedAlgebraReal` at declaration time. A caller
whose `NormedAlgebra ℝ 𝔸` is a free variable (the `FQFP.TrotterError.*` pattern) will not match it
by unification, so the `@[simp]` attribute will not fire there; such a caller has to identify the
instances first (via the `Unique` instance). This is a deliberate consequence of the scope
decision above, not an oversight — but it is the thing to reconsider first if the lemma turns out
to be awkward to use from the Trotter files.

## History

An earlier revision of this file lived in a `RealScalar` namespace and exposed a much larger API
(`ratAction`, `ratCastCLM`, `realAction`, `realAction_rat`, `norm_realAction_le`,
`realAction_mul`, `realAction_one_central`, `realAction_mul_scalar`, `realActionRingHom`,
`realAlgebra`, `realNormedAlgebra`, with the last two carrying `@[instance_reducible]`). That
version has been deleted; the current file builds the same `ℚ → ℝ` extension directly on top of
`IsDenseInducing.extendRingHom`, so none of those intermediate declarations are needed. The two
API notes above are the parts of that revision worth keeping.
