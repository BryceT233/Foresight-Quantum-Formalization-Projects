# Foresight Quantum Formalization Projects (FQFP)

This repository collects Lean 4 formalization projects developed at
**Foresight Quantum** using Mathlib. The projects live under `FQFP/`;
`FQFP.lean` is the umbrella import.

## Library structure

- **`FQFP/Algebra`** — Ordered word products and certificates, list-product
  identities, polynomial evaluation, polynomial-module calculus, and iterated Lie brackets.
  `Algebra/Lie/BCH/` develops homogeneous Lie recursion, associative BCH
  coefficients, finite truncations, and compatibility between representations.
- **`FQFP/Basic/Rel`** — Set-theoretic relations, composition, inverses and graphs,
  independently of any category structure.
- **`FQFP/RingTheory/PowerSeries/Noncommutative`** — Formal power series over
  noncommutative coefficient algebras, scalar substitution, exponential and
  logarithm, and formal differentiation. These results require no analytic
  convergence assumptions.
- **`FQFP/RingTheory/MvPolynomial`** — Polynomial derivations and degree bounds,
  total-degree projections with monomial bases, compressed derivations, and
  augmentation-ideal stability. `RingTheory/Derivation/Ideal` treats stable
  ideals and quotient derivations over general commutative algebras.
- **`FQFP/LinearAlgebra`** — Derivations of symmetric algebras and matrix
  coordinates for algebraic dual endomorphisms.
- **`FQFP/Topology/Algebra/MvPolynomial`** — Polynomial identity on a nonempty
  open set.
- **`FQFP/Data/Nat/Choose`** — Additional multinomial coefficient lemmas.
- **`FQFP/Analysis`** — List-product calculus, interval-integral bounds, and
  time-ordered evolution in `ODE/`. `Normed/Algebra/` supplies shared word,
  commutator, exponential, and logarithm estimates. Its `BCH/` directory proves
  BCH remainder bounds; `ProductFormula/` develops Trotter–Suzuki formulas,
  order conditions, and error estimates based on *A Theory of Trotter Error*
  (Childs–Su–Tran–Wiebe–Zhu). The main error results are in
  `FQFP.Analysis.Normed.Algebra.ProductFormula.ErrorBounds`. See the
  [formalization site](https://brycet233.github.io/TrotterError/).
  `ODE/` also develops autonomous and forced linear evolution, matrix formulas,
  and coordinate nonuniqueness. `PDE/Carleman/` develops multipoint fields,
  their infinite linear hierarchy, and exact finite-level truncation residuals.
  Taylor vanishing orders, iterated product derivatives, polynomial coefficient
  cancellation and general power-order asymptotics have independent calculus
  and asymptotics modules.
- **`FQFP/Carleman`** — Polynomial ODE Carleman approximants, their matrix
  formulas and conditional error bounds, and the scalar quadratic example.
  `TwoModeBurgers/` proves monomial and energy
  iterate results, polynomial closure obstructions, and the energy Krylov
  dichotomy. General convergence of
  the finite truncations requires further analytic estimates.
- **`FQFP/CategoryTheory`** — Dagger categories and their projections, isometries,
  unitaries, positive morphisms, kernels and biproducts; semiadditive categories;
  monoidal dagger structures, braidings and duals; scalars, states, effects and
  measurement. Basic dagger, monoidal dagger and dagger kernels have separate
  modules. States and scalars require only a monoidal category.
  Ordinary bicone maps and semiadditive biproducts have their own modules.
  `Category/RelCat/` extends Mathlib's standard category of relations with its
  dagger, tensor, biproduct, kernel, duality and measurement structures.
- **`FQFP/CQM`** — Concrete `QuditCat` and `HilbCat` models, the teleportation
  protocol, and its qubit and Boolean-relation examples.

Import `FQFP` for the whole library, or import individual modules such as
`FQFP.Algebra.Lie.BCH.Coefficients`,
`FQFP.Analysis.Normed.Algebra.ProductFormula.ErrorBounds`, or
`FQFP.CategoryTheory.Dagger.Basic` for a smaller dependency set.
`FQFP.lean` is the only umbrella file; subject and compatibility umbrellas have
been removed. Declaration names, including the `FQFP.BCH` and `TrotterError`
namespaces, are unchanged. Paper provenance remains in module documentation.

New shared results belong under the mathematical subject they extend. Algebraic
foundations must not import this project's analysis or application modules.

Build the umbrella library with `lake build FQFP`. See [AGENTS.md](AGENTS.md)
for the full development and lint workflow.

Run `python scripts/check.py` for the unified build, declaration/style lint,
tool tests and all `FQFPTest/` Lean regressions. CI runs the same command.
The default style linter includes `FQFPTest/`. For before/after API verification,
including module-qualified private identities and global registrations, see
[API snapshot tools](scripts/API_SNAPSHOTS.md).
