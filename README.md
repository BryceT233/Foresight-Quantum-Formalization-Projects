# Foresight Quantum Formalization Projects (FQFP)

FQFP is a Lean 4 library developed by a research group at Foresight Quantum.
It builds on Mathlib. The modules under `FQFP/` are organized by mathematical
subject, following roughly the same layout as Mathlib.

## Project history

Bingyu Xia started this repository to formalize the opening chapters of
Chris Heunen and Jamie Vicary’s [*Categorical Quantum Mechanics: An Introduction*][cqm].

We later used DeepSeek V4 Pro through the DeepSeek harness to formalize
the product-formula error bounds in [*A Theory of Trotter Error*][childs] by
Andrew M. Childs, Yuan Su, Minh C. Tran, Nathan Wiebe, and Shuchen Zhu.
During that work, we incorporated selected results from two of Jue Xu’s Lean 4
repositories. [Lean-BCH][bch] formalizes the Baker-Campbell-Hausdorff formula
in complete normed algebras and gives explicit bounds on the remainder.
[Lean-Trotter][trotter] proves convergence rates and error bounds for the
Lie-Trotter product formula, Strang splitting, and the fourth-order Suzuki formula.

We then began formalizing the main results of *Trotter Error
Bounds in Lean 4 with a Cancellation-Aware Analysis of the Fourth-Order Suzuki
Formula*. We are now incorporating results from
[Physlib’s `QuantumInfo` directory][quantuminfo] with help from GPT-Astra.

[cqm]: https://www.cs.ox.ac.uk/files/7051/notes.pdf
[childs]: https://arxiv.org/abs/1912.08854
[bch]: https://github.com/Jue-Xu/Lean-BCH
[trotter]: https://github.com/Jue-Xu/Lean-Trotter
[quantuminfo]: https://github.com/leanprover-community/physlib/tree/master/QuantumInfo

## Library structure

- [CategoryTheory](FQFP/CategoryTheory) covers dagger categories, monoidal
  structure, states, and measurements as foundations for categorical quantum
  mechanics. The category of relations gives a concrete model.
- [CQM](FQFP/CQM) formalizes quantum teleportation and finite-dimensional
  quantum information. The qudit modules cover states, measurements, and
  quantum channels and their dilations. They also give bounds involving
  fidelity, trace distance, and entropy.
- [Algebra](FQFP/Algebra) develops the Baker-Campbell-Hausdorff (BCH)
  expansion and uses identities between noncommutative words to verify the
  commutator coefficients in the fourth-order Suzuki formula.
- [Analysis](FQFP/Analysis) proves bounds on the BCH remainder and the error
  in Trotter-Suzuki product formulas. These include estimates that account for
  cancellation in the fourth-order formula. See the [Trotter error formalization](https://brycet233.github.io/TrotterError/).
- [Carleman](FQFP/Carleman) studies finite truncations of the Carleman
  linearization of polynomial ODEs. It gives conditional error bounds, works
  through a scalar quadratic example, and studies polynomial closure for a
  two-mode Burgers system.

Import `FQFP` for the whole library. For fewer dependencies, import individual
modules such as `FQFP.Algebra.Lie.BCH.Coefficients`,
`FQFP.Analysis.Normed.Algebra.ProductFormula.ErrorBounds`, or
`FQFP.CategoryTheory.Dagger.Basic`.

`FQFP.lean` is the only umbrella file. We removed the subject and compatibility
umbrellas and kept the existing declaration names, including those in the
`FQFP.BCH` and `TrotterError` namespaces. Module documentation identifies the
source papers.

Place new shared results under the mathematical subject they extend. Keep the
algebraic foundations independent of this project's analysis and application
modules.

## Build and checks

Build the full library with `lake build FQFP`.

To run the same checks as CI, use `python scripts/check.py`. It builds the
library, runs the declaration and style linters, tests the tools, and runs all
Lean regression tests in `FQFPTest/`. The style linter checks `FQFPTest/` by
default.

Use the [API snapshot tools](scripts/API_SNAPSHOTS.md) to compare the API
before and after a change. The comparison covers module-qualified private
identities and global registrations.
