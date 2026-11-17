# Foresight Quantum Formalization Projects (FQFP)

This repository collects results formalized in Lean 4 by a research group at
**Foresight Quantum**. The library builds on Mathlib and loosely follows its
directory structure, grouping results under `FQFP/` by mathematical subject.

## Project history

Bingyu Xia started this repository to formalize the opening chapters of
Chris Heunen and Jamie Vicary’s [*Categorical Quantum Mechanics: An Introduction*][cqm].

The group later used DeepSeek V4 Pro through the DeepSeek harness to formalize
the product-formula error bounds in [*A Theory of Trotter Error*][childs] by
Andrew M. Childs, Yuan Su, Minh C. Tran, Nathan Wiebe, and Shuchen Zhu.
Along the way, the group incorporated selected results from two of Jue Xu’s
Lean 4 repositories. [Lean-BCH][bch] formalizes the Baker–Campbell–Hausdorff
formula in complete normed algebras and gives explicit bounds on its remainder.
[Lean-Trotter][trotter] proves convergence rates and error bounds for the
Lie–Trotter product formula, Strang splitting, and the fourth-order Suzuki formula.

The group then took on the formalization of the main results in *Trotter Error
Bounds in Lean 4 with a Cancellation-Aware Analysis of the Fourth-Order Suzuki
Formula*. With help from GPT-Astra, the group is now incorporating results from
[Physlib’s `QuantumInfo` directory][quantuminfo].

[cqm]: https://www.cs.ox.ac.uk/files/7051/notes.pdf
[childs]: https://arxiv.org/abs/1912.08854
[bch]: https://github.com/Jue-Xu/Lean-BCH
[trotter]: https://github.com/Jue-Xu/Lean-Trotter
[quantuminfo]: https://github.com/leanprover-community/physlib/tree/master/QuantumInfo

## Library structure

- [CategoryTheory](FQFP/CategoryTheory) develops the categorical foundations of
  quantum mechanics, including dagger categories, monoidal structure, states,
  and measurements. The category of relations provides a concrete model.
- [CQM](FQFP/CQM) formalizes quantum teleportation and finite-dimensional
  quantum information. Its qudit modules cover states and measurements, quantum
  channels and their dilations, and bounds involving fidelity, trace distance,
  and entropy.
- [Algebra](FQFP/Algebra) develops the Baker–Campbell–Hausdorff expansion and
  uses identities between noncommutative words to verify commutator coefficients
  for the fourth-order Suzuki formula.
- [Analysis](FQFP/Analysis) proves BCH remainder bounds and Trotter–Suzuki
  error bounds, including estimates that account for cancellation in the
  fourth-order formula. See the [Trotter error formalization](https://brycet233.github.io/TrotterError/).
- [Carleman](FQFP/Carleman) studies finite truncations of the Carleman
  linearization of polynomial ODEs, with conditional error bounds, a scalar
  quadratic example, and results on polynomial closure for a two-mode Burgers system.

Import `FQFP` for the whole library, or import individual modules such as
`FQFP.Algebra.Lie.BCH.Coefficients`,
`FQFP.Analysis.Normed.Algebra.ProductFormula.ErrorBounds`, or
`FQFP.CategoryTheory.Dagger.Basic` for a smaller dependency set.
`FQFP.lean` is the only umbrella file; subject and compatibility umbrellas have
been removed. Declaration names, including the `FQFP.BCH` and `TrotterError`
namespaces, are unchanged. Paper provenance remains in module documentation.

New shared results belong under the mathematical subject they extend. Algebraic
foundations must not import this project's analysis or application modules.

Build the umbrella library with `lake build FQFP`.

Run `python scripts/check.py` for the unified build, declaration/style lint,
tool tests and all `FQFPTest/` Lean regressions. CI runs the same command.
The default style linter includes `FQFPTest/`. For before/after API verification,
including module-qualified private identities and global registrations, see
[API snapshot tools](scripts/API_SNAPSHOTS.md).
