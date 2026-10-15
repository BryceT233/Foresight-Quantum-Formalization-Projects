# Foresight Quantum Formalization Projects (FQFP)

**Assisted by Deepseek Harness**

This repository collects Lean 4 formalization projects developed at
**Foresight Quantum** using Mathlib. The projects live under `FQFP/`;
`FQFP.lean` is the umbrella import.

## Projects

- **`FQFP/BCH`** — Baker–Campbell–Hausdorff word expansions, commutator
  identities, and norm estimates for the quintic term and its Taylor remainder.
- **`FQFP/Carleman`** — Polynomial ODE Carleman linearization, finite
  truncations, matrix evolution, and conditional error bounds. `PDE/` develops
  multipoint fields, their infinite linear hierarchy, and the exact residual
  of a finite-level truncation. `TwoModeBurgers/` proves monomial and energy
  iterate results, polynomial closure obstructions, and the energy Krylov
  dichotomy. Import `FQFP.Carleman` for this project. General convergence of
  the finite truncations requires further analytic estimates.
- **`FQFP/CQM`** — Categorical quantum mechanics: dagger and monoidal dagger
  categories, dagger kernels and biproducts, states, effects and measurement,
  with concrete `QuditCat`, `HilbCat`, and `RelCat` models. The recent changes
  simplify the projection, isometry, unitary, and positivity APIs in
  `Category/DaggerCategory.lean`.
- **`FQFP/TrotterError`** — Trotter/Suzuki product-formula error bounds based on
  *A Theory of Trotter Error* (Childs–Su–Tran–Wiebe–Zhu). The main results are
  in `FQFP.TrotterError.MainTheorem`. See the
  [formalization site](https://brycet233.github.io/TrotterError/).

To use one project without importing the whole library, import its relevant
module directly. New projects can be added under `FQFP/` and imported from
`FQFP.lean`.

## Build & Lint

Always run these steps in order before committing:

```bash
lake exe cache get        # fetch Mathlib cached oleans (skip if already cached)
lake build FQFP           # build only this project, not all of Mathlib
lake exe runLinter        # Mathlib declaration linter
lake exe lint-style       # Mathlib style checker
```

Never run bare `lake build` — it rebuilds Mathlib from source (~30+ min).
After `lake update`, re-run `lake exe cache get`.

See `AGENTS.md` for the full development conventions (tactic selection,
heartbeat diagnostics, naming, lint cleanup).
