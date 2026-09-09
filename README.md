# Foresight Quantum Formalization Project (FQP)

**Assisted by Deepseek Harness**

This repository is the umbrella for the Lean 4 formalization projects developed
at **Foresight Quantum**. Each company project lives in its own directory under
`FQP/`, and the top-level `FQP.lean` module imports everything.

## Projects

- **`FQP/CQM`** — Categorical Quantum Mechanics. Formalizes dagger categories,
  monoidal (and symmetric braided) categories, and category-theoretic
  constructions for quantum mechanics: `Category/DaggerCategory`,
  `Category/MonoidalCategory`, `QuditCat/Basic`, `HilbCat`, `RelCat`.
- **`FQP/TrotterError`** — Trotter/Suzuki product-formula error bounds
  (Childs–Su–Tran–Wiebe–Zhu). Entry point is `FQP/TrotterError/MainTheorem`.
  See the [formalization site](https://brycet233.github.io/TrotterError/).

New projects are added as further top-level directories under `FQP/` and
imported from `FQP.lean`.

## Build & Lint

Always run these steps in order before committing:

```bash
lake exe cache get        # fetch Mathlib cached oleans (skip if already cached)
lake build FQP            # build only this project, not all of Mathlib
lake exe runLinter        # Mathlib declaration linter
lake exe lint-style       # Mathlib style checker
```

Never run bare `lake build` — it rebuilds Mathlib from source (~30+ min).
After `lake update`, re-run `lake exe cache get`.

See `AGENTS.md` for the full development conventions (tactic selection,
heartbeat diagnostics, naming, lint cleanup).
