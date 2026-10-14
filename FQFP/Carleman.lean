/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.MatrixEvolution
public import FQFP.Carleman.Ideals
public import FQFP.Carleman.Counterexamples
public import FQFP.Carleman.SymmetricDerivation
public import FQFP.Carleman.ScalarQuadratic
public import FQFP.Carleman.ErrorBounds

/-!
# Polynomial ODE Carleman linearization

Import `FQFP.Carleman` to use the complete formalization within FQFP.
The original roadmap is not part of the library.

The construction proceeds from a polynomial vector field to its derivation,
the dual evolution of polynomial observables, the finite observable projection,
and the unique compressed dual trajectory. State recovery reads degree-one
observables. The exact lifted trajectory satisfies the compressed equation
with the discarded high-degree contribution as residual.

The finite trajectory has a matrix exponential expression in any finite basis.
Affine fields give exact positive-order approximants. Origin-preserving fields
also induce derivations on the quotients by augmentation-ideal powers.

The scalar quadratic example `x' = x²` has an explicit finite geometric-series
approximant, exact truncation error, and uniform convergence on `[-T,T]` when
`|x₀| * T < 1`.

For general polynomial fields, finite basis coordinates admit conditional
Grönwall and `ε t exp(Kt)` bounds from generator and residual norm estimates.
State recovery has an explicit coefficient factor in an arbitrary basis and
constant one when the basis contains the coordinate observables.

Infinite coordinate evolution alone need not be unique. General polynomial
convergence as the truncation order tends to infinity requires further
analytic estimates beyond the scalar quadratic case proved here.
-/
