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
public import FQFP.Carleman.PDE.Fields
public import FQFP.Carleman.PDE.SpatialDerivative
public import FQFP.Carleman.PDE.Hierarchy
public import FQFP.Carleman.PDE.Truncation
public import FQFP.Carleman.TwoModeBurgers.Closure
public import FQFP.Carleman.TwoModeBurgers.EnergyLeading
public import FQFP.Carleman.TwoModeBurgers.Encoding
public import FQFP.Carleman.TwoModeBurgers.EnergyPolynomial

/-!
# Polynomial ODE Carleman linearization

The PDE foundation defines continuous multipoint lifts and proves their time
product rule at fixed spatial points, including derivatives within a time interval.
It also supplies spatial substitutions, slot operators with explicit domains,
and coordinate derivatives taken before diagonal restriction.
Solutions of a quadratic field equation lift to its infinite linear hierarchy,
with explicit spatial domains and pointwise time derivatives.
Finite-level compression has an exact top-level residual and a pointwise
error equation against any given solution of the truncated system.

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

The two-mode Burgers model has a concrete polynomial Lie derivation, its
monomial action formula, exact leading coefficients for coordinate and energy
iterates, finite-dimensional coordinate obstructions, and an energy closure
dichotomy by equality of damping rates, including arbitrary nonconstant
polynomials of energy. The coordinate obstruction also
excludes polynomial encoders with polynomial decoders and affine latent
dynamics on a nonempty open set.

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
