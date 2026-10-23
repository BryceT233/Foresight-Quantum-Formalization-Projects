/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.Terms
public import FQFP.BCH.Algebra.QuinticTaylor
public import FQFP.BCH.BCHElement
public import FQFP.BCH.BCHCommutator
public import FQFP.BCH.BCHSymmetric
public import FQFP.BCH.BCHTerms
public import FQFP.BCH.ChildsBasis
public import FQFP.BCH.DynkinReeQuintic
public import FQFP.BCH.DynkinReeSextic
public import FQFP.BCH.DynkinReeSeptic
public import FQFP.BCH.DynkinReeOctic
public import FQFP.BCH.NestedCommNorm
public import FQFP.BCH.QuinticRemainder
public import FQFP.BCH.QuinticTaylor2

/-!
# Baker–Campbell–Hausdorff polynomials and estimates

The algebraic layer provides homogeneous polynomials, their finite Taylor
expansions, and coefficient certificates through degree eight. The analytic
layer estimates the logarithm of a product of exponentials and its remainders.
General word and normed-algebra results live in this project's `Algebra` and `Analysis`
subdirectories.

This entry point includes the coefficient certificates in ordinary project builds.
-/
