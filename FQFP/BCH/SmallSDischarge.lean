/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.DynkinReeToolbox
public import FQFP.BCH.DynkinReeQuintic
public import FQFP.BCH.DynkinReeSextic
public import FQFP.BCH.DynkinReeSeptic

/-!
# The small-`s` discharge

Ported from `Lean-BCH/BCH/SmallSDischarge.lean`. That file has two halves, and this module —
together with the `DynkinRee*` modules it imports — is the port of both.

## The two halves

**The pure identities** (done) are the degree-`k` cancellation steps

    ½·W_k + ⅓·(y³)_k - ¼·(y⁴)_k + … ± (1/k)·z^k - bch⟨k⟩Term = 0,

where `z = a + b`, `T_k` is the degree-`k` part of `y = exp a * exp b - 1`, and `bch⟨k⟩Term` is the
degree-`k` term of `BCHTerms.lean`. Each is stated with rational coefficients only, so it is settled
by `ℚ`-free computation over integer coefficient tables. They live one degree to a file:

* `DynkinReeToolbox.lean` — the shared pieces `z = a + b` and `T₂ … T₇`, the table `bchTTable` and
  its bridges, and the degree-4 cancellation `quintic_pure_identity`;
* `DynkinReeQuintic.lean` — degree 5, `sextic_pure_identity`;
* `DynkinReeSextic.lean` — degree 6, `septic_pure_identity`;
* `DynkinReeSeptic.lean` — degree 7, `octic_pure_identity` (the `(1/7)·z⁷` cancellation).

The theorem names are the source's, and they are one ahead of the degree they settle
(`octic_pure_identity` proves the degree-7 cancellation); each file says so in its own docstring.

**The remainder chain** (not ported yet) is everything that turns those identities into norm bounds:
the `pow{n}_sub_zpow{n}_telescope` identities, the `y{m}_sub_z{m}_sub_…` decompositions and their
bounds, the `I1`/`I2` residual decompositions, the `R_…_eq_neg_deg…_residual` rewrites, the
`norm_bch_*_remainder_large_s_le` bounds, and the four `pieceB_{sextic,septic,octic,nonic}_decomp`
theorems the pure identities feed. That is ~7.6k lines of the source, and this module is where it
goes.

## Status

The source file is 8384 lines and 80 declarations. The pure identities of degrees 4–7 and their
supporting tables are ported; **degree 8 (`nonic_pure_identity`) and the whole remainder chain are
not**. Splitting the identities into per-degree files is what made degree 7 affordable: it replaced
~1550 lines of generated integer normal forms with an incremental collapse along the `++`-chain of
pieces (`WordAlgebra.collapseK_append`), which is also the shape degree 8 needs — a literal normal
form of the degree-8 size exceeds the default budget on its own. The remainder chain is expected to
split by topic the same way, into a telescoping module, a residual-decomposition module, and a
`pieceB`/`large_s` module.

## Provenance

See `artifacts/bch-port.md` §3.3 for the overall plan and
`artifacts/abstractions/smallsdischarge-split.md` for the split, its measurements, and the degree-8
feasibility readings.

**Assisted by Deepseek Harness**
-/
