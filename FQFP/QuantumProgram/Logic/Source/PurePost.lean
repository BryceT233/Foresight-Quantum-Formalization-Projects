/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/SharpPost.lean: uniqueness of the pure output in two total source derivations.

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Assertion.PurePost
public import FQFP.QuantumProgram.Logic.Source.Rules

/-!
# Uniqueness of pure postconditions in the source logic
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Two total source derivations with unguarded pure assertions agree on the output density. -/
theorem SourceDerivTot.pure_post_unique (σ : Store) {p : Command Store Cell H} {w u v : UnitState H}
    (hu : SourceDerivTot (.ofEffect (.pure w) fun _ => True) p (.ofEffect (.pure u) fun _ => True))
    (hv : SourceDerivTot (.ofEffect (.pure w) fun _ => True) p
      (.ofEffect (.pure v) fun _ => True)) : Density.pure u = Density.pure v := by
  apply validTot_pure_post_unique σ (w := w) (p := p)
  · simpa only [CQAssertion.toAssn_ofEffect_true] using hu.sound
  · simpa only [CQAssertion.toAssn_ofEffect_true] using hv.sound

end QuantumProgram
