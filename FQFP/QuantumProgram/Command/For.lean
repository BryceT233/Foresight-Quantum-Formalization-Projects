/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/For.lean: the finite sequential fold and its empty and nonempty equations.

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Command.Basic

/-!
# Finite sequential iteration

A list of indexed commands runs from left to right using sequential composition.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {ι Store Cell : Type*} {H : Qudit}

/-- Sequence the indexed commands from left to right, ending with skip. -/
def Command.forList (l : List ι) (body : ι → Command Store Cell H) : Command Store Cell H :=
  l.foldr (fun i rest => (body i).seq rest) .skip

/-- The empty iteration performs a skip. -/
@[simp] theorem Command.forList_nil (body : ι → Command Store Cell H) :
    forList [] body = .skip := rfl

/-- A nonempty iteration executes its head before its tail. -/
@[simp] theorem Command.forList_cons (i : ι) (l : List ι) (body : ι → Command Store Cell H) :
    forList (i :: l) body = (body i).seq (forList l body) := rfl

end QuantumProgram
