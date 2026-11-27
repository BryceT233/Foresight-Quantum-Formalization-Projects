/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/Maths/Basis.lean (little-endian register split and reversible table addition)
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Register.Permutation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Reversible lookup addition on two equal-width qubit registers

The low word is the accumulator and the high word is the table input. Wires within each word
are ordered from the least significant bit to the most significant bit.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

/-- The first `k` wires form the low accumulator word, the next `k` the high input word.
The basis is indexed by the mathematical pair `(y, b)`. -/
noncomputable def tableAddBasis (k : ℕ) :
    OrthonormalBasis (Fin (2 ^ k) × Fin (2 ^ k)) ℂ (qubitMemory (2 * k)).state :=
  (registerBasis (ZBasis 2) (2 * k)).reindex
    (finFunctionFinEquiv.trans ((finCongr (by rw [two_mul, pow_add])).trans finProdFinEquiv.symm))

/-- Ideal lookup-add unitary in the data register's computational basis. -/
noncomputable def tableAddUnitary {k : ℕ} (z : Fin (2 ^ k) → Fin (2 ^ k)) :
    UnitaryProgram (qubitMemory (2 * k)) :=
  let B := tableAddBasis k
  let perm := Equiv.prodShear (Equiv.refl (Fin (2 ^ k))) fun y => (Equiv.subRight (z y)).symm
  let U := B.equiv B perm
  haveI := isUnitary_isoMk_coe_LIEquiv (H₁ := qubitMemory (2 * k)) (H₂ := qubitMemory (2 * k)) U
  .gateHom .whole (isoMk U.toLinearEquiv).hom

/-- The accumulator wraps modulo `2^k` and the input word is preserved. -/
theorem tableAddUnitary_basis {k : ℕ} (z : Fin (2 ^ k) → Fin (2 ^ k)) (y b : Fin (2 ^ k)) :
    (tableAddUnitary z).toOperator (tableAddBasis k (y, b)) = tableAddBasis k (y, b + z y) :=
  (tableAddBasis k).equiv_apply_basis (tableAddBasis k)
    (Equiv.prodShear (.refl _) fun y => (Equiv.subRight (z y)).symm) (y, b)

end QuantumProgram
