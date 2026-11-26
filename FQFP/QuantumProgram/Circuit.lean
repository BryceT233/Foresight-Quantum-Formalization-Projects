/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CategoryTheory.Dagger.Basic
public import FQFP.CategoryTheory.Monoidal.Dagger.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Local gates on static tensor registers

A register is a path to a factor in a parenthesized tensor product. Whiskering along
this path extends an endomorphism by identities. In a monoidal dagger category this
extension preserves unitarity, so a circuit of local unitary gates denotes a unitary.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace QuantumProgram

universe v u

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A static register selecting a tensor factor of the memory, including the whole memory. -/
inductive Register : C → C → Type u where
  /-- Select the whole memory. -/
  | whole {H : C} : Register H H
  /-- Select a register in the left factor. -/
  | left {A B S : C} (r : Register A S) : Register (A ⊗ B) S
  /-- Select a register in the right factor. -/
  | right {A B S : C} (r : Register B S) : Register (A ⊗ B) S

/-- Morphism underlying register extension, computed by whiskering along the path.
For operators use `Register.liftEnd`. -/
def Register.liftHom : {H S : C} → Register H S → (S ⟶ S) → (H ⟶ H)
  | _, _, .whole, f => f
  | _, _, .left (B := B) r, f => r.liftHom f ▷ B
  | _, _, .right (A := A) r, f => A ◁ r.liftHom f

/-- Extending the identity on a register gives the identity on memory. -/
theorem Register.liftHom_id {H S : C} (r : Register H S) : r.liftHom (𝟙 S) = 𝟙 H := by
  induction r <;> simp [liftHom, *]

/-- Extending sequential gates is the same as composing their extensions. -/
theorem Register.liftHom_comp {H S : C} (r : Register H S) (f g : S ⟶ S) :
    r.liftHom (f ≫ g) = r.liftHom f ≫ r.liftHom g := by
  induction r <;> simp [liftHom, *, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]

/-- Extend operators on a register to operators on the entire memory. -/
def Register.liftEnd {H S : C} (r : Register H S) : End S →* End H where
  toFun A := .of (r.liftHom A.asHom)
  map_one' := End.ext r.liftHom_id
  map_mul' A B := End.ext (r.liftHom_comp B.asHom A.asHom)

@[simp] theorem Register.liftEnd_asHom {H S : C} (r : Register H S) (A : End S) :
    (r.liftEnd A).asHom = r.liftHom A.asHom := rfl

@[simp] theorem Register.liftEnd_whole {H : C} (A : End H) :
    Register.whole.liftEnd A = A := rfl

end Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalDaggerCategory C] {H S : C}

/-- Taking the dagger commutes with extending a gate along a register. -/
theorem Register.dagger_liftHom (r : Register H S) (f : S ⟶ S) :
    (r.liftHom f)† = r.liftHom f† := by
  induction r <;> simp [liftHom, *]

/-- Extending an operator commutes with taking its adjoint. -/
theorem Register.liftEnd_star (r : Register H S) (A : End S) :
    r.liftEnd (star A) = star (r.liftEnd A) := End.ext (r.dagger_liftHom A.asHom).symm

/-- A self-adjoint register operation remains self-adjoint on the entire memory. -/
theorem Register.isSelfAdjoint_liftEnd (r : Register H S) {A : End S} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (r.liftEnd A) := by
  rw [isSelfAdjoint_iff, ← r.liftEnd_star, hA.star_eq]

/-- Extending a unitary gate along a register preserves unitarity. -/
instance Register.isUnitary_liftHom (r : Register H S) (f : S ⟶ S) [IsUnitary f] :
    IsUnitary (r.liftHom f) := by
  rw [isUnitary_iff, r.dagger_liftHom, ← r.liftHom_comp, ← r.liftHom_comp]
  simp [r.liftHom_id]

/-- The morphism underlying a lifted unitary operator is unitary. -/
instance Register.isUnitary_liftEnd_asHom (r : Register H S) (A : End S) [IsUnitary A.asHom] :
    IsUnitary (r.liftEnd A).asHom := by
  rw [r.liftEnd_asHom]
  infer_instance

/-- A straight-line program of local unitary gates in a monoidal dagger category. -/
inductive UnitaryProgram (H : C) : Type (max u v) where
  /-- Apply a unitary endomorphism to its selected register. -/
  | gate {S : C} (r : Register H S) (U : End S) [unitary : IsUnitary U.asHom]
  /-- Execute the first program and then the second. -/
  | seq (first second : UnitaryProgram H)

namespace UnitaryProgram

/-- Apply a local gate given by its underlying unitary morphism. -/
abbrev gateHom (r : Register H S) (U : S ⟶ S) [unitary : IsUnitary U] : UnitaryProgram H :=
  .gate r (.of U)

/-- The operator on the whole memory denoted by a program, in order of action on states. -/
def denoteEnd : UnitaryProgram H → End H
  | .gate r U (unitary := _) => r.liftEnd U
  | .seq p q => q.denoteEnd * p.denoteEnd

/-- The underlying morphism of the program operator. -/
abbrev denoteHom (p : UnitaryProgram H) : H ⟶ H := p.denoteEnd.asHom

/-- The denotation of every unitary program is unitary. -/
instance isUnitary_denoteHom (p : UnitaryProgram H) : IsUnitary p.denoteHom := by
  induction p with
  | gate r U => exact inferInstanceAs (IsUnitary (r.liftEnd U).asHom)
  | seq p q hp hq => exact inferInstanceAs (IsUnitary (p.denoteHom ≫ q.denoteHom))

/-- The program operator belongs to the unitary group of the endomorphism monoid. -/
theorem denoteEnd_mem_unitary (p : UnitaryProgram H) : p.denoteEnd ∈ unitary (End H) :=
  (End.mem_unitary_iff _).mpr (isUnitary_denoteHom p)

/-- The operator of a local gate is its register extension. -/
theorem denoteEnd_gate (r : Register H S) (U : End S) [IsUnitary U.asHom] :
    (gate r U).denoteEnd = r.liftEnd U := rfl

/-- Operator semantics of a gate supplied as a morphism. -/
theorem denoteEnd_gateHom (r : Register H S) (U : S ⟶ S) [IsUnitary U] :
    (gateHom r U).denoteEnd = r.liftEnd (.of U) := rfl

/-- The first program executed acts on the right in the operator product. -/
theorem denoteEnd_seq (p q : UnitaryProgram H) :
    (p.seq q).denoteEnd = q.denoteEnd * p.denoteEnd := rfl

/-- Sequential execution composes the underlying morphisms in execution order. -/
theorem denoteHom_seq (p q : UnitaryProgram H) :
    (p.seq q).denoteHom = p.denoteHom ≫ q.denoteHom := rfl

/-- The underlying morphism of a local gate is its register extension. -/
theorem denoteHom_gate (r : Register H S) (U : End S) [IsUnitary U.asHom] :
    (gate r U).denoteHom = r.liftHom U.asHom := rfl

/-- Execute a list of programs in order. The empty sequence acts as the identity. -/
def sequence : List (UnitaryProgram H) → UnitaryProgram H
  | [] => .gate .whole 1
  | [p] => p
  | p :: q :: ps => p.seq (sequence (q :: ps))

/-- The denotation of a list composes the gate denotations in execution order. -/
theorem denoteHom_sequence (ps : List (UnitaryProgram H)) :
    (sequence ps).denoteHom = ps.foldr (fun p f => p.denoteHom ≫ f) (𝟙 H) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases ps with
    | nil => simp [sequence]
    | cons q qs => exact congrArg (p.denoteHom ≫ ·) ih

/-- The operator of a list of programs is their product in reverse execution order. -/
theorem denoteEnd_sequence (ps : List (UnitaryProgram H)) :
    (sequence ps).denoteEnd = (ps.reverse.map denoteEnd).prod := by
  rw [List.prod_eq_foldl, List.foldl_map, List.foldl_reverse]
  apply End.ext
  change (sequence ps).denoteHom = _
  rw [denoteHom_sequence]
  exact List.foldr_hom End.asHom (fun _ _ ↦ rfl)

end UnitaryProgram

end QuantumProgram
