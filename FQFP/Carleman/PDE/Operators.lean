/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.PDE.Fields
public import Mathlib.LinearAlgebra.Pi

/-!
# Spatial substitutions and slot operators

Pullbacks are algebraic linear maps on multipoint fields. Slot operators have
explicit domains: every slice supplied to the underlying operator must belong
to its domain submodule. No boundedness or spatial regularity is assumed for
an arbitrary field. The quadratic slice inserts its second factor immediately
after the chosen slot, preserving the ordered convention of the PDE hierarchy.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace Carleman.PDE

/-- A spatial field before taking its multipoint lift. -/
abbrev SpatialField (m n : ℕ) := (Fin m → ℝ) → Fin n → ℝ

/-- Pull back spatial points and component tuples, possibly changing the number of slots. -/
def fieldPullback {m n k l : ℕ}
    (px : (Fin k → (Fin m → ℝ)) → (Fin l → (Fin m → ℝ)))
    (pj : (Fin k → Fin n) → (Fin l → Fin n)) :
    MultipointField m n l →ₗ[ℝ] MultipointField m n k where
  toFun f xs js := f (px xs) (pj js)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma fieldPullback_comp {m n k l r : ℕ}
    (px : (Fin k → (Fin m → ℝ)) → (Fin l → (Fin m → ℝ)))
    (pj : (Fin k → Fin n) → (Fin l → Fin n))
    (qx : (Fin l → (Fin m → ℝ)) → (Fin r → (Fin m → ℝ)))
    (qj : (Fin l → Fin n) → (Fin r → Fin n)) :
    (fieldPullback px pj).comp (fieldPullback qx qj) =
      fieldPullback (qx ∘ px) (qj ∘ pj) := rfl

/-- Reindex both spatial and component slots by a map of slot indices. -/
def reindexField {m n k l : ℕ} (r : Fin l → Fin k) :
    MultipointField m n l →ₗ[ℝ] MultipointField m n k :=
  fieldPullback (fun xs => xs ∘ r) (fun js => js ∘ r)

lemma reindexField_multipointLift {m n k : ℕ} (e : Fin k ≃ Fin k)
    (u : SpatialField m n) : reindexField e (multipointLift u) = multipointLift u := by
  ext xs js
  exact multipointLift_reindex u e xs js

/-- Replace one spatial variable by another, keeping component slots unchanged. -/
def substituteSpatialSlot {m n k : ℕ} (p q : Fin k) :
    MultipointField m n k →ₗ[ℝ] MultipointField m n k :=
  fieldPullback (fun xs => Function.update xs p (xs q)) id

lemma substituteSpatialSlot_self {m n k : ℕ} (p : Fin k) :
    substituteSpatialSlot (m := m) (n := n) p p = LinearMap.id := by
  ext f xs js
  simp [substituteSpatialSlot, fieldPullback]

/-- Restrict an inserted spatial point to an existing point, with its component fixed. -/
def diagonalRestriction {m n k : ℕ} (p : Fin (k + 1)) (q : Fin k) (c : Fin n) :
    MultipointField m n (k + 1) →ₗ[ℝ] MultipointField m n k :=
  fieldPullback (fun xs => p.insertNth (xs q) xs) (fun js => p.insertNth c js)

lemma diagonalRestriction_multipointLift {m n k : ℕ} (u : SpatialField m n)
    (p : Fin (k + 1)) (q : Fin k) (c : Fin n)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    diagonalRestriction p q c (multipointLift u) xs js =
      u (xs q) c * multipointLift u xs js :=
  multipointLift_insertNth u p (xs q) c xs js

/-- Insert the fixed factor of a constant forcing into a lower-level field. -/
def insertFieldFactor {m n k : ℕ} (c : SpatialField m n) (p : Fin (k + 1)) :
    MultipointField m n k →ₗ[ℝ] MultipointField m n (k + 1) where
  toFun f xs js := c (xs p) (js p) * f (p.removeNth xs) (p.removeNth js)
  map_add' f g := by ext xs js; exact mul_add _ _ _
  map_smul' a f := by ext xs js; exact mul_left_comm _ _ _

lemma insertFieldFactor_multipointLift {m n k : ℕ} (c u : SpatialField m n)
    (p : Fin (k + 1)) (xs : Fin (k + 1) → (Fin m → ℝ)) (js : Fin (k + 1) → Fin n) :
    insertFieldFactor c p (multipointLift u) xs js =
      c (xs p) (js p) * ∏ i ∈ Finset.univ.erase p, u (xs i) (js i) := by
  change c (xs p) (js p) * multipointLift u (p.removeNth xs) (p.removeNth js) = _
  rw [multipointLift_removeNth]

/-- A one-slot slice varies the selected spatial point and component only. -/
def slotSlice {m n k : ℕ} (p : Fin k)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    MultipointField m n k →ₗ[ℝ] SpatialField m n where
  toFun f x c := f (Function.update xs p x) (Function.update js p c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma slotSlice_multipointLift {m n k : ℕ} (u : SpatialField m n) (p : Fin k)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    slotSlice p xs js (multipointLift u) =
      (∏ i ∈ Finset.univ.erase p, u (xs i) (js i)) • u := by
  ext x c
  change multipointLift u (Function.update xs p x) (Function.update js p c) = _
  rw [multipointLift_update]
  exact mul_comm _ _

/-- The two-slot slice inserts its second slot immediately after the selected slot. -/
def pairSlice {m n k : ℕ} (p : Fin k)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    MultipointField m n (k + 1) →ₗ[ℝ] MultipointField m n 2 where
  toFun f zs cs :=
    f (p.succ.insertNth (zs 1) (Function.update xs p (zs 0)))
      (p.succ.insertNth (cs 1) (Function.update js p (cs 0)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma pairSlice_multipointLift {m n k : ℕ} (u : SpatialField m n) (p : Fin k)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    pairSlice p xs js (multipointLift u) =
      (∏ i ∈ Finset.univ.erase p, u (xs i) (js i)) •
        (multipointLift u : MultipointField m n 2) := by
  ext zs cs
  change multipointLift u _ _ = _
  rw [multipointLift_insertNth, multipointLift_update]
  simp only [Pi.smul_apply, smul_eq_mul, multipointLift, Fin.prod_univ_two]
  ring

/-- The fields all of whose slices lie in the domain of a given spatial operator. -/
def sliceDomain {m n k r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : (Fin k → (Fin m → ℝ)) → (Fin k → Fin n) →
      (MultipointField m n r →ₗ[ℝ] V)) (S : Submodule ℝ V) :
    Submodule ℝ (MultipointField m n r) :=
  ⨅ xs, ⨅ js, S.comap (s xs js)

lemma mem_sliceDomain {m n k r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : (Fin k → (Fin m → ℝ)) → (Fin k → Fin n) →
      (MultipointField m n r →ₗ[ℝ] V)) (S : Submodule ℝ V)
    (f : MultipointField m n r) :
    f ∈ sliceDomain s S ↔ ∀ xs js, s xs js f ∈ S := by
  simp [sliceDomain]

/-- A slice restricted to the common admissible domain takes values in the operator domain. -/
def domainSlice {m n k r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : (Fin k → (Fin m → ℝ)) → (Fin k → Fin n) →
      (MultipointField m n r →ₗ[ℝ] V)) (S : Submodule ℝ V)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) : sliceDomain s S →ₗ[ℝ] S :=
  ((s xs js).comp (sliceDomain s S).subtype).codRestrict S
    (fun f => (mem_sliceDomain s S f).mp f.property xs js)

/-- Apply a domain-restricted spatial operator to each slice and read the chosen slot. -/
def slicedAction {m n k r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : (Fin k → (Fin m → ℝ)) → (Fin k → Fin n) →
      (MultipointField m n r →ₗ[ℝ] V)) (S : Submodule ℝ V)
    (L : S →ₗ[ℝ] SpatialField m n) (p : Fin k) :
    sliceDomain s S →ₗ[ℝ] MultipointField m n k :=
  LinearMap.pi fun xs => LinearMap.pi fun js =>
    (LinearMap.proj (js p)).comp ((LinearMap.proj (xs p)).comp
      (L.comp (domainSlice s S xs js)))

lemma multipointLift_mem_slotDomain {m n k : ℕ} (S : Submodule ℝ (SpatialField m n))
    (u : S) (p : Fin k) : multipointLift (u : SpatialField m n) ∈ sliceDomain (slotSlice p) S := by
  rw [mem_sliceDomain]
  intro xs js
  rw [slotSlice_multipointLift]
  exact S.smul_mem _ u.property

lemma multipointLift_mem_pairDomain {m n k : ℕ}
    (S : Submodule ℝ (MultipointField m n 2)) (u : SpatialField m n)
    (hu : (multipointLift u : MultipointField m n 2) ∈ S) (p : Fin k) :
    (multipointLift u : MultipointField m n (k + 1)) ∈ sliceDomain (pairSlice p) S := by
  rw [mem_sliceDomain]
  intro xs js
  rw [pairSlice_multipointLift]
  exact S.smul_mem _ hu

/-- The linear slot term factors out all untouched coordinates of a lifted field. -/
lemma slicedAction_slotSlice_multipointLift {m n k : ℕ}
    (S : Submodule ℝ (SpatialField m n)) (L : S →ₗ[ℝ] SpatialField m n) (u : S)
    (p : Fin k) (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    slicedAction (slotSlice p) S L p
        ⟨multipointLift (u : SpatialField m n), multipointLift_mem_slotDomain S u p⟩ xs js =
      L u (xs p) (js p) *
        ∏ i ∈ Finset.univ.erase p, (u : SpatialField m n) (xs i) (js i) := by
  let c := ∏ i ∈ Finset.univ.erase p, (u : SpatialField m n) (xs i) (js i)
  have hslice : domainSlice (slotSlice p) S xs js
      ⟨multipointLift (u : SpatialField m n), multipointLift_mem_slotDomain S u p⟩ = c • u :=
    Subtype.ext (slotSlice_multipointLift _ _ _ _)
  change L _ (xs p) (js p) = _
  rw [hslice, map_smul]
  exact mul_comm _ _

/-- The quadratic slot term factors out all coordinates outside the chosen pair. -/
lemma slicedAction_pairSlice_multipointLift {m n k : ℕ}
    (S : Submodule ℝ (MultipointField m n 2)) (Q : S →ₗ[ℝ] SpatialField m n)
    (u : SpatialField m n) (hu : (multipointLift u : MultipointField m n 2) ∈ S)
    (p : Fin k) (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    slicedAction (pairSlice p) S Q p
        ⟨multipointLift u, multipointLift_mem_pairDomain S u hu p⟩ xs js =
      Q ⟨multipointLift u, hu⟩ (xs p) (js p) *
        ∏ i ∈ Finset.univ.erase p, u (xs i) (js i) := by
  let c := ∏ i ∈ Finset.univ.erase p, u (xs i) (js i)
  have hslice : domainSlice (pairSlice p) S xs js
      ⟨multipointLift u, multipointLift_mem_pairDomain S u hu p⟩ =
      c • ⟨multipointLift u, hu⟩ := Subtype.ext (pairSlice_multipointLift _ _ _ _)
  change Q _ (xs p) (js p) = _
  rw [hslice, map_smul]
  exact mul_comm _ _

/-- The common domain for all slot contributions to a hierarchy block. -/
def blockDomain {m n k r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : Fin k → (Fin k → (Fin m → ℝ)) → (Fin k → Fin n) →
      (MultipointField m n r →ₗ[ℝ] V)) (S : Submodule ℝ V) :
    Submodule ℝ (MultipointField m n r) :=
  ⨅ p, sliceDomain (s p) S

lemma mem_blockDomain {m n k r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : Fin k → (Fin k → (Fin m → ℝ)) → (Fin k → Fin n) →
      (MultipointField m n r →ₗ[ℝ] V)) (S : Submodule ℝ V)
    (f : MultipointField m n r) :
    f ∈ blockDomain s S ↔ ∀ p, f ∈ sliceDomain (s p) S := by
  simp [blockDomain]

/-- Sum slot actions after restricting each one to their common domain. -/
def slotBlock {m n k r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : Fin k → (Fin k → (Fin m → ℝ)) → (Fin k → Fin n) →
      (MultipointField m n r →ₗ[ℝ] V)) (S : Submodule ℝ V)
    (L : S →ₗ[ℝ] SpatialField m n) : blockDomain s S →ₗ[ℝ] MultipointField m n k :=
  ∑ p, (slicedAction (s p) S L p).comp
    (Submodule.inclusion (iInf_le (fun q => sliceDomain (s q) S) p))

/-- The forcing block maps the immediately lower level `k` into level `k + 1`. -/
def forcingBlock {m n k : ℕ} (c : SpatialField m n) :
    MultipointField m n k →ₗ[ℝ] MultipointField m n (k + 1) :=
  ∑ p, insertFieldFactor c p

/-- The degree-preserving block from a domain-restricted linear spatial operator. -/
def linearBlock {m n k : ℕ} (S : Submodule ℝ (SpatialField m n))
    (L : S →ₗ[ℝ] SpatialField m n) :
    blockDomain (slotSlice (k := k)) S →ₗ[ℝ] MultipointField m n k :=
  slotBlock slotSlice S L

/-- The quadratic block maps level `k + 1` to level `k`, retaining the inserted slot order. -/
def quadraticBlock {m n k : ℕ} (S : Submodule ℝ (MultipointField m n 2))
    (Q : S →ₗ[ℝ] SpatialField m n) :
    blockDomain (pairSlice (k := k)) S →ₗ[ℝ] MultipointField m n k :=
  slotBlock pairSlice S Q

lemma multipointLift_mem_linearBlockDomain {m n k : ℕ}
    (S : Submodule ℝ (SpatialField m n)) (u : S) :
    (multipointLift (u : SpatialField m n) : MultipointField m n k) ∈
      blockDomain slotSlice S := by
  rw [mem_blockDomain]
  exact multipointLift_mem_slotDomain S u

lemma multipointLift_mem_quadraticBlockDomain {m n k : ℕ}
    (S : Submodule ℝ (MultipointField m n 2)) (u : SpatialField m n)
    (hu : (multipointLift u : MultipointField m n 2) ∈ S) :
    (multipointLift u : MultipointField m n (k + 1)) ∈ blockDomain pairSlice S := by
  rw [mem_blockDomain]
  exact multipointLift_mem_pairDomain S u hu

lemma forcingBlock_multipointLift {m n k : ℕ} (c u : SpatialField m n)
    (xs : Fin (k + 1) → (Fin m → ℝ)) (js : Fin (k + 1) → Fin n) :
    forcingBlock c (multipointLift u) xs js =
      ∑ p : Fin (k + 1), c (xs p) (js p) *
        ∏ i ∈ Finset.univ.erase p, u (xs i) (js i) := by
  simp only [forcingBlock, LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  exact insertFieldFactor_multipointLift c u p xs js

lemma linearBlock_multipointLift {m n k : ℕ}
    (S : Submodule ℝ (SpatialField m n)) (L : S →ₗ[ℝ] SpatialField m n) (u : S)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    linearBlock S L
        ⟨multipointLift (u : SpatialField m n), multipointLift_mem_linearBlockDomain S u⟩ xs js =
      ∑ p : Fin k, L u (xs p) (js p) *
        ∏ i ∈ Finset.univ.erase p, (u : SpatialField m n) (xs i) (js i) := by
  simp only [linearBlock, slotBlock, LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro p _
  exact slicedAction_slotSlice_multipointLift S L u p xs js

lemma quadraticBlock_multipointLift {m n k : ℕ}
    (S : Submodule ℝ (MultipointField m n 2)) (Q : S →ₗ[ℝ] SpatialField m n)
    (u : SpatialField m n) (hu : (multipointLift u : MultipointField m n 2) ∈ S)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    quadraticBlock S Q
        ⟨multipointLift u, multipointLift_mem_quadraticBlockDomain S u hu⟩ xs js =
      ∑ p : Fin k, Q ⟨multipointLift u, hu⟩ (xs p) (js p) *
        ∏ i ∈ Finset.univ.erase p, u (xs i) (js i) := by
  simp only [quadraticBlock, slotBlock, LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro p _
  exact slicedAction_pairSlice_multipointLift S Q u hu p xs js

end Carleman.PDE
