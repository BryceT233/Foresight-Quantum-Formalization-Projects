/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/ForMathlib/Misc.lean: existence of an equivalence preserving finite multisets
of values. The proof generalizes FQFP's fiber-counting argument for Schmidt coefficients.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import Mathlib.Data.Fintype.EquivFin

/-!
# Matching finite families by their values
-/

public section

/-- Two finite families with the same multiset of values admit a value-preserving relabeling. -/
theorem Fintype.exists_equiv_of_multiset_eq {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (f : ι → α) (g : κ → α) (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : ι ≃ κ, ∀ i, g (e i) = f i := by
  classical
  have hc (a : α) : Fintype.card {i // f i = a} = Fintype.card {j // g j = a} := by
    simpa [Multiset.count_map, Fintype.card_subtype, Finset.filter_val, Finset.card_def, eq_comm]
      using congrArg (Multiset.count a) h
  exact ⟨Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hc a)), Equiv.ofFiberEquiv_map _⟩
