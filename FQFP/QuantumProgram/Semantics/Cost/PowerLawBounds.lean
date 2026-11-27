/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Semantics.Cost.Bounds
public import FQFP.QuantumProgram.Semantics.Cost.PowerLaw

/-!
# Power-law bounds for program families

A bound holds uniformly over all input states once the natural problem size is large enough.
The store type, address type, quantum memory and primitive prices may all vary with size.
-/

@[expose] public section

open Filter
open scoped NNReal ENNReal

namespace QuantumProgram

variable {Store Cell : ℕ → Type*} {H : ℕ → Qudit} {model : ∀ n, CostModel (H n)}
    {p q : ∀ n, Command (Store n) (Cell n) (H n)} {m k : PowerLawCost}

/-- At all sufficiently large natural sizes, the bound holds uniformly over input states. -/
def PowerLawCostBound (model : ∀ n, CostModel (H n)) (p : ∀ n, Command (Store n) (Cell n) (H n))
    (m : PowerLawCost) : Prop :=
  ∀ᶠ n : ℕ in atTop, CostBound (model n) (p n) (m.eval n)

namespace PowerLawCostBound

/-- A larger power law also bounds the family once the size is large enough. -/
theorem mono (hp : PowerLawCostBound model p m) (h : m ≤ k) : PowerLawCostBound model p k := by
  filter_upwards [hp, (PowerLawCost.le_iff_eventually_eval_le tendsto_natCast_atTop_atTop).mp h]
    with n hn hmk
  exact hn.mono hmk

/-- Use any power law that eventually bounds the sum of the two sequential budgets. -/
theorem seq_of_add_le {r : PowerLawCost} (hp : PowerLawCostBound model p m)
    (hq : PowerLawCostBound model q k)
    (hadd : ∀ᶠ n : ℕ in atTop, m.eval n + k.eval n ≤ r.eval n) :
    PowerLawCostBound model (fun n => (p n).seq (q n)) r := by
  filter_upwards [hp, hq, hadd] with n hp' hq' hr
  exact (hp'.seq hq').mono hr

/-- Sequential composition adds the costs at each size. -/
theorem seq (hp : PowerLawCostBound model p m) (hq : PowerLawCostBound model q k) :
    PowerLawCostBound model (fun n => (p n).seq (q n)) (m.sumBound k) := by
  refine hp.seq_of_add_le hq ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact m.add_eval_le_sumBound k (by exact_mod_cast hn)

/-- A conditional is eventually bounded by the lexicographically larger branch bound. -/
theorem ite (b : ∀ n, Store n → Bool)
    (hp : PowerLawCostBound model p m) (hq : PowerLawCostBound model q k) :
    PowerLawCostBound model (fun n => .ite (b n) (p n) (q n)) (max m k) := by
  filter_upwards [hp.mono (le_max_left m k), hq.mono (le_max_right m k)] with n hn hn'
  simpa only [max_self] using hn.ite (b n) hn'

/-- A finite iteration may use different prices for its entries at each problem size.
The sum charges each list occurrence. -/
theorem forList_of_sum_le {ι : ℕ → Type*} (l : ∀ n, List (ι n))
    (body : ∀ n, ι n → Command (Store n) (Cell n) (H n)) (price : ∀ n, ι n → ℝ≥0)
    (hbody : ∀ᶠ n : ℕ in atTop, ∀ i ∈ l n, CostBound (model n) (body n i) (price n i))
    (hsum : ∀ᶠ n : ℕ in atTop, ((l n).map (price n)).sum ≤ m.eval n) :
    PowerLawCostBound model (fun n => .forList (l n) (body n)) m := by
  filter_upwards [hbody, hsum] with n hn htotal
  exact (CostBound.forList (l n) hn).mono htotal

/-- Multiply a bound on list length by a uniform bound on the cost of its visited entries. -/
theorem forList {ι : ℕ → Type*} (l : ∀ n, List (ι n))
    (body : ∀ n, ι n → Command (Store n) (Cell n) (H n))
    (hlen : ∀ᶠ n : ℕ in atTop, ((l n).length : ℝ≥0) ≤ k.eval n)
    (hbody : ∀ᶠ n : ℕ in atTop, ∀ i ∈ l n, CostBound (model n) (body n i) (m.eval n)) :
    PowerLawCostBound model (fun n => .forList (l n) (body n)) (k.product m) := by
  refine forList_of_sum_le l body (fun n _ => m.eval n) hbody ?_
  filter_upwards [hlen] with n hn
  simpa [List.map_const', nsmul_eq_mul, PowerLawCost.eval_product] using
    mul_le_mul_left hn (m.eval n)

/-- A power law for the body cost and one for the expected entry count multiply. -/
theorem whileDo {b : ∀ n, Store n → Bool} (hp : PowerLawCostBound model p m)
    (hk : ∀ᶠ n : ℕ in atTop, ∀ s : CQState (Store n) (H n),
      expectedIterations (b n) (p n) s ≤ (k.eval n : ℝ≥0∞) * s.mass) :
    PowerLawCostBound model (fun n => .whileDo (b n) (p n)) (m.product k) := by
  filter_upwards [hp, hk] with n hn hn'
  rw [PowerLawCost.eval_product]
  exact hn.whileDo hn'

/-- An eventual bound on the inverse exit probability multiplies the body budget. -/
theorem whileDo_of_exit_probability {b : ∀ n, Store n → Bool} (hp : PowerLawCostBound model p m)
    (e : ℕ → ℝ≥0)
    (hexit : ∀ᶠ n : ℕ in atTop, ∃ he : e n ≤ 1, 0 < e n ∧
      validTot (((Assertion.identity (H := H n)).scaled (e n) he).mand (b n)) (p n)
        (Assertion.identity.mandNot (b n)))
    (hinv : ∀ᶠ n : ℕ in atTop, (e n)⁻¹ ≤ k.eval n) :
    PowerLawCostBound model (fun n => .whileDo (b n) (p n)) (m.product k) := by
  refine hp.whileDo ?_
  filter_upwards [hexit, hinv] with n he hk
  obtain ⟨_, hpos, hwp⟩ := he
  intro s
  exact (expectedIterations_le_inv_mul_of_exit_probability hpos hwp
    (whileActiveMass_le_mass (b n) (p n) 0 s)).trans
    (mul_le_mul_left (ENNReal.coe_le_coe.mpr hk) _)

end PowerLawCostBound

end QuantumProgram
