/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.MeasurePrepare
public import FQFP.CQM.Qudit.Classical.Channel

/-!
# Classical channels on qudit registers

Measure the input register in its chosen basis and prepare the corresponding row of
the classical transition matrix as a diagonal density on the output register.
-/

@[expose] public noncomputable section

namespace Qudit.MemorylessChannel

variable {I O : Type*} [Fintype I] [Fintype O] {H K : Qudit}

/-- Realize a classical transition law as a measure-and-prepare quantum channel. -/
def toQuantumChannel (C : MemorylessChannel I O) (b : OrthonormalBasis I ℂ H.state)
    (c : OrthonormalBasis O ℂ K.state) : QuantumChannel H K :=
  (POVM.ofBasis b).measurePrepare fun i => (Ensemble.ofPure (C.row i) (UnitState.ofBasis c)).mix

/-- The output probabilities are obtained by applying the transition law to the Born
probabilities of the input, including inputs with coherence in the measurement basis. -/
lemma probability_toQuantumChannel (C : MemorylessChannel I O)
    (b : OrthonormalBasis I ℂ H.state) (c : OrthonormalBasis O ℂ K.state) (ρ : Density H) (o : O) :
    (POVM.ofBasis c).probability ((C.toQuantumChannel b c).map ρ) o =
      ∑ i, (POVM.ofBasis b).probability ρ i * (C.row i).weights o := by
  rw [toQuantumChannel, POVM.map_measurePrepare, Ensemble.mix, POVM.probability_mixture]
  apply Finset.sum_congr rfl
  intro i _
  change _ * (POVM.ofBasis c).probability
    (Ensemble.ofPure (C.row i) (UnitState.ofBasis c)).mix o = _
  rw [POVM.probability_ofBasis, Ensemble.op_mix_ofPure_ofBasis_apply, inner_smul_right,
    c.inner_eq_one, mul_one, Complex.ofReal_re]
  rfl

/-- Sending one basis symbol recovers its full row of classical transition probabilities. -/
lemma probability_toQuantumChannel_basis (C : MemorylessChannel I O)
    (b : OrthonormalBasis I ℂ H.state) (c : OrthonormalBasis O ℂ K.state) (i : I) (o : O) :
    (POVM.ofBasis c).probability
      ((C.toQuantumChannel b c).map (Density.pure (UnitState.ofBasis b i))) o =
        (C.row i).weights o := by
  classical
  rw [probability_toQuantumChannel]
  simp [POVM.probability_ofBasis_ofBasis]

end Qudit.MemorylessChannel
