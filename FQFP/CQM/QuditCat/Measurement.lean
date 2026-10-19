/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.QuditCat.Dagger
public import FQFP.CQM.QuditCat.Monoidal
public import FQFP.CQM.QuditCat.Biproducts
public import FQFP.CQM.Category.Measurement

/-!
# Measurement in finite-dimensional complex Hilbert spaces

The categorical probability scalar is evaluated at `1 : ℂ`. An orthonormal basis resolves
the identity, so its bra effects satisfy the abstract Born rule.

## Main definitions

* `scalarRingEquiv`: categorical scalars interpreted as complex numbers.
* `basisMeasurement`: the coordinate map into an explicit orthogonal sum.

## Main results

* `isUnitary_basisMeasurement`: the complete/disjoint theorem applied to an orthonormal basis.
* `sum_probability_orthonormalBasis`: the identity-resolution Born rule.
* `scalarRingEquiv_probability_ketArrow_braArrow`: squared inner-product amplitudes.
* `hadamard_zero_probability`: both Hadamard outcomes have probability `1/2`.
* `counterexample_probability_sum`: complete effects need not have probability sum one.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.DaggerCategory
open scoped BigOperators

namespace QuditCat

noncomputable section

/-- Evaluation at `1` identifies categorical scalars with complex numbers. -/
def scalarRingEquiv : Scalar QuditCat ≃+* ℂ where
  toFun s := s.asHom.hom (1 : ℂ)
  invFun z := .of (ofHom (.lsmul ℂ ℂ z))
  left_inv s := by ext; simp
  right_inv z := by change z • (1 : ℂ) = z; simp
  map_mul' _ _ := by simp
  map_add' _ _ := by simp

/-- A ket is an isometry precisely when its vector has unit norm. -/
theorem isIsometry_ketArrow_iff {H : QuditCat} (v : H.state) :
    IsIsometry (ketArrow v) ↔ ‖v‖ = 1 := by
  constructor
  · intro h
    have h1 := norm_hom_of_isIsometry (ketArrow v) (1 : ℂ)
    simpa [ketArrow, ket, norm_smul] using h1
  · intro hv
    rw [isIsometry_iff, ketArrow_dagger, ketArrow_comp_braArrow, inner_self_eq_norm_sq_to_K, hv]
    simpa using ofHom_lsmul_one

/-- The bra effects of an orthonormal basis resolve the identity. -/
theorem sum_braArrow_comp_ketArrow {H : QuditCat} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) :
    ∑ i, braArrow (b i) ≫ ketArrow (b i) = 𝟙 H := by
  apply hom_ext
  ext x
  simp only [hom_sum, LinearMap.sum_apply, hom_comp, LinearMap.comp_apply,
    hom_id, LinearMap.id_apply]
  simpa [braArrow, ketArrow, bra, ket] using (b.sum_repr' x)

/-- The bra effects of an orthonormal basis detect every nonzero process. -/
theorem complete_braArrow_orthonormalBasis {H : QuditCat} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) : Effect.Complete (fun i ↦ braArrow (b i)) := by
  intro Y f hf
  calc
    f = f ≫ 𝟙 H := (Category.comp_id f).symm
    _ = f ≫ ∑ i, braArrow (b i) ≫ ketArrow (b i) := by
      rw [sum_braArrow_comp_ketArrow b]
    _ = 0 := by simp [Semiadditive.comp_sum, ← Category.assoc, hf]

/-- The bra effects of an orthonormal basis are normalized and pairwise orthogonal. -/
theorem disjoint_braArrow_orthonormalBasis {H : QuditCat} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) : Effect.Disjoint (fun i ↦ braArrow (b i)) := by
  constructor
  · intro i
    rw [braArrow_dagger, ketArrow_comp_braArrow, b.inner_eq_one]
    exact ofHom_lsmul_one
  · intro i j hij
    rw [braArrow_dagger, ketArrow_comp_braArrow, b.inner_eq_zero hij]
    apply hom_ext
    simp

/-- The coordinate measurement map into an explicit orthogonal sum of scalar objects. -/
def basisMeasurement {H : QuditCat} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) : H ⟶ of (EuclideanSpace ℂ ι) :=
  (sumBicone (fun _ : ι ↦ of ℂ)).lift (sumBiconeIsBilimit _)
    (fun i ↦ braArrow (b i))

/-- Each component of a basis measurement is its usual inner-product amplitude. -/
theorem basisMeasurement_apply {H : QuditCat} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) (v : H.state) (i : ι) :
    ((basisMeasurement b).hom v).ofLp i = inner ℂ (b i) v :=
  congrArg (fun f ↦ f.hom v)
    ((sumBicone (fun _ : ι ↦ of ℂ)).lift_π (sumBiconeIsBilimit _)
      (fun j ↦ braArrow (b j)) i)

/-- The underlying linear map of a basis measurement is the orthonormal coordinate map. -/
@[simp]
theorem hom_basisMeasurement {H : QuditCat} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) :
    (basisMeasurement b).hom = b.repr.toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change ((basisMeasurement b).hom v).ofLp i = b.repr v i
  rw [b.repr_apply_apply]
  exact basisMeasurement_apply b v i

/-- **Example 2.54**: a basis measurement is unitary by the abstract complete/disjoint theorem. -/
theorem isUnitary_basisMeasurement {H : QuditCat} {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) : IsUnitary (basisMeasurement b) :=
  Effect.isUnitary_bicone_lift_of_complete_disjoint
    (sumBicone (fun _ : ι ↦ of ℂ)) (sumBiconeIsBilimit _)
    (fun i ↦ braArrow (b i)) (complete_braArrow_orthonormalBasis b)
    (disjoint_braArrow_orthonormalBasis b)

/-- The categorical Born rule for the bra effects of an orthonormal basis. -/
theorem sum_probability_orthonormalBasis {H : QuditCat} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) (v : H.state) (hv : ‖v‖ = 1) :
    ∑ i, probability (ketArrow v) (braArrow (b i)) = 1 := by
  let : IsIsometry (ketArrow v) := (isIsometry_ketArrow_iff v).2 hv
  exact Effect.sum_probability_eq_one_of_sum_comp_dagger_eq_id
    (fun i ↦ braArrow (b i)) (by simpa using sum_braArrow_comp_ketArrow b)
    (ketArrow v)

/-- Evaluating a categorical Born scalar gives the squared modulus of the amplitude. -/
theorem scalarRingEquiv_probability_ketArrow_braArrow {H : QuditCat} (v w : H.state) :
    scalarRingEquiv (probability (ketArrow v) (braArrow w)) =
      (‖inner ℂ w v‖ ^ 2 : ℂ) := by
  change (ketArrow v ≫ braArrow w ≫ (braArrow w)† ≫ (ketArrow v)†).hom 1 = _
  rw [braArrow_dagger, ketArrow_dagger]
  simp only [ketArrow, ket, braArrow, bra, hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    coe_innerₛₗ_apply, Function.comp_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [inner_smul_right, ← inner_conj_symm w v, mul_comm, RCLike.mul_conj,
    RCLike.norm_conj]
  norm_cast

/-- Every probability in the qudit model is a nonnegative real scalar. -/
theorem probability_re_nonneg {H : QuditCat} (v w : H.state) :
    0 ≤ (scalarRingEquiv (probability (ketArrow v) (braArrow w))).re := by
  rw [scalarRingEquiv_probability_ketArrow_braArrow]
  norm_cast
  positivity

/-- A qudit Born scalar has zero imaginary part. -/
@[simp]
theorem probability_im_eq_zero {H : QuditCat} (v w : H.state) :
    (scalarRingEquiv (probability (ketArrow v) (braArrow w))).im = 0 := by
  rw [scalarRingEquiv_probability_ketArrow_braArrow]
  norm_cast

/-- Real probabilities for an orthonormal-basis measurement sum to one. -/
theorem sum_probability_re_orthonormalBasis {H : QuditCat} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) (v : H.state) (hv : ‖v‖ = 1) :
    ∑ i, (scalarRingEquiv (probability (ketArrow v) (braArrow (b i)))).re = 1 := by
  have h := congrArg (fun s : Scalar QuditCat ↦ (scalarRingEquiv s).re)
    (sum_probability_orthonormalBasis b v hv)
  simpa only [map_sum, Complex.re_sum, map_one, Complex.one_re] using h

/-- A probability from a complete orthonormal-basis measurement is at most one. -/
theorem probability_re_le_one_orthonormalBasis {H : QuditCat} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) (v : H.state) (hv : ‖v‖ = 1) (i : ι) :
    (scalarRingEquiv (probability (ketArrow v) (braArrow (b i)))).re ≤ 1 := by
  rw [← sum_probability_re_orthonormalBasis b v hv]
  exact Finset.single_le_sum (fun j _ ↦ probability_re_nonneg v (b j))
    (Finset.mem_univ i)

/-- Measuring a basis vector in its own basis gives a Kronecker distribution. -/
theorem probability_basis_vector {H : QuditCat} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : OrthonormalBasis ι ℂ H.state) (i j : ι) :
    scalarRingEquiv (probability (ketArrow (b i)) (braArrow (b j))) =
      if i = j then 1 else 0 := by
  rw [scalarRingEquiv_probability_ketArrow_braArrow]
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, b.inner_eq_zero hji]

/-- The first computational basis outcome has probability one in state `|0⟩`. -/
theorem qubit_zero_probability_zero : scalarRingEquiv
    (probability (ketArrow (ZBasis 2 0)) (braArrow (ZBasis 2 0))) = 1 := by
  simpa using probability_basis_vector (ZBasis 2) 0 0

/-- The other computational basis outcome has probability zero in state `|0⟩`. -/
theorem qubit_zero_probability_one : scalarRingEquiv
    (probability (ketArrow (ZBasis 2 0)) (braArrow (ZBasis 2 1))) = 0 := by
  simpa using probability_basis_vector (ZBasis 2) 0 1

/-- Bra addition is the additive structure on linear functionals. -/
theorem braArrow_add {H : QuditCat} (v w : H.state) :
    braArrow (v + w) = braArrow v + braArrow w := by
  apply hom_ext
  ext x
  simp [braArrow, bra]

/-- The two effects in the printed Proposition 2.55 counterexample. -/
def counterexampleEffect (i : Fin 2) : Effect Qubit :=
  if i = 0 then braArrow (ZBasis 2 0) else
    braArrow (ZBasis 2 0 + ZBasis 2 1)

/-- The counterexample effects are complete: they distinguish both basis directions. -/
theorem counterexample_complete : Effect.Complete counterexampleEffect := by
  intro Y f hf
  have h0 : f ≫ braArrow (ZBasis 2 0) = 0 := by
    simpa [counterexampleEffect] using hf 0
  have h1 : f ≫ braArrow (ZBasis 2 0 + ZBasis 2 1) = 0 := by
    simpa [counterexampleEffect] using hf 1
  have hother : f ≫ braArrow (ZBasis 2 1) = 0 := by
    rwa [braArrow_add, Preadditive.comp_add, h0, zero_add] at h1
  have hall : ∀ i : Fin 2, f ≫ braArrow (ZBasis 2 i) = 0 := by
    intro i
    fin_cases i
    · exact h0
    · exact hother
  calc
    f = f ≫ 𝟙 Qubit := (Category.comp_id f).symm
    _ = f ≫ ∑ i : Fin 2, braArrow (ZBasis 2 i) ≫ ketArrow (ZBasis 2 i) := by
      rw [sum_braArrow_comp_ketArrow (ZBasis 2)]
    _ = ∑ i : Fin 2, (f ≫ braArrow (ZBasis 2 i)) ≫ ketArrow (ZBasis 2 i) := by
      rw [Semiadditive.comp_sum]
      simp only [Category.assoc]
    _ = 0 := by simp [hall]

/-- Both printed-proposition effects assign probability one to `|0⟩`. -/
theorem counterexample_probability_zero :
    scalarRingEquiv
      (probability (ketArrow (ZBasis 2 0)) (counterexampleEffect 0)) = 1 := by
  simpa [counterexampleEffect] using qubit_zero_probability_zero

/-- The overlapping second effect also assigns probability one to `|0⟩`. -/
theorem counterexample_probability_one :
    scalarRingEquiv
      (probability (ketArrow (ZBasis 2 0)) (counterexampleEffect 1)) = 1 := by
  have h : counterexampleEffect 1 = braArrow (ZBasis 2 0 + ZBasis 2 1) := by
    simp [counterexampleEffect]
  rw [h, scalarRingEquiv_probability_ketArrow_braArrow]
  simp [inner_add_left]

/-- The printed Proposition 2.55 fails: these complete effects have probability sum `2`. -/
theorem counterexample_probability_sum :
    scalarRingEquiv
      (∑ i : Fin 2, probability (ketArrow (ZBasis 2 0)) (counterexampleEffect i)) = 2 := by
  rw [map_sum, Fin.sum_univ_two, counterexample_probability_zero, counterexample_probability_one]
  norm_num

/-- The input in the printed-proposition counterexample is a unit state. -/
theorem counterexample_unit_state : IsIsometry (ketArrow (ZBasis 2 0)) :=
  (isIsometry_ketArrow_iff _).2 ((ZBasis 2).orthonormal.norm_eq_one 0)

/-- The complete effects in the printed-proposition example do not normalize probabilities. -/
theorem counterexample_probability_sum_ne_one :
    (∑ i : Fin 2, probability (ketArrow (ZBasis 2 0)) (counterexampleEffect i)) ≠ 1 := by
  intro h
  have hsum := counterexample_probability_sum
  rw [h, map_one] at hsum
  norm_num at hsum

/-- The overlapping effects fail disjointness, consistently with the corrected Born rule. -/
theorem counterexample_not_disjoint : ¬ Effect.Disjoint counterexampleEffect := by
  intro hx
  let : IsIsometry (ketArrow (ZBasis 2 0)) := counterexample_unit_state
  apply counterexample_probability_sum_ne_one
  exact Effect.sum_probability_eq_one_of_complete_disjoint_bicone
    (sumBicone (fun _ : Fin 2 ↦ 𝟙_ QuditCat)) (sumBiconeIsBilimit _)
    counterexampleEffect counterexample_complete hx (ketArrow (ZBasis 2 0))

/-- The Hadamard gate sends `|0⟩` to the equal superposition state. -/
theorem hadamard_zero_apply :
    Qubit.H.asHom.hom (ZBasis 2 0) =
      ((√2)⁻¹ : ℂ) • (ZBasis 2 0 + ZBasis 2 1) := by
  change (Matrix.toLin (ZBasis 2).toBasis (ZBasis 2).toBasis
    (((√2)⁻¹ : ℂ) • !![1, 1; 1, -1])) ((ZBasis 2).toBasis 0) = _
  rw [Matrix.toLin_self]
  simp [Fin.sum_univ_two, smul_add]

/-- The state obtained by applying Hadamard to the computational `|0⟩`. -/
def hadamardZero : Qubit.state := Qubit.H.asHom.hom (ZBasis 2 0)

/-- Hadamard produces a unit state, hence the abstract Born rule applies. -/
theorem hadamard_zero_unit : ‖hadamardZero‖ = 1 := by
  simp [hadamardZero, (ZBasis 2).orthonormal.norm_eq_one]

/-- The Hadamard state gives normalized probabilities in the computational basis. -/
theorem hadamard_zero_probability_sum :
    ∑ i : Fin 2, probability (ketArrow hadamardZero) (braArrow (ZBasis 2 i)) = 1 :=
  sum_probability_orthonormalBasis (ZBasis 2) hadamardZero hadamard_zero_unit

/-- Each computational-basis outcome of the Hadamard state has probability `1/2`. -/
theorem hadamard_zero_probability (i : Fin 2) :
    scalarRingEquiv (probability (ketArrow hadamardZero) (braArrow (ZBasis 2 i))) =
      (1 / 2 : ℂ) := by
  rw [scalarRingEquiv_probability_ketArrow_braArrow, hadamardZero,
    hadamard_zero_apply]
  fin_cases i <;> simp [inner_smul_right, inner_add_right, ← Complex.ofReal_pow]

end

end QuditCat
