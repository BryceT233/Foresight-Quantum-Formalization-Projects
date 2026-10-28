/-
Prove2Me definition bundle for the TrotterError milestone nodes.

The def/structure layer needed by the target's formal_statement, so that
the statement compiles standalone. Generated from the FQFP TrotterError
development; source spans are taken verbatim.

Source: https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects/tree/d6bfac12d15bc59fcc5f90206ac3312da602eb3d
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Multinomial

namespace TrotterError

-- TrotterError.ProductFormulaData
/-- The data of a general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` (`eq:pf`): `Υ` stages, `Γ` summands, real coefficients
`a_{(υ,γ)}` uniformly bounded by `1` in absolute value, and per-stage permutations
`π_υ`. -/
structure ProductFormulaData (Υ Γ : ℕ) where
  /-- Real coefficients `a_{(υ,γ)}`. -/
  coeff : Fin Υ × Fin Γ → ℝ
  /-- Permutation `π_υ` of the summands within stage `υ`. -/
  perm : Fin Υ → Equiv.Perm (Fin Γ)
  /-- The coefficients are uniformly bounded by `1` in absolute value. -/
  coeff_abs_le_one : ∀ i : Fin Υ × Fin Γ, |coeff i| ≤ 1
open ProductFormulaData

variable {Υ Γ : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸]
variable (P : ProductFormulaData Υ Γ)
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open NormedSpace Finset
open scoped Topology
open Finset LieAlgebra
open scoped algebraMap
attribute [local instance] LieRing.ofAssociativeRing
open NormedSpace MeasureTheory
open scoped ContDiff algebraMap
open NormedSpace Finset LieAlgebra MeasureTheory
open scoped BigOperators algebraMap
open NormedSpace
open scoped Topology BigOperators Interval
open NormedSpace MeasureTheory Finset
open scoped Topology ContDiff
open Asymptotics
open scoped Topology ContDiff algebraMap

/-! #### from FQFP.TrotterError.ProductFormula -/

namespace ProductFormulaData


-- TrotterError.ProductFormulaData.evalIndexList
/-- The flattened list of factor indices `(υ, γ)`, in `eval`'s product order: the outer `Υ`-layer
runs right-to-left and, within each stage, the inner `Γ`-layer runs right-to-left. -/
def evalIndexList (Υ Γ : ℕ) : List (Fin Υ × Fin Γ) :=
  List.product (List.finRange Υ).reverse (List.finRange Γ).reverse

-- TrotterError.ProductFormulaData.generator
/-- The `(υ,γ)`-th generator `a_{(υ,γ)} H_{π_υ(γ)}`: the coefficient-scaled, permuted summand. -/
noncomputable def generator {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) : 𝔸 :=
  P.coeff i • H (P.perm i.1 i.2)

-- TrotterError.ProductFormulaData.evalFactor
/-- The `(υ, γ)`-th factor `e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of the product formula. -/
noncomputable def evalFactor {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸 :=
  exp (t • P.generator H i)

-- TrotterError.ProductFormulaData.eval
/-- The product formula `𝒮(t)` evaluated on summands `H` at time `t`. The product
is taken in the paper's right-to-left order `∏_{γ=1}^{Γ} A_γ = A_Γ ⋯ A_1`. -/
noncomputable def eval {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ((evalIndexList Υ Γ).map (fun i => P.evalFactor H i t)).prod

-- TrotterError.ProductFormulaData.derivProd
/-- The ordered product in `𝔸` of the `(υ, γ)`-factors `A^{q} * exp (r • A)` in `eval`'s order. -/
noncomputable def derivProd {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (q : Fin Υ × Fin Γ → ℕ) (t : ℝ) : 𝔸 :=
  (((List.finRange Υ).reverse).map (fun υ : Fin Υ =>
    (((List.finRange Γ).reverse).map (fun γ : Fin Γ =>
      ((P.generator H (υ, γ)) ^ (q (υ, γ))) *
        exp ((t * P.coeff (υ, γ)) • H (P.perm υ γ)))).prod)).prod
end ProductFormulaData


/-! #### from FQFP.TrotterError.Commutator -/


-- TrotterError.adPow
/-- The `q`-fold iterated adjoint `ad_A^q = (ad A)^q`, as an ℝ-linear endomorphism of `𝔸`. -/
abbrev adPow {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (q : ℕ) : Module.End ℝ 𝔸 :=
  (ad ℝ 𝔸 A) ^ q

-- TrotterError.adSequence
/-- The iterated `ad` over a sequence of operators with multiplicities,
`ad_{A ⟨s-1⟩}^{q ⟨s-1⟩} ⋯ ad_{A ⟨0⟩}^{q ⟨0⟩}(B)`, where `A ⟨0⟩` is applied first
(innermost) and `A ⟨s-1⟩` is applied last (outermost). -/
def adSequence {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) : 𝔸 :=
  match s with
  | 0 => B
  | s + 1 =>
      adPow (A (Fin.last s)) (q (Fin.last s))
        (adSequence (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc) B)

-- TrotterError.αCommConj
/-- The paper's `α_comm(A_s, …, A_1, B)`: the multinomial-weighted sum
`Σ_{q₁+⋯+q_s = p} (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`. -/
noncomputable def αCommConj {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ q ∈ Finset.finAntidiagonal s p,
    (Nat.multinomial (Finset.univ : Finset (Fin s)) q : ℝ) * ‖adSequence A q B‖

/-! #### from FQFP.TrotterError.ExpSMulConj -/


-- TrotterError.expSMulConj
/-- Single conjugation `e^{τA} X e^{-τA} = exp (τ • A) * X * exp ((-τ) • A)`. -/
noncomputable def expSMulConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (τ : ℝ) : 𝔸 :=
  exp (τ • A) * X * exp ((-τ) • A)

-- TrotterError.expSMulConjLin
/-- The single conjugation `expSMulConj A · τ` as an ℝ-linear endomorphism of `𝔸`. -/
noncomputable def expSMulConjLin {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (A : 𝔸)
    (τ : ℝ) : 𝔸 →ₗ[ℝ] 𝔸 where
  toFun := fun X => expSMulConj A X τ
  map_add' _ _ := by unfold expSMulConj; noncomm_ring
  map_smul' _ _ := by simp [expSMulConj]

/-! #### from FQFP.TrotterError.Prefactor -/


-- TrotterError.upperSum
/-- `upperSum K j` is the sum of `K γ` over `γ > j` (the paper's `Σ_{γ₂ = γ₁+1}^Γ H_{γ₂}`). -/
abbrev upperSum {𝔸 : Type*} [AddCommMonoid 𝔸] {Γ : ℕ} (K : Fin Γ → 𝔸) (j : Fin Γ) :
    𝔸 := Finset.sum (univ.filter (fun γ => j < γ)) (fun γ => K γ)

-- TrotterError.secondOrderKernel
/-- The second-order kernel `𝒯₂(τ)` of prefactor.tex:60, anti-Hermitian-generator form:
`e^{τB} (A/2) e^{-τB} - A/2 - e^{-(τ/2)A} B e^{(τ/2)A} + B`. -/
noncomputable def secondOrderKernel {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A B : 𝔸) (τ : ℝ) : 𝔸 :=
  expSMulConj B ((1 / 2 : ℝ) • A) τ - (1 / 2 : ℝ) • A -
    expSMulConj A B (-(τ / 2)) + B

/-! #### from FQFP.TrotterError.Suzuki -/


-- TrotterError.lieTrotter
/-- The first-order Lie-Trotter formula `∏_{γ=1}^Γ e^{t K_γ} = e^{t K_{Γ-1}} ⋯ e^{t K_0}` (the
paper's `∏_{γ=1}^Γ A_γ = A_Γ ⋯ A_1` convention, in 0-based `Fin Γ`), defined by peeling the
innermost (rightmost) factor `K 0`. -/
noncomputable def lieTrotter {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    {Γ : ℕ} (K : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  match Γ with
  | 0 => 1
  | n + 1 => lieTrotter (fun i : Fin n => K i.succ) t * exp (t • K 0)

-- TrotterError.suzuki2
/-- The second-order Suzuki formula, defined recursively by peeling the outermost (index-`0`)
factor: `S₂(K, t) = e^{(t/2)K₀} · S₂(K ∘ Fin.succ, t) · e^{(t/2)K₀}`. This is the ordered product
`e^{(t/2)K₀} ⋯ e^{(t/2)K_{Γ-1}} · e^{(t/2)K_{Γ-1}} ⋯ e^{(t/2)K₀}` (the paper's
`∏_{γ=Γ}^1 e^{(t/2)K_γ} · ∏_{γ=1}^Γ e^{(t/2)K_γ}`, in anti-Hermitian-generator form). -/
noncomputable def suzuki2 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {Γ : ℕ} (K : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  match Γ with
  | 0 => 1
  | n + 1 => exp ((t / 2) • K 0) * suzuki2 (fun i : Fin n => K i.succ) t * exp ((t / 2) • K 0)

/-! #### from FQFP.TrotterError.TimeOrderedExp -/


-- TrotterError.dysonTerm
/-- The `n`-th term of the Dyson (Neumann/Picard) series for the time-ordered exponential:
`D₀ = 1` and `D_{n+1}(t) = ∫ τ in t₁..t, H τ * D_n τ`. The interval integral is oriented,
so this is defined for every `t : ℝ` (not only `t ≥ t₁`). -/
noncomputable def dysonTerm (H : ℝ → 𝔸) (t₁ : ℝ) : ℕ → ℝ → 𝔸
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ τ in t₁..t, H τ * dysonTerm H t₁ n τ

-- TrotterError.timeOrderedExp
/-- The time-ordered exponential `exp_T(∫_{t₁}^{t₂} H(τ) dτ)`, defined for a continuous
generator `H` as the sum of the Dyson series. For `t₁ ≤ t₂` this is the unique solution of
`U' = H·U`, `U(t₁) = 1`; for `t₂ < t₁` it is the inverse evolution (a theorem, not
built into the definition). -/
noncomputable def timeOrderedExp (H : ℝ → 𝔸) (t₁ t₂ : ℝ) : 𝔸 :=
  ∑' n : ℕ, dysonTerm H t₁ n t₂

/-! #### from FQFP.TrotterError.CommutatorExpansion -/


-- TrotterError.multiConj
/-- The multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA₀} B e^{-τA₀}⋯e^{-τA_{s-1}}`, where
`A ⟨0⟩` is innermost (the paper's `A₁`, applied first) and `A ⟨s-1⟩` is outermost (the paper's
`A_s`). -/
noncomputable def multiConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) : 𝔸 :=
  (List.ofFn (fun i : Fin s => exp (τ • A i))).reverse.prod * B *
    (List.ofFn (fun i : Fin s => exp (-τ • A i))).prod

-- TrotterError.commutatorRemainderTerm
/-- The single `(j, q)` summand of `commutatorRemainder`. -/
@[irreducible]
noncomputable def commutatorRemainderTerm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) : 𝔸 :=
  ((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod *
    (∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
      expSMulConj (A j) (adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B) u) *
    ((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod

-- TrotterError.commutatorRemainder
/-- The operator-valued remainder `𝒞(τ)` of `thm:comm_exp_conj` (theory.tex:229-235). The outer
sum runs over 0-based layer indices `j : Fin s` with `k := j + 1` the 1-based index of the paper,
so `A j` is `A_k`, the antidiagonal condition `q₁ + ⋯ + q_k = p` is `q ∈ finAntidiagonal (j + 1) p`
with `q (Fin.last j) = q_k`, and `q_k ≠ 0` is `q (Fin.last j) ≠ 0`. The `ad` sequence is
`adSequence (A ∘ Fin.castLE …) q B = ad_{A_k}^{q_k} ⋯ ad_{A₁}^{q₁}(B)`. -/
noncomputable def commutatorRemainder {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : 𝔸 :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    commutatorRemainderTerm A B τ j q

-- TrotterError.conjCoeff
/-- The `τ^j` coefficient of the multi-layer conjugation, as the multinomial-weighted sum
`Σ_{q ∈ finAntidiagonal s j} (∏ i, q_i!⁻¹) • adSequence A q B`. -/
noncomputable def conjCoeff {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (j : ℕ) : 𝔸 :=
  ∑ q ∈ finAntidiagonal s j,
    ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A q B

-- TrotterError.layerSum
/-- The layer-by-layer sum of multinomial-weighted `adSequence` norms appearing in the bound of
`commutatorRemainder`, summed over the 1-based layers `1..s`. -/
noncomputable def layerSum {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖

/-! #### from FQFP.TrotterError.ErrorTypes -/


-- TrotterError.factorProdOver
/-- The ordered product `∏_{j ∈ l} e^{s a_j H_j}` of the product-formula factors over a sublist `l`
of `evalIndexList`. -/
noncomputable def factorProdOver {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (s : ℝ) (l : List (Fin Υ × Fin Γ)) : 𝔸 :=
  (l.map (fun j => P.evalFactor H j s)).prod

-- TrotterError.prefixFactorProd
/-- `∏_{j ≻ i}^{←} e^{t a_j H_j}`, the product of the factors strictly before `i`. -/
noncomputable def prefixFactorProd {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸 :=
  factorProdOver P H t ((evalIndexList Υ Γ).take ((evalIndexList Υ Γ).idxOf i))

-- TrotterError.strictSuffixFactorProd
/-- `∏_{j ≺ i}^{←} e^{t a_j H_j}`, the product of the factors strictly after `i`. -/
noncomputable def strictSuffixFactorProd {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸 :=
  factorProdOver P H t ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1))

-- TrotterError.suffixFactorProd
/-- `∏_{j ≤ i}^{←} e^{t a_j H_j}`, the product of the factor `i` and everything after it. -/
noncomputable abbrev suffixFactorProd {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸 :=
  P.evalFactor H i t * strictSuffixFactorProd P H i t

-- TrotterError.invPrefixFactorProd
/-- `∏_{j ≻ i}^{→} e^{-t a_j H_j}`, the inverse of `prefixFactorProd`. -/
noncomputable def invPrefixFactorProd {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸 :=
  factorProdOver P H (-t) (((evalIndexList Υ Γ).take ((evalIndexList Υ Γ).idxOf i)).reverse)

-- TrotterError.invStrictSuffixFactorProd
/-- `∏_{j ≺ i}^{→} e^{-t a_j H_j}`, the inverse of `strictSuffixFactorProd`. -/
noncomputable def invStrictSuffixFactorProd {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸 :=
  factorProdOver P H (-t) (((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).reverse)

-- TrotterError.posDerivSum
/-- The position-indexed derivative sum of the product formula. -/
noncomputable def posDerivSum {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ∑ k : Fin (evalIndexList Υ Γ).length,
    (((evalIndexList Υ Γ).take (k : ℕ)).map (fun i => P.evalFactor H i t)).prod
      * ((P.generator H ((evalIndexList Υ Γ).get k)) *
        P.evalFactor H ((evalIndexList Υ Γ).get k) t)
      * (((evalIndexList Υ Γ).drop ((k : ℕ) + 1)).map (fun i => P.evalFactor H i t)).prod

-- TrotterError.evalDeriv
/-- The factor-indexed derivative of `P.eval H` at time `t` (the paper's `d/dt 𝒮`). -/
noncomputable def evalDeriv {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ∑ i : Fin Υ × Fin Γ,
    prefixFactorProd P H i t * (P.generator H i) * suffixFactorProd P H i t

-- TrotterError.additiveResidual
/-- The additive residual `ℛ(t)` of `type.tex:17-20`: `ℛ(t) = 𝒮'(t) - H·𝒮(t)`, so that
`d/dt 𝒮 = H·𝒮 + ℛ` (`type.tex:12`). -/
noncomputable def additiveResidual {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  evalDeriv P H t - (∑ γ, H γ) * P.eval H t

-- TrotterError.exponentiatedGenerator
/-- The exponentiated generator `ℱ(t)` of `type.tex:54`. -/
noncomputable def exponentiatedGenerator {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ∑ i : Fin Υ × Fin Γ, prefixFactorProd P H i t * P.generator H i * invPrefixFactorProd P H i t

-- TrotterError.additiveKernel
/-- The additive kernel `𝒯(τ)` of `type.tex:33-35`. -/
noncomputable def additiveKernel {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (H : Fin Γ → 𝔸) :
    ℝ → 𝔸 :=
  fun τ => (∑ i : Fin Υ × Fin Γ, invStrictSuffixFactorProd P H i τ *
    P.generator H i * strictSuffixFactorProd P H i τ)
  - factorProdOver P H (-τ) ((evalIndexList Υ Γ).reverse) * (∑ γ, H γ) *
    factorProdOver P H τ (evalIndexList Υ Γ)

-- TrotterError.exponentiatedError
/-- The exponentiated error `ℰ(τ) = ℱ(τ) - H` of `type.tex:62`. -/
noncomputable def exponentiatedError {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    (H : Fin Γ → 𝔸) : ℝ → 𝔸 :=
  fun τ => exponentiatedGenerator P H τ - (∑ γ, H γ)

-- TrotterError.interactionGenerator
/-- The interaction-picture generator `τ ↦ e^{-τH} ℰ(τ) e^{τH}` used in `multiplicativeError`. -/
noncomputable def interactionGenerator {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    (H : Fin Γ → 𝔸) : ℝ → 𝔸 :=
  fun τ => exp ((-τ) • (∑ γ, H γ)) * exponentiatedError P H τ * exp (τ • (∑ γ, H γ))

-- TrotterError.multiplicativeError
/-- The multiplicative error `ℳ(t)` of `type.tex:72`. -/
noncomputable def multiplicativeError {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  timeOrderedExp (interactionGenerator P H) 0 t - 1

/-! #### from FQFP.TrotterError.OrderCondition -/

namespace ProductFormulaData


-- TrotterError.ProductFormulaData.IsOrderOf
/-- `P` is a `p`-th order formula on summands `H` if `‖𝒮(t) − e^{tH}‖ = O(t^{p+1})`
as `t → 0` (`prelim.tex:150`). -/
def IsOrderOf {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (p : ℕ) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) : Prop :=
  (fun t : ℝ => ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖)
    =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1))
end ProductFormulaData


end TrotterError
