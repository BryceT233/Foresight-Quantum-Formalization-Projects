/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.Table

/-!
# Homogeneous terms of symmetric BCH

The cubic commutator and the quintic and septic ordered-word tables give the homogeneous
corrections for the symmetric product `exp (a/2) * exp b * exp (a/2)`. Rational coefficients are
interpreted in an arbitrary rational algebra, and every product retains its word order.

## Main definitions

* `symmetricBchCubicTerm`: the cubic Strang correction.
* `symmetricBchQuinticTermTable`: the thirty quintic integer numerators.
* `symmetricBchQuinticTerm`: the quintic Strang correction with denominator `5760`.
* `symmetricBchSepticTermTable`: the 126 septic integer numerators.
* `symmetricBchSepticTerm`: the septic Strang correction with denominator `967680`.

## Main results

* `symmetricBchCubicTerm_smul`, `symmetricBchQuinticTerm_smul`,
  `symmetricBchSepticTerm_smul`: homogeneity.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

/-- The cubic correction `-(1/24)[a,[a,b]] + (1/12)[b,[b,a]]` of symmetric BCH. -/
def symmetricBchCubicTerm {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) : A :=
  -((24 : ℚ)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)) +
    (12 : ℚ)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)

/-- The thirty ordered-word numerators of the quintic symmetric BCH correction.
Every word has length five; the common denominator is `5760`. -/
def symmetricBchQuinticTermTable : WordTable.Table (Fin 2) :=
  [
    ([0, 0, 0, 0, 1], 7),
    ([0, 0, 0, 1, 0], -28),
    ([0, 0, 0, 1, 1], -28),
    ([0, 0, 1, 0, 0], 42),
    ([0, 0, 1, 0, 1], 72),
    ([0, 0, 1, 1, 0], 12),
    ([0, 0, 1, 1, 1], 32),
    ([0, 1, 0, 0, 0], -28),
    ([0, 1, 0, 0, 1], -48),
    ([0, 1, 0, 1, 0], -48),
    ([0, 1, 0, 1, 1], -48),
    ([0, 1, 1, 0, 0], 12),
    ([0, 1, 1, 0, 1], -48),
    ([0, 1, 1, 1, 0], 32),
    ([0, 1, 1, 1, 1], -8),
    ([1, 0, 0, 0, 0], 7),
    ([1, 0, 0, 0, 1], 32),
    ([1, 0, 0, 1, 0], -48),
    ([1, 0, 0, 1, 1], -48),
    ([1, 0, 1, 0, 0], 72),
    ([1, 0, 1, 0, 1], 192),
    ([1, 0, 1, 1, 0], -48),
    ([1, 0, 1, 1, 1], 32),
    ([1, 1, 0, 0, 0], -28),
    ([1, 1, 0, 0, 1], -48),
    ([1, 1, 0, 1, 0], -48),
    ([1, 1, 0, 1, 1], -48),
    ([1, 1, 1, 0, 0], 32),
    ([1, 1, 1, 0, 1], 32),
    ([1, 1, 1, 1, 0], -8)]

/-- The quintic correction of symmetric BCH, evaluated from its ordered-word table. -/
def symmetricBchQuinticTerm {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) : A :=
  (5760 : ℚ)⁻¹ • WordTable.eval 1 ![a, b] symmetricBchQuinticTermTable

/-- Every word of the quintic symmetric BCH table has length five. -/
theorem symmetricBchQuinticTermTable_length (p : List (Fin 2) × ℤ)
    (hp : p ∈ symmetricBchQuinticTermTable) : p.1.length = 5 := by
  have hall : symmetricBchQuinticTermTable.all (fun q ↦ q.1.length == 5) = true := by decide
  simpa only [beq_iff_eq] using List.all_eq_true.mp hall p hp

/-- **Homogeneity of the quintic symmetric BCH correction.** -/
theorem symmetricBchQuinticTerm_smul {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra ℚ A] [Algebra R A] (a b : A) (c : R) :
    symmetricBchQuinticTerm (c • a) (c • b) = c ^ 5 • symmetricBchQuinticTerm a b := by
  have hletters : (![c • a, c • b] : Fin 2 → A) = fun i ↦ c • (![a, b] : Fin 2 → A) i := by
    funext i
    fin_cases i <;> rfl
  simp only [symmetricBchQuinticTerm, hletters]
  rw [WordTable.eval_smul_of_length _ _ _ 5 symmetricBchQuinticTermTable_length, smul_comm]

/-- **Homogeneity of the cubic symmetric BCH correction.** -/
theorem symmetricBchCubicTerm_smul {R A : Type*} [CommSemiring R] [Ring A]
    [Algebra ℚ A] [Algebra R A] (a b : A) (c : R) :
    symmetricBchCubicTerm (c • a) (c • b) = c ^ 3 • symmetricBchCubicTerm a b := by
  have triple (x y z : A) :
      (c • x) * ((c • y) * (c • z)) = c ^ 3 • (x * (y * z)) := by
    simp only [smul_mul_smul_comm]
    congr 1
    ring
  have triple' (x y z : A) :
      ((c • x) * (c • y)) * (c • z) = c ^ 3 • ((x * y) * z) := by
    simp only [smul_mul_smul_comm]
    congr 1
    ring
  simp only [symmetricBchCubicTerm, mul_sub, sub_mul, triple, triple', ← smul_sub,
    smul_comm (c ^ 3), smul_add, smul_neg]

/-- The 126 ordered-word numerators of the septic symmetric BCH correction.
Every word has length seven; the common denominator is `967680`. -/
def symmetricBchSepticTermTable : WordTable.Table (Fin 2) :=
  [
    ([0, 0, 0, 0, 0, 0, 1], -31),
    ([0, 0, 0, 0, 0, 1, 0], 186),
    ([0, 0, 0, 0, 0, 1, 1], 186),
    ([0, 0, 0, 0, 1, 0, 0], -465),
    ([0, 0, 0, 0, 1, 0, 1], -612),
    ([0, 0, 0, 0, 1, 1, 0], -318),
    ([0, 0, 0, 0, 1, 1, 1], -416),
    ([0, 0, 0, 1, 0, 0, 0], 620),
    ([0, 0, 0, 1, 0, 0, 1], 816),
    ([0, 0, 0, 1, 0, 1, 0], 816),
    ([0, 0, 0, 1, 0, 1, 1], 816),
    ([0, 0, 0, 1, 1, 0, 0], 228),
    ([0, 0, 0, 1, 1, 0, 1], 816),
    ([0, 0, 0, 1, 1, 1, 0], 32),
    ([0, 0, 0, 1, 1, 1, 1], 424),
    ([0, 0, 1, 0, 0, 0, 0], -465),
    ([0, 0, 1, 0, 0, 0, 1], -864),
    ([0, 0, 1, 0, 0, 1, 0], 144),
    ([0, 0, 1, 0, 0, 1, 1], 144),
    ([0, 0, 1, 0, 1, 0, 0], -1368),
    ([0, 0, 1, 0, 1, 0, 1], -2880),
    ([0, 0, 1, 0, 1, 1, 0], 144),
    ([0, 0, 1, 0, 1, 1, 1], -864),
    ([0, 0, 1, 1, 0, 0, 0], 228),
    ([0, 0, 1, 1, 0, 0, 1], 144),
    ([0, 0, 1, 1, 0, 1, 0], 144),
    ([0, 0, 1, 1, 0, 1, 1], 144),
    ([0, 0, 1, 1, 1, 0, 0], -192),
    ([0, 0, 1, 1, 1, 0, 1], -864),
    ([0, 0, 1, 1, 1, 1, 0], 312),
    ([0, 0, 1, 1, 1, 1, 1], -192),
    ([0, 1, 0, 0, 0, 0, 0], 186),
    ([0, 1, 0, 0, 0, 0, 1], 480),
    ([0, 1, 0, 0, 0, 1, 0], -192),
    ([0, 1, 0, 0, 0, 1, 1], -192),
    ([0, 1, 0, 0, 1, 0, 0], 144),
    ([0, 1, 0, 0, 1, 0, 1], 1152),
    ([0, 1, 0, 0, 1, 1, 0], -864),
    ([0, 1, 0, 0, 1, 1, 1], -192),
    ([0, 1, 0, 1, 0, 0, 0], 816),
    ([0, 1, 0, 1, 0, 0, 1], 1152),
    ([0, 1, 0, 1, 0, 1, 0], 1152),
    ([0, 1, 0, 1, 0, 1, 1], 1152),
    ([0, 1, 0, 1, 1, 0, 0], 144),
    ([0, 1, 0, 1, 1, 0, 1], 1152),
    ([0, 1, 0, 1, 1, 1, 0], -192),
    ([0, 1, 0, 1, 1, 1, 1], 480),
    ([0, 1, 1, 0, 0, 0, 0], -318),
    ([0, 1, 1, 0, 0, 0, 1], -192),
    ([0, 1, 1, 0, 0, 1, 0], -864),
    ([0, 1, 1, 0, 0, 1, 1], -864),
    ([0, 1, 1, 0, 1, 0, 0], 144),
    ([0, 1, 1, 0, 1, 0, 1], 1152),
    ([0, 1, 1, 0, 1, 1, 0], -864),
    ([0, 1, 1, 0, 1, 1, 1], -192),
    ([0, 1, 1, 1, 0, 0, 0], 32),
    ([0, 1, 1, 1, 0, 0, 1], -192),
    ([0, 1, 1, 1, 0, 1, 0], -192),
    ([0, 1, 1, 1, 0, 1, 1], -192),
    ([0, 1, 1, 1, 1, 0, 0], 312),
    ([0, 1, 1, 1, 1, 0, 1], 480),
    ([0, 1, 1, 1, 1, 1, 0], -192),
    ([0, 1, 1, 1, 1, 1, 1], 32),
    ([1, 0, 0, 0, 0, 0, 0], -31),
    ([1, 0, 0, 0, 0, 0, 1], -192),
    ([1, 0, 0, 0, 0, 1, 0], 480),
    ([1, 0, 0, 0, 0, 1, 1], 480),
    ([1, 0, 0, 0, 1, 0, 0], -864),
    ([1, 0, 0, 0, 1, 0, 1], -1536),
    ([1, 0, 0, 0, 1, 1, 0], -192),
    ([1, 0, 0, 0, 1, 1, 1], -640),
    ([1, 0, 0, 1, 0, 0, 0], 816),
    ([1, 0, 0, 1, 0, 0, 1], 1152),
    ([1, 0, 0, 1, 0, 1, 0], 1152),
    ([1, 0, 0, 1, 0, 1, 1], 1152),
    ([1, 0, 0, 1, 1, 0, 0], 144),
    ([1, 0, 0, 1, 1, 0, 1], 1152),
    ([1, 0, 0, 1, 1, 1, 0], -192),
    ([1, 0, 0, 1, 1, 1, 1], 480),
    ([1, 0, 1, 0, 0, 0, 0], -612),
    ([1, 0, 1, 0, 0, 0, 1], -1536),
    ([1, 0, 1, 0, 0, 1, 0], 1152),
    ([1, 0, 1, 0, 0, 1, 1], 1152),
    ([1, 0, 1, 0, 1, 0, 0], -2880),
    ([1, 0, 1, 0, 1, 0, 1], -6912),
    ([1, 0, 1, 0, 1, 1, 0], 1152),
    ([1, 0, 1, 0, 1, 1, 1], -1536),
    ([1, 0, 1, 1, 0, 0, 0], 816),
    ([1, 0, 1, 1, 0, 0, 1], 1152),
    ([1, 0, 1, 1, 0, 1, 0], 1152),
    ([1, 0, 1, 1, 0, 1, 1], 1152),
    ([1, 0, 1, 1, 1, 0, 0], -864),
    ([1, 0, 1, 1, 1, 0, 1], -1536),
    ([1, 0, 1, 1, 1, 1, 0], 480),
    ([1, 0, 1, 1, 1, 1, 1], -192),
    ([1, 1, 0, 0, 0, 0, 0], 186),
    ([1, 1, 0, 0, 0, 0, 1], 480),
    ([1, 1, 0, 0, 0, 1, 0], -192),
    ([1, 1, 0, 0, 0, 1, 1], -192),
    ([1, 1, 0, 0, 1, 0, 0], 144),
    ([1, 1, 0, 0, 1, 0, 1], 1152),
    ([1, 1, 0, 0, 1, 1, 0], -864),
    ([1, 1, 0, 0, 1, 1, 1], -192),
    ([1, 1, 0, 1, 0, 0, 0], 816),
    ([1, 1, 0, 1, 0, 0, 1], 1152),
    ([1, 1, 0, 1, 0, 1, 0], 1152),
    ([1, 1, 0, 1, 0, 1, 1], 1152),
    ([1, 1, 0, 1, 1, 0, 0], 144),
    ([1, 1, 0, 1, 1, 0, 1], 1152),
    ([1, 1, 0, 1, 1, 1, 0], -192),
    ([1, 1, 0, 1, 1, 1, 1], 480),
    ([1, 1, 1, 0, 0, 0, 0], -416),
    ([1, 1, 1, 0, 0, 0, 1], -640),
    ([1, 1, 1, 0, 0, 1, 0], -192),
    ([1, 1, 1, 0, 0, 1, 1], -192),
    ([1, 1, 1, 0, 1, 0, 0], -864),
    ([1, 1, 1, 0, 1, 0, 1], -1536),
    ([1, 1, 1, 0, 1, 1, 0], -192),
    ([1, 1, 1, 0, 1, 1, 1], -640),
    ([1, 1, 1, 1, 0, 0, 0], 424),
    ([1, 1, 1, 1, 0, 0, 1], 480),
    ([1, 1, 1, 1, 0, 1, 0], 480),
    ([1, 1, 1, 1, 0, 1, 1], 480),
    ([1, 1, 1, 1, 1, 0, 0], -192),
    ([1, 1, 1, 1, 1, 0, 1], -192),
    ([1, 1, 1, 1, 1, 1, 0], 32)]

/-- Every word of the septic symmetric BCH table has length seven. -/
theorem symmetricBchSepticTermTable_length (p : List (Fin 2) × ℤ)
    (hp : p ∈ symmetricBchSepticTermTable) : p.1.length = 7 := by
  have hall : symmetricBchSepticTermTable.all (fun q ↦ q.1.length == 7) = true := by decide
  simpa only [beq_iff_eq] using List.all_eq_true.mp hall p hp

/-- The septic correction of symmetric BCH, evaluated from its ordered-word table. -/
def symmetricBchSepticTerm {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) : A :=
  (967680 : ℚ)⁻¹ • WordTable.eval 1 ![a, b] symmetricBchSepticTermTable

/-- **Homogeneity of the septic symmetric BCH correction.** -/
theorem symmetricBchSepticTerm_smul {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra ℚ A] [Algebra R A] (a b : A) (c : R) :
    symmetricBchSepticTerm (c • a) (c • b) = c ^ 7 • symmetricBchSepticTerm a b := by
  have hletters : (![c • a, c • b] : Fin 2 → A) = fun i ↦ c • (![a, b] : Fin 2 → A) i := by
    funext i
    fin_cases i <;> rfl
  simp only [symmetricBchSepticTerm, hletters]
  rw [WordTable.eval_smul_of_length _ _ _ 7 symmetricBchSepticTermTable_length, smul_comm]

end FQFP.BCH
