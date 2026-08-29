import FibonacciRibbonKernel.ExteriorElementary
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases
import Mathlib.GroupTheory.Perm.Fin

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R : Type*} [CommRing R]

abbrev FourRow (R : Type*) [CommRing R] := Fin 4 → R

noncomputable def topFourAlternating (degree : ℕ) :
    FourRow R [⋀^Fin degree]→ₗ[R] R := by
  classical
  by_cases hdegree : degree = 4
  · subst degree
    exact Matrix.detRowAlternating
  · exact 0

noncomputable def topFourDeterminant :
    ExteriorAlgebra R (FourRow R) →ₗ[R] R :=
  ExteriorAlgebra.liftAlternating (topFourAlternating (R := R))

theorem topFourDeterminant_iMulti (rows : Fin 4 → FourRow R) :
    topFourDeterminant (R := R) (ExteriorAlgebra.ιMulti R 4 rows) =
      Matrix.det rows := by
  rw [topFourDeterminant,
    ExteriorAlgebra.liftAlternating_apply_ιMulti]
  change Matrix.detRowAlternating rows = Matrix.det rows
  rfl

@[simp] theorem topFourDeterminant_iota_product
    (first second third fourth : FourRow R) :
    topFourDeterminant (R := R)
        (ExteriorAlgebra.ι R first *
          (ExteriorAlgebra.ι R second *
            (ExteriorAlgebra.ι R third * ExteriorAlgebra.ι R fourth))) =
      Matrix.det ![first, second, third, fourth] := by
  have h := topFourDeterminant_iMulti (R := R)
    ![first, second, third, fourth]
  simpa [ExteriorAlgebra.ιMulti_apply] using h

noncomputable def fourBasisVector (index : Fin 4) : FourRow R :=
  (Pi.basisFun R (Fin 4)) index

noncomputable def fourOneForm (coordinates : FourRow R) :
    ExteriorAlgebra R (FourRow R) :=
  coordinates 0 • ExteriorAlgebra.ι R (fourBasisVector 0) +
    coordinates 1 • ExteriorAlgebra.ι R (fourBasisVector 1) +
    coordinates 2 • ExteriorAlgebra.ι R (fourBasisVector 2) +
    coordinates 3 • ExteriorAlgebra.ι R (fourBasisVector 3)

noncomputable def fourTwoForm (coordinates : Fin 4 → Fin 4 → R) :
    ExteriorAlgebra R (FourRow R) :=
  coordinates 0 1 • (ExteriorAlgebra.ι R (fourBasisVector 0) *
      ExteriorAlgebra.ι R (fourBasisVector 1)) +
  coordinates 0 2 • (ExteriorAlgebra.ι R (fourBasisVector 0) *
      ExteriorAlgebra.ι R (fourBasisVector 2)) +
  coordinates 0 3 • (ExteriorAlgebra.ι R (fourBasisVector 0) *
      ExteriorAlgebra.ι R (fourBasisVector 3)) +
  coordinates 1 2 • (ExteriorAlgebra.ι R (fourBasisVector 1) *
      ExteriorAlgebra.ι R (fourBasisVector 2)) +
  coordinates 1 3 • (ExteriorAlgebra.ι R (fourBasisVector 1) *
      ExteriorAlgebra.ι R (fourBasisVector 3)) +
  coordinates 2 3 • (ExteriorAlgebra.ι R (fourBasisVector 2) *
      ExteriorAlgebra.ι R (fourBasisVector 3))

def fourRowSum : List (FourRow R) → FourRow R
  | [] => 0
  | head :: tail => head + fourRowSum tail

def fourPairSum : List (FourRow R) → Fin 4 → Fin 4 → R
  | [], _, _ => 0
  | head :: tail, left, right =>
      head left * fourRowSum tail right -
        head right * fourRowSum tail left + fourPairSum tail left right

@[simp] theorem fourRowSum_nil : fourRowSum ([] : List (FourRow R)) = 0 := rfl
@[simp] theorem fourRowSum_cons (head : FourRow R) (tail : List (FourRow R)) :
    fourRowSum (head :: tail) = head + fourRowSum tail := rfl
@[simp] theorem fourPairSum_nil (left right : Fin 4) :
    fourPairSum ([] : List (FourRow R)) left right = 0 := rfl
@[simp] theorem fourPairSum_cons (head : FourRow R)
    (tail : List (FourRow R)) (left right : Fin 4) :
    fourPairSum (head :: tail) left right =
      head left * fourRowSum tail right - head right * fourRowSum tail left +
        fourPairSum tail left right := rfl

theorem iota_fourRow_eq_oneForm (row : FourRow R) :
    ExteriorAlgebra.ι R row = fourOneForm row := by
  have hrow : row = row 0 • fourBasisVector 0 + row 1 • fourBasisVector 1 +
      row 2 • fourBasisVector 2 + row 3 • fourBasisVector 3 := by
    funext index
    fin_cases index <;> simp [fourBasisVector]
  calc
    ExteriorAlgebra.ι R row = ExteriorAlgebra.ι R
        (row 0 • fourBasisVector 0 + row 1 • fourBasisVector 1 +
          row 2 • fourBasisVector 2 + row 3 • fourBasisVector 3) :=
      congrArg _ hrow
    _ = row 0 • ExteriorAlgebra.ι R (fourBasisVector 0) +
          row 1 • ExteriorAlgebra.ι R (fourBasisVector 1) +
          row 2 • ExteriorAlgebra.ι R (fourBasisVector 2) +
          row 3 • ExteriorAlgebra.ι R (fourBasisVector 3) := by simp
    _ = fourOneForm row := rfl

theorem fourOneForm_mul (left right : FourRow R) :
    fourOneForm left * fourOneForm right =
      fourTwoForm (fun i j => left i * right j - left j * right i) := by
  unfold fourOneForm fourTwoForm
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero,
    ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero]
  rw [iota_mul_iota_neg (R := R) (fourBasisVector 1) (fourBasisVector 0),
    iota_mul_iota_neg (R := R) (fourBasisVector 2) (fourBasisVector 0),
    iota_mul_iota_neg (R := R) (fourBasisVector 3) (fourBasisVector 0),
    iota_mul_iota_neg (R := R) (fourBasisVector 2) (fourBasisVector 1),
    iota_mul_iota_neg (R := R) (fourBasisVector 3) (fourBasisVector 1),
    iota_mul_iota_neg (R := R) (fourBasisVector 3) (fourBasisVector 2)]
  module

theorem exteriorElementary_one_eq_fourOneForm (rows : List (FourRow R)) :
    exteriorElementary (R := R) 1 rows = fourOneForm (fourRowSum rows) := by
  induction rows with
  | nil => simp [fourOneForm]
  | cons head tail ih =>
      rw [exteriorElementary_cons_one, iota_fourRow_eq_oneForm, ih]
      unfold fourOneForm
      simp only [fourRowSum_cons, Pi.add_apply, add_smul]
      module

theorem exteriorElementary_two_eq_fourTwoForm (rows : List (FourRow R)) :
    exteriorElementary (R := R) 2 rows = fourTwoForm (fourPairSum rows) := by
  induction rows with
  | nil => simp [fourTwoForm]
  | cons head tail ih =>
      rw [exteriorElementary_cons_two, iota_fourRow_eq_oneForm,
        exteriorElementary_one_eq_fourOneForm, fourOneForm_mul, ih]
      have hpair : fourPairSum (head :: tail) = fun i j =>
          head i * fourRowSum tail j - head j * fourRowSum tail i +
            fourPairSum tail i j := rfl
      rw [hpair]
      unfold fourTwoForm
      module

def pfaffianFour (pair : Fin 4 → Fin 4 → R) : R :=
  pair 0 1 * pair 2 3 - pair 0 2 * pair 1 3 + pair 0 3 * pair 1 2

noncomputable def fourInjectiveDet (rows : Fin 4 → FourRow R) : R := by
  classical
  exact if Function.Injective rows then Matrix.det rows else 0

def fourIndexSign (indices : Fin 4 → Fin 4) : ℤˣ :=
  (if indices 0 < indices 1 then 1 else -1) *
    (if indices 0 < indices 2 then 1 else -1) *
    (if indices 1 < indices 2 then 1 else -1) *
    (if indices 0 < indices 3 then 1 else -1) *
    (if indices 1 < indices 3 then 1 else -1) *
    (if indices 2 < indices 3 then 1 else -1)

noncomputable def fourPermutationOfInjective
    (indices : Fin 4 → Fin 4) (hinjective : Function.Injective indices) :
    Equiv.Perm (Fin 4) :=
  Equiv.ofBijective indices
    ((Fintype.bijective_iff_injective_and_card indices).2 ⟨hinjective, rfl⟩)

theorem det_fourBasisVector_comp_of_injective
    [Nontrivial R] (indices : Fin 4 → Fin 4)
    (hinjective : Function.Injective indices) :
    Matrix.det (fun row => fourBasisVector (R := R) (indices row)) =
      ((fourIndexSign indices : ℤ) : R) := by
  let permutation := fourPermutationOfInjective indices hinjective
  have hfun : (fun row => fourBasisVector (R := R) (indices row)) =
      fourBasisVector (R := R) ∘ permutation := by
    funext row
    rfl
  have hbasis : Matrix.det (fourBasisVector (R := R)) = (1 : R) := by
    rw [show fourBasisVector (R := R) = (1 : Matrix (Fin 4) (Fin 4) R) by
      ext i j
      by_cases hij : i = j <;>
        simp [fourBasisVector, Matrix.one_apply, hij]]
    exact Matrix.det_one
  have hperm := Matrix.detRowAlternating.map_perm
    (fourBasisVector (R := R)) permutation
  have hbasisAlt :
      Matrix.detRowAlternating (fourBasisVector (R := R)) = (1 : R) := hbasis
  rw [hfun]
  change Matrix.detRowAlternating
      (fourBasisVector (R := R) ∘ permutation) = _
  rw [hperm, hbasisAlt]
  have hsign := permutation.sign_eq_prod_prod_Iio
  have hpermutation : (permutation : Fin 4 → Fin 4) = indices := rfl
  have hIio0 : Finset.Iio (0 : Fin 4) = ∅ := by decide
  have hIio1 : Finset.Iio (1 : Fin 4) = {0} := by decide
  have hIio2 : Finset.Iio (2 : Fin 4) = {0, 1} := by decide
  have hIio3 : Finset.Iio (3 : Fin 4) = {0, 1, 2} := by decide
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  have hprod :
      (∏ j, ∏ i ∈ Finset.Iio j,
          (if permutation i < permutation j then 1 else -1)) =
        fourIndexSign indices := by
    rw [hpermutation, huniv]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 4) ∉ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 4) ∉ {(2 : Fin 4), (3 : Fin 4)})]
    rw [Finset.prod_insert (by decide : (2 : Fin 4) ∉ {(3 : Fin 4)})]
    rw [Finset.prod_singleton]
    rw [hIio0, hIio1, hIio2, hIio3]
    rw [Finset.prod_insert (by decide : (0 : Fin 4) ∉ {(1 : Fin 4)})]
    rw [Finset.prod_singleton]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 4) ∉ {(1 : Fin 4), (2 : Fin 4)})]
    rw [Finset.prod_insert (by decide : (1 : Fin 4) ∉ {(2 : Fin 4)})]
    rw [Finset.prod_singleton]
    simp only [Finset.prod_singleton, Finset.prod_empty, one_mul]
    unfold fourIndexSign
    ac_rfl
  rw [hsign, hprod, Units.smul_def]
  simp

theorem fourInjectiveDet_basis
    [Nontrivial R] (indices : Fin 4 → Fin 4) :
    fourInjectiveDet (R := R)
        (fun row => fourBasisVector (R := R) (indices row)) =
      if _ : Function.Injective indices then
        ((fourIndexSign indices : ℤ) : R) else 0 := by
  classical
  have hinjectiveIff :
      Function.Injective (fun row => fourBasisVector (R := R) (indices row)) ↔
        Function.Injective indices := by
    constructor
    · intro hrows left right heq
      apply hrows
      exact congrArg (fourBasisVector (R := R)) heq
    · intro hindices
      exact (Pi.basisFun R (Fin 4)).injective.comp hindices
  by_cases hinjective : Function.Injective indices
  · have hrows := hinjectiveIff.mpr hinjective
    simpa [fourInjectiveDet, hrows, hinjective] using
      det_fourBasisVector_comp_of_injective (R := R) indices hinjective
  · have hrows : ¬Function.Injective
        (fun row => fourBasisVector (R := R) (indices row)) := by
      intro h
      exact hinjective (hinjectiveIff.mp h)
    simp [fourInjectiveDet, hrows, hinjective]

theorem fourInjectiveDet_basis_rows
    [Nontrivial R] (i0 i1 i2 i3 : Fin 4) :
    fourInjectiveDet (R := R)
        ![fourBasisVector i0, fourBasisVector i1,
          fourBasisVector i2, fourBasisVector i3] =
      if _ : Function.Injective ![i0, i1, i2, i3] then
        (((fourIndexSign ![i0, i1, i2, i3]) : ℤ) : R) else 0 := by
  have hrows :
      ![fourBasisVector (R := R) i0, fourBasisVector i1,
          fourBasisVector i2, fourBasisVector i3] =
        (fun row => fourBasisVector (R := R) (![i0, i1, i2, i3] row)) := by
    funext row
    fin_cases row <;> rfl
  rw [hrows]
  exact fourInjectiveDet_basis (R := R) ![i0, i1, i2, i3]

theorem topFourDeterminant_iota_product_if
    (first second third fourth : FourRow R) :
    topFourDeterminant (R := R)
        (ExteriorAlgebra.ι R first *
          (ExteriorAlgebra.ι R second *
            (ExteriorAlgebra.ι R third * ExteriorAlgebra.ι R fourth))) =
      fourInjectiveDet ![first, second, third, fourth] := by
  classical
  rw [topFourDeterminant_iota_product]
  unfold fourInjectiveDet
  split_ifs with hinjective
  · rfl
  · apply Matrix.detRowAlternating.map_eq_zero_of_not_injective
    exact hinjective

set_option maxHeartbeats 1000000 in
theorem fourTwoForm_sq_top [Nontrivial R] (pair : Fin 4 → Fin 4 → R) :
    topFourDeterminant (R := R) (fourTwoForm pair ^ 2) =
      2 * pfaffianFour pair := by
  classical
  unfold fourTwoForm pfaffianFour
  rw [pow_two]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  simp only [mul_assoc, map_add, map_smul,
    topFourDeterminant_iota_product_if]
  simp only [fourInjectiveDet_basis_rows]
  simp +decide [fourIndexSign]
  ring

theorem topFourDeterminant_exterior_minor_sum_pfaffian
    [Nontrivial R] (rows : List (FourRow R)) :
    topFourDeterminant (R := R) (exteriorElementary 2 rows ^ 2) =
      2 * pfaffianFour (fourPairSum rows) := by
  rw [exteriorElementary_two_eq_fourTwoForm]
  exact fourTwoForm_sq_top _

end FibonacciRibbonKernel
