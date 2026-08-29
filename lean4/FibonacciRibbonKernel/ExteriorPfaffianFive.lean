import FibonacciRibbonKernel.ExteriorCoordinates
import Mathlib.GroupTheory.Perm.Fin

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R : Type*} [CommRing R]

def borderedPfaffianFive
    (pair : Fin 5 → Fin 5 → R) (single : Fin 5 → R) : R :=
  pair 0 1 * pair 2 3 * single 4 -
    pair 0 1 * pair 2 4 * single 3 +
    pair 0 1 * single 2 * pair 3 4 -
    pair 0 2 * pair 1 3 * single 4 +
    pair 0 2 * pair 1 4 * single 3 -
    pair 0 2 * single 1 * pair 3 4 +
    pair 0 3 * pair 1 2 * single 4 -
    pair 0 3 * pair 1 4 * single 2 +
    pair 0 3 * single 1 * pair 2 4 -
    pair 0 4 * pair 1 2 * single 3 +
    pair 0 4 * pair 1 3 * single 2 -
    pair 0 4 * single 1 * pair 2 3 +
    single 0 * pair 1 2 * pair 3 4 -
    single 0 * pair 1 3 * pair 2 4 +
    single 0 * pair 1 4 * pair 2 3

noncomputable def fiveVolume : ExteriorAlgebra R (FiveRow R) :=
  ExteriorAlgebra.ι R (fiveBasisVector 0) *
    (ExteriorAlgebra.ι R (fiveBasisVector 1) *
      (ExteriorAlgebra.ι R (fiveBasisVector 2) *
        (ExteriorAlgebra.ι R (fiveBasisVector 3) *
          ExteriorAlgebra.ι R (fiveBasisVector 4))))

@[simp] theorem topFiveDeterminant_iota_product
    (first second third fourth fifth : FiveRow R) :
    topFiveDeterminant (R := R)
        (ExteriorAlgebra.ι R first *
          (ExteriorAlgebra.ι R second *
            (ExteriorAlgebra.ι R third *
              (ExteriorAlgebra.ι R fourth * ExteriorAlgebra.ι R fifth)))) =
      Matrix.det ![first, second, third, fourth, fifth] := by
  have h := topFiveDeterminant_iMulti (R := R)
    ![first, second, third, fourth, fifth]
  simpa [ExteriorAlgebra.ιMulti_apply] using h

noncomputable def fiveInjectiveDet (rows : Fin 5 → FiveRow R) : R := by
  classical
  exact if Function.Injective rows then Matrix.det rows else 0

def fiveIndexSign (indices : Fin 5 → Fin 5) : ℤˣ :=
  (if indices 0 < indices 1 then 1 else -1) *
    (if indices 0 < indices 2 then 1 else -1) *
    (if indices 1 < indices 2 then 1 else -1) *
    (if indices 0 < indices 3 then 1 else -1) *
    (if indices 1 < indices 3 then 1 else -1) *
    (if indices 2 < indices 3 then 1 else -1) *
    (if indices 0 < indices 4 then 1 else -1) *
    (if indices 1 < indices 4 then 1 else -1) *
    (if indices 2 < indices 4 then 1 else -1) *
    (if indices 3 < indices 4 then 1 else -1)

noncomputable def fivePermutationOfInjective
    (indices : Fin 5 → Fin 5) (hinjective : Function.Injective indices) :
    Equiv.Perm (Fin 5) :=
  Equiv.ofBijective indices
    ((Fintype.bijective_iff_injective_and_card indices).2 ⟨hinjective, rfl⟩)

set_option maxRecDepth 10000 in
theorem det_fiveBasisVector_comp_of_injective
    [Nontrivial R]
    (indices : Fin 5 → Fin 5) (hinjective : Function.Injective indices) :
    Matrix.det (fun row => fiveBasisVector (R := R) (indices row)) =
      ((fiveIndexSign indices : ℤ) : R) := by
  let permutation := fivePermutationOfInjective indices hinjective
  have hfun : (fun row => fiveBasisVector (R := R) (indices row)) =
      fiveBasisVector (R := R) ∘ permutation := by
    funext row
    rfl
  have hbasis : Matrix.det (fiveBasisVector (R := R)) = (1 : R) := by
    rw [show fiveBasisVector (R := R) = (1 : Matrix (Fin 5) (Fin 5) R) by
      ext i j
      by_cases hij : i = j <;>
        simp [fiveBasisVector, Matrix.one_apply, hij]]
    exact Matrix.det_one
  have hperm := Matrix.detRowAlternating.map_perm
    (fiveBasisVector (R := R)) permutation
  have hbasisAlt :
      Matrix.detRowAlternating (fiveBasisVector (R := R)) = (1 : R) := by
    exact hbasis
  rw [hfun]
  change Matrix.detRowAlternating
      (fiveBasisVector (R := R) ∘ permutation) = _
  rw [hperm, hbasisAlt]
  have hsign := permutation.sign_eq_prod_prod_Iio
  have hpermutation : (permutation : Fin 5 → Fin 5) = indices := rfl
  have hIio0 : Finset.Iio (0 : Fin 5) = ∅ := by decide
  have hIio1 : Finset.Iio (1 : Fin 5) = {0} := by decide
  have hIio2 : Finset.Iio (2 : Fin 5) = {0, 1} := by decide
  have hIio3 : Finset.Iio (3 : Fin 5) = {0, 1, 2} := by decide
  have hIio4 : Finset.Iio (4 : Fin 5) = {0, 1, 2, 3} := by decide
  have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
  have hprod :
      (∏ j, ∏ i ∈ Finset.Iio j,
          (if permutation i < permutation j then 1 else -1)) =
        fiveIndexSign indices := by
    rw [hpermutation]
    rw [huniv]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 5) ∉ {(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 5) ∉ {(2 : Fin 5), (3 : Fin 5), (4 : Fin 5)})]
    rw [Finset.prod_insert (by decide :
      (2 : Fin 5) ∉ {(3 : Fin 5), (4 : Fin 5)})]
    rw [Finset.prod_insert (by decide : (3 : Fin 5) ∉ {(4 : Fin 5)})]
    rw [Finset.prod_singleton]
    rw [hIio0, hIio1, hIio2, hIio3, hIio4]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 5) ∉ {(1 : Fin 5)})]
    rw [Finset.prod_singleton]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 5) ∉ {(1 : Fin 5), (2 : Fin 5)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 5) ∉ {(2 : Fin 5)})]
    rw [Finset.prod_singleton]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 5) ∉ {(1 : Fin 5), (2 : Fin 5), (3 : Fin 5)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 5) ∉ {(2 : Fin 5), (3 : Fin 5)})]
    rw [Finset.prod_insert (by decide :
      (2 : Fin 5) ∉ {(3 : Fin 5)})]
    rw [Finset.prod_singleton]
    simp only [Finset.prod_singleton, Finset.prod_empty, one_mul]
    unfold fiveIndexSign
    ac_rfl
  rw [hsign, hprod]
  rw [Units.smul_def]
  simp

theorem fiveInjectiveDet_basis
    [Nontrivial R]
    (indices : Fin 5 → Fin 5) :
    fiveInjectiveDet (R := R)
        (fun row => fiveBasisVector (R := R) (indices row)) =
      if _ : Function.Injective indices then
        ((fiveIndexSign indices : ℤ) : R) else 0 := by
  classical
  have hinjectiveIff :
      Function.Injective (fun row => fiveBasisVector (R := R) (indices row)) ↔
        Function.Injective indices := by
    constructor
    · intro hrows left right heq
      apply hrows
      exact congrArg (fiveBasisVector (R := R)) heq
    · intro hindices
      exact (Pi.basisFun R (Fin 5)).injective.comp hindices
  by_cases hinjective : Function.Injective indices
  · have hrows := hinjectiveIff.mpr hinjective
    simpa [fiveInjectiveDet, hrows, hinjective] using
      det_fiveBasisVector_comp_of_injective (R := R) indices hinjective
  · have hrows : ¬Function.Injective
        (fun row => fiveBasisVector (R := R) (indices row)) := by
      intro h
      exact hinjective (hinjectiveIff.mp h)
    simp [fiveInjectiveDet, hrows, hinjective]

theorem fiveInjectiveDet_basis_rows
    [Nontrivial R]
    (i0 i1 i2 i3 i4 : Fin 5) :
    fiveInjectiveDet (R := R)
        ![fiveBasisVector i0, fiveBasisVector i1, fiveBasisVector i2,
          fiveBasisVector i3, fiveBasisVector i4] =
      if _ : Function.Injective ![i0, i1, i2, i3, i4] then
        (((fiveIndexSign ![i0, i1, i2, i3, i4]) : ℤ) : R)
      else 0 := by
  have hrows :
      ![fiveBasisVector (R := R) i0, fiveBasisVector i1, fiveBasisVector i2,
          fiveBasisVector i3, fiveBasisVector i4] =
        (fun row => fiveBasisVector (R := R) (![i0, i1, i2, i3, i4] row)) := by
    funext row
    fin_cases row <;> rfl
  rw [hrows]
  exact fiveInjectiveDet_basis (R := R) ![i0, i1, i2, i3, i4]

theorem topFiveDeterminant_iota_product_if
    (first second third fourth fifth : FiveRow R) :
    topFiveDeterminant (R := R)
        (ExteriorAlgebra.ι R first *
          (ExteriorAlgebra.ι R second *
            (ExteriorAlgebra.ι R third *
              (ExteriorAlgebra.ι R fourth * ExteriorAlgebra.ι R fifth)))) =
      fiveInjectiveDet ![first, second, third, fourth, fifth] := by
  classical
  rw [topFiveDeterminant_iota_product]
  unfold fiveInjectiveDet
  split_ifs with hinjective
  · rfl
  · apply Matrix.detRowAlternating.map_eq_zero_of_not_injective
    exact hinjective

theorem iota_swap_mul_tail (left right : FiveRow R)
    (element : ExteriorAlgebra R (FiveRow R)) :
    ExteriorAlgebra.ι R left * (ExteriorAlgebra.ι R right * element) =
      -(ExteriorAlgebra.ι R right * (ExteriorAlgebra.ι R left * element)) := by
  rw [← mul_assoc, iota_mul_iota_neg, neg_mul, mul_assoc]

@[simp] theorem iota_five_repeat_first_last
    (first second third fourth : FiveRow R) :
    ExteriorAlgebra.ι R first *
        (ExteriorAlgebra.ι R second *
          (ExteriorAlgebra.ι R third *
            (ExteriorAlgebra.ι R fourth * ExteriorAlgebra.ι R first))) = 0 := by
  have hzero : ExteriorAlgebra.ιMulti R 5
      ![first, second, third, fourth, first] = 0 := by
    apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
    intro hinjective
    have heq : (0 : Fin 5) = 4 := hinjective (by rfl)
    exact (by decide : (0 : Fin 5) ≠ 4) heq
  simpa [ExteriorAlgebra.ιMulti_apply] using hzero

theorem iota_five_rotate_last
    (first second third fourth fifth : FiveRow R) :
    ExteriorAlgebra.ι R first *
        (ExteriorAlgebra.ι R second *
          (ExteriorAlgebra.ι R third *
            (ExteriorAlgebra.ι R fourth * ExteriorAlgebra.ι R fifth))) =
      ExteriorAlgebra.ι R fifth *
        (ExteriorAlgebra.ι R first *
          (ExteriorAlgebra.ι R second *
            (ExteriorAlgebra.ι R third * ExteriorAlgebra.ι R fourth))) := by
  calc
    _ = -(ExteriorAlgebra.ι R first *
        (ExteriorAlgebra.ι R second *
          (ExteriorAlgebra.ι R third *
            (ExteriorAlgebra.ι R fifth * ExteriorAlgebra.ι R fourth)))) := by
      rw [iota_mul_iota_neg (R := R) fourth fifth]
      noncomm_ring
    _ = ExteriorAlgebra.ι R first *
        (ExteriorAlgebra.ι R second *
          (ExteriorAlgebra.ι R fifth *
            (ExteriorAlgebra.ι R third * ExteriorAlgebra.ι R fourth))) := by
      rw [iota_swap_mul_tail (R := R) third fifth
        (ExteriorAlgebra.ι R fourth)]
      noncomm_ring
    _ = -(ExteriorAlgebra.ι R first *
        (ExteriorAlgebra.ι R fifth *
          (ExteriorAlgebra.ι R second *
            (ExteriorAlgebra.ι R third * ExteriorAlgebra.ι R fourth)))) := by
      rw [iota_swap_mul_tail (R := R) second fifth
        (ExteriorAlgebra.ι R third * ExteriorAlgebra.ι R fourth), mul_neg]
    _ = _ := by
      rw [iota_swap_mul_tail (R := R) first fifth
        (ExteriorAlgebra.ι R second *
          (ExteriorAlgebra.ι R third * ExteriorAlgebra.ι R fourth)), neg_neg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem fiveTwoForm_sq_mul_fiveOneForm
    [Nontrivial R]
    (pair : Fin 5 → Fin 5 → R) (single : Fin 5 → R) :
    topFiveDeterminant (R := R)
        (fiveTwoForm pair ^ 2 * fiveOneForm single) =
      2 * borderedPfaffianFive pair single := by
  classical
  unfold fiveTwoForm fiveOneForm borderedPfaffianFive
  rw [pow_two]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  simp only [mul_assoc]
  simp only [map_add, map_smul, topFiveDeterminant_iota_product_if]
  simp only [fiveInjectiveDet_basis_rows]
  simp +decide [fiveIndexSign]
  ring

/-- The five-row minor-summation identity in explicit bordered-Pfaffian
coordinates.  This is the finite algebraic core of the odd-height Gessel
determinant, before specializing the row list to factorial vectors. -/
theorem topFiveDeterminant_exteriorElementary_five_eq_borderedPfaffian
    [Nontrivial R] (rows : List (FiveRow R)) :
    2 * topFiveDeterminant (R := R) (exteriorElementary 5 rows) =
      2 * borderedPfaffianFive (fivePairSum rows) (fiveRowSum rows) := by
  calc
    2 * topFiveDeterminant (R := R) (exteriorElementary 5 rows) =
        topFiveDeterminant (R := R)
          (exteriorElementary 2 rows ^ 2 * exteriorElementary 1 rows) :=
      (topFiveDeterminant_exterior_minor_sum (R := R) rows).symm
    _ = topFiveDeterminant (R := R)
          (fiveTwoForm (fivePairSum rows) ^ 2 *
            fiveOneForm (fiveRowSum rows)) := by
      rw [exteriorElementary_two_eq_fiveTwoForm,
        exteriorElementary_one_eq_fiveOneForm]
    _ = 2 * borderedPfaffianFive (fivePairSum rows) (fiveRowSum rows) :=
      fiveTwoForm_sq_mul_fiveOneForm _ _

end FibonacciRibbonKernel
