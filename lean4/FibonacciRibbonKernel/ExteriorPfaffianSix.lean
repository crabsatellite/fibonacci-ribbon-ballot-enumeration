import FibonacciRibbonKernel.ExteriorCoordinatesSix
import Mathlib.GroupTheory.Perm.Fin

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R : Type*} [CommRing R]

def pfaffianSix (pair : Fin 6 → Fin 6 → R) : R :=
  pair 0 1 * pair 2 3 * pair 4 5 -
    pair 0 1 * pair 2 4 * pair 3 5 +
    pair 0 1 * pair 2 5 * pair 3 4 -
    pair 0 2 * pair 1 3 * pair 4 5 +
    pair 0 2 * pair 1 4 * pair 3 5 -
    pair 0 2 * pair 1 5 * pair 3 4 +
    pair 0 3 * pair 1 2 * pair 4 5 -
    pair 0 3 * pair 1 4 * pair 2 5 +
    pair 0 3 * pair 1 5 * pair 2 4 -
    pair 0 4 * pair 1 2 * pair 3 5 +
    pair 0 4 * pair 1 3 * pair 2 5 -
    pair 0 4 * pair 1 5 * pair 2 3 +
    pair 0 5 * pair 1 2 * pair 3 4 -
    pair 0 5 * pair 1 3 * pair 2 4 +
    pair 0 5 * pair 1 4 * pair 2 3

noncomputable def sixInjectiveDet (rows : Fin 6 → SixRow R) : R := by
  classical
  exact if Function.Injective rows then Matrix.det rows else 0

def sixIndexSign (indices : Fin 6 → Fin 6) : ℤˣ :=
  (if indices 0 < indices 1 then 1 else -1) *
    (if indices 0 < indices 2 then 1 else -1) *
    (if indices 1 < indices 2 then 1 else -1) *
    (if indices 0 < indices 3 then 1 else -1) *
    (if indices 1 < indices 3 then 1 else -1) *
    (if indices 2 < indices 3 then 1 else -1) *
    (if indices 0 < indices 4 then 1 else -1) *
    (if indices 1 < indices 4 then 1 else -1) *
    (if indices 2 < indices 4 then 1 else -1) *
    (if indices 3 < indices 4 then 1 else -1) *
    (if indices 0 < indices 5 then 1 else -1) *
    (if indices 1 < indices 5 then 1 else -1) *
    (if indices 2 < indices 5 then 1 else -1) *
    (if indices 3 < indices 5 then 1 else -1) *
    (if indices 4 < indices 5 then 1 else -1)

noncomputable def sixPermutationOfInjective
    (indices : Fin 6 → Fin 6) (hinjective : Function.Injective indices) :
    Equiv.Perm (Fin 6) :=
  Equiv.ofBijective indices
    ((Fintype.bijective_iff_injective_and_card indices).2 ⟨hinjective, rfl⟩)

set_option maxRecDepth 15000 in
theorem det_sixBasisVector_comp_of_injective
    [Nontrivial R]
    (indices : Fin 6 → Fin 6) (hinjective : Function.Injective indices) :
    Matrix.det (fun row => sixBasisVector (R := R) (indices row)) =
      ((sixIndexSign indices : ℤ) : R) := by
  let permutation := sixPermutationOfInjective indices hinjective
  have hfun : (fun row => sixBasisVector (R := R) (indices row)) =
      sixBasisVector (R := R) ∘ permutation := by
    funext row
    rfl
  have hbasis : Matrix.det (sixBasisVector (R := R)) = (1 : R) := by
    rw [show sixBasisVector (R := R) = (1 : Matrix (Fin 6) (Fin 6) R) by
      ext i j
      by_cases hij : i = j <;>
        simp [sixBasisVector, Matrix.one_apply, hij]]
    exact Matrix.det_one
  have hperm := Matrix.detRowAlternating.map_perm
    (sixBasisVector (R := R)) permutation
  have hbasisAlt :
      Matrix.detRowAlternating (sixBasisVector (R := R)) = (1 : R) := hbasis
  rw [hfun]
  change Matrix.detRowAlternating
      (sixBasisVector (R := R) ∘ permutation) = _
  rw [hperm, hbasisAlt]
  have hsign := permutation.sign_eq_prod_prod_Iio
  have hpermutation : (permutation : Fin 6 → Fin 6) = indices := rfl
  have hIio0 : Finset.Iio (0 : Fin 6) = ∅ := by decide
  have hIio1 : Finset.Iio (1 : Fin 6) = {0} := by decide
  have hIio2 : Finset.Iio (2 : Fin 6) = {0, 1} := by decide
  have hIio3 : Finset.Iio (3 : Fin 6) = {0, 1, 2} := by decide
  have hIio4 : Finset.Iio (4 : Fin 6) = {0, 1, 2, 3} := by decide
  have hIio5 : Finset.Iio (5 : Fin 6) = {0, 1, 2, 3, 4} := by decide
  have huniv : (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by decide
  have hprod :
      (∏ j, ∏ i ∈ Finset.Iio j,
          (if permutation i < permutation j then 1 else -1)) =
        sixIndexSign indices := by
    rw [hpermutation, huniv]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 6) ∉ {(1 : Fin 6), (2 : Fin 6), (3 : Fin 6),
        (4 : Fin 6), (5 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 6) ∉ {(2 : Fin 6), (3 : Fin 6), (4 : Fin 6), (5 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (2 : Fin 6) ∉ {(3 : Fin 6), (4 : Fin 6), (5 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (3 : Fin 6) ∉ {(4 : Fin 6), (5 : Fin 6)})]
    rw [Finset.prod_insert (by decide : (4 : Fin 6) ∉ {(5 : Fin 6)})]
    rw [Finset.prod_singleton]
    rw [hIio0, hIio1, hIio2, hIio3, hIio4, hIio5]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 6) ∉ {(1 : Fin 6)})]
    rw [Finset.prod_singleton]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 6) ∉ {(1 : Fin 6), (2 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 6) ∉ {(2 : Fin 6)})]
    rw [Finset.prod_singleton]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 6) ∉ {(1 : Fin 6), (2 : Fin 6), (3 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 6) ∉ {(2 : Fin 6), (3 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (2 : Fin 6) ∉ {(3 : Fin 6)})]
    rw [Finset.prod_singleton]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 6) ∉ {(1 : Fin 6), (2 : Fin 6), (3 : Fin 6), (4 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 6) ∉ {(2 : Fin 6), (3 : Fin 6), (4 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (2 : Fin 6) ∉ {(3 : Fin 6), (4 : Fin 6)})]
    rw [Finset.prod_insert (by decide :
      (3 : Fin 6) ∉ {(4 : Fin 6)})]
    rw [Finset.prod_singleton]
    simp only [Finset.prod_singleton, Finset.prod_empty, one_mul]
    unfold sixIndexSign
    ac_rfl
  rw [hsign, hprod, Units.smul_def]
  simp

theorem sixInjectiveDet_basis
    [Nontrivial R] (indices : Fin 6 → Fin 6) :
    sixInjectiveDet (R := R)
        (fun row => sixBasisVector (R := R) (indices row)) =
      if _ : Function.Injective indices then
        ((sixIndexSign indices : ℤ) : R) else 0 := by
  classical
  have hinjectiveIff :
      Function.Injective (fun row => sixBasisVector (R := R) (indices row)) ↔
        Function.Injective indices := by
    constructor
    · intro hrows left right heq
      apply hrows
      exact congrArg (sixBasisVector (R := R)) heq
    · intro hindices
      exact (Pi.basisFun R (Fin 6)).injective.comp hindices
  by_cases hinjective : Function.Injective indices
  · have hrows := hinjectiveIff.mpr hinjective
    simpa [sixInjectiveDet, hrows, hinjective] using
      det_sixBasisVector_comp_of_injective (R := R) indices hinjective
  · have hrows : ¬Function.Injective
        (fun row => sixBasisVector (R := R) (indices row)) := by
      intro h
      exact hinjective (hinjectiveIff.mp h)
    simp [sixInjectiveDet, hrows, hinjective]

theorem sixInjectiveDet_basis_rows
    [Nontrivial R] (i0 i1 i2 i3 i4 i5 : Fin 6) :
    sixInjectiveDet (R := R)
        ![sixBasisVector i0, sixBasisVector i1, sixBasisVector i2,
          sixBasisVector i3, sixBasisVector i4, sixBasisVector i5] =
      if _ : Function.Injective ![i0, i1, i2, i3, i4, i5] then
        (((sixIndexSign ![i0, i1, i2, i3, i4, i5]) : ℤ) : R)
      else 0 := by
  have hrows :
      ![sixBasisVector (R := R) i0, sixBasisVector i1, sixBasisVector i2,
          sixBasisVector i3, sixBasisVector i4, sixBasisVector i5] =
        (fun row => sixBasisVector (R := R)
          (![i0, i1, i2, i3, i4, i5] row)) := by
    funext row
    fin_cases row <;> rfl
  rw [hrows]
  exact sixInjectiveDet_basis (R := R) ![i0, i1, i2, i3, i4, i5]

theorem topSixDeterminant_iota_product_if
    (first second third fourth fifth sixth : SixRow R) :
    topSixDeterminant (R := R)
        (ExteriorAlgebra.ι R first *
          (ExteriorAlgebra.ι R second *
            (ExteriorAlgebra.ι R third *
              (ExteriorAlgebra.ι R fourth *
                (ExteriorAlgebra.ι R fifth * ExteriorAlgebra.ι R sixth))))) =
      sixInjectiveDet ![first, second, third, fourth, fifth, sixth] := by
  classical
  rw [topSixDeterminant_iota_product]
  unfold sixInjectiveDet
  split_ifs with hinjective
  · rfl
  · apply Matrix.detRowAlternating.map_eq_zero_of_not_injective
    exact hinjective

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sixTwoForm_cube_top
    [Nontrivial R] (pair : Fin 6 → Fin 6 → R) :
    topSixDeterminant (R := R) (sixTwoForm pair ^ 3) =
      6 * pfaffianSix pair := by
  classical
  unfold sixTwoForm pfaffianSix
  rw [show (3 : ℕ) = 2 + 1 by omega, pow_succ, pow_two]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  simp only [mul_assoc]
  simp only [map_add, map_smul, topSixDeterminant_iota_product_if]
  simp only [sixInjectiveDet_basis_rows]
  simp +decide [sixIndexSign]
  ring

theorem topSixDeterminant_exteriorElementary_two_cube_eq_pfaffian
    [Nontrivial R] (rows : List (SixRow R)) :
    topSixDeterminant (R := R) (exteriorElementary 2 rows ^ 3) =
      6 * pfaffianSix (sixPairSum rows) := by
  rw [exteriorElementary_two_eq_sixTwoForm]
  exact sixTwoForm_cube_top _

end FibonacciRibbonKernel
