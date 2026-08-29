import FibonacciRibbonKernel.ExteriorPfaffianFour
import FibonacciRibbonKernel.FiveFactorialRows

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries

def fourVector {A : Type*} (a b c d : A) : Fin 4 → A :=
  Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Fin.elim0)))

@[simp] theorem fourVector_zero {A : Type*} (a b c d : A) :
    fourVector a b c d 0 = a := rfl
@[simp] theorem fourVector_one {A : Type*} (a b c d : A) :
    fourVector a b c d 1 = b := rfl
@[simp] theorem fourVector_two {A : Type*} (a b c d : A) :
    fourVector a b c d 2 = c := by rfl
@[simp] theorem fourVector_three {A : Type*} (a b c d : A) :
    fourVector a b c d 3 = d := by rfl

theorem sum_fin_four {A : Type*} [AddCommMonoid A] (function : Fin 4 → A) :
    (∑ index, function index) =
      function 0 + function 1 + function 2 + function 3 := by
  rw [show (Finset.univ : Finset (Fin 4)) =
      {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} by decide]
  rw [Finset.sum_insert (by decide :
    (0 : Fin 4) ∉ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})]
  rw [Finset.sum_insert (by decide :
    (1 : Fin 4) ∉ {(2 : Fin 4), (3 : Fin 4)})]
  rw [Finset.sum_insert (by decide : (2 : Fin 4) ∉ {(3 : Fin 4)})]
  rw [Finset.sum_singleton]
  ac_rfl

noncomputable def fourFactorialScalarRow (index : ℕ) : FourRow ℚ :=
  fun column => reciprocalFactorialInt
    ((index : ℤ) - (column.rev.val : ℤ))

noncomputable def fourFactorialPowerSeriesRow (index : ℕ) : FourRow ℚ⟦X⟧ :=
  fun column => PowerSeries.monomial index
    (fourFactorialScalarRow index column)

noncomputable def fourFactorialPowerSeriesMatrix
    (a b c d : ℕ) : Matrix (Fin 4) (Fin 4) ℚ⟦X⟧ :=
  fun row => fourVector (fourFactorialPowerSeriesRow a)
    (fourFactorialPowerSeriesRow b) (fourFactorialPowerSeriesRow c)
    (fourFactorialPowerSeriesRow d) row

noncomputable def fourFactorialScalarMatrix
    (a b c d : ℕ) : Matrix (Fin 4) (Fin 4) ℚ :=
  fun row => fourVector (fourFactorialScalarRow a)
    (fourFactorialScalarRow b) (fourFactorialScalarRow c)
    (fourFactorialScalarRow d) row

noncomputable def fourMonomialScale (a b c d : ℕ) : Fin 4 → ℚ⟦X⟧ :=
  fourVector (PowerSeries.monomial a 1) (PowerSeries.monomial b 1)
    (PowerSeries.monomial c 1) (PowerSeries.monomial d 1)

theorem fourFactorialPowerSeriesMatrix_factor (a b c d : ℕ) :
    fourFactorialPowerSeriesMatrix a b c d =
      Matrix.diagonal (fourMonomialScale a b c d) *
        PowerSeries.C.mapMatrix (fourFactorialScalarMatrix a b c d) := by
  apply Matrix.ext
  intro row column
  rw [Matrix.diagonal_mul]
  unfold fourFactorialPowerSeriesMatrix fourMonomialScale
    fourFactorialScalarMatrix
  fin_cases row <;> exact monomial_eq_monomial_one_mul_C _ _

theorem det_fourFactorialPowerSeriesRows (a b c d : ℕ) :
    Matrix.det (fourFactorialPowerSeriesMatrix a b c d) =
      PowerSeries.monomial (a + b + c + d)
        (Matrix.det (fourFactorialScalarMatrix a b c d)) := by
  rw [fourFactorialPowerSeriesMatrix_factor, Matrix.det_mul,
    Matrix.det_diagonal]
  have hmap := PowerSeries.C.map_det (fourFactorialScalarMatrix a b c d)
  rw [← hmap]
  have hprod : (∏ row, fourMonomialScale a b c d row) =
      PowerSeries.monomial (a + b + c + d) 1 := by
    rw [show (Finset.univ : Finset (Fin 4)) =
        {(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)} by decide]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 4) ∉ {(1 : Fin 4), (2 : Fin 4), (3 : Fin 4)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 4) ∉ {(2 : Fin 4), (3 : Fin 4)})]
    rw [Finset.prod_insert (by decide : (2 : Fin 4) ∉ {(3 : Fin 4)})]
    rw [Finset.prod_singleton]
    rw [show fourMonomialScale a b c d 0 = PowerSeries.monomial a 1 by rfl,
      show fourMonomialScale a b c d 1 = PowerSeries.monomial b 1 by rfl,
      show fourMonomialScale a b c d 2 = PowerSeries.monomial c 1 by rfl,
      show fourMonomialScale a b c d 3 = PowerSeries.monomial d 1 by rfl]
    rw [PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial]
    simp only [mul_one]
    apply congrArg (fun degree => PowerSeries.monomial degree (1 : ℚ))
    omega
  rw [hprod, ← monomial_eq_monomial_one_mul_C]

theorem topFourDeterminant_exteriorListProduct_fourFactorialRows
    (a b c d : ℕ) :
    topFourDeterminant (R := ℚ⟦X⟧)
        (exteriorListProduct (R := ℚ⟦X⟧)
          [fourFactorialPowerSeriesRow a, fourFactorialPowerSeriesRow b,
            fourFactorialPowerSeriesRow c, fourFactorialPowerSeriesRow d]) =
      PowerSeries.monomial (a + b + c + d)
        (Matrix.det (fourFactorialScalarMatrix a b c d)) := by
  rw [show exteriorListProduct (R := ℚ⟦X⟧)
      [fourFactorialPowerSeriesRow a, fourFactorialPowerSeriesRow b,
        fourFactorialPowerSeriesRow c, fourFactorialPowerSeriesRow d] =
      ExteriorAlgebra.ι ℚ⟦X⟧ (fourFactorialPowerSeriesRow a) *
        (ExteriorAlgebra.ι ℚ⟦X⟧ (fourFactorialPowerSeriesRow b) *
          (ExteriorAlgebra.ι ℚ⟦X⟧ (fourFactorialPowerSeriesRow c) *
            ExteriorAlgebra.ι ℚ⟦X⟧ (fourFactorialPowerSeriesRow d))) by
        simp [exteriorListProduct]]
  rw [topFourDeterminant_iota_product]
  rw [show Matrix.det
      ![fourFactorialPowerSeriesRow a, fourFactorialPowerSeriesRow b,
        fourFactorialPowerSeriesRow c, fourFactorialPowerSeriesRow d] =
      Matrix.det (fourFactorialPowerSeriesMatrix a b c d) by rfl,
    det_fourFactorialPowerSeriesRows]

end FibonacciRibbonKernel
