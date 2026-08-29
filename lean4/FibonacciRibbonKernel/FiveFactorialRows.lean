import FibonacciRibbonKernel.ExteriorSublists
import FibonacciRibbonKernel.FrobeniusDeterminant
import FibonacciRibbonKernel.ExteriorPfaffianFive

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries

def fiveVector {A : Type*} (a b c d e : A) : Fin 5 → A :=
  Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (Fin.cons e Fin.elim0))))

@[simp] theorem fiveVector_zero {A : Type*} (a b c d e : A) :
    fiveVector a b c d e 0 = a := rfl

@[simp] theorem fiveVector_one {A : Type*} (a b c d e : A) :
    fiveVector a b c d e 1 = b := rfl

@[simp] theorem fiveVector_two {A : Type*} (a b c d e : A) :
    fiveVector a b c d e 2 = c := by rfl

@[simp] theorem fiveVector_three {A : Type*} (a b c d e : A) :
    fiveVector a b c d e 3 = d := by rfl

@[simp] theorem fiveVector_four {A : Type*} (a b c d e : A) :
    fiveVector a b c d e 4 = e := by rfl

theorem sum_fin_five {A : Type*} [AddCommMonoid A] (function : Fin 5 → A) :
    (∑ index, function index) =
      function 0 + function 1 + function 2 + function 3 + function 4 := by
  rw [show (Finset.univ : Finset (Fin 5)) =
      {(0 : Fin 5), (1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)} by decide]
  rw [Finset.sum_insert (by decide :
    (0 : Fin 5) ∉ {(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)})]
  rw [Finset.sum_insert (by decide :
    (1 : Fin 5) ∉ {(2 : Fin 5), (3 : Fin 5), (4 : Fin 5)})]
  rw [Finset.sum_insert (by decide :
    (2 : Fin 5) ∉ {(3 : Fin 5), (4 : Fin 5)})]
  rw [Finset.sum_insert (by decide : (3 : Fin 5) ∉ {(4 : Fin 5)})]
  rw [Finset.sum_singleton]
  ac_rfl

noncomputable def fiveFactorialScalarRow (index : ℕ) : FiveRow ℚ :=
  fun column => reciprocalFactorialInt
    ((index : ℤ) - (column.rev.val : ℤ))

noncomputable def fiveFactorialPowerSeriesRow (index : ℕ) :
    FiveRow ℚ⟦X⟧ :=
  fun column => PowerSeries.monomial index
    (fiveFactorialScalarRow index column)

noncomputable def fiveFactorialPowerSeriesMatrix
    (a b c d e : ℕ) : Matrix (Fin 5) (Fin 5) ℚ⟦X⟧ :=
  fun row => fiveVector
    (fiveFactorialPowerSeriesRow a)
    (fiveFactorialPowerSeriesRow b)
    (fiveFactorialPowerSeriesRow c)
    (fiveFactorialPowerSeriesRow d)
    (fiveFactorialPowerSeriesRow e) row

noncomputable def fiveFactorialScalarMatrix
    (a b c d e : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun row => fiveVector
    (fiveFactorialScalarRow a) (fiveFactorialScalarRow b)
    (fiveFactorialScalarRow c) (fiveFactorialScalarRow d)
    (fiveFactorialScalarRow e) row

noncomputable def fiveMonomialScale (a b c d e : ℕ) : Fin 5 → ℚ⟦X⟧ :=
  fiveVector (PowerSeries.monomial a 1)
    (PowerSeries.monomial b 1) (PowerSeries.monomial c 1)
    (PowerSeries.monomial d 1) (PowerSeries.monomial e 1)

theorem monomial_eq_monomial_one_mul_C (degree : ℕ) (coefficient : ℚ) :
    PowerSeries.monomial degree coefficient =
      PowerSeries.monomial degree 1 * PowerSeries.C coefficient := by
  rw [← PowerSeries.monomial_zero_eq_C_apply,
    PowerSeries.monomial_mul_monomial]
  simp

theorem fiveFactorialPowerSeriesMatrix_factor
    (a b c d e : ℕ) :
    fiveFactorialPowerSeriesMatrix a b c d e =
      Matrix.diagonal (fiveMonomialScale a b c d e) *
        PowerSeries.C.mapMatrix (fiveFactorialScalarMatrix a b c d e) := by
  apply Matrix.ext
  intro row column
  rw [Matrix.diagonal_mul]
  unfold fiveFactorialPowerSeriesMatrix fiveMonomialScale
    fiveFactorialScalarMatrix
  fin_cases row <;> exact monomial_eq_monomial_one_mul_C _ _

theorem det_fiveFactorialPowerSeriesRows
    (a b c d e : ℕ) :
    Matrix.det (fiveFactorialPowerSeriesMatrix a b c d e) =
      PowerSeries.monomial (a + b + c + d + e)
        (Matrix.det (fiveFactorialScalarMatrix a b c d e)) := by
  rw [fiveFactorialPowerSeriesMatrix_factor, Matrix.det_mul,
    Matrix.det_diagonal]
  have hmap := PowerSeries.C.map_det (fiveFactorialScalarMatrix a b c d e)
  rw [← hmap]
  have hprod : (∏ row, fiveMonomialScale a b c d e row) =
      PowerSeries.monomial (a + b + c + d + e) 1 := by
    rw [show (Finset.univ : Finset (Fin 5)) =
        {(0 : Fin 5), (1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)} by decide]
    rw [Finset.prod_insert (by decide :
      (0 : Fin 5) ∉ {(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)})]
    rw [Finset.prod_insert (by decide :
      (1 : Fin 5) ∉ {(2 : Fin 5), (3 : Fin 5), (4 : Fin 5)})]
    rw [Finset.prod_insert (by decide :
      (2 : Fin 5) ∉ {(3 : Fin 5), (4 : Fin 5)})]
    rw [Finset.prod_insert (by decide : (3 : Fin 5) ∉ {(4 : Fin 5)})]
    rw [Finset.prod_singleton]
    rw [show fiveMonomialScale a b c d e 0 =
        PowerSeries.monomial a 1 by rfl,
      show fiveMonomialScale a b c d e 1 =
        PowerSeries.monomial b 1 by rfl,
      show fiveMonomialScale a b c d e 2 =
        PowerSeries.monomial c 1 by rfl,
      show fiveMonomialScale a b c d e 3 =
        PowerSeries.monomial d 1 by rfl,
      show fiveMonomialScale a b c d e 4 =
        PowerSeries.monomial e 1 by rfl]
    rw [PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial]
    simp only [mul_one]
    apply congrArg (fun degree => PowerSeries.monomial degree (1 : ℚ))
    omega
  rw [hprod, ← monomial_eq_monomial_one_mul_C]

theorem topFiveDeterminant_exteriorListProduct_fiveFactorialRows
    (a b c d e : ℕ) :
    topFiveDeterminant (R := ℚ⟦X⟧)
        (exteriorListProduct (R := ℚ⟦X⟧)
          [fiveFactorialPowerSeriesRow a,
            fiveFactorialPowerSeriesRow b,
            fiveFactorialPowerSeriesRow c,
            fiveFactorialPowerSeriesRow d,
            fiveFactorialPowerSeriesRow e]) =
      PowerSeries.monomial (a + b + c + d + e)
        (Matrix.det (fiveFactorialScalarMatrix a b c d e)) := by
  rw [show exteriorListProduct (R := ℚ⟦X⟧)
      [fiveFactorialPowerSeriesRow a, fiveFactorialPowerSeriesRow b,
        fiveFactorialPowerSeriesRow c, fiveFactorialPowerSeriesRow d,
        fiveFactorialPowerSeriesRow e] =
      ExteriorAlgebra.ι ℚ⟦X⟧ (fiveFactorialPowerSeriesRow a) *
        (ExteriorAlgebra.ι ℚ⟦X⟧ (fiveFactorialPowerSeriesRow b) *
          (ExteriorAlgebra.ι ℚ⟦X⟧ (fiveFactorialPowerSeriesRow c) *
            (ExteriorAlgebra.ι ℚ⟦X⟧ (fiveFactorialPowerSeriesRow d) *
              ExteriorAlgebra.ι ℚ⟦X⟧
                (fiveFactorialPowerSeriesRow e)))) by
        simp [exteriorListProduct]]
  rw [topFiveDeterminant_iota_product,
    show Matrix.det
        ![fiveFactorialPowerSeriesRow a,
          fiveFactorialPowerSeriesRow b,
          fiveFactorialPowerSeriesRow c,
          fiveFactorialPowerSeriesRow d,
          fiveFactorialPowerSeriesRow e] =
        Matrix.det (fiveFactorialPowerSeriesMatrix a b c d e) by
      rfl,
    det_fiveFactorialPowerSeriesRows]

end FibonacciRibbonKernel
