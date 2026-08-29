import FibonacciRibbonKernel.FiveFactorialRows
import FibonacciRibbonKernel.ExteriorMinorSumSix
import FibonacciRibbonKernel.FrobeniusDeterminant

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries

def sixVector {A : Type*} (a b c d e f : A) : Fin 6 → A :=
  Fin.cons a
    (Fin.cons b (Fin.cons c
      (Fin.cons d (Fin.cons e (Fin.cons f Fin.elim0)))))

@[simp] theorem sixVector_zero {A : Type*} (a b c d e f : A) :
    sixVector a b c d e f 0 = a := rfl
@[simp] theorem sixVector_one {A : Type*} (a b c d e f : A) :
    sixVector a b c d e f 1 = b := rfl
@[simp] theorem sixVector_two {A : Type*} (a b c d e f : A) :
    sixVector a b c d e f 2 = c := by rfl
@[simp] theorem sixVector_three {A : Type*} (a b c d e f : A) :
    sixVector a b c d e f 3 = d := by rfl
@[simp] theorem sixVector_four {A : Type*} (a b c d e f : A) :
    sixVector a b c d e f 4 = e := by rfl
@[simp] theorem sixVector_five {A : Type*} (a b c d e f : A) :
    sixVector a b c d e f 5 = f := by rfl

theorem sum_fin_six {A : Type*} [AddCommMonoid A] (function : Fin 6 → A) :
    (∑ index, function index) =
      function 0 + function 1 + function 2 + function 3 +
        function 4 + function 5 := by
  rw [show (Finset.univ : Finset (Fin 6)) =
      {(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (3 : Fin 6),
        (4 : Fin 6), (5 : Fin 6)} by decide]
  rw [Finset.sum_insert (by decide :
    (0 : Fin 6) ∉ {(1 : Fin 6), (2 : Fin 6), (3 : Fin 6),
      (4 : Fin 6), (5 : Fin 6)})]
  rw [Finset.sum_insert (by decide :
    (1 : Fin 6) ∉ {(2 : Fin 6), (3 : Fin 6), (4 : Fin 6), (5 : Fin 6)})]
  rw [Finset.sum_insert (by decide :
    (2 : Fin 6) ∉ {(3 : Fin 6), (4 : Fin 6), (5 : Fin 6)})]
  rw [Finset.sum_insert (by decide :
    (3 : Fin 6) ∉ {(4 : Fin 6), (5 : Fin 6)})]
  rw [Finset.sum_insert (by decide : (4 : Fin 6) ∉ {(5 : Fin 6)})]
  rw [Finset.sum_singleton]
  ac_rfl

noncomputable def sixFactorialScalarRow (index : ℕ) : SixRow ℚ :=
  fun column => reciprocalFactorialInt
    ((index : ℤ) - (column.rev.val : ℤ))

noncomputable def sixFactorialPowerSeriesRow (index : ℕ) :
    SixRow ℚ⟦X⟧ :=
  fun column => PowerSeries.monomial index
    (sixFactorialScalarRow index column)

noncomputable def sixFactorialPowerSeriesMatrix
    (a b c d e f : ℕ) : Matrix (Fin 6) (Fin 6) ℚ⟦X⟧ :=
  fun row => sixVector
    (sixFactorialPowerSeriesRow a) (sixFactorialPowerSeriesRow b)
    (sixFactorialPowerSeriesRow c) (sixFactorialPowerSeriesRow d)
    (sixFactorialPowerSeriesRow e) (sixFactorialPowerSeriesRow f) row

noncomputable def sixFactorialScalarMatrix
    (a b c d e f : ℕ) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun row => sixVector
    (sixFactorialScalarRow a) (sixFactorialScalarRow b)
    (sixFactorialScalarRow c) (sixFactorialScalarRow d)
    (sixFactorialScalarRow e) (sixFactorialScalarRow f) row

noncomputable def sixMonomialScale (a b c d e f : ℕ) : Fin 6 → ℚ⟦X⟧ :=
  sixVector (PowerSeries.monomial a 1) (PowerSeries.monomial b 1)
    (PowerSeries.monomial c 1) (PowerSeries.monomial d 1)
    (PowerSeries.monomial e 1) (PowerSeries.monomial f 1)

theorem sixFactorialPowerSeriesMatrix_factor
    (a b c d e f : ℕ) :
    sixFactorialPowerSeriesMatrix a b c d e f =
      Matrix.diagonal (sixMonomialScale a b c d e f) *
        PowerSeries.C.mapMatrix (sixFactorialScalarMatrix a b c d e f) := by
  apply Matrix.ext
  intro row column
  rw [Matrix.diagonal_mul]
  unfold sixFactorialPowerSeriesMatrix sixMonomialScale
    sixFactorialScalarMatrix
  fin_cases row <;> exact monomial_eq_monomial_one_mul_C _ _

theorem det_sixFactorialPowerSeriesRows
    (a b c d e f : ℕ) :
    Matrix.det (sixFactorialPowerSeriesMatrix a b c d e f) =
      PowerSeries.monomial (a + b + c + d + e + f)
        (Matrix.det (sixFactorialScalarMatrix a b c d e f)) := by
  rw [sixFactorialPowerSeriesMatrix_factor, Matrix.det_mul,
    Matrix.det_diagonal]
  have hmap := PowerSeries.C.map_det (sixFactorialScalarMatrix a b c d e f)
  rw [← hmap]
  have hprod : (∏ row, sixMonomialScale a b c d e f row) =
      PowerSeries.monomial (a + b + c + d + e + f) 1 := by
    rw [show (Finset.univ : Finset (Fin 6)) =
        {(0 : Fin 6), (1 : Fin 6), (2 : Fin 6), (3 : Fin 6),
          (4 : Fin 6), (5 : Fin 6)} by decide]
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
    rw [show sixMonomialScale a b c d e f 0 =
        PowerSeries.monomial a 1 by rfl,
      show sixMonomialScale a b c d e f 1 =
        PowerSeries.monomial b 1 by rfl,
      show sixMonomialScale a b c d e f 2 =
        PowerSeries.monomial c 1 by rfl,
      show sixMonomialScale a b c d e f 3 =
        PowerSeries.monomial d 1 by rfl,
      show sixMonomialScale a b c d e f 4 =
        PowerSeries.monomial e 1 by rfl,
      show sixMonomialScale a b c d e f 5 =
        PowerSeries.monomial f 1 by rfl]
    rw [PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial,
      PowerSeries.monomial_mul_monomial]
    simp only [mul_one]
    apply congrArg (fun degree => PowerSeries.monomial degree (1 : ℚ))
    omega
  rw [hprod, ← monomial_eq_monomial_one_mul_C]

theorem topSixDeterminant_exteriorListProduct_sixFactorialRows
    (a b c d e f : ℕ) :
    topSixDeterminant (R := ℚ⟦X⟧)
        (exteriorListProduct (R := ℚ⟦X⟧)
          [sixFactorialPowerSeriesRow a, sixFactorialPowerSeriesRow b,
            sixFactorialPowerSeriesRow c, sixFactorialPowerSeriesRow d,
            sixFactorialPowerSeriesRow e, sixFactorialPowerSeriesRow f]) =
      PowerSeries.monomial (a + b + c + d + e + f)
        (Matrix.det (sixFactorialScalarMatrix a b c d e f)) := by
  rw [show exteriorListProduct (R := ℚ⟦X⟧)
      [sixFactorialPowerSeriesRow a, sixFactorialPowerSeriesRow b,
        sixFactorialPowerSeriesRow c, sixFactorialPowerSeriesRow d,
        sixFactorialPowerSeriesRow e, sixFactorialPowerSeriesRow f] =
      ExteriorAlgebra.ι ℚ⟦X⟧ (sixFactorialPowerSeriesRow a) *
        (ExteriorAlgebra.ι ℚ⟦X⟧ (sixFactorialPowerSeriesRow b) *
          (ExteriorAlgebra.ι ℚ⟦X⟧ (sixFactorialPowerSeriesRow c) *
            (ExteriorAlgebra.ι ℚ⟦X⟧ (sixFactorialPowerSeriesRow d) *
              (ExteriorAlgebra.ι ℚ⟦X⟧ (sixFactorialPowerSeriesRow e) *
                ExteriorAlgebra.ι ℚ⟦X⟧
                  (sixFactorialPowerSeriesRow f))))) by
        simp [exteriorListProduct]]
  rw [topSixDeterminant_iota_product]
  rw [show Matrix.det
      ![sixFactorialPowerSeriesRow a, sixFactorialPowerSeriesRow b,
        sixFactorialPowerSeriesRow c, sixFactorialPowerSeriesRow d,
        sixFactorialPowerSeriesRow e, sixFactorialPowerSeriesRow f] =
      Matrix.det (sixFactorialPowerSeriesMatrix a b c d e f) by rfl,
    det_sixFactorialPowerSeriesRows]

end FibonacciRibbonKernel
