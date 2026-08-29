import FibonacciRibbonKernel.GeneralShiftedPartitions
import FibonacciRibbonKernel.ExteriorSublists

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

abbrev GeneralRow (dimension : ℕ) (R : Type*) := Fin dimension → R

noncomputable def generalFactorialScalarRow
    (dimension index : ℕ) : GeneralRow dimension ℚ :=
  fun column => reciprocalFactorialInt
    ((index : ℤ) - (column.rev.val : ℤ))

noncomputable def generalFactorialPowerSeriesRow
    (dimension index : ℕ) : GeneralRow dimension ℚ⟦X⟧ :=
  fun column => PowerSeries.monomial index
    (generalFactorialScalarRow dimension index column)

noncomputable def generalFactorialScalarMatrix
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Matrix (Fin dimension) (Fin dimension) ℚ :=
  fun row => generalFactorialScalarRow dimension (values row)

noncomputable def generalFactorialPowerSeriesMatrix
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Matrix (Fin dimension) (Fin dimension) ℚ⟦X⟧ :=
  fun row => generalFactorialPowerSeriesRow dimension (values row)

noncomputable def generalMonomialScale
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Fin dimension → ℚ⟦X⟧ :=
  fun row => PowerSeries.monomial (values row) 1

theorem general_monomial_eq_monomial_one_mul_C
    (degree : ℕ) (coefficient : ℚ) :
    PowerSeries.monomial degree coefficient =
      PowerSeries.monomial degree 1 * PowerSeries.C coefficient := by
  rw [← PowerSeries.monomial_zero_eq_C_apply,
    PowerSeries.monomial_mul_monomial]
  simp

theorem generalFactorialPowerSeriesMatrix_factor
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    generalFactorialPowerSeriesMatrix values =
      Matrix.diagonal (generalMonomialScale values) *
        PowerSeries.C.mapMatrix (generalFactorialScalarMatrix values) := by
  apply Matrix.ext
  intro row column
  rw [Matrix.diagonal_mul]
  unfold generalFactorialPowerSeriesMatrix generalMonomialScale
  unfold generalFactorialScalarMatrix generalFactorialPowerSeriesRow
  exact general_monomial_eq_monomial_one_mul_C _ _

theorem prod_monomial_one
    {indexType : Type*} [Fintype indexType] [DecidableEq indexType]
    (degrees : indexType → ℕ) :
    (∏ index, PowerSeries.monomial (degrees index) (1 : ℚ)) =
      PowerSeries.monomial (∑ index, degrees index) 1 := by
  classical
  induction (Finset.univ : Finset indexType) using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      rw [Finset.prod_insert hindex, Finset.sum_insert hindex, ih,
        PowerSeries.monomial_mul_monomial]
      simp only [mul_one]

theorem det_generalFactorialPowerSeriesRows
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Matrix.det (generalFactorialPowerSeriesMatrix values) =
      PowerSeries.monomial (∑ row, values row)
        (Matrix.det (generalFactorialScalarMatrix values)) := by
  rw [generalFactorialPowerSeriesMatrix_factor, Matrix.det_mul,
    Matrix.det_diagonal]
  have hmap := PowerSeries.C.map_det (generalFactorialScalarMatrix values)
  rw [← hmap]
  change (∏ row, PowerSeries.monomial (values row) (1 : ℚ)) *
      PowerSeries.C (Matrix.det (generalFactorialScalarMatrix values)) = _
  rw [prod_monomial_one]
  exact (general_monomial_eq_monomial_one_mul_C _ _).symm

theorem generalFactorialScalarMatrix_eq_factorialKernelMatrix
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    generalFactorialScalarMatrix tuple.values =
      factorialKernelMatrix (fun row => (tuple.values row : ℤ)) := by
  rfl

theorem boundedFactorialDeterminant_eq_generalStrictMatrix
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    boundedFactorialDeterminant shape =
      Matrix.det
        (generalFactorialScalarMatrix shape.toStrictShiftedTuple.values) := by
  unfold boundedFactorialDeterminant
  apply congrArg Matrix.det
  apply Matrix.ext
  intro row column
  unfold factorialKernelMatrix generalFactorialScalarMatrix
  unfold generalFactorialScalarRow BoundedPartition.shiftedRows
  rw [BoundedPartition.toStrictShiftedTuple_values]
  push_cast
  rfl

theorem strictGeneralMatrix_eq_boundedFactorialDeterminant
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    Matrix.det (generalFactorialScalarMatrix tuple.values) =
      boundedFactorialDeterminant tuple.toBoundedPartition := by
  rw [boundedFactorialDeterminant_eq_generalStrictMatrix]
  rw [tuple.roundtrip_values]

/-- Arbitrary-rank Frobenius summation on strict shifted coordinates.  This
is the uniform producer that the rank-4/5/6 exterior constructions had
previously established separately. -/
theorem unrestrictedCount_div_factorial_eq_sum_strictShifted
    (rank size : ℕ) :
    (unrestrictedCount rank size : ℚ) / (size.factorial : ℚ) =
      ∑ tuple : StrictShiftedTuple rank size,
        Matrix.det (generalFactorialScalarMatrix tuple.values) := by
  rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  push_cast
  rw [← (boundedPartitionStrictShiftedEquiv rank size).sum_comp]
  have hfactorial : (size.factorial : ℚ) ≠ 0 := by positivity
  apply (div_eq_iff hfactorial).2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro shape hshape
  change (standardTableauNumber shape : ℚ) =
    Matrix.det (generalFactorialScalarMatrix
      shape.toStrictShiftedTuple.values) * (size.factorial : ℚ)
  rw [← boundedFactorialDeterminant_eq_generalStrictMatrix shape,
    standardTableauNumber_eq_factorial_mul_boundedFactorialDeterminant]
  ring

noncomputable def generalUnrestrictedFactorialSeries (rank : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun size =>
    (unrestrictedCount rank size : ℚ) / (size.factorial : ℚ)

@[simp] theorem generalUnrestrictedFactorialSeries_coeff
    (rank size : ℕ) :
    PowerSeries.coeff size (generalUnrestrictedFactorialSeries rank) =
      (unrestrictedCount rank size : ℚ) / (size.factorial : ℚ) := by
  simp [generalUnrestrictedFactorialSeries]

theorem generalUnrestrictedFactorialSeries_coeff_eq_strictShifted
    (rank size : ℕ) :
    PowerSeries.coeff size (generalUnrestrictedFactorialSeries rank) =
      ∑ tuple : StrictShiftedTuple rank size,
        Matrix.det (generalFactorialScalarMatrix tuple.values) := by
  rw [generalUnrestrictedFactorialSeries_coeff,
    unrestrictedCount_div_factorial_eq_sum_strictShifted]

end FibonacciRibbonKernel
