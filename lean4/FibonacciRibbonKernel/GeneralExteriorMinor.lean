import FibonacciRibbonKernel.GeneralFactorialRows
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries

variable {R : Type*} [CommRing R]

noncomputable def generalTopAlternating
    (dimension degree : ℕ) :
    GeneralRow dimension R [⋀^Fin degree]→ₗ[R] R := by
  classical
  by_cases hdegree : degree = dimension
  · subst degree
    exact Matrix.detRowAlternating
  · exact 0

/-- Top exterior determinant coefficient in arbitrary finite dimension. -/
noncomputable def generalTopDeterminant (dimension : ℕ) :
    ExteriorAlgebra R (GeneralRow dimension R) →ₗ[R] R :=
  ExteriorAlgebra.liftAlternating
    (generalTopAlternating (R := R) dimension)

theorem generalTopDeterminant_iMulti
    (dimension : ℕ) (rows : Fin dimension → GeneralRow dimension R) :
    generalTopDeterminant (R := R) dimension
        (ExteriorAlgebra.ιMulti R dimension rows) =
      Matrix.det rows := by
  rw [generalTopDeterminant,
    ExteriorAlgebra.liftAlternating_apply_ιMulti]
  simp only [generalTopAlternating, dite_true]
  change Matrix.detRowAlternating rows = Matrix.det rows
  rfl

noncomputable def listRowsOfLength
    {dimension : ℕ} (rows : List (GeneralRow dimension R))
    (hlength : rows.length = dimension) :
    Fin dimension → GeneralRow dimension R :=
  fun index => rows.get (Fin.cast hlength.symm index)

theorem exteriorListProduct_eq_map_prod
    {M : Type*} [AddCommGroup M] [Module R M] (rows : List M) :
    exteriorListProduct (R := R) rows =
      (rows.map (ExteriorAlgebra.ι R)).prod := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
      simp [exteriorListProduct, ih]

theorem exteriorListProduct_eq_iMulti_listRows
    {dimension : ℕ} (rows : List (GeneralRow dimension R))
    (hlength : rows.length = dimension) :
    exteriorListProduct (R := R) rows =
      ExteriorAlgebra.ιMulti R dimension
        (listRowsOfLength rows hlength) := by
  rw [exteriorListProduct_eq_map_prod, ExteriorAlgebra.ιMulti_apply]
  apply congrArg List.prod
  apply List.ext_get_iff.mpr
  constructor
  · simp [hlength]
  · intro index hleft hright
    simp [listRowsOfLength]
    rfl

theorem generalTopDeterminant_exteriorListProduct
    {dimension : ℕ} (rows : List (GeneralRow dimension R))
    (hlength : rows.length = dimension) :
    generalTopDeterminant (R := R) dimension
        (exteriorListProduct (R := R) rows) =
      Matrix.det (listRowsOfLength rows hlength) := by
  rw [exteriorListProduct_eq_iMulti_listRows rows hlength,
    generalTopDeterminant_iMulti]

noncomputable def generalSelectedDeterminant
    (dimension : ℕ) (rows : List (GeneralRow dimension R)) : R :=
  if hlength : rows.length = dimension then
    Matrix.det (listRowsOfLength rows hlength)
  else 0

/-- Arbitrary-dimensional finite minor-summation identity. -/
theorem generalTopDeterminant_exteriorElementary_eq_sum_sublists
    (dimension : ℕ) (rows : List (GeneralRow dimension R)) :
    generalTopDeterminant (R := R) dimension
        (exteriorElementary dimension rows) =
      ((rows.sublistsLen dimension).map fun selected =>
        generalSelectedDeterminant dimension selected).sum := by
  rw [exteriorElementary_eq_sum_sublistsLen]
  simp only [map_list_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro selected hselected
  have hlength := List.length_of_sublistsLen hselected
  rw [generalSelectedDeterminant, dif_pos hlength]
  exact generalTopDeterminant_exteriorListProduct selected hlength

theorem generalTopDeterminant_factorial_iMulti
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    generalTopDeterminant (R := ℚ⟦X⟧) dimension
        (ExteriorAlgebra.ιMulti (ℚ⟦X⟧) dimension
          (fun row => generalFactorialPowerSeriesRow dimension (values row))) =
      PowerSeries.monomial (∑ row, values row)
        (Matrix.det (generalFactorialScalarMatrix values)) := by
  rw [generalTopDeterminant_iMulti]
  change Matrix.det (generalFactorialPowerSeriesMatrix values) = _
  exact det_generalFactorialPowerSeriesRows values

theorem generalTopDeterminant_strictShiftedTuple
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    generalTopDeterminant (R := ℚ⟦X⟧) (rank + 1)
        (ExteriorAlgebra.ιMulti (ℚ⟦X⟧) (rank + 1)
          (fun row => generalFactorialPowerSeriesRow (rank + 1)
            (tuple.values row))) =
      PowerSeries.monomial (size + staircaseWeight rank)
        (boundedFactorialDeterminant tuple.toBoundedPartition) := by
  rw [generalTopDeterminant_factorial_iMulti, tuple.sum_eq,
    strictGeneralMatrix_eq_boundedFactorialDeterminant]

noncomputable def generalExteriorTruncation (dimension bound : ℕ) : ℚ⟦X⟧ :=
  generalTopDeterminant (R := ℚ⟦X⟧) dimension
    (exteriorElementary dimension
      ((List.range bound).reverse.map
        (generalFactorialPowerSeriesRow dimension)))

theorem generalExteriorTruncation_eq_selected_sum
    (dimension bound : ℕ) :
    generalExteriorTruncation dimension bound =
      ((((List.range bound).reverse.map
          (generalFactorialPowerSeriesRow dimension)).sublistsLen dimension).map
        (generalSelectedDeterminant dimension)).sum := by
  unfold generalExteriorTruncation
  exact generalTopDeterminant_exteriorElementary_eq_sum_sublists
    dimension ((List.range bound).reverse.map
      (generalFactorialPowerSeriesRow dimension))

end FibonacciRibbonKernel
