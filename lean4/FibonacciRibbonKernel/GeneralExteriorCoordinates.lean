import FibonacciRibbonKernel.GeneralExteriorCoefficient
import FibonacciRibbonKernel.GeneralClosedCoordinates
import Mathlib.LinearAlgebra.Pi

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

abbrev GeneralSeriesRow (dimension : ℕ) := Fin dimension → ℚ⟦X⟧

noncomputable def generalBasisVector
    (dimension : ℕ) (index : Fin dimension) : GeneralSeriesRow dimension :=
  (Pi.basisFun ℚ⟦X⟧ (Fin dimension)) index

noncomputable def generalOneForm
    {dimension : ℕ} (coordinates : GeneralSeriesRow dimension) :
    ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension) :=
  ∑ index, coordinates index •
    ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension index)

noncomputable def generalFullTwoForm
    {dimension : ℕ} (coordinates : Fin dimension → Fin dimension → ℚ⟦X⟧) :
    ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension) :=
  ∑ left, ∑ right, coordinates left right •
    (ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension left) *
      ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension right))

noncomputable def generalTwoForm
    {dimension : ℕ} (coordinates : Fin dimension → Fin dimension → ℚ⟦X⟧) :
    ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension) :=
  PowerSeries.C (1 / 2 : ℚ) • generalFullTwoForm coordinates

theorem generalSeriesRow_basis_expansion
    {dimension : ℕ} (row : GeneralSeriesRow dimension) :
    row = ∑ index, row index • generalBasisVector dimension index := by
  symm
  simpa [generalBasisVector] using
    (Pi.basisFun ℚ⟦X⟧ (Fin dimension)).sum_repr row

theorem iota_generalSeriesRow_eq_oneForm
    {dimension : ℕ} (row : GeneralSeriesRow dimension) :
    ExteriorAlgebra.ι ℚ⟦X⟧ row = generalOneForm row := by
  conv_lhs => rw [generalSeriesRow_basis_expansion row]
  simp [generalOneForm]

theorem generalOneForm_mul
    {dimension : ℕ} (left right : GeneralSeriesRow dimension) :
    generalOneForm left * generalOneForm right =
      generalFullTwoForm (fun i j => left i * right j) := by
  unfold generalOneForm generalFullTwoForm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem generalFullTwoForm_swap
    {dimension : ℕ}
    (coordinates : Fin dimension → Fin dimension → ℚ⟦X⟧) :
    generalFullTwoForm (fun i j => coordinates j i) =
      -generalFullTwoForm coordinates := by
  unfold generalFullTwoForm
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iota_mul_iota_neg (R := ℚ⟦X⟧)
    (generalBasisVector dimension j) (generalBasisVector dimension i)]
  rw [smul_neg]

theorem generalFullTwoForm_sub
    {dimension : ℕ}
    (left right : Fin dimension → Fin dimension → ℚ⟦X⟧) :
    generalFullTwoForm (fun i j => left i j - right i j) =
      generalFullTwoForm left - generalFullTwoForm right := by
  unfold generalFullTwoForm
  simp only [sub_smul, Finset.sum_sub_distrib]

theorem generalOneForm_mul_eq_twoForm
    {dimension : ℕ} (left right : GeneralSeriesRow dimension) :
    generalOneForm left * generalOneForm right =
      generalTwoForm (fun i j => left i * right j - left j * right i) := by
  rw [generalOneForm_mul]
  unfold generalTwoForm
  rw [generalFullTwoForm_sub]
  have hswap := generalFullTwoForm_swap
    (fun i j => left i * right j)
  rw [show generalFullTwoForm (fun i j => left j * right i) =
      -generalFullTwoForm (fun i j => left i * right j) from hswap]
  rw [sub_neg_eq_add]
  have htwo : generalFullTwoForm (fun i j => left i * right j) +
      generalFullTwoForm (fun i j => left i * right j) =
        (2 : ℚ⟦X⟧) •
          generalFullTwoForm (fun i j => left i * right j) := by
    rw [two_smul]
  rw [htwo, smul_smul]
  have hscalar : PowerSeries.C (1 / 2 : ℚ) * (2 : ℚ⟦X⟧) = 1 := by
    change PowerSeries.C (1 / 2 : ℚ) * PowerSeries.C 2 = PowerSeries.C 1
    rw [← map_mul]
    norm_num
  rw [hscalar, one_smul]

theorem generalOneForm_add
    {dimension : ℕ} (left right : GeneralSeriesRow dimension) :
    generalOneForm (left + right) = generalOneForm left + generalOneForm right := by
  unfold generalOneForm
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem generalTwoForm_add
    {dimension : ℕ}
    (left right : Fin dimension → Fin dimension → ℚ⟦X⟧) :
    generalTwoForm (fun i j => left i j + right i j) =
      generalTwoForm left + generalTwoForm right := by
  unfold generalTwoForm generalFullTwoForm
  simp only [add_smul, Finset.sum_add_distrib, smul_add]

theorem exteriorElementary_one_eq_generalOneForm
    {dimension : ℕ} (rows : List (GeneralSeriesRow dimension)) :
    exteriorElementary 1 rows = generalOneForm (generalRowSum rows) := by
  induction rows with
  | nil => simp [generalOneForm]
  | cons head tail ih =>
      rw [exteriorElementary_cons_one, generalRowSum_cons,
        generalOneForm_add, ← ih, iota_generalSeriesRow_eq_oneForm]

theorem exteriorElementary_two_eq_generalTwoForm
    {dimension : ℕ} (rows : List (GeneralSeriesRow dimension)) :
    exteriorElementary 2 rows = generalTwoForm (generalPairSum rows) := by
  induction rows with
  | nil => simp [generalTwoForm, generalFullTwoForm]
  | cons head tail ih =>
      rw [exteriorElementary_cons_two]
      change ExteriorAlgebra.ι ℚ⟦X⟧ head * exteriorElementary 1 tail +
          exteriorElementary 2 tail =
        generalTwoForm (fun left right =>
          head left * generalRowSum tail right -
            head right * generalRowSum tail left +
              generalPairSum tail left right)
      rw [iota_generalSeriesRow_eq_oneForm,
        exteriorElementary_one_eq_generalOneForm,
        generalOneForm_mul_eq_twoForm, ih]
      rw [← generalTwoForm_add]

end FibonacciRibbonKernel
