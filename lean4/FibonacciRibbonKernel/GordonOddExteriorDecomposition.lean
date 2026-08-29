import FibonacciRibbonKernel.GordonOddPfaffianDeterminant

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

theorem gordonSkewQ_skew (left right : ℕ) :
    gordonSkewQ left right = -gordonSkewQ right left := by
  by_cases hleft : left < right
  · simp [gordonSkewQ, hleft, hleft.asymm]
  · by_cases hright : right < left
    · simp [gordonSkewQ, hright, hright.asymm]
    · have heq : left = right := by omega
      subst right
      simp [gordonSkewQ]

noncomputable def gordonOddLeftIndex
    (halfDimension : ℕ) (index : Fin halfDimension) :
    Fin (2 * halfDimension + 1) :=
  ⟨halfDimension - 1 - index.val, by omega⟩

noncomputable def gordonOddCenterIndex (halfDimension : ℕ) :
    Fin (2 * halfDimension + 1) :=
  ⟨halfDimension, by omega⟩

noncomputable def gordonOddRightIndex
    (halfDimension : ℕ) (index : Fin halfDimension) :
    Fin (2 * halfDimension + 1) :=
  ⟨halfDimension + 1 + index.val, by omega⟩

theorem gordonOddLeftIndex_injective (halfDimension : ℕ) :
    Function.Injective (gordonOddLeftIndex halfDimension) := by
  intro left right heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp [gordonOddLeftIndex] at hval
  omega

theorem gordonOddRightIndex_injective (halfDimension : ℕ) :
    Function.Injective (gordonOddRightIndex halfDimension) := by
  intro left right heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp [gordonOddRightIndex] at hval
  omega

@[simp] theorem gordonOddLeftIndex_eq_iff
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOddLeftIndex halfDimension left =
        gordonOddLeftIndex halfDimension right ↔ left = right :=
  (gordonOddLeftIndex_injective halfDimension).eq_iff

@[simp] theorem gordonOddRightIndex_eq_iff
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOddRightIndex halfDimension left =
        gordonOddRightIndex halfDimension right ↔ left = right :=
  (gordonOddRightIndex_injective halfDimension).eq_iff

@[simp] theorem gordonOddLeftIndex_ne_center
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddLeftIndex halfDimension index ≠
      gordonOddCenterIndex halfDimension := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [gordonOddLeftIndex, gordonOddCenterIndex] at hval
  omega

@[simp] theorem gordonOddRightIndex_ne_center
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddRightIndex halfDimension index ≠
      gordonOddCenterIndex halfDimension := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [gordonOddRightIndex, gordonOddCenterIndex] at hval
  omega

@[simp] theorem gordonOddLeftIndex_ne_rightIndex
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOddLeftIndex halfDimension left ≠
      gordonOddRightIndex halfDimension right := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [gordonOddLeftIndex, gordonOddRightIndex] at hval
  omega

@[simp] theorem gordonOddRightIndex_ne_leftIndex
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOddRightIndex halfDimension left ≠
      gordonOddLeftIndex halfDimension right :=
  (gordonOddLeftIndex_ne_rightIndex halfDimension right left).symm

@[simp] theorem gordonOddLeftIndex_rev_val
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonOddLeftIndex halfDimension index).rev.val =
      halfDimension + 1 + index.val := by
  simp [gordonOddLeftIndex, Fin.rev]
  omega

@[simp] theorem gordonOddCenterIndex_rev_val (halfDimension : ℕ) :
    (gordonOddCenterIndex halfDimension).rev.val = halfDimension := by
  simp [gordonOddCenterIndex, Fin.rev]
  omega

@[simp] theorem gordonOddRightIndex_rev_val
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonOddRightIndex halfDimension index).rev.val =
      halfDimension - 1 - index.val := by
  simp [gordonOddRightIndex, Fin.rev]
  omega

noncomputable def gordonOddScaledBasis
    (halfDimension : ℕ) (index : Fin (2 * halfDimension + 1)) :
    GeneralSeriesRow (2 * halfDimension + 1) :=
  (X : ℚ⟦X⟧) ^ index.rev.val •
    generalBasisVector (2 * halfDimension + 1) index

noncomputable def gordonOddPlusRow
    (halfDimension : ℕ) (index : Fin halfDimension) :
    GeneralSeriesRow (2 * halfDimension + 1) :=
  gordonOddScaledBasis halfDimension (gordonOddLeftIndex halfDimension index) +
    gordonOddScaledBasis halfDimension (gordonOddRightIndex halfDimension index)

noncomputable def gordonOddMinusRow
    (halfDimension : ℕ) (index : Fin halfDimension) :
    GeneralSeriesRow (2 * halfDimension + 1) :=
  gordonOddScaledBasis halfDimension (gordonOddLeftIndex halfDimension index) -
    gordonOddScaledBasis halfDimension (gordonOddRightIndex halfDimension index)

noncomputable def gordonOddUnitRow (halfDimension : ℕ) :
    GeneralSeriesRow (2 * halfDimension + 1) :=
  fun column => X ^ column.rev.val

noncomputable def gordonOddMixedRow
    (halfDimension : ℕ) (row : Fin halfDimension) :
    GeneralSeriesRow (2 * halfDimension + 1) :=
  gordonHalfScalar •
    ∑ column, gordonOddCumulativeEntry row.val column.val •
      gordonOddMinusRow halfDimension column

noncomputable def gordonOddBoundaryRow (halfDimension : ℕ) :
    GeneralSeriesRow (2 * halfDimension + 1) :=
  ∑ column, generalBesselPairQ (column.val + 1) •
    gordonOddMinusRow halfDimension column

@[simp] theorem gordonOddScaledBasis_apply
    (halfDimension : ℕ) (index column : Fin (2 * halfDimension + 1)) :
    gordonOddScaledBasis halfDimension index column =
      if index = column then X ^ index.rev.val else 0 := by
  simp [gordonOddScaledBasis]

@[simp] theorem gordonOddPlusRow_apply_left
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddPlusRow halfDimension row
        (gordonOddLeftIndex halfDimension column) =
      if row = column then X ^ (halfDimension + 1 + row.val) else 0 := by
  by_cases heq : row = column
  · subst column
    simp [gordonOddPlusRow]
    congr 1
    simp [gordonOddLeftIndex]
    omega
  · simp [gordonOddPlusRow, heq]

@[simp] theorem gordonOddPlusRow_apply_right
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddPlusRow halfDimension row
        (gordonOddRightIndex halfDimension column) =
      if row = column then X ^ (halfDimension - 1 - row.val) else 0 := by
  by_cases heq : row = column
  · subst column
    simp [gordonOddPlusRow]
    congr 1
    simp [gordonOddRightIndex]
    omega
  · simp [gordonOddPlusRow, heq]

@[simp] theorem gordonOddPlusRow_apply_center
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddPlusRow halfDimension row
        (gordonOddCenterIndex halfDimension) = 0 := by
  simp [gordonOddPlusRow]

@[simp] theorem gordonOddMinusRow_apply_left
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMinusRow halfDimension row
        (gordonOddLeftIndex halfDimension column) =
      if row = column then X ^ (halfDimension + 1 + row.val) else 0 := by
  by_cases heq : row = column
  · subst column
    simp [gordonOddMinusRow]
    congr 1
    simp [gordonOddLeftIndex]
    omega
  · simp [gordonOddMinusRow, heq]

@[simp] theorem gordonOddMinusRow_apply_right
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMinusRow halfDimension row
        (gordonOddRightIndex halfDimension column) =
      if row = column then -(X ^ (halfDimension - 1 - row.val)) else 0 := by
  by_cases heq : row = column
  · subst column
    simp [gordonOddMinusRow]
    congr 1
    simp [gordonOddRightIndex]
    omega
  · simp [gordonOddMinusRow, heq]

@[simp] theorem gordonOddMinusRow_apply_center
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddMinusRow halfDimension row
        (gordonOddCenterIndex halfDimension) = 0 := by
  simp [gordonOddMinusRow]

@[simp] theorem gordonOddMixedRow_apply_left
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixedRow halfDimension row
        (gordonOddLeftIndex halfDimension column) =
      gordonHalfScalar * gordonOddCumulativeEntry row.val column.val *
        X ^ (halfDimension + 1 + column.val) := by
  simp [gordonOddMixedRow]
  ring

@[simp] theorem gordonOddMixedRow_apply_right
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixedRow halfDimension row
        (gordonOddRightIndex halfDimension column) =
      -gordonHalfScalar * gordonOddCumulativeEntry row.val column.val *
        X ^ (halfDimension - 1 - column.val) := by
  simp [gordonOddMixedRow]
  ring

@[simp] theorem gordonOddMixedRow_apply_center
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddMixedRow halfDimension row
        (gordonOddCenterIndex halfDimension) = 0 := by
  simp [gordonOddMixedRow]

@[simp] theorem gordonOddBoundaryRow_apply_left
    (halfDimension : ℕ) (column : Fin halfDimension) :
    gordonOddBoundaryRow halfDimension
        (gordonOddLeftIndex halfDimension column) =
      generalBesselPairQ (column.val + 1) *
        X ^ (halfDimension + 1 + column.val) := by
  simp [gordonOddBoundaryRow]

@[simp] theorem gordonOddBoundaryRow_apply_right
    (halfDimension : ℕ) (column : Fin halfDimension) :
    gordonOddBoundaryRow halfDimension
        (gordonOddRightIndex halfDimension column) =
      -generalBesselPairQ (column.val + 1) *
        X ^ (halfDimension - 1 - column.val) := by
  simp [gordonOddBoundaryRow]

@[simp] theorem gordonOddBoundaryRow_apply_center
    (halfDimension : ℕ) :
    gordonOddBoundaryRow halfDimension
        (gordonOddCenterIndex halfDimension) = 0 := by
  simp [gordonOddBoundaryRow]

@[simp] theorem gordonOddUnitRow_apply_left
    (halfDimension : ℕ) (column : Fin halfDimension) :
    gordonOddUnitRow halfDimension
        (gordonOddLeftIndex halfDimension column) =
      X ^ (halfDimension + 1 + column.val) := by
  simp [gordonOddUnitRow]
  congr 1
  simp [gordonOddLeftIndex]
  omega

@[simp] theorem gordonOddUnitRow_apply_right
    (halfDimension : ℕ) (column : Fin halfDimension) :
    gordonOddUnitRow halfDimension
        (gordonOddRightIndex halfDimension column) =
      X ^ (halfDimension - 1 - column.val) := by
  simp [gordonOddUnitRow]
  congr 1
  simp [gordonOddRightIndex]
  omega

@[simp] theorem gordonOddUnitRow_apply_center (halfDimension : ℕ) :
    gordonOddUnitRow halfDimension (gordonOddCenterIndex halfDimension) =
      X ^ halfDimension := by
  simp [gordonOddUnitRow]
  congr 1
  simp [gordonOddCenterIndex]
  omega

theorem generalClosedSingle_eq_exp_smul_oddUnit
    (halfDimension : ℕ) :
    (fun column : Fin (2 * halfDimension + 1) =>
        generalClosedSingle column) =
      PowerSeries.exp ℚ • gordonOddUnitRow halfDimension := by
  funext column
  unfold generalClosedSingle gordonOddUnitRow
  simp
  ring

theorem gordonOddCumulativeEntry_sub_transpose (row column : ℕ) :
    gordonOddCumulativeEntry row column -
        gordonOddCumulativeEntry column row =
      2 * (generalBesselPairQ (column + 1) -
        generalBesselPairQ (row + 1) - gordonSkewQ row column) := by
  unfold gordonOddCumulativeEntry
  rw [show column + row + 2 = row + column + 2 by omega,
    gordonSkewQ_skew]
  ring

theorem gordonOddCumulativeEntry_add_transpose (row column : ℕ) :
    gordonOddCumulativeEntry row column +
        gordonOddCumulativeEntry column row =
      2 * (generalBesselPairQ (column + 1) +
        generalBesselPairQ (row + 1) -
          generalBesselPairQ (row + column + 2)) := by
  unfold gordonOddCumulativeEntry
  rw [show column + row + 2 = row + column + 2 by omega,
    gordonSkewQ_skew]
  ring

theorem gordonSkewQ_oddLeftIndices
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonSkewQ (gordonOddLeftIndex halfDimension left).val
        (gordonOddLeftIndex halfDimension right).val =
      -gordonSkewQ left.val right.val := by
  by_cases hleft : left.val < right.val
  · have hindex : (gordonOddLeftIndex halfDimension right).val <
        (gordonOddLeftIndex halfDimension left).val := by
      change halfDimension - 1 - right.val <
        halfDimension - 1 - left.val
      omega
    have hnot : ¬(gordonOddLeftIndex halfDimension left).val <
        (gordonOddLeftIndex halfDimension right).val := by omega
    have hsub : (gordonOddLeftIndex halfDimension left).val -
        (gordonOddLeftIndex halfDimension right).val =
          right.val - left.val := by
      change (halfDimension - 1 - left.val) -
        (halfDimension - 1 - right.val) = right.val - left.val
      omega
    simp only [gordonSkewQ, if_neg hnot, if_pos hindex,
      if_pos hleft, hsub]
  · by_cases hright : right.val < left.val
    · have hindex : (gordonOddLeftIndex halfDimension left).val <
          (gordonOddLeftIndex halfDimension right).val := by
        change halfDimension - 1 - left.val <
          halfDimension - 1 - right.val
        omega
      have hsub : (gordonOddLeftIndex halfDimension right).val -
          (gordonOddLeftIndex halfDimension left).val =
            left.val - right.val := by
        change (halfDimension - 1 - right.val) -
          (halfDimension - 1 - left.val) = left.val - right.val
        omega
      simp only [gordonSkewQ, if_pos hindex, if_neg hleft,
        if_pos hright, hsub, neg_neg]
    · have heq : left = right := Fin.ext (by omega)
      subst right
      simp [gordonSkewQ]

theorem gordonSkewQ_oddRightIndices
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonSkewQ (gordonOddRightIndex halfDimension left).val
        (gordonOddRightIndex halfDimension right).val =
      gordonSkewQ left.val right.val := by
  by_cases hleft : left.val < right.val
  · have hindex : (gordonOddRightIndex halfDimension left).val <
        (gordonOddRightIndex halfDimension right).val := by
      change halfDimension + 1 + left.val < halfDimension + 1 + right.val
      omega
    have hsub : (gordonOddRightIndex halfDimension right).val -
        (gordonOddRightIndex halfDimension left).val =
          right.val - left.val := by
      change (halfDimension + 1 + right.val) -
          (halfDimension + 1 + left.val) = right.val - left.val
      omega
    simp only [gordonSkewQ, if_pos hindex, if_pos hleft, hsub]
  · by_cases hright : right.val < left.val
    · have hindex : (gordonOddRightIndex halfDimension right).val <
          (gordonOddRightIndex halfDimension left).val := by
        change halfDimension + 1 + right.val < halfDimension + 1 + left.val
        omega
      have hnot : ¬(gordonOddRightIndex halfDimension left).val <
          (gordonOddRightIndex halfDimension right).val := by omega
      have hsub : (gordonOddRightIndex halfDimension left).val -
          (gordonOddRightIndex halfDimension right).val =
            left.val - right.val := by
        change (halfDimension + 1 + left.val) -
          (halfDimension + 1 + right.val) = left.val - right.val
        omega
      simp only [gordonSkewQ, if_neg hnot, if_pos hindex,
        if_neg hleft, if_pos hright, hsub]
    · have heq : left = right := Fin.ext (by omega)
      subst right
      simp [gordonSkewQ]

theorem gordonSkewQ_oddLeft_rightIndices
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonSkewQ (gordonOddLeftIndex halfDimension left).val
        (gordonOddRightIndex halfDimension right).val =
      generalBesselPairQ (left.val + right.val + 2) := by
  have hindex : (gordonOddLeftIndex halfDimension left).val <
      (gordonOddRightIndex halfDimension right).val := by
    change halfDimension - 1 - left.val <
      halfDimension + 1 + right.val
    omega
  have hsub : (gordonOddRightIndex halfDimension right).val -
      (gordonOddLeftIndex halfDimension left).val =
        left.val + right.val + 2 := by
    change (halfDimension + 1 + right.val) -
      (halfDimension - 1 - left.val) = left.val + right.val + 2
    omega
  simp only [gordonSkewQ, if_pos hindex, hsub]

noncomputable def gordonOddOuterCoordinate
    (halfDimension : ℕ)
    (left right : Fin (2 * halfDimension + 1)) : ℚ⟦X⟧ :=
  (∑ row, (gordonOddPlusRow halfDimension row left *
      gordonOddMixedRow halfDimension row right -
    gordonOddPlusRow halfDimension row right *
      gordonOddMixedRow halfDimension row left)) +
    (gordonOddBoundaryRow halfDimension left *
        gordonOddUnitRow halfDimension right -
      gordonOddBoundaryRow halfDimension right *
        gordonOddUnitRow halfDimension left)

theorem gordonOddOuterCoordinate_skew
    (halfDimension : ℕ) (left right : Fin (2 * halfDimension + 1)) :
    gordonOddOuterCoordinate halfDimension left right =
      -gordonOddOuterCoordinate halfDimension right left := by
  unfold gordonOddOuterCoordinate
  have hpair :
      (∑ row, (gordonOddPlusRow halfDimension row left *
          gordonOddMixedRow halfDimension row right -
        gordonOddPlusRow halfDimension row right *
          gordonOddMixedRow halfDimension row left)) =
        -(∑ row, (gordonOddPlusRow halfDimension row right *
          gordonOddMixedRow halfDimension row left -
        gordonOddPlusRow halfDimension row left *
          gordonOddMixedRow halfDimension row right)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro row hrow
    ring
  rw [hpair]
  ring

theorem gordonOddOuterCoordinate_left_left
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddLeftIndex halfDimension left)
        (gordonOddLeftIndex halfDimension right) =
      generalClosedPair (gordonOddLeftIndex halfDimension left)
        (gordonOddLeftIndex halfDimension right) := by
  rw [generalClosedPair_eq_scaled_gordonSkewQ,
    gordonSkewQ_oddLeftIndices]
  rw [gordonOddLeftIndex_rev_val, gordonOddLeftIndex_rev_val]
  simp [gordonOddOuterCoordinate]
  rw [show
      X ^ (halfDimension + 1 + left.val) *
            (gordonHalfScalar *
              gordonOddCumulativeEntry left.val right.val *
                X ^ (halfDimension + 1 + right.val)) -
          X ^ (halfDimension + 1 + right.val) *
            (gordonHalfScalar *
              gordonOddCumulativeEntry right.val left.val *
                X ^ (halfDimension + 1 + left.val)) +
          (generalBesselPairQ (left.val + 1) *
                X ^ (halfDimension + 1 + left.val) *
              X ^ (halfDimension + 1 + right.val) -
            generalBesselPairQ (right.val + 1) *
                X ^ (halfDimension + 1 + right.val) *
              X ^ (halfDimension + 1 + left.val)) =
        (gordonHalfScalar *
            (gordonOddCumulativeEntry left.val right.val -
              gordonOddCumulativeEntry right.val left.val) +
          generalBesselPairQ (left.val + 1) -
            generalBesselPairQ (right.val + 1)) *
          (X ^ (halfDimension + 1 + left.val) *
            X ^ (halfDimension + 1 + right.val)) by ring,
    gordonOddCumulativeEntry_sub_transpose]
  rw [show gordonHalfScalar *
          (2 * (generalBesselPairQ (right.val + 1) -
            generalBesselPairQ (left.val + 1) -
              gordonSkewQ left.val right.val)) =
        (gordonHalfScalar * 2) *
          (generalBesselPairQ (right.val + 1) -
            generalBesselPairQ (left.val + 1) -
              gordonSkewQ left.val right.val) by ring,
    gordonHalfScalar_mul_two, one_mul]
  rw [← pow_add]
  ring

theorem gordonOddOuterCoordinate_right_right
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddRightIndex halfDimension left)
        (gordonOddRightIndex halfDimension right) =
      generalClosedPair (gordonOddRightIndex halfDimension left)
        (gordonOddRightIndex halfDimension right) := by
  rw [generalClosedPair_eq_scaled_gordonSkewQ,
    gordonSkewQ_oddRightIndices]
  rw [gordonOddRightIndex_rev_val, gordonOddRightIndex_rev_val]
  simp [gordonOddOuterCoordinate]
  rw [Finset.sum_add_distrib]
  simp
  rw [show
      -(X ^ (halfDimension - 1 - left.val) *
            (gordonHalfScalar *
              gordonOddCumulativeEntry left.val right.val *
                X ^ (halfDimension - 1 - right.val))) +
          X ^ (halfDimension - 1 - right.val) *
            (gordonHalfScalar *
              gordonOddCumulativeEntry right.val left.val *
                X ^ (halfDimension - 1 - left.val)) +
          (-(generalBesselPairQ (left.val + 1) *
                X ^ (halfDimension - 1 - left.val) *
              X ^ (halfDimension - 1 - right.val)) +
            generalBesselPairQ (right.val + 1) *
                X ^ (halfDimension - 1 - right.val) *
              X ^ (halfDimension - 1 - left.val)) =
        (-gordonHalfScalar *
            (gordonOddCumulativeEntry left.val right.val -
              gordonOddCumulativeEntry right.val left.val) -
          generalBesselPairQ (left.val + 1) +
            generalBesselPairQ (right.val + 1)) *
          (X ^ (halfDimension - 1 - left.val) *
            X ^ (halfDimension - 1 - right.val)) by ring,
    gordonOddCumulativeEntry_sub_transpose]
  rw [show -gordonHalfScalar *
          (2 * (generalBesselPairQ (right.val + 1) -
            generalBesselPairQ (left.val + 1) -
              gordonSkewQ left.val right.val)) =
        -(gordonHalfScalar * 2) *
          (generalBesselPairQ (right.val + 1) -
            generalBesselPairQ (left.val + 1) -
              gordonSkewQ left.val right.val) by ring,
    gordonHalfScalar_mul_two]
  rw [← pow_add]
  ring

theorem gordonOddOuterCoordinate_left_right
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddLeftIndex halfDimension left)
        (gordonOddRightIndex halfDimension right) =
      generalClosedPair (gordonOddLeftIndex halfDimension left)
        (gordonOddRightIndex halfDimension right) := by
  rw [generalClosedPair_eq_scaled_gordonSkewQ,
    gordonSkewQ_oddLeft_rightIndices]
  rw [gordonOddLeftIndex_rev_val, gordonOddRightIndex_rev_val]
  simp [gordonOddOuterCoordinate]
  rw [show
      -(X ^ (halfDimension + 1 + left.val) *
            (gordonHalfScalar *
              gordonOddCumulativeEntry left.val right.val *
                X ^ (halfDimension - 1 - right.val))) -
          X ^ (halfDimension - 1 - right.val) *
            (gordonHalfScalar *
              gordonOddCumulativeEntry right.val left.val *
                X ^ (halfDimension + 1 + left.val)) +
          (generalBesselPairQ (left.val + 1) *
                X ^ (halfDimension + 1 + left.val) *
              X ^ (halfDimension - 1 - right.val) +
            generalBesselPairQ (right.val + 1) *
                X ^ (halfDimension - 1 - right.val) *
              X ^ (halfDimension + 1 + left.val)) =
        (-gordonHalfScalar *
            (gordonOddCumulativeEntry left.val right.val +
              gordonOddCumulativeEntry right.val left.val) +
          generalBesselPairQ (left.val + 1) +
            generalBesselPairQ (right.val + 1)) *
          (X ^ (halfDimension + 1 + left.val) *
            X ^ (halfDimension - 1 - right.val)) by ring,
    gordonOddCumulativeEntry_add_transpose]
  rw [show -gordonHalfScalar *
          (2 * (generalBesselPairQ (right.val + 1) +
            generalBesselPairQ (left.val + 1) -
              generalBesselPairQ (left.val + right.val + 2))) =
        -(gordonHalfScalar * 2) *
          (generalBesselPairQ (right.val + 1) +
            generalBesselPairQ (left.val + 1) -
              generalBesselPairQ (left.val + right.val + 2)) by ring,
    gordonHalfScalar_mul_two]
  rw [← pow_add]
  ring

theorem gordonSkewQ_oddLeft_center
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonSkewQ (gordonOddLeftIndex halfDimension index).val
        (gordonOddCenterIndex halfDimension).val =
      generalBesselPairQ (index.val + 1) := by
  have hindex : (gordonOddLeftIndex halfDimension index).val <
      (gordonOddCenterIndex halfDimension).val := by
    change halfDimension - 1 - index.val < halfDimension
    omega
  have hsub : (gordonOddCenterIndex halfDimension).val -
      (gordonOddLeftIndex halfDimension index).val = index.val + 1 := by
    change halfDimension - (halfDimension - 1 - index.val) = index.val + 1
    omega
  simp only [gordonSkewQ, if_pos hindex, hsub]

theorem gordonSkewQ_oddRight_center
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonSkewQ (gordonOddRightIndex halfDimension index).val
        (gordonOddCenterIndex halfDimension).val =
      -generalBesselPairQ (index.val + 1) := by
  have hindex : (gordonOddCenterIndex halfDimension).val <
      (gordonOddRightIndex halfDimension index).val := by
    change halfDimension < halfDimension + 1 + index.val
    omega
  have hnot : ¬(gordonOddRightIndex halfDimension index).val <
      (gordonOddCenterIndex halfDimension).val := by omega
  have hsub : (gordonOddRightIndex halfDimension index).val -
      (gordonOddCenterIndex halfDimension).val = index.val + 1 := by
    change (halfDimension + 1 + index.val) - halfDimension = index.val + 1
    omega
  simp only [gordonSkewQ, if_neg hnot, if_pos hindex, hsub]

theorem gordonOddOuterCoordinate_left_center
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddLeftIndex halfDimension index)
        (gordonOddCenterIndex halfDimension) =
      generalClosedPair (gordonOddLeftIndex halfDimension index)
        (gordonOddCenterIndex halfDimension) := by
  rw [generalClosedPair_eq_scaled_gordonSkewQ,
    gordonSkewQ_oddLeft_center]
  rw [gordonOddLeftIndex_rev_val, gordonOddCenterIndex_rev_val]
  simp [gordonOddOuterCoordinate]
  rw [show generalBesselPairQ (index.val + 1) *
          X ^ (halfDimension + 1 + index.val) * X ^ halfDimension =
        (X ^ (halfDimension + 1 + index.val) * X ^ halfDimension) *
          generalBesselPairQ (index.val + 1) by ring,
    ← pow_add]

theorem gordonOddOuterCoordinate_right_center
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddRightIndex halfDimension index)
        (gordonOddCenterIndex halfDimension) =
      generalClosedPair (gordonOddRightIndex halfDimension index)
        (gordonOddCenterIndex halfDimension) := by
  rw [generalClosedPair_eq_scaled_gordonSkewQ,
    gordonSkewQ_oddRight_center]
  rw [gordonOddRightIndex_rev_val, gordonOddCenterIndex_rev_val]
  simp [gordonOddOuterCoordinate]
  rw [show generalBesselPairQ (index.val + 1) *
          X ^ (halfDimension - 1 - index.val) * X ^ halfDimension =
        (X ^ (halfDimension - 1 - index.val) * X ^ halfDimension) *
          generalBesselPairQ (index.val + 1) by ring,
    ← pow_add]

theorem gordonOddOuterCoordinate_center_center (halfDimension : ℕ) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddCenterIndex halfDimension)
        (gordonOddCenterIndex halfDimension) =
      generalClosedPair (gordonOddCenterIndex halfDimension)
        (gordonOddCenterIndex halfDimension) := by
  rw [generalClosedPair_self]
  simp [gordonOddOuterCoordinate]

theorem gordonOddOuterCoordinate_right_left
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddRightIndex halfDimension left)
        (gordonOddLeftIndex halfDimension right) =
      generalClosedPair (gordonOddRightIndex halfDimension left)
        (gordonOddLeftIndex halfDimension right) := by
  rw [gordonOddOuterCoordinate_skew, generalClosedPair_skew]
  exact congrArg Neg.neg
    (gordonOddOuterCoordinate_left_right halfDimension right left)

theorem gordonOddOuterCoordinate_center_left
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddCenterIndex halfDimension)
        (gordonOddLeftIndex halfDimension index) =
      generalClosedPair (gordonOddCenterIndex halfDimension)
        (gordonOddLeftIndex halfDimension index) := by
  rw [gordonOddOuterCoordinate_skew, generalClosedPair_skew]
  exact congrArg Neg.neg
    (gordonOddOuterCoordinate_left_center halfDimension index)

theorem gordonOddOuterCoordinate_center_right
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddOuterCoordinate halfDimension
        (gordonOddCenterIndex halfDimension)
        (gordonOddRightIndex halfDimension index) =
      generalClosedPair (gordonOddCenterIndex halfDimension)
        (gordonOddRightIndex halfDimension index) := by
  rw [gordonOddOuterCoordinate_skew, generalClosedPair_skew]
  exact congrArg Neg.neg
    (gordonOddOuterCoordinate_right_center halfDimension index)

theorem gordonOddIndex_cases
    (halfDimension : ℕ) (index : Fin (2 * halfDimension + 1)) :
    (∃ source : Fin halfDimension,
        index = gordonOddLeftIndex halfDimension source) ∨
      index = gordonOddCenterIndex halfDimension ∨
        ∃ source : Fin halfDimension,
          index = gordonOddRightIndex halfDimension source := by
  by_cases hleft : index.val < halfDimension
  · let source : Fin halfDimension :=
      ⟨halfDimension - 1 - index.val, by omega⟩
    left
    refine ⟨source, Fin.ext ?_⟩
    simp [source, gordonOddLeftIndex]
    omega
  · by_cases hcenter : index.val = halfDimension
    · right
      left
      exact Fin.ext hcenter
    · have hright : halfDimension + 1 ≤ index.val := by omega
      let source : Fin halfDimension :=
        ⟨index.val - (halfDimension + 1), by omega⟩
      right
      right
      refine ⟨source, Fin.ext ?_⟩
      simp [source, gordonOddRightIndex]
      omega

theorem gordonOddOuterCoordinate_eq_closedPair
    (halfDimension : ℕ)
    (left right : Fin (2 * halfDimension + 1)) :
    gordonOddOuterCoordinate halfDimension left right =
      generalClosedPair left right := by
  rcases gordonOddIndex_cases halfDimension left with
    ⟨leftSource, rfl⟩ | rfl | ⟨leftSource, rfl⟩ <;>
  rcases gordonOddIndex_cases halfDimension right with
    ⟨rightSource, rfl⟩ | rfl | ⟨rightSource, rfl⟩
  · exact gordonOddOuterCoordinate_left_left halfDimension leftSource rightSource
  · exact gordonOddOuterCoordinate_left_center halfDimension leftSource
  · exact gordonOddOuterCoordinate_left_right halfDimension leftSource rightSource
  · exact gordonOddOuterCoordinate_center_left halfDimension rightSource
  · exact gordonOddOuterCoordinate_center_center halfDimension
  · exact gordonOddOuterCoordinate_center_right halfDimension rightSource
  · exact gordonOddOuterCoordinate_right_left halfDimension leftSource rightSource
  · exact gordonOddOuterCoordinate_right_center halfDimension leftSource
  · exact gordonOddOuterCoordinate_right_right halfDimension leftSource rightSource

noncomputable def gordonOddPairTwoForm (halfDimension : ℕ) :
    ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow (2 * halfDimension + 1)) :=
  (exteriorIotaPairList (R := ℚ⟦X⟧)
    (gordonOddPlusRow halfDimension) (gordonOddMixedRow halfDimension)).sum

noncomputable def gordonOddUnitForm (halfDimension : ℕ) :
    ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow (2 * halfDimension + 1)) :=
  generalOneForm (gordonOddUnitRow halfDimension)

noncomputable def gordonOddBoundaryForm (halfDimension : ℕ) :
    ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow (2 * halfDimension + 1)) :=
  generalOneForm (gordonOddBoundaryRow halfDimension) *
    gordonOddUnitForm halfDimension

theorem gordonOddPairTwoForm_eq_coordinate (halfDimension : ℕ) :
    gordonOddPairTwoForm halfDimension =
      generalTwoForm (fun left right : Fin (2 * halfDimension + 1) =>
        ∑ row, (gordonOddPlusRow halfDimension row left *
          gordonOddMixedRow halfDimension row right -
        gordonOddPlusRow halfDimension row right *
          gordonOddMixedRow halfDimension row left)) := by
  unfold gordonOddPairTwoForm exteriorIotaPairList
  rw [List.sum_ofFn]
  simp_rw [iota_generalSeriesRow_eq_oneForm,
    generalOneForm_mul_eq_twoForm]
  rw [← generalTwoForm_fintype_sum]

theorem gordonOddBoundaryForm_eq_coordinate (halfDimension : ℕ) :
    gordonOddBoundaryForm halfDimension =
      generalTwoForm (fun left right : Fin (2 * halfDimension + 1) =>
        gordonOddBoundaryRow halfDimension left *
            gordonOddUnitRow halfDimension right -
          gordonOddBoundaryRow halfDimension right *
            gordonOddUnitRow halfDimension left) := by
  unfold gordonOddBoundaryForm gordonOddUnitForm
  exact generalOneForm_mul_eq_twoForm
    (gordonOddBoundaryRow halfDimension) (gordonOddUnitRow halfDimension)

theorem gordonClosedOddTwoForm_decomposition (halfDimension : ℕ) :
    generalTwoForm (fun left right : Fin (2 * halfDimension + 1) =>
        generalClosedPair left right) =
      gordonOddPairTwoForm halfDimension +
        gordonOddBoundaryForm halfDimension := by
  rw [gordonOddPairTwoForm_eq_coordinate,
    gordonOddBoundaryForm_eq_coordinate, ← generalTwoForm_add]
  apply congrArg generalTwoForm
  funext left right
  exact (gordonOddOuterCoordinate_eq_closedPair
    halfDimension left right).symm

theorem generalOneForm_smul
    {dimension : ℕ} (scalar : ℚ⟦X⟧)
    (row : GeneralSeriesRow dimension) :
    generalOneForm (scalar • row) = scalar • generalOneForm row := by
  unfold generalOneForm
  simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem gordonOddPairTwoForm_commutes_unit (halfDimension : ℕ) :
    Commute (gordonOddPairTwoForm halfDimension)
      (gordonOddUnitForm halfDimension) := by
  unfold gordonOddPairTwoForm gordonOddUnitForm exteriorIotaPairList
  apply Commute.list_sum_left
  intro pair hpair
  rw [List.mem_ofFn] at hpair
  obtain ⟨index, rfl⟩ := hpair
  rw [← iota_generalSeriesRow_eq_oneForm]
  have hleft :
      ExteriorAlgebra.ι ℚ⟦X⟧ (gordonOddUnitRow halfDimension) *
          (ExteriorAlgebra.ι ℚ⟦X⟧ (gordonOddPlusRow halfDimension index) *
            ExteriorAlgebra.ι ℚ⟦X⟧ (gordonOddMixedRow halfDimension index)) =
        (ExteriorAlgebra.ι ℚ⟦X⟧ (gordonOddPlusRow halfDimension index) *
            ExteriorAlgebra.ι ℚ⟦X⟧ (gordonOddMixedRow halfDimension index)) *
          ExteriorAlgebra.ι ℚ⟦X⟧ (gordonOddUnitRow halfDimension) := by
    simpa [exteriorElementary] using
      iota_mul_exteriorElementary_two (R := ℚ⟦X⟧)
        (gordonOddUnitRow halfDimension)
        [gordonOddPlusRow halfDimension index,
          gordonOddMixedRow halfDimension index]
  exact hleft.symm

theorem gordonOddBoundaryForm_sq_zero (halfDimension : ℕ) :
    gordonOddBoundaryForm halfDimension *
        gordonOddBoundaryForm halfDimension = 0 := by
  unfold gordonOddBoundaryForm gordonOddUnitForm
  rw [← iota_generalSeriesRow_eq_oneForm,
    ← iota_generalSeriesRow_eq_oneForm]
  exact exterior_iota_pair_sq_zero (R := ℚ⟦X⟧)
    (gordonOddBoundaryRow halfDimension) (gordonOddUnitRow halfDimension)

theorem gordonOddBoundaryForm_commutes_pair (halfDimension : ℕ) :
    Commute (gordonOddBoundaryForm halfDimension)
      (gordonOddPairTwoForm halfDimension) := by
  unfold gordonOddBoundaryForm gordonOddUnitForm
  unfold gordonOddPairTwoForm exteriorIotaPairList
  apply Commute.list_sum_right
  intro pair hpair
  rw [List.mem_ofFn] at hpair
  obtain ⟨index, rfl⟩ := hpair
  rw [← iota_generalSeriesRow_eq_oneForm,
    ← iota_generalSeriesRow_eq_oneForm]
  exact exterior_iota_pairs_commute (R := ℚ⟦X⟧)
    (gordonOddBoundaryRow halfDimension) (gordonOddUnitRow halfDimension)
    (gordonOddPlusRow halfDimension index) (gordonOddMixedRow halfDimension index)

theorem gordonOddBoundaryForm_mul_unit_zero (halfDimension : ℕ) :
    gordonOddBoundaryForm halfDimension *
        gordonOddUnitForm halfDimension = 0 := by
  unfold gordonOddBoundaryForm gordonOddUnitForm
  rw [← iota_generalSeriesRow_eq_oneForm,
    ← iota_generalSeriesRow_eq_oneForm]
  rw [mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero]

theorem gordonClosedOddTwoForm_pow_mul_unit
    (halfDimension : ℕ) :
    (generalTwoForm (fun left right : Fin (2 * halfDimension + 1) =>
        generalClosedPair left right)) ^ halfDimension *
        gordonOddUnitForm halfDimension =
      (gordonOddPairTwoForm halfDimension) ^ halfDimension *
        gordonOddUnitForm halfDimension := by
  rw [gordonClosedOddTwoForm_decomposition]
  have hpower := add_pow_of_commute_sq_zero
    (gordonOddBoundaryForm halfDimension)
    (gordonOddPairTwoForm halfDimension)
    (gordonOddBoundaryForm_commutes_pair halfDimension)
    (gordonOddBoundaryForm_sq_zero halfDimension) halfDimension
  have hpowerPair :
      (gordonOddPairTwoForm halfDimension +
          gordonOddBoundaryForm halfDimension) ^ halfDimension =
        gordonOddPairTwoForm halfDimension ^ halfDimension +
          halfDimension •
            (gordonOddBoundaryForm halfDimension *
              gordonOddPairTwoForm halfDimension ^ (halfDimension - 1)) := by
    calc
      (gordonOddPairTwoForm halfDimension +
          gordonOddBoundaryForm halfDimension) ^ halfDimension =
        (gordonOddBoundaryForm halfDimension +
          gordonOddPairTwoForm halfDimension) ^ halfDimension :=
            congrArg (· ^ halfDimension) (add_comm _ _)
      _ = _ := hpower
  have hcross :
      halfDimension •
          (gordonOddBoundaryForm halfDimension *
            gordonOddPairTwoForm halfDimension ^ (halfDimension - 1)) *
        gordonOddUnitForm halfDimension = 0 := by
    simp only [nsmul_eq_mul, mul_assoc]
    have hcommute :=
      (gordonOddPairTwoForm_commutes_unit halfDimension).pow_left
        (halfDimension - 1)
    rw [hcommute.eq]
    rw [← mul_assoc (gordonOddBoundaryForm halfDimension),
      gordonOddBoundaryForm_mul_unit_zero, zero_mul, mul_zero]
  calc
    (gordonOddPairTwoForm halfDimension +
        gordonOddBoundaryForm halfDimension) ^ halfDimension *
          gordonOddUnitForm halfDimension =
      (gordonOddPairTwoForm halfDimension ^ halfDimension +
        halfDimension •
          (gordonOddBoundaryForm halfDimension *
            gordonOddPairTwoForm halfDimension ^ (halfDimension - 1))) *
        gordonOddUnitForm halfDimension :=
          congrArg (fun element => element * gordonOddUnitForm halfDimension)
            hpowerPair
    _ = _ := by rw [add_mul, hcross, add_zero]

noncomputable def gordonOddInterleavedRows (halfDimension : ℕ) :
    List (GeneralSeriesRow (2 * halfDimension + 1)) :=
  (List.ofFn fun index : Fin halfDimension =>
    [gordonOddPlusRow halfDimension index,
      gordonOddMixedRow halfDimension index]).flatten ++
    [gordonOddUnitRow halfDimension]

theorem gordonOddInterleavedRows_length (halfDimension : ℕ) :
    (gordonOddInterleavedRows halfDimension).length =
      2 * halfDimension + 1 := by
  unfold gordonOddInterleavedRows
  rw [List.length_append, List.length_flatten,
    List.map_ofFn, List.sum_ofFn]
  simp
  omega

theorem exteriorOddIotaPairList_prod_mul_unit_eq_interleaved
    (halfDimension : ℕ) :
    (exteriorIotaPairList (R := ℚ⟦X⟧)
      (gordonOddPlusRow halfDimension)
      (gordonOddMixedRow halfDimension)).prod *
        gordonOddUnitForm halfDimension =
      exteriorListProduct (R := ℚ⟦X⟧)
        (gordonOddInterleavedRows halfDimension) := by
  rw [exteriorListProduct_eq_map_prod]
  unfold gordonOddInterleavedRows gordonOddUnitForm
  rw [List.map_append, List.prod_append]
  simp only [List.map_singleton, List.prod_singleton,
    ← iota_generalSeriesRow_eq_oneForm]
  apply congrArg (· * ExteriorAlgebra.ι ℚ⟦X⟧
    (gordonOddUnitRow halfDimension))
  unfold exteriorIotaPairList
  rw [List.map_flatten, List.prod_flatten]
  apply congrArg List.prod
  rw [← List.ofFn_comp', ← List.ofFn_comp']
  rw [List.ofFn_inj]
  funext index
  simp

theorem generalClosedOddAssembly_eq_interleaved_det
    (halfDimension : ℕ) :
    generalClosedOddAssembly halfDimension =
      (halfDimension.factorial : ℚ⟦X⟧) *
        (PowerSeries.exp ℚ *
          Matrix.det (listRowsOfLength
            (gordonOddInterleavedRows halfDimension)
            (gordonOddInterleavedRows_length halfDimension))) := by
  unfold generalClosedOddAssembly
  rw [generalClosedSingle_eq_exp_smul_oddUnit,
    generalOneForm_smul]
  rw [mul_smul_comm]
  rw [map_smul]
  change PowerSeries.exp ℚ •
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension + 1)
        ((generalTwoForm (fun i j : Fin (2 * halfDimension + 1) =>
          generalClosedPair i j)) ^ halfDimension *
            gordonOddUnitForm halfDimension) = _
  rw [gordonClosedOddTwoForm_pow_mul_unit]
  unfold gordonOddPairTwoForm
  rw [exteriorIotaPairList_sum_pow]
  rw [smul_mul_assoc]
  rw [map_smul]
  rw [exteriorOddIotaPairList_prod_mul_unit_eq_interleaved]
  rw [generalTopDeterminant_exteriorListProduct
    (gordonOddInterleavedRows halfDimension)
    (gordonOddInterleavedRows_length halfDimension)]
  ring

end FibonacciRibbonKernel
