import FibonacciRibbonKernel.GordonExteriorPairPower

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

theorem generalClosedPair_skew
    {dimension : ℕ} (left right : Fin dimension) :
    generalClosedPair left right = -generalClosedPair right left := by
  ext degree
  rw [map_neg, generalClosedPair_coeff_formula,
    generalClosedPair_coeff_formula, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro high hhigh
  split_ifs <;> ring

noncomputable def gordonSkewQ (left right : ℕ) : ℚ⟦X⟧ :=
  if left < right then generalBesselPairQ (right - left)
  else if right < left then -generalBesselPairQ (left - right)
  else 0

theorem generalClosedPair_eq_scaled_gordonSkewQ
    {dimension : ℕ} (left right : Fin dimension) :
    generalClosedPair left right =
      X ^ (left.rev.val + right.rev.val) *
        gordonSkewQ left.val right.val := by
  cases dimension with
  | zero => exact Fin.elim0 left
  | succ rank =>
    by_cases hleft : left.val < right.val
    · have hgap : left.rev.val = right.rev.val + (right.val - left.val) := by
        simp [Fin.rev]
        omega
      rw [generalClosedPair_eq_X_rev_sum_mul_pairQ left right hgap,
        universalPairQ_eq_generalBesselPairQ (right.val - left.val) (by omega)]
      simp [gordonSkewQ, hleft]
    · by_cases hright : right.val < left.val
      · rw [generalClosedPair_skew left right]
        have hgap : right.rev.val = left.rev.val + (left.val - right.val) := by
          simp [Fin.rev]
          omega
        rw [generalClosedPair_eq_X_rev_sum_mul_pairQ right left hgap,
          universalPairQ_eq_generalBesselPairQ (left.val - right.val) (by omega)]
        simp [gordonSkewQ, hleft, hright, add_comm]
      · have heq : left = right := Fin.ext (by omega)
        subst right
        rw [generalClosedPair_self]
        simp [gordonSkewQ]

theorem gordonCumulativeEntry_add_transpose (row column : ℕ) :
    gordonCumulativeEntry row column +
        gordonCumulativeEntry column row =
      2 * generalBesselPairQ (row + column + 1) := by
  by_cases hleft : row < column
  · simp [gordonCumulativeEntry, hleft, hleft.asymm]
    ring
  · by_cases hright : column < row
    · simp [gordonCumulativeEntry, hright, hright.asymm]
      ring
    · have heq : row = column := by omega
      subst column
      simp [gordonCumulativeEntry]
      ring

theorem gordonCumulativeEntry_sub_transpose (row column : ℕ) :
    gordonCumulativeEntry row column -
        gordonCumulativeEntry column row =
      2 * gordonSkewQ row column := by
  by_cases hleft : row < column
  · simp [gordonCumulativeEntry, gordonSkewQ, hleft, hleft.asymm]
    ring
  · by_cases hright : column < row
    · simp [gordonCumulativeEntry, gordonSkewQ, hright, hright.asymm]
      ring
    · have heq : row = column := by omega
      subst column
      simp [gordonCumulativeEntry, gordonSkewQ]

noncomputable def gordonLeftIndex
    (halfDimension : ℕ) (index : Fin halfDimension) :
    Fin (2 * halfDimension) :=
  ⟨halfDimension - 1 - index.val, by omega⟩

noncomputable def gordonRightIndex
    (halfDimension : ℕ) (index : Fin halfDimension) :
    Fin (2 * halfDimension) :=
  ⟨halfDimension + index.val, by omega⟩

theorem gordonLeftIndex_injective (halfDimension : ℕ) :
    Function.Injective (gordonLeftIndex halfDimension) := by
  intro left right heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp [gordonLeftIndex] at hval
  omega

theorem gordonRightIndex_injective (halfDimension : ℕ) :
    Function.Injective (gordonRightIndex halfDimension) := by
  intro left right heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp [gordonRightIndex] at hval
  omega

theorem gordonLeftIndex_ne_rightIndex
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonLeftIndex halfDimension left ≠
      gordonRightIndex halfDimension right := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [gordonLeftIndex, gordonRightIndex] at hval
  omega

@[simp] theorem gordonLeftIndex_eq_iff
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonLeftIndex halfDimension left = gordonLeftIndex halfDimension right ↔
      left = right :=
  (gordonLeftIndex_injective halfDimension).eq_iff

@[simp] theorem gordonRightIndex_eq_iff
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonRightIndex halfDimension left = gordonRightIndex halfDimension right ↔
      left = right :=
  (gordonRightIndex_injective halfDimension).eq_iff

@[simp] theorem gordonLeftIndex_eq_rightIndex_iff
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonLeftIndex halfDimension left = gordonRightIndex halfDimension right ↔
      False := by
  constructor
  · intro h
    exact gordonLeftIndex_ne_rightIndex halfDimension left right h
  · intro h
    contradiction

@[simp] theorem gordonRightIndex_eq_leftIndex_iff
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonRightIndex halfDimension left = gordonLeftIndex halfDimension right ↔
      False := by
  constructor
  · intro h
    exact gordonLeftIndex_ne_rightIndex halfDimension right left h.symm
  · intro h
    contradiction

@[simp] theorem gordonLeftIndex_rev_val
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonLeftIndex halfDimension index).rev.val =
      halfDimension + index.val := by
  simp [gordonLeftIndex, Fin.rev]
  omega

@[simp] theorem gordonRightIndex_rev_val
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonRightIndex halfDimension index).rev.val =
      halfDimension - 1 - index.val := by
  simp [gordonRightIndex, Fin.rev]
  omega

noncomputable def gordonScaledBasis
    (halfDimension : ℕ) (index : Fin (2 * halfDimension)) :
    GeneralSeriesRow (2 * halfDimension) :=
  (X : ℚ⟦X⟧) ^ index.rev.val •
    generalBasisVector (2 * halfDimension) index

@[simp] theorem generalBasisVector_apply
    (dimension : ℕ) (index column : Fin dimension) :
    generalBasisVector dimension index column =
      if index = column then 1 else 0 := by
  rw [generalBasisVector, Pi.basisFun_apply]
  by_cases heq : index = column
  · subst column
    simp
  · have hreverse : column ≠ index := by
      intro h
      exact heq h.symm
    simp [heq, hreverse]

@[simp] theorem gordonScaledBasis_apply
    (halfDimension : ℕ) (index column : Fin (2 * halfDimension)) :
    gordonScaledBasis halfDimension index column =
      if index = column then X ^ index.rev.val else 0 := by
  unfold gordonScaledBasis
  simp

noncomputable def gordonPlusRow
    (halfDimension : ℕ) (index : Fin halfDimension) :
    GeneralSeriesRow (2 * halfDimension) :=
  gordonScaledBasis halfDimension (gordonLeftIndex halfDimension index) +
    gordonScaledBasis halfDimension (gordonRightIndex halfDimension index)

noncomputable def gordonMinusRow
    (halfDimension : ℕ) (index : Fin halfDimension) :
    GeneralSeriesRow (2 * halfDimension) :=
  gordonScaledBasis halfDimension (gordonLeftIndex halfDimension index) -
    gordonScaledBasis halfDimension (gordonRightIndex halfDimension index)

@[simp] theorem gordonPlusRow_apply_left
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonPlusRow halfDimension row (gordonLeftIndex halfDimension column) =
      if row = column then X ^ (halfDimension + row.val) else 0 := by
  by_cases heq : row = column
  · subst column
    simp only [gordonPlusRow, Pi.add_apply, gordonScaledBasis_apply,
      gordonRightIndex_eq_leftIndex_iff,
      if_pos, if_false, add_zero, gordonLeftIndex_rev_val]
  ·
    simp only [gordonPlusRow, Pi.add_apply, gordonScaledBasis_apply,
      gordonLeftIndex_eq_iff, gordonRightIndex_eq_leftIndex_iff,
      heq, if_false, zero_add]

@[simp] theorem gordonPlusRow_apply_right
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonPlusRow halfDimension row (gordonRightIndex halfDimension column) =
      if row = column then X ^ (halfDimension - 1 - row.val) else 0 := by
  by_cases heq : row = column
  · subst column
    simp only [gordonPlusRow, Pi.add_apply, gordonScaledBasis_apply,
      gordonLeftIndex_eq_rightIndex_iff,
      if_false, if_pos, zero_add, gordonRightIndex_rev_val]
  ·
    simp only [gordonPlusRow, Pi.add_apply, gordonScaledBasis_apply,
      gordonLeftIndex_eq_rightIndex_iff, gordonRightIndex_eq_iff,
      heq, if_false, add_zero]

@[simp] theorem gordonMinusRow_apply_left
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMinusRow halfDimension row (gordonLeftIndex halfDimension column) =
      if row = column then X ^ (halfDimension + row.val) else 0 := by
  by_cases heq : row = column
  · subst column
    simp only [gordonMinusRow, Pi.sub_apply, gordonScaledBasis_apply,
      gordonRightIndex_eq_leftIndex_iff,
      if_pos, if_false, sub_zero, gordonLeftIndex_rev_val]
  ·
    simp only [gordonMinusRow, Pi.sub_apply, gordonScaledBasis_apply,
      gordonLeftIndex_eq_iff, gordonRightIndex_eq_leftIndex_iff,
      heq, if_false, sub_self]

@[simp] theorem gordonMinusRow_apply_right
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMinusRow halfDimension row (gordonRightIndex halfDimension column) =
      if row = column then -(X ^ (halfDimension - 1 - row.val)) else 0 := by
  by_cases heq : row = column
  · subst column
    simp only [gordonMinusRow, Pi.sub_apply, gordonScaledBasis_apply,
      gordonLeftIndex_eq_rightIndex_iff,
      if_false, if_pos, zero_sub, gordonRightIndex_rev_val]
  ·
    simp only [gordonMinusRow, Pi.sub_apply, gordonScaledBasis_apply,
      gordonLeftIndex_eq_rightIndex_iff, gordonRightIndex_eq_iff,
      heq, if_false, sub_self]

noncomputable def gordonHalfScalar : ℚ⟦X⟧ :=
  PowerSeries.C (1 / 2 : ℚ)

theorem gordonHalfScalar_mul_two :
    gordonHalfScalar * 2 = 1 := by
  unfold gordonHalfScalar
  change PowerSeries.C (1 / 2 : ℚ) * PowerSeries.C 2 = PowerSeries.C 1
  rw [← map_mul]
  norm_num

theorem gordonSkewQ_leftIndices
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonSkewQ (gordonLeftIndex halfDimension left).val
        (gordonLeftIndex halfDimension right).val =
      -gordonSkewQ left.val right.val := by
  by_cases hleft : left.val < right.val
  · have hindex : (gordonLeftIndex halfDimension right).val <
        (gordonLeftIndex halfDimension left).val := by
      change halfDimension - 1 - right.val <
        halfDimension - 1 - left.val
      omega
    have hnot : ¬(gordonLeftIndex halfDimension left).val <
        (gordonLeftIndex halfDimension right).val := by omega
    have hsub : (gordonLeftIndex halfDimension left).val -
        (gordonLeftIndex halfDimension right).val =
          right.val - left.val := by
      change (halfDimension - 1 - left.val) -
        (halfDimension - 1 - right.val) = right.val - left.val
      omega
    simp only [gordonSkewQ, if_neg hnot, if_pos hindex,
      if_pos hleft, hsub]
  · by_cases hright : right.val < left.val
    · have hindex : (gordonLeftIndex halfDimension left).val <
          (gordonLeftIndex halfDimension right).val := by
        change halfDimension - 1 - left.val <
          halfDimension - 1 - right.val
        omega
      have hsub : (gordonLeftIndex halfDimension right).val -
          (gordonLeftIndex halfDimension left).val =
            left.val - right.val := by
        change (halfDimension - 1 - right.val) -
          (halfDimension - 1 - left.val) = left.val - right.val
        omega
      simp only [gordonSkewQ, if_pos hindex, if_neg hleft,
        if_pos hright, hsub, neg_neg]
    · have heq : left = right := Fin.ext (by omega)
      subst right
      simp [gordonSkewQ]

theorem gordonSkewQ_rightIndices
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonSkewQ (gordonRightIndex halfDimension left).val
        (gordonRightIndex halfDimension right).val =
      gordonSkewQ left.val right.val := by
  by_cases hleft : left.val < right.val
  · have hindex : (gordonRightIndex halfDimension left).val <
        (gordonRightIndex halfDimension right).val := by
      change halfDimension + left.val < halfDimension + right.val
      omega
    have hsub : (gordonRightIndex halfDimension right).val -
        (gordonRightIndex halfDimension left).val =
          right.val - left.val := by
      change (halfDimension + right.val) - (halfDimension + left.val) =
        right.val - left.val
      omega
    simp only [gordonSkewQ, if_pos hindex, if_pos hleft, hsub]
  · by_cases hright : right.val < left.val
    · have hindex : (gordonRightIndex halfDimension right).val <
          (gordonRightIndex halfDimension left).val := by
        change halfDimension + right.val < halfDimension + left.val
        omega
      have hnot : ¬(gordonRightIndex halfDimension left).val <
          (gordonRightIndex halfDimension right).val := by omega
      have hsub : (gordonRightIndex halfDimension left).val -
          (gordonRightIndex halfDimension right).val =
            left.val - right.val := by
        change (halfDimension + left.val) - (halfDimension + right.val) =
          left.val - right.val
        omega
      simp only [gordonSkewQ, if_neg hnot, if_pos hindex,
        if_neg hleft, if_pos hright, hsub]
    · have heq : left = right := Fin.ext (by omega)
      subst right
      simp [gordonSkewQ]

theorem gordonSkewQ_left_rightIndices
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonSkewQ (gordonLeftIndex halfDimension left).val
        (gordonRightIndex halfDimension right).val =
      generalBesselPairQ (left.val + right.val + 1) := by
  have hindex : (gordonLeftIndex halfDimension left).val <
      (gordonRightIndex halfDimension right).val := by
    change halfDimension - 1 - left.val < halfDimension + right.val
    omega
  have hsub : (gordonRightIndex halfDimension right).val -
      (gordonLeftIndex halfDimension left).val =
        left.val + right.val + 1 := by
    change (halfDimension + right.val) -
      (halfDimension - 1 - left.val) = left.val + right.val + 1
    omega
  simp only [gordonSkewQ, if_pos hindex, hsub]

noncomputable def gordonMixedRow
    (halfDimension : ℕ) (row : Fin halfDimension) :
    GeneralSeriesRow (2 * halfDimension) :=
  (-gordonHalfScalar) •
    ∑ column, gordonCumulativeEntry row.val column.val •
      gordonMinusRow halfDimension column

@[simp] theorem gordonMixedRow_apply_left
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixedRow halfDimension row (gordonLeftIndex halfDimension column) =
      -gordonHalfScalar * gordonCumulativeEntry row.val column.val *
        X ^ (halfDimension + column.val) := by
  simp [gordonMixedRow]
  ring

@[simp] theorem gordonMixedRow_apply_right
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixedRow halfDimension row (gordonRightIndex halfDimension column) =
      gordonHalfScalar * gordonCumulativeEntry row.val column.val *
        X ^ (halfDimension - 1 - column.val) := by
  simp [gordonMixedRow]
  ring

noncomputable def gordonOuterCoordinate
    (halfDimension : ℕ)
    (left right : Fin (2 * halfDimension)) : ℚ⟦X⟧ :=
  ∑ row, (gordonPlusRow halfDimension row left *
      gordonMixedRow halfDimension row right -
    gordonPlusRow halfDimension row right *
      gordonMixedRow halfDimension row left)

theorem gordonOuterCoordinate_skew
    (halfDimension : ℕ) (left right : Fin (2 * halfDimension)) :
    gordonOuterCoordinate halfDimension left right =
      -gordonOuterCoordinate halfDimension right left := by
  unfold gordonOuterCoordinate
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro row hrow
  ring

theorem gordonOuterCoordinate_left_left
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOuterCoordinate halfDimension
        (gordonLeftIndex halfDimension left)
        (gordonLeftIndex halfDimension right) =
      generalClosedPair (gordonLeftIndex halfDimension left)
        (gordonLeftIndex halfDimension right) := by
  rw [generalClosedPair_eq_scaled_gordonSkewQ,
    gordonSkewQ_leftIndices]
  rw [gordonLeftIndex_rev_val, gordonLeftIndex_rev_val]
  simp [gordonOuterCoordinate]
  rw [Finset.sum_add_distrib]
  simp
  rw [show
      -(X ^ (halfDimension + left.val) *
            (gordonHalfScalar *
              gordonCumulativeEntry left.val right.val *
                X ^ (halfDimension + right.val))) +
          X ^ (halfDimension + right.val) *
            (gordonHalfScalar *
              gordonCumulativeEntry right.val left.val *
                X ^ (halfDimension + left.val)) =
        -gordonHalfScalar *
          (gordonCumulativeEntry left.val right.val -
            gordonCumulativeEntry right.val left.val) *
          (X ^ (halfDimension + left.val) *
            X ^ (halfDimension + right.val)) by ring,
    gordonCumulativeEntry_sub_transpose]
  rw [← pow_add]
  rw [show -gordonHalfScalar * (2 * gordonSkewQ left.val right.val) =
      -(gordonHalfScalar * 2) * gordonSkewQ left.val right.val by ring,
    gordonHalfScalar_mul_two]
  ring

theorem gordonOuterCoordinate_right_right
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOuterCoordinate halfDimension
        (gordonRightIndex halfDimension left)
        (gordonRightIndex halfDimension right) =
      generalClosedPair (gordonRightIndex halfDimension left)
        (gordonRightIndex halfDimension right) := by
  rw [generalClosedPair_eq_scaled_gordonSkewQ,
    gordonSkewQ_rightIndices]
  rw [gordonRightIndex_rev_val, gordonRightIndex_rev_val]
  simp [gordonOuterCoordinate]
  rw [show
      X ^ (halfDimension - 1 - left.val) *
            (gordonHalfScalar *
              gordonCumulativeEntry left.val right.val *
                X ^ (halfDimension - 1 - right.val)) -
          X ^ (halfDimension - 1 - right.val) *
            (gordonHalfScalar *
              gordonCumulativeEntry right.val left.val *
                X ^ (halfDimension - 1 - left.val)) =
        gordonHalfScalar *
          (gordonCumulativeEntry left.val right.val -
            gordonCumulativeEntry right.val left.val) *
          (X ^ (halfDimension - 1 - left.val) *
            X ^ (halfDimension - 1 - right.val)) by ring,
    gordonCumulativeEntry_sub_transpose]
  rw [← pow_add]
  rw [← mul_assoc gordonHalfScalar 2,
    gordonHalfScalar_mul_two, one_mul]
  ring

theorem gordonOuterCoordinate_left_right
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOuterCoordinate halfDimension
        (gordonLeftIndex halfDimension left)
        (gordonRightIndex halfDimension right) =
      generalClosedPair (gordonLeftIndex halfDimension left)
        (gordonRightIndex halfDimension right) := by
  rw [generalClosedPair_eq_scaled_gordonSkewQ,
    gordonSkewQ_left_rightIndices]
  rw [gordonLeftIndex_rev_val, gordonRightIndex_rev_val]
  simp [gordonOuterCoordinate]
  rw [Finset.sum_add_distrib]
  simp
  rw [show
      X ^ (halfDimension + left.val) *
            (gordonHalfScalar *
              gordonCumulativeEntry left.val right.val *
                X ^ (halfDimension - 1 - right.val)) +
          X ^ (halfDimension - 1 - right.val) *
            (gordonHalfScalar *
              gordonCumulativeEntry right.val left.val *
                X ^ (halfDimension + left.val)) =
        gordonHalfScalar *
          (gordonCumulativeEntry left.val right.val +
            gordonCumulativeEntry right.val left.val) *
          (X ^ (halfDimension + left.val) *
            X ^ (halfDimension - 1 - right.val)) by ring,
    gordonCumulativeEntry_add_transpose]
  rw [← pow_add]
  rw [← mul_assoc gordonHalfScalar 2,
    gordonHalfScalar_mul_two, one_mul]
  ring

theorem gordonOuterCoordinate_right_left
    (halfDimension : ℕ) (left right : Fin halfDimension) :
    gordonOuterCoordinate halfDimension
        (gordonRightIndex halfDimension left)
        (gordonLeftIndex halfDimension right) =
      generalClosedPair (gordonRightIndex halfDimension left)
        (gordonLeftIndex halfDimension right) := by
  rw [gordonOuterCoordinate_skew, generalClosedPair_skew]
  exact congrArg Neg.neg
    (gordonOuterCoordinate_left_right halfDimension right left)

theorem gordonIndex_cases
    (halfDimension : ℕ) (index : Fin (2 * halfDimension)) :
    (∃ source : Fin halfDimension,
        index = gordonLeftIndex halfDimension source) ∨
      ∃ source : Fin halfDimension,
        index = gordonRightIndex halfDimension source := by
  by_cases hleft : index.val < halfDimension
  · let source : Fin halfDimension :=
      ⟨halfDimension - 1 - index.val, by omega⟩
    left
    refine ⟨source, Fin.ext ?_⟩
    simp [source, gordonLeftIndex]
    omega
  · have hright : halfDimension ≤ index.val := by omega
    let source : Fin halfDimension :=
      ⟨index.val - halfDimension, by omega⟩
    right
    refine ⟨source, Fin.ext ?_⟩
    simp [source, gordonRightIndex]
    omega

theorem gordonOuterCoordinate_eq_closedPair
    (halfDimension : ℕ) (left right : Fin (2 * halfDimension)) :
    gordonOuterCoordinate halfDimension left right =
      generalClosedPair left right := by
  rcases gordonIndex_cases halfDimension left with
    ⟨leftSource, rfl⟩ | ⟨leftSource, rfl⟩ <;>
  rcases gordonIndex_cases halfDimension right with
    ⟨rightSource, rfl⟩ | ⟨rightSource, rfl⟩
  · exact gordonOuterCoordinate_left_left halfDimension leftSource rightSource
  · exact gordonOuterCoordinate_left_right halfDimension leftSource rightSource
  · exact gordonOuterCoordinate_right_left halfDimension leftSource rightSource
  · exact gordonOuterCoordinate_right_right halfDimension leftSource rightSource

theorem generalTwoForm_fintype_sum
    {dimension count : ℕ}
    (coordinates : Fin count → Fin dimension → Fin dimension → ℚ⟦X⟧) :
    generalTwoForm (fun left right =>
        ∑ index, coordinates index left right) =
      ∑ index, generalTwoForm (coordinates index) := by
  unfold generalTwoForm generalFullTwoForm
  simp only [Finset.sum_smul, Finset.smul_sum]
  calc
    (∑ left, ∑ right, ∑ index,
        PowerSeries.C (1 / 2 : ℚ) •
          coordinates index left right •
            (ExteriorAlgebra.ι ℚ⟦X⟧
                (generalBasisVector dimension left) *
              ExteriorAlgebra.ι ℚ⟦X⟧
                (generalBasisVector dimension right))) =
      ∑ left, ∑ index, ∑ right,
        PowerSeries.C (1 / 2 : ℚ) •
          coordinates index left right •
            (ExteriorAlgebra.ι ℚ⟦X⟧
                (generalBasisVector dimension left) *
              ExteriorAlgebra.ι ℚ⟦X⟧
                (generalBasisVector dimension right)) := by
        apply Finset.sum_congr rfl
        intro left hleft
        rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

noncomputable def gordonPairTwoForm (halfDimension : ℕ) :
    ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow (2 * halfDimension)) :=
  (exteriorIotaPairList (R := ℚ⟦X⟧)
    (gordonPlusRow halfDimension) (gordonMixedRow halfDimension)).sum

theorem gordonPairTwoForm_eq_closedTwoForm (halfDimension : ℕ) :
    gordonPairTwoForm halfDimension =
      generalTwoForm (fun left right : Fin (2 * halfDimension) =>
        generalClosedPair left right) := by
  unfold gordonPairTwoForm exteriorIotaPairList
  rw [List.sum_ofFn]
  simp_rw [iota_generalSeriesRow_eq_oneForm,
    generalOneForm_mul_eq_twoForm]
  rw [← generalTwoForm_fintype_sum]
  apply congrArg generalTwoForm
  funext left right
  exact gordonOuterCoordinate_eq_closedPair halfDimension left right

noncomputable def gordonInterleavedRows (halfDimension : ℕ) :
    List (GeneralSeriesRow (2 * halfDimension)) :=
  (List.ofFn fun index : Fin halfDimension =>
    [gordonPlusRow halfDimension index,
      gordonMixedRow halfDimension index]).flatten

noncomputable def gordonInterleavedEquiv (halfDimension : ℕ) :
    Fin halfDimension × Fin 2 ≃ Fin (2 * halfDimension) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm halfDimension 2))

noncomputable def gordonInterleavedRow
    (halfDimension : ℕ) (row : Fin (2 * halfDimension)) :
    GeneralSeriesRow (2 * halfDimension) :=
  let source := (gordonInterleavedEquiv halfDimension).symm row
  ![gordonPlusRow halfDimension source.1,
    gordonMixedRow halfDimension source.1] source.2

@[simp] theorem gordonInterleavedRow_even
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonInterleavedRow halfDimension
        (gordonInterleavedEquiv halfDimension (index, 0)) =
      gordonPlusRow halfDimension index := by
  simp [gordonInterleavedRow]

@[simp] theorem gordonInterleavedRow_odd
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonInterleavedRow halfDimension
        (gordonInterleavedEquiv halfDimension (index, 1)) =
      gordonMixedRow halfDimension index := by
  simp [gordonInterleavedRow]

theorem gordonInterleavedRows_eq_ofFn (halfDimension : ℕ) :
    gordonInterleavedRows halfDimension =
      List.ofFn (gordonInterleavedRow halfDimension) := by
  unfold gordonInterleavedRows
  symm
  rw [List.ofFn_congr (Nat.mul_comm 2 halfDimension)]
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  rw [List.ofFn_inj]
  funext index
  rw [List.ofFn_succ]
  congr 1
  · convert gordonInterleavedRow_even halfDimension index using 1
    apply congrArg (gordonInterleavedRow halfDimension)
    apply Fin.ext
    simp [gordonInterleavedEquiv, finProdFinEquiv]
    omega
  · rw [List.ofFn_succ]
    congr 1
    · convert gordonInterleavedRow_odd halfDimension index using 1
      apply congrArg (gordonInterleavedRow halfDimension)
      apply Fin.ext
      simp [gordonInterleavedEquiv, finProdFinEquiv]
      omega

theorem gordonInterleavedRows_length (halfDimension : ℕ) :
    (gordonInterleavedRows halfDimension).length = 2 * halfDimension := by
  unfold gordonInterleavedRows
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  simp
  omega

theorem listRowsOfLength_gordonInterleavedRows
    (halfDimension : ℕ) :
    listRowsOfLength (gordonInterleavedRows halfDimension)
        (gordonInterleavedRows_length halfDimension) =
      gordonInterleavedRow halfDimension := by
  funext row
  unfold listRowsOfLength
  simp [gordonInterleavedRows_eq_ofFn]

theorem exteriorIotaPairList_prod_eq_interleaved
    (halfDimension : ℕ) :
    (exteriorIotaPairList (R := ℚ⟦X⟧)
      (gordonPlusRow halfDimension) (gordonMixedRow halfDimension)).prod =
      exteriorListProduct (R := ℚ⟦X⟧)
        (gordonInterleavedRows halfDimension) := by
  rw [exteriorListProduct_eq_map_prod]
  unfold exteriorIotaPairList gordonInterleavedRows
  rw [List.map_flatten, List.prod_flatten]
  apply congrArg List.prod
  rw [← List.ofFn_comp', ← List.ofFn_comp']
  rw [List.ofFn_inj]
  funext index
  simp

theorem generalClosedEvenAssembly_eq_interleaved_det
    (halfDimension : ℕ) :
    generalClosedEvenAssembly halfDimension =
      (halfDimension.factorial : ℚ⟦X⟧) *
        Matrix.det (listRowsOfLength
          (gordonInterleavedRows halfDimension)
          (gordonInterleavedRows_length halfDimension)) := by
  unfold generalClosedEvenAssembly
  rw [← gordonPairTwoForm_eq_closedTwoForm]
  unfold gordonPairTwoForm
  rw [exteriorIotaPairList_sum_pow]
  rw [map_smul]
  rw [exteriorIotaPairList_prod_eq_interleaved]
  rw [generalTopDeterminant_exteriorListProduct]
  rfl

end FibonacciRibbonKernel
