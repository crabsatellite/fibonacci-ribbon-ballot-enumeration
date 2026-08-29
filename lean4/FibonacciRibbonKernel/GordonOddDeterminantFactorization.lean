import FibonacciRibbonKernel.GordonOddExteriorDecomposition

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical Matrix

abbrev GordonOddBlockIndex (halfDimension : ℕ) :=
  (Fin 2 × Fin halfDimension) ⊕ Unit

noncomputable def gordonOddRowEquiv (halfDimension : ℕ) :
    GordonOddBlockIndex halfDimension ≃ Fin (2 * halfDimension + 1) :=
  (Equiv.sumCongr (gordonRowBlockEquiv halfDimension)
      finOneEquiv.symm).trans finSumFinEquiv

noncomputable def gordonOddCoordinateMap
    (halfDimension : ℕ) :
    GordonOddBlockIndex halfDimension → Fin (2 * halfDimension + 1)
  | Sum.inl (tag, index) =>
      if tag = 0 then gordonOddLeftIndex halfDimension index
      else gordonOddRightIndex halfDimension index
  | Sum.inr _ => gordonOddCenterIndex halfDimension

theorem gordonOddCoordinateMap_bijective (halfDimension : ℕ) :
    Function.Bijective (gordonOddCoordinateMap halfDimension) := by
  constructor
  · intro left right heq
    rcases left with ⟨⟨leftTag, leftIndex⟩⟩ | leftUnit <;>
      rcases right with ⟨⟨rightTag, rightIndex⟩⟩ | rightUnit
    · fin_cases leftTag <;> fin_cases rightTag
      · have hindex := gordonOddLeftIndex_injective halfDimension heq
        subst rightIndex
        rfl
      · exfalso
        exact gordonOddLeftIndex_ne_rightIndex halfDimension leftIndex rightIndex heq
      · exfalso
        exact gordonOddRightIndex_ne_leftIndex halfDimension leftIndex rightIndex heq
      · have hindex := gordonOddRightIndex_injective halfDimension heq
        subst rightIndex
        rfl
    · fin_cases leftTag
      · exfalso
        exact gordonOddLeftIndex_ne_center halfDimension leftIndex heq
      · exfalso
        exact gordonOddRightIndex_ne_center halfDimension leftIndex heq
    · fin_cases rightTag
      · exfalso
        exact gordonOddLeftIndex_ne_center halfDimension rightIndex heq.symm
      · exfalso
        exact gordonOddRightIndex_ne_center halfDimension rightIndex heq.symm
    · rfl
  · intro target
    rcases gordonOddIndex_cases halfDimension target with
      ⟨index, rfl⟩ | rfl | ⟨index, rfl⟩
    · exact ⟨Sum.inl (0, index), by simp [gordonOddCoordinateMap]⟩
    · exact ⟨Sum.inr (), by simp [gordonOddCoordinateMap]⟩
    · exact ⟨Sum.inl (1, index), by simp [gordonOddCoordinateMap]⟩

noncomputable def gordonOddCoordinateEquiv (halfDimension : ℕ) :
    GordonOddBlockIndex halfDimension ≃ Fin (2 * halfDimension + 1) :=
  Equiv.ofBijective (gordonOddCoordinateMap halfDimension)
    (gordonOddCoordinateMap_bijective halfDimension)

@[simp] theorem gordonOddRowEquiv_pair_zero
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddRowEquiv halfDimension (Sum.inl (0, index)) =
      (gordonRowBlockEquiv halfDimension (0, index)).castSucc := by
  rfl

@[simp] theorem gordonOddRowEquiv_pair_one
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddRowEquiv halfDimension (Sum.inl (1, index)) =
      (gordonRowBlockEquiv halfDimension (1, index)).castSucc := by
  rfl

@[simp] theorem gordonOddRowEquiv_unit (halfDimension : ℕ) :
    gordonOddRowEquiv halfDimension (Sum.inr ()) =
      Fin.last (2 * halfDimension) := by
  rfl

@[simp] theorem gordonOddCoordinateEquiv_pair_zero
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddCoordinateEquiv halfDimension (Sum.inl (0, index)) =
      gordonOddLeftIndex halfDimension index := by
  rfl

@[simp] theorem gordonOddCoordinateEquiv_pair_one
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddCoordinateEquiv halfDimension (Sum.inl (1, index)) =
      gordonOddRightIndex halfDimension index := by
  rfl

@[simp] theorem gordonOddCoordinateEquiv_unit (halfDimension : ℕ) :
    gordonOddCoordinateEquiv halfDimension (Sum.inr ()) =
      gordonOddCenterIndex halfDimension := by
  rfl

noncomputable def gordonOddCoordinateRowPermutation (halfDimension : ℕ) :
    Equiv.Perm (GordonOddBlockIndex halfDimension) :=
  (gordonOddCoordinateEquiv halfDimension).trans
    (gordonOddRowEquiv halfDimension).symm

noncomputable def gordonOddOrderPermutation (halfDimension : ℕ) :
    Equiv.Perm (Fin (2 * halfDimension + 1)) :=
  (gordonOddRowEquiv halfDimension).symm.trans
    (gordonOddCoordinateEquiv halfDimension)

@[simp] theorem gordonOddOrderPermutation_apply_pair_zero
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddOrderPermutation halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (0, index))) =
      gordonOddCoordinateEquiv halfDimension (Sum.inl (0, index)) := by
  unfold gordonOddOrderPermutation
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]

@[simp] theorem gordonOddOrderPermutation_apply_pair_one
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOddOrderPermutation halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (1, index))) =
      gordonOddCoordinateEquiv halfDimension (Sum.inl (1, index)) := by
  unfold gordonOddOrderPermutation
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]

@[simp] theorem gordonOddOrderPermutation_apply_unit (halfDimension : ℕ) :
    gordonOddOrderPermutation halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inr ())) =
      gordonOddCoordinateEquiv halfDimension (Sum.inr ()) := by
  unfold gordonOddOrderPermutation
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]

theorem gordonOddRowEquiv_pair_zero_val
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonOddRowEquiv halfDimension (Sum.inl (0, index))).val =
      2 * index.val := by
  rw [gordonOddRowEquiv_pair_zero]
  exact gordonRowBlockEquiv_zero_val halfDimension index

theorem gordonOddRowEquiv_pair_one_val
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonOddRowEquiv halfDimension (Sum.inl (1, index))).val =
      2 * index.val + 1 := by
  rw [gordonOddRowEquiv_pair_one]
  exact gordonRowBlockEquiv_one_val halfDimension index

theorem gordonOddOrderPermutation_inner_pair_odd
    (halfDimension : ℕ) (column : Fin halfDimension) :
    ∏ row ∈ Finset.Iio
        (gordonOddRowEquiv halfDimension (Sum.inl (1, column))),
      (if gordonOddOrderPermutation halfDimension row <
          gordonOddOrderPermutation halfDimension
            (gordonOddRowEquiv halfDimension (Sum.inl (1, column)))
        then (1 : ℤˣ) else -1) = 1 := by
  apply Finset.prod_eq_one
  intro row hrow
  rw [if_pos]
  obtain ⟨source, rfl⟩ := (gordonOddRowEquiv halfDimension).surjective row
  rcases source with ⟨⟨tag, index⟩⟩ | _unit
  · fin_cases tag
    · change gordonOddOrderPermutation halfDimension
          (gordonOddRowEquiv halfDimension (Sum.inl (0, index))) <
        gordonOddOrderPermutation halfDimension
          (gordonOddRowEquiv halfDimension (Sum.inl (1, column)))
      rw [gordonOddOrderPermutation_apply_pair_zero,
        gordonOddOrderPermutation_apply_pair_one,
        gordonOddCoordinateEquiv_pair_zero,
        gordonOddCoordinateEquiv_pair_one]
      change (gordonOddLeftIndex halfDimension index).val <
        (gordonOddRightIndex halfDimension column).val
      simp [gordonOddLeftIndex, gordonOddRightIndex]
      omega
    · change gordonOddOrderPermutation halfDimension
          (gordonOddRowEquiv halfDimension (Sum.inl (1, index))) <
        gordonOddOrderPermutation halfDimension
          (gordonOddRowEquiv halfDimension (Sum.inl (1, column)))
      have hposition := Finset.mem_Iio.mp hrow
      change gordonOddRowEquiv halfDimension (Sum.inl (1, index)) <
        gordonOddRowEquiv halfDimension (Sum.inl (1, column)) at hposition
      rw [gordonOddOrderPermutation_apply_pair_one,
        gordonOddOrderPermutation_apply_pair_one,
        gordonOddCoordinateEquiv_pair_one,
        gordonOddCoordinateEquiv_pair_one]
      change (gordonOddRightIndex halfDimension index).val <
        (gordonOddRightIndex halfDimension column).val
      have hpositionVal :
          (gordonOddRowEquiv halfDimension (Sum.inl (1, index))).val <
            (gordonOddRowEquiv halfDimension (Sum.inl (1, column))).val :=
        hposition
      rw [gordonOddRowEquiv_pair_one_val,
        gordonOddRowEquiv_pair_one_val] at hpositionVal
      change halfDimension + 1 + index.val <
        halfDimension + 1 + column.val
      omega
  · have hposition := Finset.mem_Iio.mp hrow
    rw [gordonOddRowEquiv_unit, gordonOddRowEquiv_pair_one] at hposition
    exact absurd hposition (not_lt_of_ge (Fin.le_last _))

theorem gordonOddOrderPermutation_inner_pair_even
    (halfDimension : ℕ) (column : Fin halfDimension) :
    ∏ row ∈ Finset.Iio
        (gordonOddRowEquiv halfDimension (Sum.inl (0, column))),
      (if gordonOddOrderPermutation halfDimension row <
          gordonOddOrderPermutation halfDimension
            (gordonOddRowEquiv halfDimension (Sum.inl (0, column)))
        then (1 : ℤˣ) else -1) = 1 := by
  have hnot : ∀ row ∈ Finset.Iio
      (gordonOddRowEquiv halfDimension (Sum.inl (0, column))),
      ¬gordonOddOrderPermutation halfDimension row <
        gordonOddOrderPermutation halfDimension
          (gordonOddRowEquiv halfDimension (Sum.inl (0, column))) := by
    intro row hrow
    obtain ⟨source, rfl⟩ := (gordonOddRowEquiv halfDimension).surjective row
    rcases source with ⟨⟨tag, index⟩⟩ | _unit
    · have hposition := Finset.mem_Iio.mp hrow
      fin_cases tag
      · change ¬gordonOddOrderPermutation halfDimension
            (gordonOddRowEquiv halfDimension (Sum.inl (0, index))) <
          gordonOddOrderPermutation halfDimension
            (gordonOddRowEquiv halfDimension (Sum.inl (0, column)))
        rw [gordonOddOrderPermutation_apply_pair_zero,
          gordonOddOrderPermutation_apply_pair_zero,
          gordonOddCoordinateEquiv_pair_zero,
          gordonOddCoordinateEquiv_pair_zero]
        have hpositionVal :
            (gordonOddRowEquiv halfDimension (Sum.inl (0, index))).val <
              (gordonOddRowEquiv halfDimension (Sum.inl (0, column))).val := by
          exact hposition
        rw [gordonOddRowEquiv_pair_zero_val,
          gordonOddRowEquiv_pair_zero_val] at hpositionVal
        change ¬(halfDimension - 1 - index.val) <
          (halfDimension - 1 - column.val)
        omega
      · change ¬gordonOddOrderPermutation halfDimension
            (gordonOddRowEquiv halfDimension (Sum.inl (1, index))) <
          gordonOddOrderPermutation halfDimension
            (gordonOddRowEquiv halfDimension (Sum.inl (0, column)))
        rw [gordonOddOrderPermutation_apply_pair_one,
          gordonOddOrderPermutation_apply_pair_zero,
          gordonOddCoordinateEquiv_pair_one,
          gordonOddCoordinateEquiv_pair_zero]
        change ¬(gordonOddRightIndex halfDimension index).val <
          (gordonOddLeftIndex halfDimension column).val
        simp [gordonOddRightIndex, gordonOddLeftIndex]
        omega
    · have hposition := Finset.mem_Iio.mp hrow
      rw [gordonOddRowEquiv_unit, gordonOddRowEquiv_pair_zero] at hposition
      exact absurd hposition (not_lt_of_ge (Fin.le_last _))
  rw [Finset.prod_congr rfl (fun row hrow => if_neg (hnot row hrow))]
  rw [Finset.prod_const]
  have hcard :
      (Finset.Iio
        (gordonOddRowEquiv halfDimension (Sum.inl (0, column)))).card =
        2 * column.val := by
    rw [Fin.card_Iio, gordonOddRowEquiv_pair_zero_val]
  rw [hcard, pow_mul]
  norm_num

theorem gordonOddOrderPermutation_inner_unit (halfDimension : ℕ) :
    ∏ row ∈ Finset.Iio (Fin.last (2 * halfDimension)),
      (if gordonOddOrderPermutation halfDimension row <
          gordonOddOrderPermutation halfDimension (Fin.last (2 * halfDimension))
        then (1 : ℤˣ) else -1) =
      (-1 : ℤˣ) ^ halfDimension := by
  rw [Fin.Iio_last_eq_map, Finset.prod_map]
  change (∏ row : Fin (2 * halfDimension),
      (if gordonOddOrderPermutation halfDimension row.castSucc <
          gordonOddOrderPermutation halfDimension (Fin.last (2 * halfDimension))
        then (1 : ℤˣ) else -1)) = _
  rw [← (gordonRowBlockEquiv halfDimension).prod_comp]
  rw [Fintype.prod_prod_type, Fin.prod_univ_two]
  have hzero : ∀ index : Fin halfDimension,
      gordonOddOrderPermutation halfDimension
          ((gordonInterleavedEquiv halfDimension) (index, 0)).castSucc <
        gordonOddOrderPermutation halfDimension (Fin.last (2 * halfDimension)) := by
    intro index
    have hrow :
        ((gordonInterleavedEquiv halfDimension) (index, 0)).castSucc =
          gordonOddRowEquiv halfDimension (Sum.inl (0, index)) := by
      rw [gordonOddRowEquiv_pair_zero, gordonRowBlockEquiv_zero]
    have hlast : Fin.last (2 * halfDimension) =
        gordonOddRowEquiv halfDimension (Sum.inr ()) := by
      rw [gordonOddRowEquiv_unit]
    rw [hrow, hlast,
      gordonOddOrderPermutation_apply_pair_zero,
      gordonOddOrderPermutation_apply_unit,
      gordonOddCoordinateEquiv_pair_zero,
      gordonOddCoordinateEquiv_unit]
    change (gordonOddLeftIndex halfDimension index).val <
      (gordonOddCenterIndex halfDimension).val
    simp [gordonOddLeftIndex, gordonOddCenterIndex]
    omega
  have hone : ∀ index : Fin halfDimension,
      ¬gordonOddOrderPermutation halfDimension
          ((gordonInterleavedEquiv halfDimension) (index, 1)).castSucc <
        gordonOddOrderPermutation halfDimension (Fin.last (2 * halfDimension)) := by
    intro index
    have hrow :
        ((gordonInterleavedEquiv halfDimension) (index, 1)).castSucc =
          gordonOddRowEquiv halfDimension (Sum.inl (1, index)) := by
      rw [gordonOddRowEquiv_pair_one, gordonRowBlockEquiv_one]
    have hlast : Fin.last (2 * halfDimension) =
        gordonOddRowEquiv halfDimension (Sum.inr ()) := by
      rw [gordonOddRowEquiv_unit]
    rw [hrow, hlast,
      gordonOddOrderPermutation_apply_pair_one,
      gordonOddOrderPermutation_apply_unit,
      gordonOddCoordinateEquiv_pair_one,
      gordonOddCoordinateEquiv_unit]
    change ¬(gordonOddRightIndex halfDimension index).val <
      (gordonOddCenterIndex halfDimension).val
    simp [gordonOddRightIndex, gordonOddCenterIndex]
    omega
  have hprodZero :
      (∏ index : Fin halfDimension,
        (if gordonOddOrderPermutation halfDimension
              ((gordonInterleavedEquiv halfDimension) (index, 0)).castSucc <
            gordonOddOrderPermutation halfDimension
              (Fin.last (2 * halfDimension))
          then (1 : ℤˣ) else -1)) = 1 := by
    apply Finset.prod_eq_one
    intro index hindex
    rw [if_pos (hzero index)]
  have hprodOne :
      (∏ index : Fin halfDimension,
        (if gordonOddOrderPermutation halfDimension
              ((gordonInterleavedEquiv halfDimension) (index, 1)).castSucc <
            gordonOddOrderPermutation halfDimension
              (Fin.last (2 * halfDimension))
          then (1 : ℤˣ) else -1)) =
        (-1 : ℤˣ) ^ halfDimension := by
    calc
      (∏ index : Fin halfDimension,
        (if gordonOddOrderPermutation halfDimension
              ((gordonInterleavedEquiv halfDimension) (index, 1)).castSucc <
            gordonOddOrderPermutation halfDimension
              (Fin.last (2 * halfDimension))
          then (1 : ℤˣ) else -1)) =
        ∏ _index : Fin halfDimension, (-1 : ℤˣ) := by
          apply Finset.prod_congr rfl
          intro index hindex
          rw [if_neg (hone index)]
      _ = _ := Fin.prod_const halfDimension (-1 : ℤˣ)
  have hprodZeroBlock :
      (∏ index : Fin halfDimension,
        (if gordonOddOrderPermutation halfDimension
              ((gordonRowBlockEquiv halfDimension) (0, index)).castSucc <
            gordonOddOrderPermutation halfDimension
              (Fin.last (2 * halfDimension))
          then (1 : ℤˣ) else -1)) = 1 := by
    simpa only [gordonRowBlockEquiv_zero] using hprodZero
  have hprodOneBlock :
      (∏ index : Fin halfDimension,
        (if gordonOddOrderPermutation halfDimension
              ((gordonRowBlockEquiv halfDimension) (1, index)).castSucc <
            gordonOddOrderPermutation halfDimension
              (Fin.last (2 * halfDimension))
          then (1 : ℤˣ) else -1)) =
        (-1 : ℤˣ) ^ halfDimension := by
    simpa only [gordonRowBlockEquiv_one] using hprodOne
  rw [hprodZeroBlock, hprodOneBlock, one_mul]

theorem gordonOddOrderPermutation_sign (halfDimension : ℕ) :
    (gordonOddOrderPermutation halfDimension).sign =
      (-1 : ℤˣ) ^ halfDimension := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  rw [Fin.prod_univ_castSucc]
  have hprefix :
      (∏ column : Fin (2 * halfDimension),
        ∏ row ∈ Finset.Iio column.castSucc,
          (if gordonOddOrderPermutation halfDimension row <
              gordonOddOrderPermutation halfDimension column.castSucc
            then (1 : ℤˣ) else -1)) = 1 := by
    apply Finset.prod_eq_one
    intro column hcolumn
    obtain ⟨source, hsource⟩ :=
      (gordonRowBlockEquiv halfDimension).surjective column
    rcases source with ⟨tag, index⟩
    fin_cases tag
    · rw [← hsource]
      exact gordonOddOrderPermutation_inner_pair_even halfDimension index
    · rw [← hsource]
      exact gordonOddOrderPermutation_inner_pair_odd halfDimension index
  rw [hprefix, one_mul]
  simpa [gordonOddRowEquiv_unit] using
    gordonOddOrderPermutation_inner_unit halfDimension

theorem gordonOddCoordinateRowPermutation_sign (halfDimension : ℕ) :
    (gordonOddCoordinateRowPermutation halfDimension).sign =
      (-1 : ℤˣ) ^ halfDimension := by
  have hsign := Equiv.Perm.sign_eq_sign_of_equiv
    (gordonOddCoordinateRowPermutation halfDimension)
    (gordonOddOrderPermutation halfDimension)
    (gordonOddRowEquiv halfDimension)
    (by
      intro source
      simp [gordonOddCoordinateRowPermutation, gordonOddOrderPermutation])
  rw [hsign, gordonOddOrderPermutation_sign]

noncomputable def gordonOddReflectionBlock
    (halfDimension : ℕ) (index : Fin halfDimension) :
    Matrix (Fin 2) (Fin 2) ℚ⟦X⟧ :=
  !![(X : ℚ⟦X⟧) ^ (halfDimension + 1 + index.val),
      X ^ (halfDimension - 1 - index.val);
     X ^ (halfDimension + 1 + index.val),
      -(X ^ (halfDimension - 1 - index.val))]

theorem gordonOddReflectionBlock_det
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonOddReflectionBlock halfDimension index).det =
      (-2 : ℚ⟦X⟧) *
        X ^ ((halfDimension + 1 + index.val) +
          (halfDimension - 1 - index.val)) := by
  rw [Matrix.det_fin_two]
  unfold gordonOddReflectionBlock
  simp
  rw [← pow_add]
  ring

noncomputable def gordonOddReflectionPairMatrix (halfDimension : ℕ) :
    Matrix (Fin 2 × Fin halfDimension) (Fin 2 × Fin halfDimension) ℚ⟦X⟧ :=
  Matrix.blockDiagonal (fun index : Fin halfDimension =>
    gordonOddReflectionBlock halfDimension index)

theorem gordonOddReflectionPairExponent_sum (halfDimension : ℕ) :
    (∑ index : Fin halfDimension,
      ((halfDimension + 1 + index.val) +
        (halfDimension - 1 - index.val))) =
      2 * halfDimension * halfDimension := by
  by_cases hzero : halfDimension = 0
  · subst halfDimension
    simp
  · have hterm : ∀ index : Fin halfDimension,
        (halfDimension + 1 + index.val) +
            (halfDimension - 1 - index.val) =
          2 * halfDimension := by
      intro index
      omega
    simp_rw [hterm]
    simp
    ring

theorem gordonOddReflectionPairMatrix_det (halfDimension : ℕ) :
    (gordonOddReflectionPairMatrix halfDimension).det =
      (-2 : ℚ⟦X⟧) ^ halfDimension *
        X ^ (2 * halfDimension * halfDimension) := by
  unfold gordonOddReflectionPairMatrix
  rw [Matrix.det_blockDiagonal]
  simp_rw [gordonOddReflectionBlock_det]
  rw [Finset.prod_mul_distrib]
  have hconstant :
      (∏ _index : Fin halfDimension, (-2 : ℚ⟦X⟧)) =
        (-2 : ℚ⟦X⟧) ^ halfDimension := by simp
  rw [hconstant]
  have hpowers :
      (∏ index : Fin halfDimension,
        (X : ℚ⟦X⟧) ^ ((halfDimension + 1 + index.val) +
          (halfDimension - 1 - index.val))) =
        X ^ (∑ index : Fin halfDimension,
          ((halfDimension + 1 + index.val) +
            (halfDimension - 1 - index.val))) := by
    simpa using Finset.prod_pow_eq_pow_sum
      (Finset.univ : Finset (Fin halfDimension))
      (fun index : Fin halfDimension =>
        (halfDimension + 1 + index.val) +
          (halfDimension - 1 - index.val)) (X : ℚ⟦X⟧)
  rw [hpowers, gordonOddReflectionPairExponent_sum]

noncomputable def gordonOddCenterMatrix (halfDimension : ℕ) :
    Matrix Unit Unit ℚ⟦X⟧ :=
  fun _ _ => X ^ halfDimension

noncomputable def gordonOddReflectionDiagonalMatrix (halfDimension : ℕ) :
    Matrix (GordonOddBlockIndex halfDimension)
      (GordonOddBlockIndex halfDimension) ℚ⟦X⟧ :=
  Matrix.fromBlocks (gordonOddReflectionPairMatrix halfDimension) 0 0
    (gordonOddCenterMatrix halfDimension)

theorem gordonOddCenterMatrix_det (halfDimension : ℕ) :
    (gordonOddCenterMatrix halfDimension).det = X ^ halfDimension := by
  rw [Matrix.det_unique]
  rfl

theorem gordonOddReflectionDiagonalMatrix_det (halfDimension : ℕ) :
    (gordonOddReflectionDiagonalMatrix halfDimension).det =
      (-2 : ℚ⟦X⟧) ^ halfDimension *
        X ^ staircaseWeight (2 * halfDimension) := by
  unfold gordonOddReflectionDiagonalMatrix
  rw [Matrix.det_fromBlocks_zero₂₁,
    gordonOddReflectionPairMatrix_det, gordonOddCenterMatrix_det]
  rw [show (-2 : ℚ⟦X⟧) ^ halfDimension *
          X ^ (2 * halfDimension * halfDimension) * X ^ halfDimension =
        (-2 : ℚ⟦X⟧) ^ halfDimension *
          (X ^ (2 * halfDimension * halfDimension) * X ^ halfDimension) by ring,
    ← pow_add]
  rw [staircaseWeight_formula]
  rw [show (2 * halfDimension + 1) * (2 * halfDimension) =
      (2 * halfDimension * halfDimension + halfDimension) * 2 by ring]
  rw [Nat.mul_div_left _ (by decide : 0 < 2)]

noncomputable def gordonOddUnitAdditionRow
    (halfDimension : ℕ) : Matrix Unit (Fin 2 × Fin halfDimension) ℚ⟦X⟧ :=
  fun _ column => if column.1 = 0 then 1 else 0

noncomputable def gordonOddUnitAdditionMatrix (halfDimension : ℕ) :
    Matrix (GordonOddBlockIndex halfDimension)
      (GordonOddBlockIndex halfDimension) ℚ⟦X⟧ :=
  Matrix.fromBlocks 1 0 (gordonOddUnitAdditionRow halfDimension) 1

theorem gordonOddUnitAdditionMatrix_det (halfDimension : ℕ) :
    (gordonOddUnitAdditionMatrix halfDimension).det = 1 := by
  unfold gordonOddUnitAdditionMatrix
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, mul_one]

noncomputable def gordonOddReflectionSourceMatrix (halfDimension : ℕ) :
    Matrix (GordonOddBlockIndex halfDimension)
      (GordonOddBlockIndex halfDimension) ℚ⟦X⟧ :=
  gordonOddUnitAdditionMatrix halfDimension *
    gordonOddReflectionDiagonalMatrix halfDimension

theorem gordonOddReflectionSourceMatrix_det (halfDimension : ℕ) :
    (gordonOddReflectionSourceMatrix halfDimension).det =
      (-2 : ℚ⟦X⟧) ^ halfDimension *
        X ^ staircaseWeight (2 * halfDimension) := by
  unfold gordonOddReflectionSourceMatrix
  rw [Matrix.det_mul, gordonOddUnitAdditionMatrix_det,
    gordonOddReflectionDiagonalMatrix_det, one_mul]

theorem gordonOddReflectionSourceMatrix_eq_blocks (halfDimension : ℕ) :
    gordonOddReflectionSourceMatrix halfDimension =
      Matrix.fromBlocks (gordonOddReflectionPairMatrix halfDimension) 0
        (gordonOddUnitAdditionRow halfDimension *
          gordonOddReflectionPairMatrix halfDimension)
        (gordonOddCenterMatrix halfDimension) := by
  unfold gordonOddReflectionSourceMatrix gordonOddUnitAdditionMatrix
    gordonOddReflectionDiagonalMatrix
  rw [Matrix.fromBlocks_multiply]
  simp

@[simp] theorem gordonOddUnitPairRow_apply_zero
    (halfDimension : ℕ) (column : Fin halfDimension) :
    (gordonOddUnitAdditionRow halfDimension *
        gordonOddReflectionPairMatrix halfDimension) () (0, column) =
      X ^ (halfDimension + 1 + column.val) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [gordonOddUnitAdditionRow, gordonOddReflectionPairMatrix,
    Matrix.blockDiagonal_apply, gordonOddReflectionBlock]

@[simp] theorem gordonOddUnitPairRow_apply_one
    (halfDimension : ℕ) (column : Fin halfDimension) :
    (gordonOddUnitAdditionRow halfDimension *
        gordonOddReflectionPairMatrix halfDimension) () (1, column) =
      X ^ (halfDimension - 1 - column.val) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [gordonOddUnitAdditionRow, gordonOddReflectionPairMatrix,
    Matrix.blockDiagonal_apply, gordonOddReflectionBlock]

noncomputable def gordonOddReflectionActualMatrix (halfDimension : ℕ) :
    Matrix (Fin (2 * halfDimension + 1))
      (Fin (2 * halfDimension + 1)) ℚ⟦X⟧ :=
  (gordonOddReflectionSourceMatrix halfDimension).reindex
    (gordonOddRowEquiv halfDimension)
    (gordonOddCoordinateEquiv halfDimension)

theorem gordonOddReflectionActualMatrix_pair_zero_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddReflectionActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (0, row))) =
      gordonOddPlusRow halfDimension row := by
  funext column
  obtain ⟨source, rfl⟩ :=
    (gordonOddCoordinateEquiv halfDimension).surjective column
  rcases source with ⟨⟨tag, index⟩⟩ | _unit
  · fin_cases tag <;>
      unfold gordonOddReflectionActualMatrix <;>
      rw [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        gordonOddReflectionSourceMatrix_eq_blocks] <;>
      simp [gordonOddReflectionPairMatrix, Matrix.blockDiagonal_apply,
        gordonOddReflectionBlock]
  · cases _unit
    unfold gordonOddReflectionActualMatrix
    rw [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      gordonOddReflectionSourceMatrix_eq_blocks]
    simp

theorem gordonOddReflectionActualMatrix_pair_one_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddReflectionActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (1, row))) =
      gordonOddMinusRow halfDimension row := by
  funext column
  obtain ⟨source, rfl⟩ :=
    (gordonOddCoordinateEquiv halfDimension).surjective column
  rcases source with ⟨⟨tag, index⟩⟩ | _unit
  · fin_cases tag <;>
      unfold gordonOddReflectionActualMatrix <;>
      rw [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        gordonOddReflectionSourceMatrix_eq_blocks] <;>
      simp [gordonOddReflectionPairMatrix, Matrix.blockDiagonal_apply,
        gordonOddReflectionBlock]
  · cases _unit
    unfold gordonOddReflectionActualMatrix
    rw [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      gordonOddReflectionSourceMatrix_eq_blocks]
    simp

theorem gordonOddReflectionActualMatrix_unit_row
    (halfDimension : ℕ) :
    gordonOddReflectionActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inr ())) =
      gordonOddUnitRow halfDimension := by
  funext column
  obtain ⟨source, rfl⟩ :=
    (gordonOddCoordinateEquiv halfDimension).surjective column
  rcases source with ⟨⟨tag, index⟩⟩ | _unit
  · fin_cases tag <;>
      unfold gordonOddReflectionActualMatrix <;>
      rw [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        gordonOddReflectionSourceMatrix_eq_blocks] <;>
      simp
  · cases _unit
    unfold gordonOddReflectionActualMatrix
    rw [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      gordonOddReflectionSourceMatrix_eq_blocks]
    simp [gordonOddCenterMatrix, gordonOddUnitRow]
    congr 1
    simp [gordonOddCenterIndex]
    omega

@[simp] theorem gordonOddReflectionActualMatrix_interleaved_zero_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddReflectionActualMatrix halfDimension
        ((gordonInterleavedEquiv halfDimension) (row, 0)).castSucc =
      gordonOddPlusRow halfDimension row := by
  simpa only [gordonOddRowEquiv_pair_zero, gordonRowBlockEquiv_zero] using
    gordonOddReflectionActualMatrix_pair_zero_row halfDimension row

@[simp] theorem gordonOddReflectionActualMatrix_interleaved_one_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddReflectionActualMatrix halfDimension
        ((gordonInterleavedEquiv halfDimension) (row, 1)).castSucc =
      gordonOddMinusRow halfDimension row := by
  simpa only [gordonOddRowEquiv_pair_one, gordonRowBlockEquiv_one] using
    gordonOddReflectionActualMatrix_pair_one_row halfDimension row

@[simp] theorem gordonOddReflectionActualMatrix_last_row
    (halfDimension : ℕ) :
    gordonOddReflectionActualMatrix halfDimension (Fin.last (2 * halfDimension)) =
      gordonOddUnitRow halfDimension := by
  simpa only [gordonOddRowEquiv_unit] using
    gordonOddReflectionActualMatrix_unit_row halfDimension

noncomputable def gordonOddMixingSumMatrix (halfDimension : ℕ) :
    Matrix (Fin halfDimension ⊕ Fin halfDimension)
      (Fin halfDimension ⊕ Fin halfDimension) ℚ⟦X⟧ :=
  Matrix.fromBlocks 1 0 0
    (gordonHalfScalar • gordonOddCumulativeMatrix halfDimension)

theorem gordonOddMixingSumMatrix_det (halfDimension : ℕ) :
    (gordonOddMixingSumMatrix halfDimension).det =
      gordonHalfScalar ^ halfDimension *
        (oddFormalGesselMatrixQ halfDimension).det := by
  unfold gordonOddMixingSumMatrix
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
    Matrix.det_smul]
  rw [gordonOddCumulativeMatrix_det_eq_formalGessel]
  simp only [Fintype.card_fin]

noncomputable def gordonOddMixingPairMatrix (halfDimension : ℕ) :
    Matrix (Fin 2 × Fin halfDimension) (Fin 2 × Fin halfDimension) ℚ⟦X⟧ :=
  (gordonOddMixingSumMatrix halfDimension).reindex
    (gordonSumBlockEquiv halfDimension) (gordonSumBlockEquiv halfDimension)

theorem gordonOddMixingPairMatrix_det (halfDimension : ℕ) :
    (gordonOddMixingPairMatrix halfDimension).det =
      gordonHalfScalar ^ halfDimension *
        (oddFormalGesselMatrixQ halfDimension).det := by
  unfold gordonOddMixingPairMatrix
  rw [Matrix.det_reindex_self, gordonOddMixingSumMatrix_det]

@[simp] theorem gordonOddMixingPairMatrix_zero_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingPairMatrix halfDimension (0, row) (0, column) =
      if row = column then 1 else 0 := by
  simp [gordonOddMixingPairMatrix, gordonOddMixingSumMatrix,
    gordonSumBlockEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.one_apply]

@[simp] theorem gordonOddMixingPairMatrix_zero_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingPairMatrix halfDimension (0, row) (1, column) = 0 := by
  simp [gordonOddMixingPairMatrix, gordonOddMixingSumMatrix,
    gordonSumBlockEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

@[simp] theorem gordonOddMixingPairMatrix_one_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingPairMatrix halfDimension (1, row) (0, column) = 0 := by
  simp [gordonOddMixingPairMatrix, gordonOddMixingSumMatrix,
    gordonSumBlockEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

@[simp] theorem gordonOddMixingPairMatrix_one_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingPairMatrix halfDimension (1, row) (1, column) =
      gordonHalfScalar * gordonOddCumulativeEntry row.val column.val := by
  simp [gordonOddMixingPairMatrix, gordonOddMixingSumMatrix,
    gordonSumBlockEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    gordonOddCumulativeMatrix]

noncomputable def gordonOddMixingSourceMatrix (halfDimension : ℕ) :
    Matrix (GordonOddBlockIndex halfDimension)
      (GordonOddBlockIndex halfDimension) ℚ⟦X⟧ :=
  Matrix.fromBlocks (gordonOddMixingPairMatrix halfDimension) 0 0 1

theorem gordonOddMixingSourceMatrix_det (halfDimension : ℕ) :
    (gordonOddMixingSourceMatrix halfDimension).det =
      gordonHalfScalar ^ halfDimension *
        (oddFormalGesselMatrixQ halfDimension).det := by
  unfold gordonOddMixingSourceMatrix
  rw [Matrix.det_fromBlocks_zero₂₁, gordonOddMixingPairMatrix_det,
    Matrix.det_one, mul_one]

noncomputable def gordonOddMixingActualMatrix (halfDimension : ℕ) :
    Matrix (Fin (2 * halfDimension + 1))
      (Fin (2 * halfDimension + 1)) ℚ⟦X⟧ :=
  (gordonOddMixingSourceMatrix halfDimension).reindex
    (gordonOddRowEquiv halfDimension) (gordonOddRowEquiv halfDimension)

@[simp] theorem gordonOddMixingActual_pair_zero_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (0, row)))
        (gordonOddRowEquiv halfDimension (Sum.inl (0, column))) =
      if row = column then 1 else 0 := by
  unfold gordonOddMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact gordonOddMixingPairMatrix_zero_zero halfDimension row column

@[simp] theorem gordonOddMixingActual_pair_zero_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (0, row)))
        (gordonOddRowEquiv halfDimension (Sum.inl (1, column))) = 0 := by
  unfold gordonOddMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact gordonOddMixingPairMatrix_zero_one halfDimension row column

@[simp] theorem gordonOddMixingActual_pair_one_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (1, row)))
        (gordonOddRowEquiv halfDimension (Sum.inl (0, column))) = 0 := by
  unfold gordonOddMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact gordonOddMixingPairMatrix_one_zero halfDimension row column

@[simp] theorem gordonOddMixingActual_pair_one_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (1, row)))
        (gordonOddRowEquiv halfDimension (Sum.inl (1, column))) =
      gordonHalfScalar * gordonOddCumulativeEntry row.val column.val := by
  unfold gordonOddMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact gordonOddMixingPairMatrix_one_one halfDimension row column

@[simp] theorem gordonOddMixingActual_pair_unit
    (halfDimension : ℕ) (tag : Fin 2) (row : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (tag, row)))
        (gordonOddRowEquiv halfDimension (Sum.inr ())) = 0 := by
  unfold gordonOddMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

@[simp] theorem gordonOddMixingActual_unit_pair
    (halfDimension : ℕ) (tag : Fin 2) (column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inr ()))
        (gordonOddRowEquiv halfDimension (Sum.inl (tag, column))) = 0 := by
  unfold gordonOddMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

@[simp] theorem gordonOddMixingActual_unit_unit (halfDimension : ℕ) :
    gordonOddMixingActualMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inr ()))
        (gordonOddRowEquiv halfDimension (Sum.inr ())) = 1 := by
  unfold gordonOddMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  unfold gordonOddMixingSourceMatrix
  simp

@[simp] theorem gordonOddMixingActual_interleaved_zero_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        ((gordonInterleavedEquiv halfDimension) (row, 0)).castSucc
        ((gordonInterleavedEquiv halfDimension) (column, 0)).castSucc =
      if row = column then 1 else 0 := by
  simpa only [gordonOddRowEquiv_pair_zero, gordonRowBlockEquiv_zero] using
    gordonOddMixingActual_pair_zero_zero halfDimension row column

@[simp] theorem gordonOddMixingActual_interleaved_zero_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        ((gordonInterleavedEquiv halfDimension) (row, 0)).castSucc
        ((gordonInterleavedEquiv halfDimension) (column, 1)).castSucc = 0 := by
  simpa only [gordonOddRowEquiv_pair_zero, gordonRowBlockEquiv_zero,
    gordonOddRowEquiv_pair_one, gordonRowBlockEquiv_one] using
    gordonOddMixingActual_pair_zero_one halfDimension row column

@[simp] theorem gordonOddMixingActual_interleaved_one_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        ((gordonInterleavedEquiv halfDimension) (row, 1)).castSucc
        ((gordonInterleavedEquiv halfDimension) (column, 0)).castSucc = 0 := by
  simpa only [gordonOddRowEquiv_pair_zero, gordonRowBlockEquiv_zero,
    gordonOddRowEquiv_pair_one, gordonRowBlockEquiv_one] using
    gordonOddMixingActual_pair_one_zero halfDimension row column

@[simp] theorem gordonOddMixingActual_interleaved_one_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        ((gordonInterleavedEquiv halfDimension) (row, 1)).castSucc
        ((gordonInterleavedEquiv halfDimension) (column, 1)).castSucc =
      gordonHalfScalar * gordonOddCumulativeEntry row.val column.val := by
  simpa only [gordonOddRowEquiv_pair_one, gordonRowBlockEquiv_one] using
    gordonOddMixingActual_pair_one_one halfDimension row column

@[simp] theorem gordonOddMixingActual_interleaved_zero_last
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        ((gordonInterleavedEquiv halfDimension) (row, 0)).castSucc
        (Fin.last (2 * halfDimension)) = 0 := by
  simpa only [gordonOddRowEquiv_pair_zero, gordonRowBlockEquiv_zero,
    gordonOddRowEquiv_unit] using
    gordonOddMixingActual_pair_unit halfDimension 0 row

@[simp] theorem gordonOddMixingActual_interleaved_one_last
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        ((gordonInterleavedEquiv halfDimension) (row, 1)).castSucc
        (Fin.last (2 * halfDimension)) = 0 := by
  simpa only [gordonOddRowEquiv_pair_one, gordonRowBlockEquiv_one,
    gordonOddRowEquiv_unit] using
    gordonOddMixingActual_pair_unit halfDimension 1 row

@[simp] theorem gordonOddMixingActual_last_interleaved_zero
    (halfDimension : ℕ) (column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        (Fin.last (2 * halfDimension))
        ((gordonInterleavedEquiv halfDimension) (column, 0)).castSucc = 0 := by
  simpa only [gordonOddRowEquiv_pair_zero, gordonRowBlockEquiv_zero,
    gordonOddRowEquiv_unit] using
    gordonOddMixingActual_unit_pair halfDimension 0 column

@[simp] theorem gordonOddMixingActual_last_interleaved_one
    (halfDimension : ℕ) (column : Fin halfDimension) :
    gordonOddMixingActualMatrix halfDimension
        (Fin.last (2 * halfDimension))
        ((gordonInterleavedEquiv halfDimension) (column, 1)).castSucc = 0 := by
  simpa only [gordonOddRowEquiv_pair_one, gordonRowBlockEquiv_one,
    gordonOddRowEquiv_unit] using
    gordonOddMixingActual_unit_pair halfDimension 1 column

@[simp] theorem gordonOddMixingActual_last_last (halfDimension : ℕ) :
    gordonOddMixingActualMatrix halfDimension
        (Fin.last (2 * halfDimension)) (Fin.last (2 * halfDimension)) = 1 := by
  simpa only [gordonOddRowEquiv_unit] using
    gordonOddMixingActual_unit_unit halfDimension

noncomputable def gordonOddFactorizedMatrix (halfDimension : ℕ) :
    Matrix (Fin (2 * halfDimension + 1))
      (Fin (2 * halfDimension + 1)) ℚ⟦X⟧ :=
  (gordonOddMixingSourceMatrix halfDimension *
      gordonOddReflectionSourceMatrix halfDimension).reindex
    (gordonOddRowEquiv halfDimension)
    (gordonOddCoordinateEquiv halfDimension)

theorem gordonOddCoordinateSignSeries (halfDimension : ℕ) :
    ((((gordonOddCoordinateRowPermutation halfDimension).sign : ℤ) :
        ℚ⟦X⟧)) = (-1 : ℚ⟦X⟧) ^ halfDimension := by
  rw [gordonOddCoordinateRowPermutation_sign]
  induction halfDimension with
  | zero => norm_num
  | succ dimension ih =>
      rw [show (-1 : ℤˣ) ^ (dimension + 1) =
          (-1 : ℤˣ) ^ dimension * (-1) by
            exact pow_succ (-1 : ℤˣ) dimension]
      rw [show (-1 : ℚ⟦X⟧) ^ (dimension + 1) =
          (-1 : ℚ⟦X⟧) ^ dimension * (-1) by
            exact pow_succ (-1 : ℚ⟦X⟧) dimension]
      rw [Units.val_mul]
      push_cast
      rw [ih]

theorem gordonOddFactorizedMatrix_det (halfDimension : ℕ) :
    (gordonOddFactorizedMatrix halfDimension).det =
      X ^ staircaseWeight (2 * halfDimension) *
        (oddFormalGesselMatrixQ halfDimension).det := by
  unfold gordonOddFactorizedMatrix
  rw [Matrix.det_reindex, Matrix.det_mul,
    gordonOddMixingSourceMatrix_det,
    gordonOddReflectionSourceMatrix_det]
  change ((((gordonOddCoordinateRowPermutation halfDimension).sign : ℤ) :
      ℚ⟦X⟧)) *
        ((gordonHalfScalar ^ halfDimension *
            (oddFormalGesselMatrixQ halfDimension).det) *
          ((-2 : ℚ⟦X⟧) ^ halfDimension *
            X ^ staircaseWeight (2 * halfDimension))) = _
  rw [gordonOddCoordinateSignSeries]
  have hcancel :
      (-1 : ℚ⟦X⟧) ^ halfDimension *
          (gordonHalfScalar ^ halfDimension *
            (-2 : ℚ⟦X⟧) ^ halfDimension) = 1 := by
    rw [← mul_pow gordonHalfScalar (-2 : ℚ⟦X⟧)]
    rw [show gordonHalfScalar * (-2 : ℚ⟦X⟧) = -1 by
      rw [mul_neg, gordonHalfScalar_mul_two]]
    rw [← mul_pow]
    norm_num
  rw [show
      (-1 : ℚ⟦X⟧) ^ halfDimension *
          ((gordonHalfScalar ^ halfDimension *
              (oddFormalGesselMatrixQ halfDimension).det) *
            ((-2 : ℚ⟦X⟧) ^ halfDimension *
              X ^ staircaseWeight (2 * halfDimension))) =
        ((-1 : ℚ⟦X⟧) ^ halfDimension *
          (gordonHalfScalar ^ halfDimension *
            (-2 : ℚ⟦X⟧) ^ halfDimension)) *
          (X ^ staircaseWeight (2 * halfDimension) *
            (oddFormalGesselMatrixQ halfDimension).det) by ring,
    hcancel, one_mul]

theorem gordonOddFactorizedMatrix_eq_actual_mul (halfDimension : ℕ) :
    gordonOddFactorizedMatrix halfDimension =
      gordonOddMixingActualMatrix halfDimension *
        gordonOddReflectionActualMatrix halfDimension := by
  unfold gordonOddFactorizedMatrix gordonOddMixingActualMatrix
    gordonOddReflectionActualMatrix
  symm
  simpa only [Matrix.coe_reindexLinearEquiv] using
    Matrix.reindexLinearEquiv_mul (R := ℚ⟦X⟧) (A := ℚ⟦X⟧)
      (gordonOddRowEquiv halfDimension)
      (gordonOddRowEquiv halfDimension)
      (gordonOddCoordinateEquiv halfDimension)
      (gordonOddMixingSourceMatrix halfDimension)
      (gordonOddReflectionSourceMatrix halfDimension)

theorem gordonOddFactorizedMatrix_pair_zero_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddFactorizedMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (0, row))) =
      gordonOddPlusRow halfDimension row := by
  rw [gordonOddFactorizedMatrix_eq_actual_mul]
  funext column
  rw [Matrix.mul_apply]
  rw [← (gordonOddRowEquiv halfDimension).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

theorem gordonOddFactorizedMatrix_pair_one_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonOddFactorizedMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inl (1, row))) =
      gordonOddMixedRow halfDimension row := by
  rw [gordonOddFactorizedMatrix_eq_actual_mul]
  funext column
  rw [Matrix.mul_apply]
  rw [← (gordonOddRowEquiv halfDimension).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [gordonOddMixedRow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro summand hsummand
  ring

theorem gordonOddFactorizedMatrix_unit_row (halfDimension : ℕ) :
    gordonOddFactorizedMatrix halfDimension
        (gordonOddRowEquiv halfDimension (Sum.inr ())) =
      gordonOddUnitRow halfDimension := by
  rw [gordonOddFactorizedMatrix_eq_actual_mul]
  funext column
  rw [Matrix.mul_apply]
  rw [← (gordonOddRowEquiv halfDimension).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

theorem gordonOddInterleavedRows_eq_ofFn_factorized (halfDimension : ℕ) :
    gordonOddInterleavedRows halfDimension =
      List.ofFn (fun row : Fin (2 * halfDimension + 1) =>
        gordonOddFactorizedMatrix halfDimension row) := by
  unfold gordonOddInterleavedRows
  symm
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · rw [List.ofFn_congr (Nat.mul_comm 2 halfDimension)]
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    rw [List.ofFn_inj]
    funext index
    rw [List.ofFn_succ]
    congr 1
    · convert gordonOddFactorizedMatrix_pair_zero_row
        halfDimension index using 1
      apply congrArg (gordonOddFactorizedMatrix halfDimension)
      apply Fin.ext
      simp [gordonOddRowEquiv, gordonRowBlockEquiv,
        gordonInterleavedEquiv, finProdFinEquiv]
      omega
    · rw [List.ofFn_succ]
      congr 1
      · convert gordonOddFactorizedMatrix_pair_one_row
          halfDimension index using 1
        apply congrArg (gordonOddFactorizedMatrix halfDimension)
        apply Fin.ext
        simp [gordonOddRowEquiv, gordonRowBlockEquiv,
          gordonInterleavedEquiv, finProdFinEquiv]
        omega
  · apply congrArg List.singleton
    simpa only [gordonOddRowEquiv_unit] using
      gordonOddFactorizedMatrix_unit_row halfDimension

theorem listRowsOfLength_congr
    {R : Type*} [CommRing R] {dimension : ℕ}
    {leftRows rightRows : List (GeneralRow dimension R)}
    (hrows : leftRows = rightRows)
    (hleft : leftRows.length = dimension)
    (hright : rightRows.length = dimension) :
    listRowsOfLength leftRows hleft =
      listRowsOfLength rightRows hright := by
  subst rightRows
  rfl

theorem listRowsOfLength_ofFn
    {R : Type*} [CommRing R] {dimension : ℕ}
    (rows : Fin dimension → GeneralRow dimension R)
    (hlength : (List.ofFn rows).length = dimension) :
    listRowsOfLength (List.ofFn rows) hlength = rows := by
  funext row
  unfold listRowsOfLength
  simp

theorem listRowsOfLength_gordonOddInterleavedRows
    (halfDimension : ℕ) :
    listRowsOfLength (gordonOddInterleavedRows halfDimension)
        (gordonOddInterleavedRows_length halfDimension) =
      gordonOddFactorizedMatrix halfDimension := by
  let targetRows := List.ofFn (fun row : Fin (2 * halfDimension + 1) =>
    gordonOddFactorizedMatrix halfDimension row)
  have htargetLength : targetRows.length = 2 * halfDimension + 1 := by
    simp [targetRows]
  have hrows : gordonOddInterleavedRows halfDimension = targetRows := by
    exact gordonOddInterleavedRows_eq_ofFn_factorized halfDimension
  have hcongr :
      listRowsOfLength (gordonOddInterleavedRows halfDimension)
          (gordonOddInterleavedRows_length halfDimension) =
        listRowsOfLength targetRows htargetLength := by
    exact listRowsOfLength_congr hrows
      (gordonOddInterleavedRows_length halfDimension) htargetLength
  calc
    listRowsOfLength (gordonOddInterleavedRows halfDimension)
        (gordonOddInterleavedRows_length halfDimension) =
      listRowsOfLength targetRows htargetLength := hcongr
    _ = _ := by
      exact listRowsOfLength_ofFn
        (fun row : Fin (2 * halfDimension + 1) =>
          gordonOddFactorizedMatrix halfDimension row) htargetLength

theorem generalOddGesselAssemblyIdentity_all (halfDimension : ℕ) :
    GeneralOddGesselAssemblyIdentity halfDimension := by
  unfold GeneralOddGesselAssemblyIdentity oddFormalGesselSeriesQ
  rw [generalClosedOddAssembly_eq_interleaved_det,
    listRowsOfLength_gordonOddInterleavedRows,
    gordonOddFactorizedMatrix_det]
  ring

theorem generalOddGesselActualBridge_all (halfDimension : ℕ) :
    GeneralOddGesselActualBridge halfDimension :=
  (generalOddGesselActualBridge_iff_assembly halfDimension).2
    (generalOddGesselAssemblyIdentity_all halfDimension)

end FibonacciRibbonKernel
