import FibonacciRibbonKernel.GordonEvenExteriorDecomposition
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.GroupTheory.Perm.Fin

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical Matrix

noncomputable def gordonReflectionBlock
    (halfDimension : ℕ) (index : Fin halfDimension) :
    Matrix (Fin 2) (Fin 2) ℚ⟦X⟧ :=
  !![(X : ℚ⟦X⟧) ^ (halfDimension + index.val),
      X ^ (halfDimension - 1 - index.val);
     X ^ (halfDimension + index.val),
      -(X ^ (halfDimension - 1 - index.val))]

theorem gordonReflectionBlock_det
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonReflectionBlock halfDimension index).det =
      (-2 : ℚ⟦X⟧) *
        X ^ ((halfDimension + index.val) +
          (halfDimension - 1 - index.val)) := by
  rw [Matrix.det_fin_two]
  unfold gordonReflectionBlock
  simp
  rw [← pow_add]
  ring

noncomputable def gordonReflectionProductMatrix
    (halfDimension : ℕ) :
    Matrix (Fin 2 × Fin halfDimension) (Fin 2 × Fin halfDimension) ℚ⟦X⟧ :=
  Matrix.blockDiagonal (fun index : Fin halfDimension =>
    gordonReflectionBlock halfDimension index)

theorem gordonReflectionExponent_sum (halfDimension : ℕ) :
    (∑ index : Fin halfDimension,
        ((halfDimension + index.val) +
          (halfDimension - 1 - index.val))) =
      staircaseWeight (2 * halfDimension - 1) := by
  by_cases hzero : halfDimension = 0
  · subst halfDimension
    simp [staircaseWeight]
  · have hpositive : 1 ≤ halfDimension := Nat.one_le_iff_ne_zero.mpr hzero
    have hterm : ∀ index : Fin halfDimension,
        (halfDimension + index.val) +
            (halfDimension - 1 - index.val) =
          2 * halfDimension - 1 := by
      intro index
      omega
    simp_rw [hterm]
    rw [staircaseWeight_formula]
    rw [show 2 * halfDimension - 1 + 1 = 2 * halfDimension by omega]
    rw [show (2 * halfDimension) * (2 * halfDimension - 1) =
        (halfDimension * (2 * halfDimension - 1)) * 2 by ring]
    rw [Nat.mul_div_left _ (by decide : 0 < 2)]
    simp

theorem gordonReflectionProductMatrix_det (halfDimension : ℕ) :
    (gordonReflectionProductMatrix halfDimension).det =
      (-2 : ℚ⟦X⟧) ^ halfDimension *
        X ^ staircaseWeight (2 * halfDimension - 1) := by
  unfold gordonReflectionProductMatrix
  rw [Matrix.det_blockDiagonal]
  simp_rw [gordonReflectionBlock_det]
  rw [Finset.prod_mul_distrib]
  have hconstant :
      (∏ _index : Fin halfDimension, (-2 : ℚ⟦X⟧)) =
        (-2 : ℚ⟦X⟧) ^ halfDimension := by simp
  rw [hconstant]
  have hpowers :
      (∏ index : Fin halfDimension,
        (X : ℚ⟦X⟧) ^ ((halfDimension + index.val) +
          (halfDimension - 1 - index.val))) =
        (X : ℚ⟦X⟧) ^ (∑ index : Fin halfDimension,
          ((halfDimension + index.val) +
            (halfDimension - 1 - index.val))) := by
    simpa using Finset.prod_pow_eq_pow_sum
      (Finset.univ : Finset (Fin halfDimension))
      (fun index : Fin halfDimension =>
        (halfDimension + index.val) +
          (halfDimension - 1 - index.val)) (X : ℚ⟦X⟧)
  rw [hpowers, gordonReflectionExponent_sum]

noncomputable def gordonMixingSumMatrix (halfDimension : ℕ) :
    Matrix (Fin halfDimension ⊕ Fin halfDimension)
      (Fin halfDimension ⊕ Fin halfDimension) ℚ⟦X⟧ :=
  Matrix.fromBlocks 1 0 0
    ((-gordonHalfScalar) • gordonCumulativeMatrix halfDimension)

theorem gordonMixingSumMatrix_det (halfDimension : ℕ) :
    (gordonMixingSumMatrix halfDimension).det =
      (-gordonHalfScalar) ^ halfDimension *
        (gordonCumulativeMatrix halfDimension).det := by
  unfold gordonMixingSumMatrix
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
    Matrix.det_smul]
  simp

def gordonSumBlockEquiv (halfDimension : ℕ) :
    Fin halfDimension ⊕ Fin halfDimension ≃ Fin 2 × Fin halfDimension where
  toFun value := value.elim (fun index => (0, index))
    (fun index => (1, index))
  invFun value := if value.1 = 0 then Sum.inl value.2 else Sum.inr value.2
  left_inv := by
    intro value
    rcases value with left | right <;> simp
  right_inv := by
    intro value
    rcases value with ⟨tag, index⟩
    fin_cases tag <;> simp

noncomputable def gordonMixingProductMatrix (halfDimension : ℕ) :
    Matrix (Fin 2 × Fin halfDimension) (Fin 2 × Fin halfDimension) ℚ⟦X⟧ :=
  (gordonMixingSumMatrix halfDimension).reindex
    (gordonSumBlockEquiv halfDimension) (gordonSumBlockEquiv halfDimension)

theorem gordonMixingProductMatrix_det (halfDimension : ℕ) :
    (gordonMixingProductMatrix halfDimension).det =
      (-gordonHalfScalar) ^ halfDimension *
        (gordonCumulativeMatrix halfDimension).det := by
  unfold gordonMixingProductMatrix
  rw [Matrix.det_reindex_self, gordonMixingSumMatrix_det]

@[simp] theorem gordonMixingProductMatrix_zero_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingProductMatrix halfDimension (0, row) (0, column) =
      if row = column then 1 else 0 := by
  simp [gordonMixingProductMatrix, gordonMixingSumMatrix,
    gordonSumBlockEquiv, Matrix.reindex_apply, Matrix.one_apply]

@[simp] theorem gordonMixingProductMatrix_zero_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingProductMatrix halfDimension (0, row) (1, column) = 0 := by
  simp [gordonMixingProductMatrix, gordonMixingSumMatrix,
    gordonSumBlockEquiv, Matrix.reindex_apply]

@[simp] theorem gordonMixingProductMatrix_one_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingProductMatrix halfDimension (1, row) (0, column) = 0 := by
  simp [gordonMixingProductMatrix, gordonMixingSumMatrix,
    gordonSumBlockEquiv, Matrix.reindex_apply]

@[simp] theorem gordonMixingProductMatrix_one_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingProductMatrix halfDimension (1, row) (1, column) =
      -gordonHalfScalar * gordonCumulativeEntry row.val column.val := by
  simp [gordonMixingProductMatrix, gordonMixingSumMatrix,
    gordonSumBlockEquiv, Matrix.reindex_apply, gordonCumulativeMatrix]

noncomputable def gordonRowBlockEquiv (halfDimension : ℕ) :
    Fin 2 × Fin halfDimension ≃ Fin (2 * halfDimension) :=
  (Equiv.prodComm (Fin 2) (Fin halfDimension)).trans
    (gordonInterleavedEquiv halfDimension)

noncomputable def gordonCoordinateBlockEquiv (halfDimension : ℕ) :
    Fin 2 × Fin halfDimension ≃ Fin (2 * halfDimension) :=
  (gordonSumBlockEquiv halfDimension).symm |>.trans
    ((Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin halfDimension))).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

@[simp] theorem gordonRowBlockEquiv_zero
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonRowBlockEquiv halfDimension (0, index) =
      gordonInterleavedEquiv halfDimension (index, 0) := by
  rfl

@[simp] theorem gordonRowBlockEquiv_one
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonRowBlockEquiv halfDimension (1, index) =
      gordonInterleavedEquiv halfDimension (index, 1) := by
  rfl

@[simp] theorem gordonCoordinateBlockEquiv_zero
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonCoordinateBlockEquiv halfDimension (0, index) =
      gordonLeftIndex halfDimension index := by
  apply Fin.ext
  simp [gordonCoordinateBlockEquiv, gordonSumBlockEquiv,
    gordonLeftIndex, Fin.revPerm]
  omega

@[simp] theorem gordonCoordinateBlockEquiv_one
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonCoordinateBlockEquiv halfDimension (1, index) =
      gordonRightIndex halfDimension index := by
  apply Fin.ext
  simp [gordonCoordinateBlockEquiv, gordonSumBlockEquiv,
    gordonRightIndex]
  omega

noncomputable def gordonReflectionActualMatrix (halfDimension : ℕ) :
    Matrix (Fin (2 * halfDimension)) (Fin (2 * halfDimension)) ℚ⟦X⟧ :=
  (gordonReflectionProductMatrix halfDimension).reindex
    (gordonRowBlockEquiv halfDimension)
    (gordonCoordinateBlockEquiv halfDimension)

@[simp] theorem gordonReflectionActualMatrix_zero_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (0, row))
        (gordonCoordinateBlockEquiv halfDimension (0, column)) =
      if row = column then X ^ (halfDimension + row.val) else 0 := by
  unfold gordonReflectionActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp [gordonReflectionProductMatrix, gordonReflectionBlock,
    Matrix.blockDiagonal_apply]

@[simp] theorem gordonReflectionActualMatrix_zero_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (0, row))
        (gordonCoordinateBlockEquiv halfDimension (1, column)) =
      if row = column then X ^ (halfDimension - 1 - row.val) else 0 := by
  unfold gordonReflectionActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp [gordonReflectionProductMatrix, gordonReflectionBlock,
    Matrix.blockDiagonal_apply]

@[simp] theorem gordonReflectionActualMatrix_one_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (1, row))
        (gordonCoordinateBlockEquiv halfDimension (0, column)) =
      if row = column then X ^ (halfDimension + row.val) else 0 := by
  unfold gordonReflectionActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp [gordonReflectionProductMatrix, gordonReflectionBlock,
    Matrix.blockDiagonal_apply]

@[simp] theorem gordonReflectionActualMatrix_one_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (1, row))
        (gordonCoordinateBlockEquiv halfDimension (1, column)) =
      if row = column then -(X ^ (halfDimension - 1 - row.val)) else 0 := by
  unfold gordonReflectionActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  simp [gordonReflectionProductMatrix, gordonReflectionBlock,
    Matrix.blockDiagonal_apply]

theorem gordonReflectionActualMatrix_zero_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (0, row)) =
      gordonPlusRow halfDimension row := by
  funext column
  obtain ⟨source, rfl⟩ :=
    (gordonCoordinateBlockEquiv halfDimension).surjective column
  rcases source with ⟨tag, index⟩
  fin_cases tag
  · change gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (0, row))
        (gordonCoordinateBlockEquiv halfDimension (0, index)) =
      gordonPlusRow halfDimension row
        (gordonCoordinateBlockEquiv halfDimension (0, index))
    rw [gordonReflectionActualMatrix_zero_zero,
      gordonCoordinateBlockEquiv_zero, gordonPlusRow_apply_left]
  · change gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (0, row))
        (gordonCoordinateBlockEquiv halfDimension (1, index)) =
      gordonPlusRow halfDimension row
        (gordonCoordinateBlockEquiv halfDimension (1, index))
    rw [gordonReflectionActualMatrix_zero_one,
      gordonCoordinateBlockEquiv_one, gordonPlusRow_apply_right]

theorem gordonReflectionActualMatrix_one_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (1, row)) =
      gordonMinusRow halfDimension row := by
  funext column
  obtain ⟨source, rfl⟩ :=
    (gordonCoordinateBlockEquiv halfDimension).surjective column
  rcases source with ⟨tag, index⟩
  fin_cases tag
  · change gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (1, row))
        (gordonCoordinateBlockEquiv halfDimension (0, index)) =
      gordonMinusRow halfDimension row
        (gordonCoordinateBlockEquiv halfDimension (0, index))
    rw [gordonReflectionActualMatrix_one_zero,
      gordonCoordinateBlockEquiv_zero, gordonMinusRow_apply_left]
  · change gordonReflectionActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (1, row))
        (gordonCoordinateBlockEquiv halfDimension (1, index)) =
      gordonMinusRow halfDimension row
        (gordonCoordinateBlockEquiv halfDimension (1, index))
    rw [gordonReflectionActualMatrix_one_one,
      gordonCoordinateBlockEquiv_one, gordonMinusRow_apply_right]

@[simp] theorem gordonReflectionActualMatrix_interleaved_zero_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonReflectionActualMatrix halfDimension
        (gordonInterleavedEquiv halfDimension (row, 0)) =
      gordonPlusRow halfDimension row := by
  simpa only [gordonRowBlockEquiv_zero] using
    gordonReflectionActualMatrix_zero_row halfDimension row

@[simp] theorem gordonReflectionActualMatrix_interleaved_one_row
    (halfDimension : ℕ) (row : Fin halfDimension) :
    gordonReflectionActualMatrix halfDimension
        (gordonInterleavedEquiv halfDimension (row, 1)) =
      gordonMinusRow halfDimension row := by
  simpa only [gordonRowBlockEquiv_one] using
    gordonReflectionActualMatrix_one_row halfDimension row

noncomputable def gordonMixingActualMatrix (halfDimension : ℕ) :
    Matrix (Fin (2 * halfDimension)) (Fin (2 * halfDimension)) ℚ⟦X⟧ :=
  (gordonMixingProductMatrix halfDimension).reindex
    (gordonRowBlockEquiv halfDimension) (gordonRowBlockEquiv halfDimension)

@[simp] theorem gordonMixingActualMatrix_zero_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (0, row))
        (gordonRowBlockEquiv halfDimension (0, column)) =
      if row = column then 1 else 0 := by
  unfold gordonMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact gordonMixingProductMatrix_zero_zero halfDimension row column

@[simp] theorem gordonMixingActualMatrix_zero_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (0, row))
        (gordonRowBlockEquiv halfDimension (1, column)) = 0 := by
  unfold gordonMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact gordonMixingProductMatrix_zero_one halfDimension row column

@[simp] theorem gordonMixingActualMatrix_one_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (1, row))
        (gordonRowBlockEquiv halfDimension (0, column)) = 0 := by
  unfold gordonMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact gordonMixingProductMatrix_one_zero halfDimension row column

@[simp] theorem gordonMixingActualMatrix_one_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingActualMatrix halfDimension
        (gordonRowBlockEquiv halfDimension (1, row))
        (gordonRowBlockEquiv halfDimension (1, column)) =
      -gordonHalfScalar * gordonCumulativeEntry row.val column.val := by
  unfold gordonMixingActualMatrix
  rw [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact gordonMixingProductMatrix_one_one halfDimension row column

@[simp] theorem gordonMixingActualMatrix_interleaved_zero_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingActualMatrix halfDimension
        (gordonInterleavedEquiv halfDimension (row, 0))
        (gordonInterleavedEquiv halfDimension (column, 0)) =
      if row = column then 1 else 0 := by
  simpa only [gordonRowBlockEquiv_zero] using
    gordonMixingActualMatrix_zero_zero halfDimension row column

@[simp] theorem gordonMixingActualMatrix_interleaved_zero_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingActualMatrix halfDimension
        (gordonInterleavedEquiv halfDimension (row, 0))
        (gordonInterleavedEquiv halfDimension (column, 1)) = 0 := by
  simpa only [gordonRowBlockEquiv_zero, gordonRowBlockEquiv_one] using
    gordonMixingActualMatrix_zero_one halfDimension row column

@[simp] theorem gordonMixingActualMatrix_interleaved_one_zero
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingActualMatrix halfDimension
        (gordonInterleavedEquiv halfDimension (row, 1))
        (gordonInterleavedEquiv halfDimension (column, 0)) = 0 := by
  simpa only [gordonRowBlockEquiv_zero, gordonRowBlockEquiv_one] using
    gordonMixingActualMatrix_one_zero halfDimension row column

@[simp] theorem gordonMixingActualMatrix_interleaved_one_one
    (halfDimension : ℕ) (row column : Fin halfDimension) :
    gordonMixingActualMatrix halfDimension
        (gordonInterleavedEquiv halfDimension (row, 1))
        (gordonInterleavedEquiv halfDimension (column, 1)) =
      -gordonHalfScalar * gordonCumulativeEntry row.val column.val := by
  simpa only [gordonRowBlockEquiv_one] using
    gordonMixingActualMatrix_one_one halfDimension row column

theorem gordonInterleavedMatrix_eq_mixing_mul_reflection
    (halfDimension : ℕ) :
    (fun row column => gordonInterleavedRow halfDimension row column) =
      gordonMixingActualMatrix halfDimension *
        gordonReflectionActualMatrix halfDimension := by
  apply Matrix.ext
  intro row column
  obtain ⟨source, rfl⟩ :=
    (gordonRowBlockEquiv halfDimension).surjective row
  rcases source with ⟨tag, index⟩
  fin_cases tag
  · rw [Matrix.mul_apply]
    rw [← (gordonRowBlockEquiv halfDimension).sum_comp]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    simp
  · rw [Matrix.mul_apply]
    rw [← (gordonRowBlockEquiv halfDimension).sum_comp]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [gordonMixedRow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro summand hsummand
    ring

noncomputable def gordonCoordinateRowPermutation (halfDimension : ℕ) :
    Equiv.Perm (Fin 2 × Fin halfDimension) :=
  (gordonCoordinateBlockEquiv halfDimension).trans
    (gordonRowBlockEquiv halfDimension).symm

noncomputable def gordonPermutationSignSeries (halfDimension : ℕ) : ℚ⟦X⟧ :=
  (((gordonCoordinateRowPermutation halfDimension).sign : ℤ) : ℚ⟦X⟧)

noncomputable def gordonOrderPermutation (halfDimension : ℕ) :
    Equiv.Perm (Fin (2 * halfDimension)) :=
  (gordonRowBlockEquiv halfDimension).symm.trans
    (gordonCoordinateBlockEquiv halfDimension)

@[simp] theorem gordonOrderPermutation_apply_zero
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOrderPermutation halfDimension
        (gordonRowBlockEquiv halfDimension (0, index)) =
      gordonCoordinateBlockEquiv halfDimension (0, index) := by
  unfold gordonOrderPermutation
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]

@[simp] theorem gordonOrderPermutation_apply_one
    (halfDimension : ℕ) (index : Fin halfDimension) :
    gordonOrderPermutation halfDimension
        (gordonRowBlockEquiv halfDimension (1, index)) =
      gordonCoordinateBlockEquiv halfDimension (1, index) := by
  unfold gordonOrderPermutation
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]

theorem gordonRowBlockEquiv_zero_val
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonRowBlockEquiv halfDimension (0, index)).val = 2 * index.val := by
  simp [gordonRowBlockEquiv, gordonInterleavedEquiv, finProdFinEquiv]

theorem gordonRowBlockEquiv_one_val
    (halfDimension : ℕ) (index : Fin halfDimension) :
    (gordonRowBlockEquiv halfDimension (1, index)).val =
      2 * index.val + 1 := by
  simp [gordonRowBlockEquiv, gordonInterleavedEquiv, finProdFinEquiv]
  omega

theorem gordonOrderPermutation_inner_odd
    (halfDimension : ℕ) (column : Fin halfDimension) :
    ∏ row ∈ Finset.Iio (gordonRowBlockEquiv halfDimension (1, column)),
        (if gordonOrderPermutation halfDimension row <
            gordonOrderPermutation halfDimension
              (gordonRowBlockEquiv halfDimension (1, column))
          then (1 : ℤˣ) else -1) = 1 := by
  apply Finset.prod_eq_one
  intro row hrow
  rw [if_pos]
  obtain ⟨source, rfl⟩ :=
    (gordonRowBlockEquiv halfDimension).surjective row
  rcases source with ⟨tag, index⟩
  fin_cases tag
  · change gordonOrderPermutation halfDimension
        (gordonRowBlockEquiv halfDimension (0, index)) <
      gordonOrderPermutation halfDimension
        (gordonRowBlockEquiv halfDimension (1, column))
    rw [gordonOrderPermutation_apply_zero,
      gordonOrderPermutation_apply_one,
      gordonCoordinateBlockEquiv_zero,
      gordonCoordinateBlockEquiv_one]
    change (gordonLeftIndex halfDimension index).val <
      (gordonRightIndex halfDimension column).val
    simp [gordonLeftIndex, gordonRightIndex]
    omega
  · change gordonOrderPermutation halfDimension
        (gordonRowBlockEquiv halfDimension (1, index)) <
      gordonOrderPermutation halfDimension
        (gordonRowBlockEquiv halfDimension (1, column))
    have hposition := Finset.mem_Iio.mp hrow
    change gordonRowBlockEquiv halfDimension (1, index) <
      gordonRowBlockEquiv halfDimension (1, column) at hposition
    rw [gordonOrderPermutation_apply_one,
      gordonOrderPermutation_apply_one,
      gordonCoordinateBlockEquiv_one,
      gordonCoordinateBlockEquiv_one]
    change (gordonRightIndex halfDimension index).val <
      (gordonRightIndex halfDimension column).val
    rw [gordonRightIndex, gordonRightIndex]
    change halfDimension + index.val < halfDimension + column.val
    have hpositionVal :
        (gordonRowBlockEquiv halfDimension (1, index)).val <
          (gordonRowBlockEquiv halfDimension (1, column)).val := hposition
    rw [gordonRowBlockEquiv_one_val,
      gordonRowBlockEquiv_one_val] at hpositionVal
    omega

theorem gordonOrderPermutation_inner_even
    (halfDimension : ℕ) (column : Fin halfDimension) :
    ∏ row ∈ Finset.Iio (gordonRowBlockEquiv halfDimension (0, column)),
        (if gordonOrderPermutation halfDimension row <
            gordonOrderPermutation halfDimension
              (gordonRowBlockEquiv halfDimension (0, column))
          then (1 : ℤˣ) else -1) = 1 := by
  have hnot : ∀ row ∈
      Finset.Iio (gordonRowBlockEquiv halfDimension (0, column)),
      ¬gordonOrderPermutation halfDimension row <
        gordonOrderPermutation halfDimension
          (gordonRowBlockEquiv halfDimension (0, column)) := by
    intro row hrow
    obtain ⟨source, rfl⟩ :=
      (gordonRowBlockEquiv halfDimension).surjective row
    rcases source with ⟨tag, index⟩
    have hposition := Finset.mem_Iio.mp hrow
    fin_cases tag
    · change ¬gordonOrderPermutation halfDimension
          (gordonRowBlockEquiv halfDimension (0, index)) <
        gordonOrderPermutation halfDimension
          (gordonRowBlockEquiv halfDimension (0, column))
      change gordonRowBlockEquiv halfDimension (0, index) <
        gordonRowBlockEquiv halfDimension (0, column) at hposition
      rw [gordonOrderPermutation_apply_zero,
        gordonOrderPermutation_apply_zero,
        gordonCoordinateBlockEquiv_zero,
        gordonCoordinateBlockEquiv_zero]
      change ¬(gordonLeftIndex halfDimension index).val <
        (gordonLeftIndex halfDimension column).val
      have hpositionVal :
          (gordonRowBlockEquiv halfDimension (0, index)).val <
            (gordonRowBlockEquiv halfDimension (0, column)).val := hposition
      rw [gordonRowBlockEquiv_zero_val,
        gordonRowBlockEquiv_zero_val] at hpositionVal
      change ¬(halfDimension - 1 - index.val) <
        (halfDimension - 1 - column.val)
      omega
    · change ¬gordonOrderPermutation halfDimension
          (gordonRowBlockEquiv halfDimension (1, index)) <
        gordonOrderPermutation halfDimension
          (gordonRowBlockEquiv halfDimension (0, column))
      change gordonRowBlockEquiv halfDimension (1, index) <
        gordonRowBlockEquiv halfDimension (0, column) at hposition
      rw [gordonOrderPermutation_apply_one,
        gordonOrderPermutation_apply_zero,
        gordonCoordinateBlockEquiv_one,
        gordonCoordinateBlockEquiv_zero]
      change ¬(gordonRightIndex halfDimension index).val <
        (gordonLeftIndex halfDimension column).val
      simp [gordonRightIndex, gordonLeftIndex]
      omega
  rw [Finset.prod_congr rfl (fun row hrow =>
    if_neg (hnot row hrow))]
  rw [Finset.prod_const]
  have hcard :
      (Finset.Iio (gordonRowBlockEquiv halfDimension (0, column))).card =
        2 * column.val := by
    rw [Fin.card_Iio, gordonRowBlockEquiv_zero_val]
  rw [hcard, pow_mul]
  norm_num

theorem gordonOrderPermutation_sign (halfDimension : ℕ) :
    (gordonOrderPermutation halfDimension).sign = 1 := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  apply Finset.prod_eq_one
  intro column hcolumn
  obtain ⟨source, rfl⟩ :=
    (gordonRowBlockEquiv halfDimension).surjective column
  rcases source with ⟨tag, index⟩
  fin_cases tag
  · exact gordonOrderPermutation_inner_even halfDimension index
  · exact gordonOrderPermutation_inner_odd halfDimension index

theorem gordonCoordinateRowPermutation_sign (halfDimension : ℕ) :
    (gordonCoordinateRowPermutation halfDimension).sign = 1 := by
  have hsign := Equiv.Perm.sign_eq_sign_of_equiv
    (gordonCoordinateRowPermutation halfDimension)
    (gordonOrderPermutation halfDimension)
    (gordonRowBlockEquiv halfDimension)
    (by
      intro source
      simp [gordonCoordinateRowPermutation, gordonOrderPermutation])
  rw [hsign, gordonOrderPermutation_sign]

theorem gordonPermutationSignSeries_eq_one (halfDimension : ℕ) :
    gordonPermutationSignSeries halfDimension = 1 := by
  unfold gordonPermutationSignSeries
  rw [gordonCoordinateRowPermutation_sign]
  norm_num

theorem gordonMixingActualMatrix_det (halfDimension : ℕ) :
    (gordonMixingActualMatrix halfDimension).det =
      (-gordonHalfScalar) ^ halfDimension *
        (gordonCumulativeMatrix halfDimension).det := by
  unfold gordonMixingActualMatrix
  rw [Matrix.det_reindex_self, gordonMixingProductMatrix_det]

theorem gordonReflectionActualMatrix_det (halfDimension : ℕ) :
    (gordonReflectionActualMatrix halfDimension).det =
      gordonPermutationSignSeries halfDimension *
        ((-2 : ℚ⟦X⟧) ^ halfDimension *
          X ^ staircaseWeight (2 * halfDimension - 1)) := by
  unfold gordonReflectionActualMatrix
  rw [Matrix.det_reindex]
  unfold gordonPermutationSignSeries gordonCoordinateRowPermutation
  rw [gordonReflectionProductMatrix_det]

theorem gordonNegativeHalf_mul_negativeTwo :
    (-gordonHalfScalar) * (-2 : ℚ⟦X⟧) = 1 := by
  rw [neg_mul_neg]
  exact gordonHalfScalar_mul_two

theorem gordonInterleavedMatrix_det_with_sign (halfDimension : ℕ) :
    Matrix.det (fun row column =>
        gordonInterleavedRow halfDimension row column) =
      gordonPermutationSignSeries halfDimension *
        (X ^ staircaseWeight (2 * halfDimension - 1) *
          (evenFormalGesselMatrixQ halfDimension).det) := by
  rw [gordonInterleavedMatrix_eq_mixing_mul_reflection,
    Matrix.det_mul, gordonMixingActualMatrix_det,
    gordonReflectionActualMatrix_det,
    gordonCumulativeMatrix_det_eq_formalGessel]
  have hcancel :
      (-gordonHalfScalar) ^ halfDimension *
          (-2 : ℚ⟦X⟧) ^ halfDimension = 1 := by
    rw [← mul_pow, gordonNegativeHalf_mul_negativeTwo, one_pow]
  rw [show
      ((-gordonHalfScalar) ^ halfDimension *
          (evenFormalGesselMatrixQ halfDimension).det) *
        (gordonPermutationSignSeries halfDimension *
          ((-2 : ℚ⟦X⟧) ^ halfDimension *
            X ^ staircaseWeight (2 * halfDimension - 1))) =
      gordonPermutationSignSeries halfDimension *
        (((-gordonHalfScalar) ^ halfDimension *
            (-2 : ℚ⟦X⟧) ^ halfDimension) *
          (X ^ staircaseWeight (2 * halfDimension - 1) *
            (evenFormalGesselMatrixQ halfDimension).det)) by ring,
    hcancel, one_mul]

theorem gordonInterleavedMatrix_det (halfDimension : ℕ) :
    Matrix.det (fun row column =>
        gordonInterleavedRow halfDimension row column) =
      X ^ staircaseWeight (2 * halfDimension - 1) *
        (evenFormalGesselMatrixQ halfDimension).det := by
  rw [gordonInterleavedMatrix_det_with_sign,
    gordonPermutationSignSeries_eq_one, one_mul]

theorem generalEvenGesselAssemblyIdentity_all (halfDimension : ℕ) :
    GeneralEvenGesselAssemblyIdentity halfDimension := by
  unfold GeneralEvenGesselAssemblyIdentity
  rw [generalClosedEvenAssembly_eq_interleaved_det,
    listRowsOfLength_gordonInterleavedRows,
    gordonInterleavedMatrix_det]

theorem generalEvenGesselActualBridge_all
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    GeneralEvenGesselActualBridge halfDimension :=
  (generalEvenGesselActualBridge_iff_assembly halfDimension hhalf).2
    (generalEvenGesselAssemblyIdentity_all halfDimension)

end FibonacciRibbonKernel
