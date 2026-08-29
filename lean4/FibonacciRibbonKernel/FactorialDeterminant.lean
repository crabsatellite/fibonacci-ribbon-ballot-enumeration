import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

namespace FibonacciRibbonKernel

open scoped Classical

/-- Reciprocal factorial with the standard zero convention at negative
integer arguments. -/
noncomputable def reciprocalFactorialInt (argument : ℤ) : ℚ :=
  if 0 ≤ argument then ((argument.toNat.factorial : ℚ) : ℚ)⁻¹ else 0

@[simp] theorem reciprocalFactorialInt_negSucc (index : ℕ) :
    reciprocalFactorialInt (Int.negSucc index) = 0 := by
  simp [reciprocalFactorialInt]

@[simp] theorem reciprocalFactorialInt_ofNat (index : ℕ) :
    reciprocalFactorialInt index = ((index.factorial : ℚ) : ℚ)⁻¹ := by
  simp [reciprocalFactorialInt]

/-- Cleared factorial shift, valid also across the zero boundary because of
the negative-index convention. -/
theorem reciprocalFactorialInt_sub_one (argument : ℤ) :
    reciprocalFactorialInt (argument - 1) =
      (argument : ℚ) * reciprocalFactorialInt argument := by
  cases argument with
  | negSucc index => simp [reciprocalFactorialInt]
  | ofNat index =>
      cases index with
      | zero => simp [reciprocalFactorialInt]
      | succ index =>
          have hsub : Int.ofNat (index + 1) - 1 = Int.ofNat index := by simp
          rw [hsub]
          rw [show reciprocalFactorialInt (Int.ofNat index) =
              (index.factorial : ℚ)⁻¹ by
                exact reciprocalFactorialInt_ofNat index]
          rw [show reciprocalFactorialInt (Int.ofNat (index + 1)) =
              ((index + 1).factorial : ℚ)⁻¹ by
                exact reciprocalFactorialInt_ofNat (index + 1)]
          rw [show ((Int.ofNat (index + 1) : ℤ) : ℚ) =
              (index + 1 : ℚ) by norm_num]
          change (index.factorial : ℚ)⁻¹ =
            (index + 1 : ℚ) * ((index + 1).factorial : ℚ)⁻¹
          rw [Nat.factorial_succ]
          push_cast
          have hfactorial : (index.factorial : ℚ) ≠ 0 := by positivity
          field_simp

theorem reciprocalFactorialInt_nat_sub {left right : ℕ}
    (h : right ≤ left) :
    reciprocalFactorialInt ((left : ℤ) - (right : ℤ)) =
      (((left - right).factorial : ℚ) : ℚ)⁻¹ := by
  unfold reciprocalFactorialInt
  have hnonnegative : (0 : ℤ) ≤ (left : ℤ) - (right : ℤ) := by omega
  rw [if_pos hnonnegative]
  rw [Int.toNat_sub]

theorem reciprocalFactorialInt_nat_sub_eq_zero {left right : ℕ}
    (h : left < right) :
    reciprocalFactorialInt ((left : ℤ) - (right : ℤ)) = 0 := by
  unfold reciprocalFactorialInt
  rw [if_neg (by omega)]

variable {indexType : Type*} [Fintype indexType] [DecidableEq indexType]

/-- Sum of determinants obtained by weighting one row coordinatewise.  This
is the adjugate trace identity used in the factorial-determinant recurrence. -/
theorem sum_det_updateRow_mul_columnWeights
    (matrix : Matrix indexType indexType ℚ) (weights : indexType → ℚ) :
    (∑ row, Matrix.det
        (matrix.updateRow row (fun column =>
          weights column * matrix row column))) =
      (∑ column, weights column) * Matrix.det matrix := by
  classical
  calc
    (∑ row, Matrix.det
        (matrix.updateRow row (fun column =>
          weights column * matrix row column))) =
        ∑ row, (matrix.transpose.cramer
          (fun column => weights column * matrix row column)) row := by
      apply Finset.sum_congr rfl
      intro row hrow
      exact (Matrix.cramer_transpose_apply
        (A := matrix) (b := fun column =>
          weights column * matrix row column) row).symm
    _ = ∑ row, ∑ column,
        Matrix.adjugate matrix column row *
          (weights column * matrix row column) := by
      apply Finset.sum_congr rfl
      intro row hrow
      rw [Matrix.cramer_eq_adjugate_mulVec]
      rw [← Matrix.adjugate_transpose]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    _ = ∑ column, weights column *
        (∑ row, matrix row column * Matrix.adjugate matrix column row) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro column hcolumn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row hrow
      ring
    _ = (∑ column, weights column) * Matrix.det matrix := by
      simp_rw [← Matrix.det_eq_sum_mul_adjugate_col matrix]
      rw [Finset.sum_mul]

/-- Factorial-kernel matrix attached to shifted row coordinates. -/
noncomputable def factorialKernelMatrix {dimension : ℕ}
    (shiftedRows : Fin dimension → ℤ) :
    Matrix (Fin dimension) (Fin dimension) ℚ :=
  fun row column =>
    reciprocalFactorialInt
      (shiftedRows row - (column.rev.val : ℤ))

theorem factorialKernelMatrix_decrement_row {dimension : ℕ}
    (shiftedRows : Fin dimension → ℤ) (row : Fin dimension) :
    factorialKernelMatrix (Function.update shiftedRows row
        (shiftedRows row - 1)) =
      (factorialKernelMatrix shiftedRows).updateRow row
        (fun column =>
          ((shiftedRows row - (column.rev.val : ℤ) : ℤ) : ℚ) *
            factorialKernelMatrix shiftedRows row column) := by
  classical
  ext current column
  by_cases hcurrent : current = row
  · subst current
    simp only [factorialKernelMatrix, Matrix.updateRow_self,
      Function.update_self]
    rw [show shiftedRows row - 1 - (column.rev.val : ℤ) =
        (shiftedRows row - (column.rev.val : ℤ)) - 1 by ring]
    exact reciprocalFactorialInt_sub_one _
  · simp [factorialKernelMatrix, Matrix.updateRow_ne, hcurrent]

theorem factorialKernel_det_decrement_sum {dimension : ℕ}
    (shiftedRows : Fin dimension → ℤ) :
    (∑ row, Matrix.det
        (factorialKernelMatrix
          (Function.update shiftedRows row (shiftedRows row - 1)))) =
      (((∑ row, shiftedRows row) -
          ∑ column : Fin dimension, (column.rev.val : ℤ) : ℤ) : ℚ) *
        Matrix.det (factorialKernelMatrix shiftedRows) := by
  classical
  let matrix := factorialKernelMatrix shiftedRows
  have hrow (row : Fin dimension) :
      (fun column =>
          ((shiftedRows row - (column.rev.val : ℤ) : ℤ) : ℚ) *
            matrix row column) =
        (shiftedRows row : ℚ) • matrix row +
          (fun column => -((column.rev.val : ℚ)) * matrix row column) := by
    funext column
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  calc
    (∑ row, Matrix.det
        (factorialKernelMatrix
          (Function.update shiftedRows row (shiftedRows row - 1)))) =
        ∑ row, Matrix.det
          (matrix.updateRow row
            (fun column =>
              ((shiftedRows row - (column.rev.val : ℤ) : ℤ) : ℚ) *
                matrix row column)) := by
      apply Finset.sum_congr rfl
      intro row hmem
      rw [factorialKernelMatrix_decrement_row]
    _ = ∑ row, ((shiftedRows row : ℚ) * Matrix.det matrix +
        Matrix.det (matrix.updateRow row
          (fun column => -((column.rev.val : ℚ)) * matrix row column))) := by
      apply Finset.sum_congr rfl
      intro row hmem
      rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
        Matrix.updateRow_eq_self]
    _ = (∑ row, (shiftedRows row : ℚ)) * Matrix.det matrix +
        ∑ row, Matrix.det (matrix.updateRow row
          (fun column => -((column.rev.val : ℚ)) * matrix row column)) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ row, (shiftedRows row : ℚ)) * Matrix.det matrix +
        (∑ column : Fin dimension, -((column.rev.val : ℚ))) *
          Matrix.det matrix := by
      rw [sum_det_updateRow_mul_columnWeights]
    _ = (((∑ row, shiftedRows row) -
          ∑ column : Fin dimension, (column.rev.val : ℤ) : ℤ) : ℚ) *
        Matrix.det (factorialKernelMatrix shiftedRows) := by
      dsimp only [matrix]
      push_cast
      rw [Finset.sum_neg_distrib]
      ring

end FibonacciRibbonKernel
