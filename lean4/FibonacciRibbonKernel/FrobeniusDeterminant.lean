import FibonacciRibbonKernel.BoundedKostkaRecurrence
import Mathlib.LinearAlgebra.Matrix.Block

namespace FibonacciRibbonKernel

open scoped Classical

theorem boundedFactorialDeterminant_zero_columns
    {rank : ℕ} (shape : BoundedPartition rank 0) :
    boundedFactorialDeterminant shape = 1 := by
  have hrow (row : Fin (rank + 1)) : (shape.1 row).val = 0 := by
    exact Fin.val_eq_zero (shape.1 row)
  unfold boundedFactorialDeterminant
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro row hmem
    change reciprocalFactorialInt
      (((shape.1 row).val : ℤ) + (row.rev.val : ℤ) -
        (row.rev.val : ℤ)) = 1
    rw [hrow row]
    norm_num [reciprocalFactorialInt]
  · intro row column hcolumnRow
    unfold factorialKernelMatrix BoundedPartition.shiftedRows
    have hnegative :
        ¬(0 : ℤ) ≤
          ((shape.1 row).val : ℤ) + (row.rev.val : ℤ) -
            (column.rev.val : ℤ) := by
      rw [hrow row]
      simp only [Nat.cast_zero, zero_add]
      simp [Fin.rev] at hcolumnRow ⊢
      omega
    unfold reciprocalFactorialInt
    rw [if_neg hnegative]

/-- Frobenius' factorial-determinant formula for every bounded partition,
proved internally by matching the Young-lattice corner recurrence. -/
theorem standardTableauNumber_eq_factorial_mul_boundedFactorialDeterminant
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    (standardTableauNumber shape : ℚ) =
      (columns.factorial : ℚ) * boundedFactorialDeterminant shape := by
  induction columns generalizing rank with
  | zero =>
      have hhook := hookFormulaStatement shape
      unfold HookFormulaStatement at hhook
      have hstandard : standardTableauNumber shape = 1 := by
        norm_num at hhook
        omega
      rw [hstandard, boundedFactorialDeterminant_zero_columns]
      norm_num
  | succ columns ih =>
      have hrecurrence := standardTableauNumber_removeRow_recurrence
        shape (Nat.succ_pos columns)
      rw [hrecurrence]
      push_cast
      calc
        (∑ removable : shape.RemovableRowIndex,
            (standardTableauNumber
              (shape.removeRow removable.1 removable.2) : ℚ)) =
            ∑ removable : shape.RemovableRowIndex,
              (columns.factorial : ℚ) *
                boundedFactorialDeterminant
                  (shape.removeRow removable.1 removable.2) := by
          apply Finset.sum_congr rfl
          intro removable hmem
          exact ih (shape.removeRow removable.1 removable.2)
        _ = (columns.factorial : ℚ) *
            ((columns + 1 : ℚ) * boundedFactorialDeterminant shape) := by
          rw [← Finset.mul_sum,
            ← boundedFactorialDeterminant_corner_recurrence_index shape]
          norm_num only [Nat.cast_add, Nat.cast_one]
        _ = ((columns + 1).factorial : ℚ) *
            boundedFactorialDeterminant shape := by
          rw [Nat.factorial_succ]
          push_cast
          ring

end FibonacciRibbonKernel
