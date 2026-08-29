import FibonacciRibbonKernel.FactorialDeterminant
import FibonacciRibbonKernel.HookBridge

namespace FibonacciRibbonKernel

open scoped Classical

/-- Strict shifted row coordinates `lambda_i+d-1-i` for a bounded
partition with `d=rank+1` rows. -/
def BoundedPartition.shiftedRows
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    Fin (rank + 1) → ℤ :=
  fun row => (shape.1 row).val + row.rev.val

/-- Frobenius factorial determinant
`det(1/(lambda_i-i+j)!)` with the negative factorial convention. -/
noncomputable def boundedFactorialDeterminant
    {rank columns : ℕ} (shape : BoundedPartition rank columns) : ℚ :=
  Matrix.det (factorialKernelMatrix shape.shiftedRows)

theorem BoundedPartition.shiftedRows_sum
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    (∑ row, shape.shiftedRows row) =
      (columns : ℤ) +
        ∑ row : Fin (rank + 1), (row.rev.val : ℤ) := by
  have hshape :
      (∑ row, ((shape.1 row).val : ℤ)) = (columns : ℤ) := by
    exact_mod_cast shape.2.2
  simp only [BoundedPartition.shiftedRows, Finset.sum_add_distrib, hshape]

/-- The factorial determinant has the exact Young-lattice predecessor
recurrence before deleting the zero non-corner terms. -/
theorem boundedFactorialDeterminant_all_row_decrements
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    (∑ row, Matrix.det
        (factorialKernelMatrix
          (Function.update shape.shiftedRows row
            (shape.shiftedRows row - 1)))) =
      (columns : ℚ) * boundedFactorialDeterminant shape := by
  rw [factorialKernel_det_decrement_sum]
  rw [shape.shiftedRows_sum]
  push_cast
  unfold boundedFactorialDeterminant
  ring

/-- A row is removable exactly when it contains a cell and decreasing that
row preserves weak decrease.  The quantified successor form is convenient
at the last row, where the condition is vacuous. -/
def BoundedPartition.RemovableRow
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) : Prop :=
  0 < (shape.1 row).val ∧
    ∀ next : Fin (rank + 1), next.val = row.val + 1 →
      (shape.1 next).val < (shape.1 row).val

noncomputable instance BoundedPartition.removableRowDecidable
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) : Decidable (shape.RemovableRow row) :=
  Classical.dec _

theorem BoundedPartition.shiftedRows_strict_succ
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin rank) :
    shape.shiftedRows row.succ < shape.shiftedRows row.castSucc := by
  unfold BoundedPartition.shiftedRows
  have hrows := shape.2.1 row
  have hrev : row.succ.rev.val + 1 = row.castSucc.rev.val := by
    simp [Fin.rev]
    omega
  omega

theorem BoundedPartition.row_eq_last_of_no_successor
    {rank columns : ℕ} (_shape : BoundedPartition rank columns)
    (row : Fin (rank + 1))
    (hno : ¬ ∃ next : Fin (rank + 1), next.val = row.val + 1) :
    row = Fin.last rank := by
  apply Fin.ext
  have hle : row.val ≤ rank := Nat.le_of_lt_succ row.isLt
  have heq : row.val = rank := by
    by_contra hne
    have hlt : row.val < rank := lt_of_le_of_ne hle hne
    let next : Fin (rank + 1) := ⟨row.val + 1, by omega⟩
    exact hno ⟨next, rfl⟩
  exact heq

theorem BoundedPartition.next_row_eq_of_not_removable
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1))
    (hpositive : 0 < (shape.1 row).val)
    (hnot : ¬ shape.RemovableRow row) :
    ∃ next : Fin (rank + 1),
      next.val = row.val + 1 ∧
        (shape.1 next).val = (shape.1 row).val := by
  unfold BoundedPartition.RemovableRow at hnot
  push Not at hnot
  obtain ⟨next, hnext, hnlt⟩ := hnot hpositive
  have hrowLt : row.val < rank := by omega
  let predecessor : Fin rank := ⟨row.val, hrowLt⟩
  have hnextEq : next = predecessor.succ := Fin.ext hnext
  have hrowEq : row = predecessor.castSucc := Fin.ext rfl
  have hle := shape.2.1 predecessor
  rw [← hnextEq, ← hrowEq] at hle
  exact ⟨next, hnext, Nat.le_antisymm hle hnlt⟩

theorem factorialKernelMatrix_decrement_eq_next_row
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    {row next : Fin (rank + 1)}
    (hnext : next.val = row.val + 1)
    (hrows : (shape.1 next).val = (shape.1 row).val) :
    factorialKernelMatrix
        (Function.update shape.shiftedRows row
          (shape.shiftedRows row - 1)) row =
      factorialKernelMatrix
        (Function.update shape.shiftedRows row
          (shape.shiftedRows row - 1)) next := by
  funext column
  unfold factorialKernelMatrix
  simp only [Function.update_self]
  have hrn : row ≠ next := by
    intro heq
    have := congrArg Fin.val heq
    omega
  simp [hrn.symm]
  unfold BoundedPartition.shiftedRows
  have hrev : next.rev.val + 1 = row.rev.val := by
    simp [Fin.rev]
    omega
  congr 1
  omega

theorem factorialKernelMatrix_decrement_last_zero
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (hzero : (shape.1 (Fin.last rank)).val = 0) :
    factorialKernelMatrix
        (Function.update shape.shiftedRows (Fin.last rank)
          (shape.shiftedRows (Fin.last rank) - 1))
        (Fin.last rank) = 0 := by
  funext column
  simp only [factorialKernelMatrix, Function.update_self, Pi.zero_apply]
  change reciprocalFactorialInt
      (shape.shiftedRows (Fin.last rank) - 1 -
        (column.rev.val : ℤ)) = 0
  have hargument :
      shape.shiftedRows (Fin.last rank) - 1 -
          (column.rev.val : ℤ) = Int.negSucc column.rev.val := by
    have hlastrev : (Fin.last rank).rev.val = 0 := by
      simp [Fin.rev]
    unfold BoundedPartition.shiftedRows
    rw [hzero, hlastrev]
    norm_num
    rw [Int.negSucc_eq]
    push_cast
    ring
  rw [hargument, reciprocalFactorialInt_negSucc]

/-- A non-removable row contributes zero to the predecessor determinant:
either it duplicates the following shifted row or it is the empty last row. -/
theorem boundedFactorialDeterminant_decrement_eq_zero_of_not_removable
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) (hnot : ¬ shape.RemovableRow row) :
    Matrix.det
        (factorialKernelMatrix
          (Function.update shape.shiftedRows row
            (shape.shiftedRows row - 1))) = 0 := by
  by_cases hpositive : 0 < (shape.1 row).val
  · obtain ⟨next, hnext, hrows⟩ :=
      shape.next_row_eq_of_not_removable row hpositive hnot
    apply Matrix.det_zero_of_row_eq
      (show row ≠ next by
        intro heq
        have := congrArg Fin.val heq
        omega)
    exact factorialKernelMatrix_decrement_eq_next_row shape hnext hrows
  · have hzero : (shape.1 row).val = 0 := by omega
    by_cases hsuccessor : ∃ next : Fin (rank + 1), next.val = row.val + 1
    · obtain ⟨next, hnext⟩ := hsuccessor
      have hrowLt : row.val < rank := by omega
      let predecessor : Fin rank := ⟨row.val, hrowLt⟩
      have hnextEq : next = predecessor.succ := Fin.ext hnext
      have hrowEq : row = predecessor.castSucc := Fin.ext rfl
      have hle : (shape.1 next).val ≤ (shape.1 row).val := by
        have hleNat := Fin.mk_le_mk.mp (shape.2.1 predecessor)
        simpa only [hnextEq, hrowEq] using hleNat
      have hnextZero : (shape.1 next).val = 0 := by omega
      apply Matrix.det_zero_of_row_eq
        (show row ≠ next by
          intro heq
          have := congrArg Fin.val heq
          omega)
      exact factorialKernelMatrix_decrement_eq_next_row shape hnext
        (hnextZero.trans hzero.symm)
    · have hlast := shape.row_eq_last_of_no_successor row hsuccessor
      subst row
      apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last rank)
      intro column
      exact congrFun (factorialKernelMatrix_decrement_last_zero shape hzero)
        column

end FibonacciRibbonKernel
