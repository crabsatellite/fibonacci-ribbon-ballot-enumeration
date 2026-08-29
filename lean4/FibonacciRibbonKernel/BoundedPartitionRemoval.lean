import FibonacciRibbonKernel.BoundedFactorialDeterminant

namespace FibonacciRibbonKernel

open scoped Classical

def BoundedPartition.decrementedRowValues
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) : Fin (rank + 1) → ℕ :=
  Function.update (fun candidate => (shape.1 candidate).val) row
    ((shape.1 row).val - 1)

@[simp] theorem BoundedPartition.decrementedRowValues_self
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) :
    shape.decrementedRowValues row row = (shape.1 row).val - 1 := by
  simp [BoundedPartition.decrementedRowValues]

theorem BoundedPartition.decrementedRowValues_of_ne
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    {row candidate : Fin (rank + 1)} (hne : candidate ≠ row) :
    shape.decrementedRowValues row candidate = (shape.1 candidate).val := by
  simp [BoundedPartition.decrementedRowValues, hne]

theorem BoundedPartition.decrementedRowValues_sum
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) (hpositive : 0 < (shape.1 row).val) :
    (∑ candidate, shape.decrementedRowValues row candidate) = columns - 1 := by
  classical
  have horiginal := Finset.add_sum_erase
    (Finset.univ : Finset (Fin (rank + 1)))
    (fun candidate => (shape.1 candidate).val) (Finset.mem_univ row)
  have hdecremented := Finset.add_sum_erase
    (Finset.univ : Finset (Fin (rank + 1)))
    (shape.decrementedRowValues row) (Finset.mem_univ row)
  rw [shape.decrementedRowValues_self] at hdecremented
  have herase :
      ∑ candidate ∈ (Finset.univ : Finset (Fin (rank + 1))).erase row,
          shape.decrementedRowValues row candidate =
        ∑ candidate ∈ (Finset.univ : Finset (Fin (rank + 1))).erase row,
          (shape.1 candidate).val := by
    apply Finset.sum_congr rfl
    intro candidate hcandidate
    exact shape.decrementedRowValues_of_ne
      (Finset.ne_of_mem_erase hcandidate)
  rw [herase] at hdecremented
  rw [shape.2.2] at horiginal
  omega

/-- Remove one outer-corner cell while retaining the fixed row bound. -/
noncomputable def BoundedPartition.removeRow
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) (hremovable : shape.RemovableRow row) :
    BoundedPartition rank (columns - 1) := by
  have hcolumns : 0 < columns := by
    by_contra hnot
    have hzero : columns = 0 := Nat.eq_zero_of_not_pos hnot
    subst columns
    have hbound := (shape.1 row).isLt
    have hpositive := hremovable.1
    omega
  have hsum := shape.decrementedRowValues_sum row hremovable.1
  let rows : Fin (rank + 1) → Fin (columns - 1 + 1) := fun candidate =>
    ⟨shape.decrementedRowValues row candidate, by
      have hle : shape.decrementedRowValues row candidate ≤
          ∑ current, shape.decrementedRowValues row current :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ candidate)
      rw [hsum] at hle
      omega⟩
  refine ⟨rows, ?_, ?_⟩
  · intro index
    change shape.decrementedRowValues row index.succ ≤
      shape.decrementedRowValues row index.castSucc
    by_cases hupper : index.castSucc = row
    · have hlower : index.succ ≠ row := by
        intro heq
        exact Fin.castSucc_lt_succ.ne (hupper.trans heq.symm)
      rw [shape.decrementedRowValues_of_ne hlower,
        hupper, shape.decrementedRowValues_self]
      have hstrict := hremovable.2 index.succ (by
        rw [← hupper]
        rfl)
      omega
    · by_cases hlower : index.succ = row
      · rw [hlower, shape.decrementedRowValues_self,
          shape.decrementedRowValues_of_ne hupper]
        have hdominant := Fin.mk_le_mk.mp (shape.2.1 index)
        rw [hlower] at hdominant
        exact (Nat.sub_le _ _).trans hdominant
      · rw [shape.decrementedRowValues_of_ne hlower,
          shape.decrementedRowValues_of_ne hupper]
        exact Fin.mk_le_mk.mp (shape.2.1 index)
  · change (∑ candidate, shape.decrementedRowValues row candidate) = columns - 1
    exact hsum

@[simp] theorem BoundedPartition.removeRow_value
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row candidate : Fin (rank + 1))
    (hremovable : shape.RemovableRow row) :
    ((shape.removeRow row hremovable).1 candidate).val =
      shape.decrementedRowValues row candidate := by
  rfl

theorem BoundedPartition.removeRow_shiftedRows
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) (hremovable : shape.RemovableRow row) :
    (shape.removeRow row hremovable).shiftedRows =
      Function.update shape.shiftedRows row (shape.shiftedRows row - 1) := by
  funext candidate
  by_cases hcandidate : candidate = row
  · subst candidate
    simp only [Function.update_self]
    unfold BoundedPartition.shiftedRows
    rw [shape.removeRow_value row row hremovable,
      shape.decrementedRowValues_self]
    rw [Nat.cast_sub hremovable.1]
    ring
  · change
      (((shape.removeRow row hremovable).1 candidate).val : ℤ) +
          (candidate.rev.val : ℤ) =
        Function.update shape.shiftedRows row
          (shape.shiftedRows row - 1) candidate
    rw [shape.removeRow_value row candidate hremovable,
      shape.decrementedRowValues_of_ne hcandidate]
    simp [hcandidate, BoundedPartition.shiftedRows]

theorem boundedFactorialDeterminant_removeRow
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) (hremovable : shape.RemovableRow row) :
    boundedFactorialDeterminant (shape.removeRow row hremovable) =
      Matrix.det
        (factorialKernelMatrix
          (Function.update shape.shiftedRows row
            (shape.shiftedRows row - 1))) := by
  unfold boundedFactorialDeterminant
  rw [shape.removeRow_shiftedRows row hremovable]

noncomputable def BoundedPartition.removableRows
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    Finset (Fin (rank + 1)) :=
  Finset.univ.filter shape.RemovableRow

theorem BoundedPartition.mem_removableRows_iff
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) :
    row ∈ shape.removableRows ↔ shape.RemovableRow row := by
  simp [BoundedPartition.removableRows]

/-- The Frobenius factorial determinant obeys the same corner-removal
recurrence as the fixed-shape standard-tableau number. -/
theorem boundedFactorialDeterminant_corner_recurrence
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    (columns : ℚ) * boundedFactorialDeterminant shape =
      ∑ item ∈ shape.removableRows.attach,
        boundedFactorialDeterminant
          (shape.removeRow item.1
            ((shape.mem_removableRows_iff item.1).mp item.2)) := by
  let decrementDet : Fin (rank + 1) → ℚ := fun row =>
    Matrix.det
      (factorialKernelMatrix
        (Function.update shape.shiftedRows row
          (shape.shiftedRows row - 1)))
  calc
    (columns : ℚ) * boundedFactorialDeterminant shape =
        ∑ row, decrementDet row :=
      (boundedFactorialDeterminant_all_row_decrements shape).symm
    _ = ∑ row ∈ shape.removableRows, decrementDet row := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro row hrow hnot
      have hnotRemovable : ¬ shape.RemovableRow row := by
        intro hremovable
        exact hnot ((shape.mem_removableRows_iff row).mpr hremovable)
      exact boundedFactorialDeterminant_decrement_eq_zero_of_not_removable
        shape row hnotRemovable
    _ = ∑ item ∈ shape.removableRows.attach, decrementDet item.1 := by
      exact (Finset.sum_attach shape.removableRows decrementDet).symm
    _ = ∑ item ∈ shape.removableRows.attach,
        boundedFactorialDeterminant
          (shape.removeRow item.1
            ((shape.mem_removableRows_iff item.1).mp item.2)) := by
      apply Finset.sum_congr rfl
      intro item hitem
      exact (boundedFactorialDeterminant_removeRow shape item.1
        ((shape.mem_removableRows_iff item.1).mp item.2)).symm

end FibonacciRibbonKernel
