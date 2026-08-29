import FibonacciRibbonKernel.EndpointEnumeration
import Mathlib.Data.Fintype.BigOperators

namespace FibonacciRibbonKernel

open scoped Classical

/-- Literal cells `(row,column)` of a bounded partition. -/
def YoungCell {rank columns : ℕ} (shape : BoundedPartition rank columns) :=
  Σ row : Fin (rank + 1), Fin (shape.1 row).val

noncomputable instance youngCellFintype
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    Fintype (YoungCell shape) := by
  classical
  unfold YoungCell
  infer_instance

/-- Number of cells strictly below a cell in its column. -/
noncomputable def YoungCell.belowCount
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (cell : YoungCell shape) : ℕ := by
  classical
  exact (Finset.univ.filter fun row : Fin (rank + 1) =>
    cell.1.val < row.val ∧ cell.2.val < (shape.1 row).val).card

/-- Literal hook length: self plus cells rightward and below. -/
noncomputable def YoungCell.hookLength
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (cell : YoungCell shape) : ℕ :=
  (shape.1 cell.1).val - cell.2.val + cell.belowCount

/-- Product of all hook lengths of a partition. -/
noncomputable def hookProduct
    {rank columns : ℕ} (shape : BoundedPartition rank columns) : ℕ :=
  ∏ cell : YoungCell shape, cell.hookLength

theorem YoungCell.hookLength_pos
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (cell : YoungCell shape) : 0 < cell.hookLength := by
  unfold YoungCell.hookLength
  have hcolumn := cell.2.isLt
  omega

theorem hookProduct_pos
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    0 < hookProduct shape := by
  unfold hookProduct
  exact Finset.prod_pos fun cell _ => cell.hookLength_pos

theorem youngCell_card
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    Fintype.card (YoungCell shape) = columns := by
  rw [show Fintype.card (YoungCell shape) =
      ∑ row : Fin (rank + 1), (shape.1 row).val by
    calc
      Fintype.card (YoungCell shape) =
          ∑ row : Fin (rank + 1), Fintype.card (Fin (shape.1 row).val) := by
            unfold YoungCell
            exact Fintype.card_sigma
      _ = ∑ row : Fin (rank + 1), (shape.1 row).val := by simp]
  exact shape.2.2

/-- Integer-safe statement exactly equivalent to the displayed hook formula. -/
def HookFormulaStatement
    {rank columns : ℕ} (shape : BoundedPartition rank columns) : Prop :=
  standardTableauNumber shape * hookProduct shape = columns.factorial

theorem hookFormulaStatement_iff
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    HookFormulaStatement shape ↔
      standardTableauNumber shape *
          (∏ cell : YoungCell shape, cell.hookLength) = columns.factorial := by
  rfl

end FibonacciRibbonKernel
