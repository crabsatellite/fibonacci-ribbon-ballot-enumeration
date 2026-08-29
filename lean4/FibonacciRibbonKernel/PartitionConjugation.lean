import FibonacciRibbonKernel.HookBridge
import FibonacciRibbonKernel.DefinitionFormulas

namespace FibonacciRibbonKernel

open scoped Classical
open YoungDiagram

theorem YoungDiagram.transpose_card (diagram : YoungDiagram) :
    diagram.transpose.card = diagram.card := by
  unfold YoungDiagram.transpose YoungDiagram.card
  simp

/-- Cells written as a dependent sum of rows of a prescribed sufficient
height. -/
def DiagramRowCell (diagram : YoungDiagram) (height : ℕ) :=
  Σ row : Fin height, Fin (diagram.rowLen row.val)

noncomputable instance diagramRowCellFintype
    (diagram : YoungDiagram) (height : ℕ) :
    Fintype (DiagramRowCell diagram height) := by
  unfold DiagramRowCell
  infer_instance

def diagramRowCellEquiv
    (diagram : YoungDiagram) (height : ℕ)
    (hheight : diagram.colLen 0 ≤ height) :
    DiagramRowCell diagram height ≃ diagram.cells where
  toFun cell := ⟨(cell.1.val, cell.2.val), by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
    exact cell.2.isLt⟩
  invFun cell := by
    have hmem : cell.1 ∈ diagram := cell.2
    have hrowCol : cell.1.1 < diagram.colLen cell.1.2 :=
      (YoungDiagram.mem_iff_lt_colLen.mp hmem)
    have hcol : diagram.colLen cell.1.2 ≤ diagram.colLen 0 :=
      diagram.colLen_anti 0 cell.1.2 (by omega)
    let row : Fin height := ⟨cell.1.1, lt_of_lt_of_le hrowCol (hcol.trans hheight)⟩
    have hcolumn : cell.1.2 < diagram.rowLen row.val :=
      YoungDiagram.mem_iff_lt_rowLen.mp hmem
    exact ⟨row, ⟨cell.1.2, hcolumn⟩⟩
  left_inv cell := by
    apply Sigma.ext
    · exact Fin.ext rfl
    · exact heq_of_eq (Fin.ext rfl)
  right_inv cell := by
    apply Subtype.ext
    exact Prod.ext rfl rfl

theorem sum_rowLen_eq_card_of_height
    (diagram : YoungDiagram) (height : ℕ)
    (hheight : diagram.colLen 0 ≤ height) :
    (∑ row : Fin height, diagram.rowLen row.val) = diagram.card := by
  calc
    (∑ row : Fin height, diagram.rowLen row.val) =
        Fintype.card (DiagramRowCell diagram height) := by
      change (∑ row : Fin height, diagram.rowLen row.val) =
        Fintype.card (Σ row : Fin height, Fin (diagram.rowLen row.val))
      rw [Fintype.card_sigma]
      simp
    _ = Fintype.card diagram.cells :=
      Fintype.card_congr (diagramRowCellEquiv diagram height hheight)
    _ = diagram.card := by simp

/-- Conjugation on the literal bounded-partition carrier used by the paper. -/
noncomputable def BoundedPartition.conjugate
    {size : ℕ} (shape : BoundedPartition size size) :
    BoundedPartition size size := by
  let diagram := shape.youngDiagram.transpose
  have hcard : diagram.card = size := by
    dsimp [diagram]
    rw [YoungDiagram.transpose_card, shape.youngDiagram_card]
  have hrowBound (row : Fin (size + 1)) :
      diagram.rowLen row.val < size + 1 := by
    have hsubset : diagram.row row.val ⊆ diagram.cells := by
      intro cell hcell
      exact (YoungDiagram.mem_row_iff.mp hcell).1
    have hle : diagram.rowLen row.val ≤ diagram.card := by
      rw [YoungDiagram.rowLen_eq_card]
      exact Finset.card_le_card hsubset
    omega
  let rows : Fin (size + 1) → Fin (size + 1) := fun row =>
    ⟨diagram.rowLen row.val, hrowBound row⟩
  refine ⟨rows, ?_, ?_⟩
  · intro row
    apply Fin.le_def.mpr
    exact diagram.rowLen_anti row.castSucc.val row.succ.val (by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega)
  · have hheight : diagram.colLen 0 ≤ size + 1 := by
      have hcolCard : diagram.colLen 0 ≤ diagram.card := by
        rw [YoungDiagram.colLen_eq_card]
        exact Finset.card_le_card (by
          intro cell hcell
          exact (YoungDiagram.mem_col_iff.mp hcell).1)
      omega
    have hsum := sum_rowLen_eq_card_of_height diagram (size + 1) hheight
    rw [hcard] at hsum
    simpa [rows] using hsum

@[simp] theorem BoundedPartition.conjugate_row
    {size : ℕ} (shape : BoundedPartition size size)
    (row : Fin (size + 1)) :
    ((shape.conjugate.1 row).val) = shape.youngDiagram.colLen row.val := by
  change shape.youngDiagram.transpose.rowLen row.val = _
  simp

theorem BoundedPartition.conjugate_youngDiagram
    {size : ℕ} (shape : BoundedPartition size size) :
    shape.conjugate.youngDiagram = shape.youngDiagram.transpose := by
  apply YoungDiagram.ext
  ext cell
  simp only [YoungDiagram.mem_cells]
  rw [shape.conjugate.mem_youngDiagram_iff]
  constructor
  · rintro ⟨row, hrow, hcolumn⟩
    rw [YoungDiagram.mem_transpose, Prod.swap_prod_mk,
      YoungDiagram.mem_iff_lt_colLen]
    rw [← hrow]
    simpa using hcolumn
  · intro hcell
    have horiginal : cell.swap ∈ shape.youngDiagram :=
      YoungDiagram.mem_transpose.mp hcell
    have hcolumn : cell.2 < shape.youngDiagram.colLen cell.1 := by
      simpa [Prod.swap] using
        (YoungDiagram.mem_iff_lt_colLen.mp horiginal)
    have hrow : cell.1 < size + 1 := by
      have hmemRow : cell.1 < shape.youngDiagram.rowLen cell.2 := by
        simpa [Prod.swap] using
          (YoungDiagram.mem_iff_lt_rowLen.mp horiginal)
      have hrowZero : shape.youngDiagram.rowLen cell.2 ≤
          shape.youngDiagram.rowLen 0 :=
        shape.youngDiagram.rowLen_anti 0 cell.2 (by omega)
      have hrowLe : shape.youngDiagram.rowLen 0 ≤
          shape.youngDiagram.card := by
        rw [YoungDiagram.rowLen_eq_card]
        exact Finset.card_le_card (by
          intro entry hentry
          exact (YoungDiagram.mem_row_iff.mp hentry).1)
      rw [shape.youngDiagram_card] at hrowLe
      omega
    exact ⟨⟨cell.1, hrow⟩, rfl, by simpa using hcolumn⟩

theorem YoungDiagram.hookLength_transpose_swap
    (diagram : YoungDiagram) (cell : ℕ × ℕ) :
    diagram.transpose.hookLength cell = diagram.hookLength cell.swap := by
  rw [YoungDiagram.hookLength_def, YoungDiagram.hookLength_def]
  simp [Prod.swap]
  omega

def diagramTransposeCellsEquiv (diagram : YoungDiagram) :
    diagram.transpose.cells ≃ diagram.cells where
  toFun := fun cell =>
    ⟨cell.1.swap, YoungDiagram.mem_transpose.mp cell.2⟩
  invFun := fun cell =>
    ⟨cell.1.swap, YoungDiagram.mem_transpose.mpr (by
      rw [Prod.swap_swap]
      exact cell.2)⟩
  left_inv := fun cell => by
    apply Subtype.ext
    exact Prod.swap_swap cell.1
  right_inv := fun cell => by
    apply Subtype.ext
    exact Prod.swap_swap cell.1

theorem BoundedPartition.conjugate_hookProduct
    {size : ℕ} (shape : BoundedPartition size size) :
    hookProduct shape.conjugate = hookProduct shape := by
  rw [hookProduct_eq_diagram_hookProduct, hookProduct_eq_diagram_hookProduct,
    shape.conjugate_youngDiagram]
  classical
  calc
    (∏ cell ∈ shape.youngDiagram.transpose.cells,
        shape.youngDiagram.transpose.hookLength cell) =
        ∏ cell : shape.youngDiagram.transpose.cells,
          shape.youngDiagram.transpose.hookLength cell.1 := by
      exact (Finset.prod_coe_sort _ _).symm
    _ = ∏ cell : shape.youngDiagram.cells,
          shape.youngDiagram.hookLength cell.1 := by
      exact Fintype.prod_equiv
        (diagramTransposeCellsEquiv shape.youngDiagram)
        (fun cell => shape.youngDiagram.transpose.hookLength cell.1)
        (fun cell => shape.youngDiagram.hookLength cell.1)
        (fun cell => FibonacciRibbonKernel.YoungDiagram.hookLength_transpose_swap
          shape.youngDiagram cell.1)
    _ = ∏ cell ∈ shape.youngDiagram.cells,
          shape.youngDiagram.hookLength cell := by
      exact Finset.prod_coe_sort _ _

/-- Conjugating the diagram preserves the literal standard-tableau number. -/
theorem BoundedPartition.standardTableauNumber_conjugate
    {size : ℕ} (shape : BoundedPartition size size) :
    standardTableauNumber shape.conjugate = standardTableauNumber shape := by
  have hleft := hookFormulaStatement shape.conjugate
  have hright := hookFormulaStatement shape
  change standardTableauNumber shape.conjugate * hookProduct shape.conjugate =
    size.factorial at hleft
  change standardTableauNumber shape * hookProduct shape = size.factorial at hright
  rw [shape.conjugate_hookProduct] at hleft
  have hpositive := hookProduct_pos shape
  exact Nat.eq_of_mul_eq_mul_right hpositive (hleft.trans hright.symm)

theorem BoundedPartition.eq_of_youngDiagram_eq
    {rank columns : ℕ} {left right : BoundedPartition rank columns}
    (hdiagram : left.youngDiagram = right.youngDiagram) : left = right := by
  apply Subtype.ext
  funext row
  apply Fin.ext
  rw [← left.youngDiagram_rowLen row, hdiagram,
    right.youngDiagram_rowLen row]

@[simp] theorem BoundedPartition.conjugate_conjugate
    {size : ℕ} (shape : BoundedPartition size size) :
    shape.conjugate.conjugate = shape := by
  apply BoundedPartition.eq_of_youngDiagram_eq
  rw [shape.conjugate.conjugate_youngDiagram,
    shape.conjugate_youngDiagram, YoungDiagram.transpose_transpose]

noncomputable def boundedPartitionConjugationEquiv (size : ℕ) :
    BoundedPartition size size ≃ BoundedPartition size size where
  toFun := BoundedPartition.conjugate
  invFun := BoundedPartition.conjugate
  left_inv := BoundedPartition.conjugate_conjugate
  right_inv := BoundedPartition.conjugate_conjugate

theorem BoundedPartition.conjugate_firstRow
    {size : ℕ} (shape : BoundedPartition size size) :
    shape.conjugate.firstRow = shape.youngDiagram.colLen 0 := by
  unfold BoundedPartition.firstRow
  exact shape.conjugate_row 0

/-! ## Changing the stored height without changing the diagram -/

noncomputable def diagramBoundedPartition
    (diagram : YoungDiagram) (rank columns : ℕ)
    (hcard : diagram.card = columns)
    (hheight : diagram.colLen 0 ≤ rank + 1) :
    BoundedPartition rank columns := by
  have hrowBound (row : Fin (rank + 1)) :
      diagram.rowLen row.val < columns + 1 := by
    have hsubset : diagram.row row.val ⊆ diagram.cells := by
      intro cell hcell
      exact (YoungDiagram.mem_row_iff.mp hcell).1
    have hle : diagram.rowLen row.val ≤ diagram.card := by
      rw [YoungDiagram.rowLen_eq_card]
      exact Finset.card_le_card hsubset
    omega
  let rows : Fin (rank + 1) → Fin (columns + 1) := fun row =>
    ⟨diagram.rowLen row.val, hrowBound row⟩
  refine ⟨rows, ?_, ?_⟩
  · intro row
    apply Fin.le_def.mpr
    exact diagram.rowLen_anti row.castSucc.val row.succ.val (by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega)
  · have hsum := sum_rowLen_eq_card_of_height diagram (rank + 1) hheight
    rw [hcard] at hsum
    simpa [rows] using hsum

@[simp] theorem diagramBoundedPartition_row
    (diagram : YoungDiagram) (rank columns : ℕ)
    (hcard : diagram.card = columns)
    (hheight : diagram.colLen 0 ≤ rank + 1)
    (row : Fin (rank + 1)) :
    ((diagramBoundedPartition diagram rank columns hcard hheight).1 row).val =
      diagram.rowLen row.val := by
  rfl

theorem diagramBoundedPartition_youngDiagram
    (diagram : YoungDiagram) (rank columns : ℕ)
    (hcard : diagram.card = columns)
    (hheight : diagram.colLen 0 ≤ rank + 1) :
    (diagramBoundedPartition diagram rank columns hcard hheight).youngDiagram =
      diagram := by
  apply YoungDiagram.ext
  ext cell
  simp only [YoungDiagram.mem_cells]
  rw [(diagramBoundedPartition diagram rank columns hcard hheight).mem_youngDiagram_iff]
  constructor
  · rintro ⟨row, hrow, hcolumn⟩
    have hcolumn' : cell.2 < diagram.rowLen cell.1 := by
      rw [← hrow]
      simpa only [diagramBoundedPartition_row] using hcolumn
    exact YoungDiagram.mem_iff_lt_rowLen.mpr hcolumn'
  · intro hcell
    have hrowCol : cell.1 < diagram.colLen cell.2 :=
      YoungDiagram.mem_iff_lt_colLen.mp hcell
    have hcol : diagram.colLen cell.2 ≤ diagram.colLen 0 :=
      diagram.colLen_anti 0 cell.2 (by omega)
    have hrow : cell.1 < rank + 1 := lt_of_lt_of_le hrowCol (hcol.trans hheight)
    exact ⟨⟨cell.1, hrow⟩, rfl, by
      rw [diagramBoundedPartition_row]
      exact YoungDiagram.mem_iff_lt_rowLen.mp hcell⟩

theorem BoundedPartition.youngDiagram_height
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    shape.youngDiagram.colLen 0 ≤ rank + 1 := by
  by_contra hnot
  have hrow : rank + 1 < shape.youngDiagram.colLen 0 := by omega
  have hmem : (rank + 1, 0) ∈ shape.youngDiagram :=
    YoungDiagram.mem_iff_lt_colLen.mpr hrow
  obtain ⟨row, hrowEq, hcolumn⟩ :=
    (shape.mem_youngDiagram_iff (rank + 1) 0).mp hmem
  omega

theorem YoungDiagram.colLen_zero_le_card (diagram : YoungDiagram) :
    diagram.colLen 0 ≤ diagram.card := by
  rw [YoungDiagram.colLen_eq_card]
  exact Finset.card_le_card (by
    intro cell hcell
    exact (YoungDiagram.mem_col_iff.mp hcell).1)

noncomputable def boundedPartitionFullHeightEquiv (rank columns : ℕ) :
    BoundedPartition rank columns ≃
      {shape : BoundedPartition columns columns //
        shape.youngDiagram.colLen 0 ≤ rank + 1} where
  toFun shape := by
    let full := diagramBoundedPartition shape.youngDiagram columns columns
      shape.youngDiagram_card
      (by
        have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
          shape.youngDiagram
        rw [shape.youngDiagram_card] at h
        omega)
    refine ⟨full, ?_⟩
    rw [diagramBoundedPartition_youngDiagram]
    exact shape.youngDiagram_height
  invFun shape :=
    diagramBoundedPartition shape.1.youngDiagram rank columns
      shape.1.youngDiagram_card shape.2
  left_inv shape := by
    apply BoundedPartition.eq_of_youngDiagram_eq
    rw [diagramBoundedPartition_youngDiagram,
      diagramBoundedPartition_youngDiagram]
  right_inv shape := by
    apply Subtype.ext
    apply BoundedPartition.eq_of_youngDiagram_eq
    rw [diagramBoundedPartition_youngDiagram,
      diagramBoundedPartition_youngDiagram]

theorem standardTableauNumber_eq_of_youngDiagram_eq
    {rankLeft rankRight columns : ℕ}
    (left : BoundedPartition rankLeft columns)
    (right : BoundedPartition rankRight columns)
    (hdiagram : left.youngDiagram = right.youngDiagram) :
    standardTableauNumber left = standardTableauNumber right := by
  have hleft := hookFormulaStatement left
  have hright := hookFormulaStatement right
  change standardTableauNumber left * hookProduct left = columns.factorial at hleft
  change standardTableauNumber right * hookProduct right = columns.factorial at hright
  have hhook : hookProduct left = hookProduct right := by
    rw [hookProduct_eq_diagram_hookProduct,
      hookProduct_eq_diagram_hookProduct, hdiagram]
  rw [hhook] at hleft
  exact Nat.eq_of_mul_eq_mul_right (hookProduct_pos right)
    (hleft.trans hright.symm)

theorem boundedPartitionFullHeightEquiv_preserves_number
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    standardTableauNumber (boundedPartitionFullHeightEquiv rank columns shape).1 =
      standardTableauNumber shape := by
  apply standardTableauNumber_eq_of_youngDiagram_eq
  simp [boundedPartitionFullHeightEquiv,
    diagramBoundedPartition_youngDiagram]

end FibonacciRibbonKernel
