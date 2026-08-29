import FibonacciRibbonKernel.HookLength
import KostkaNumbers.HookLength.HookLengthFormula

namespace FibonacciRibbonKernel

open scoped Classical
open YoungDiagram Kostka SemistandardYoungTableau

/-- The literal finite row-length list carried by a bounded partition. -/
def BoundedPartition.rowLengths
    {rank columns : ℕ} (shape : BoundedPartition rank columns) : List ℕ :=
  List.ofFn fun row : Fin (rank + 1) => (shape.1 row).val

theorem BoundedPartition.rowLengths_sorted
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    shape.rowLengths.SortedGE := by
  rw [BoundedPartition.rowLengths, List.sortedGE_ofFn_iff,
    Fin.antitone_iff_succ_le]
  intro row
  exact_mod_cast shape.2.1 row

/-- The Mathlib Young diagram with exactly the cells of the bounded partition. -/
def BoundedPartition.youngDiagram
    {rank columns : ℕ} (shape : BoundedPartition rank columns) : YoungDiagram :=
  YoungDiagram.ofRowLens shape.rowLengths shape.rowLengths_sorted

@[simp] theorem BoundedPartition.mem_youngDiagram_iff
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row column : ℕ) :
    (row, column) ∈ shape.youngDiagram ↔
      ∃ rowFin : Fin (rank + 1),
        rowFin.val = row ∧ column < (shape.1 rowFin).val := by
  rw [BoundedPartition.youngDiagram, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨hrow, hcolumn⟩
    let rowFin : Fin (rank + 1) :=
      ⟨row, by simpa [BoundedPartition.rowLengths] using hrow⟩
    refine ⟨rowFin, rfl, ?_⟩
    change column <
      (List.ofFn fun row : Fin (rank + 1) => (shape.1 row).val)[row] at hcolumn
    simpa only [List.getElem_ofFn, rowFin] using hcolumn
  · rintro ⟨rowFin, hrow, hcolumn⟩
    subst row
    refine ⟨by simpa [BoundedPartition.rowLengths] using rowFin.isLt, ?_⟩
    change column <
      (List.ofFn fun row : Fin (rank + 1) => (shape.1 row).val)[rowFin.val]
    simpa only [List.getElem_ofFn] using hcolumn

/-- Cell-by-cell identification of the manuscript carrier with Mathlib's diagram. -/
def youngCellEquivDiagramCell
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    YoungCell shape ≃ shape.youngDiagram.cells where
  toFun cell := ⟨(cell.1.val, cell.2.val), by
    rw [YoungDiagram.mem_cells, shape.mem_youngDiagram_iff]
    exact ⟨cell.1, rfl, cell.2.isLt⟩⟩
  invFun cell := by
    have hmem : cell.1 ∈ shape.youngDiagram := by
      exact cell.2
    have hrow : cell.1.1 < rank + 1 := by
      obtain ⟨rowFin, hrow, _⟩ :=
        (shape.mem_youngDiagram_iff _ _).mp hmem
      simpa [← hrow] using rowFin.isLt
    have hcolumn : cell.1.2 < (shape.1 ⟨cell.1.1, hrow⟩).val := by
      obtain ⟨rowFin, hrowEq, hcolumn⟩ :=
        (shape.mem_youngDiagram_iff _ _).mp hmem
      have hrowFin : rowFin = ⟨cell.1.1, hrow⟩ := Fin.ext hrowEq
      simpa [hrowFin] using hcolumn
    exact ⟨⟨cell.1.1, hrow⟩, ⟨cell.1.2, hcolumn⟩⟩
  left_inv cell := by
    apply Sigma.ext
    · exact Fin.ext rfl
    · exact heq_of_eq (Fin.ext rfl)
  right_inv cell := by
    apply Subtype.ext
    exact Prod.ext rfl rfl

theorem BoundedPartition.youngDiagram_card
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    shape.youngDiagram.card = columns := by
  calc
    shape.youngDiagram.card = Fintype.card shape.youngDiagram.cells := by
      simp
    _ = Fintype.card (YoungCell shape) :=
      Fintype.card_congr (youngCellEquivDiagramCell shape).symm
    _ = columns := youngCell_card shape

@[simp] theorem BoundedPartition.youngDiagram_rowLen
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) :
    shape.youngDiagram.rowLen row.val = (shape.1 row).val := by
  unfold BoundedPartition.youngDiagram
  rw [YoungDiagram.rowLen_ofRowLens' (hi := by
    simpa [BoundedPartition.rowLengths] using row.isLt)]
  simp only [BoundedPartition.rowLengths, List.getElem_ofFn]

theorem BoundedPartition.column_mem_iff
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) (column : ℕ) :
    column < (shape.1 row).val ↔
      row.val < shape.youngDiagram.colLen column := by
  rw [← YoungDiagram.mem_iff_lt_colLen]
  constructor
  · intro hcolumn
    exact (shape.mem_youngDiagram_iff _ _).mpr ⟨row, rfl, hcolumn⟩
  · intro hmem
    obtain ⟨rowFin, hrow, hcolumn⟩ :=
      (shape.mem_youngDiagram_iff _ _).mp hmem
    have : rowFin = row := Fin.ext hrow
    simpa [this] using hcolumn

/-- The literal below-cell filter is the open interval of occupied row indices. -/
theorem YoungCell.belowCount_eq_colLen_sub
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (cell : YoungCell shape) :
    cell.belowCount =
      shape.youngDiagram.colLen cell.2.val - cell.1.val - 1 := by
  classical
  let belowRows := Finset.univ.filter fun row : Fin (rank + 1) =>
    cell.1.val < row.val ∧ cell.2.val < (shape.1 row).val
  let rowEmbedding : Fin (rank + 1) ↪ ℕ := Fin.valEmbedding
  have hmap : Finset.map rowEmbedding belowRows =
      Finset.Ioo cell.1.val (shape.youngDiagram.colLen cell.2.val) := by
    ext row
    rw [Finset.mem_map, Finset.mem_Ioo]
    constructor
    · rintro ⟨rowFin, hbelow, rfl⟩
      have hpairs : cell.1.val < rowFin.val ∧
          cell.2.val < (shape.1 rowFin).val := by
        simpa [belowRows] using hbelow
      obtain ⟨hlower, hoccupied⟩ := hpairs
      exact ⟨hlower, (shape.column_mem_iff rowFin cell.2.val).mp hoccupied⟩
    · rintro ⟨hlower, hupper⟩
      have hmem : (row, cell.2.val) ∈ shape.youngDiagram :=
        (YoungDiagram.mem_iff_lt_colLen).mpr hupper
      have hrow : row < rank + 1 := by
        obtain ⟨rowFin, hrow, _⟩ :=
          (shape.mem_youngDiagram_iff _ _).mp hmem
        simpa [← hrow] using rowFin.isLt
      let rowFin : Fin (rank + 1) := ⟨row, hrow⟩
      have hoccupied : cell.2.val < (shape.1 rowFin).val :=
        (shape.column_mem_iff rowFin cell.2.val).mpr hupper
      refine ⟨rowFin, ?_, rfl⟩
      change rowFin ∈ Finset.univ.filter fun candidate : Fin (rank + 1) =>
        cell.1.val < candidate.val ∧
          cell.2.val < (shape.1 candidate).val
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ rowFin, ⟨hlower, hoccupied⟩⟩
  calc
    cell.belowCount = belowRows.card := by
      rfl
    _ = (Finset.map rowEmbedding belowRows).card :=
      (Finset.card_map rowEmbedding).symm
    _ = (Finset.Ioo cell.1.val
          (shape.youngDiagram.colLen cell.2.val)).card := by rw [hmap]
    _ = shape.youngDiagram.colLen cell.2.val - cell.1.val - 1 := by
      exact Nat.card_Ioo _ _

theorem youngCell_hookLength_eq_diagram_hookLength
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (cell : YoungCell shape) :
    cell.hookLength =
      shape.youngDiagram.hookLength (cell.1.val, cell.2.val) := by
  rw [YoungCell.hookLength, YoungCell.belowCount_eq_colLen_sub,
    YoungDiagram.hookLength_def, shape.youngDiagram_rowLen cell.1]
  change (shape.1 cell.1).val - cell.2.val +
      (shape.youngDiagram.colLen cell.2.val - cell.1.val - 1) =
    ((shape.1 cell.1).val - (cell.2.val + 1)) +
      (shape.youngDiagram.colLen cell.2.val - (cell.1.val + 1)) + 1
  have hcolumn := cell.2.isLt
  have hrow := (shape.column_mem_iff cell.1 cell.2.val).mp cell.2.isLt
  omega

theorem hookProduct_eq_diagram_hookProduct
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    hookProduct shape =
      ∏ cell ∈ shape.youngDiagram.cells,
        shape.youngDiagram.hookLength cell := by
  unfold hookProduct
  calc
    (∏ cell : YoungCell shape, cell.hookLength) =
        ∏ cell : shape.youngDiagram.cells,
          shape.youngDiagram.hookLength cell.1 := by
      apply Fintype.prod_equiv (youngCellEquivDiagramCell shape)
      intro cell
      exact youngCell_hookLength_eq_diagram_hookLength cell
    _ = ∏ cell ∈ shape.youngDiagram.cells,
          shape.youngDiagram.hookLength cell :=
      Finset.prod_coe_sort shape.youngDiagram.cells
        shape.youngDiagram.hookLength

/-- Ordinary row words of one fixed bounded-partition shape. -/
abbrev FixedShapeRowWord
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :=
  {tableau : StandardRowWordTableau rank columns //
    StandardRowWordTableau.shape tableau = shape}

theorem FixedShapeRowWord.count_eq_shape
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) (row : Fin (rank + 1)) :
    tableau.1.word.count row = (shape.1 row).val := by
  have hshape := congrArg
    (fun partition : BoundedPartition rank columns => (partition.1 row).val)
    tableau.2
  simpa [StandardRowWordTableau.shape] using hshape

def FixedShapeRowWord.positionRow
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) (position : Fin columns) :
    Fin (rank + 1) :=
  tableau.1.word[position.val]'(by
    rw [tableau.1.length_eq]
    exact position.isLt)

def FixedShapeRowWord.positionColumn
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) (position : Fin columns) : ℕ :=
  tableau.1.word.take position.val |>.count (tableau.positionRow position)

theorem FixedShapeRowWord.positionColumn_lt
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) (position : Fin columns) :
    tableau.positionColumn position <
      (shape.1 (tableau.positionRow position)).val := by
  let word := tableau.1.word
  have hposition : position.val < word.length := by
    rw [tableau.1.length_eq]
    exact position.isLt
  have hstep := List.take_concat_get' word position.val hposition
  have hprefix : word.take (position.val + 1) <+: word :=
    word.take_prefix (position.val + 1)
  obtain ⟨suffix, hsuffix⟩ :=
    List.prefix_iff_exists_append_eq.mp hprefix
  have hcount :
      (word.take position.val).count (tableau.positionRow position) + 1 ≤
        word.count (tableau.positionRow position) := by
    have hstepCount :
        (word.take position.val).count (tableau.positionRow position) + 1 =
          (word.take (position.val + 1)).count
            (tableau.positionRow position) := by
      change (word.take position.val).count word[position.val] + 1 =
        (word.take (position.val + 1)).count word[position.val]
      calc
        (word.take position.val).count word[position.val] + 1 =
            (word.take position.val ++ [word[position.val]]).count
              word[position.val] := by
          rw [List.count_append, List.count_singleton_self]
        _ = (word.take (position.val + 1)).count word[position.val] :=
          congrArg (List.count word[position.val]) hstep
    have hsuffixCount := congrArg
      (List.count (tableau.positionRow position)) hsuffix
    simp only [List.count_append] at hsuffixCount
    rw [hstepCount]
    omega
  rw [tableau.count_eq_shape] at hcount
  exact hcount

/-- The cell created by a given entry position in a standard row word. -/
def FixedShapeRowWord.positionCell
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) (position : Fin columns) :
    YoungCell shape :=
  ⟨tableau.positionRow position,
    ⟨tableau.positionColumn position, tableau.positionColumn_lt position⟩⟩

theorem FixedShapeRowWord.positionColumn_strictMono_of_sameRow
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) {left right : Fin columns}
    (hlt : left < right)
    (hrow : tableau.positionRow left = tableau.positionRow right) :
    tableau.positionColumn left < tableau.positionColumn right := by
  let word := tableau.1.word
  have hleft : left.val < word.length := by
    rw [tableau.1.length_eq]
    exact left.isLt
  have hstep := List.take_concat_get' word left.val hleft
  have hprefix : word.take (left.val + 1) <+: word.take right.val := by
    rw [List.take_isPrefix_take]
    exact Or.inl (Nat.succ_le_iff.mpr hlt)
  obtain ⟨suffix, hsuffix⟩ :=
    List.prefix_iff_exists_append_eq.mp hprefix
  have hstepCount :
      (word.take left.val).count (tableau.positionRow left) + 1 =
        (word.take (left.val + 1)).count (tableau.positionRow left) := by
    change (word.take left.val).count word[left.val] + 1 =
      (word.take (left.val + 1)).count word[left.val]
    calc
      (word.take left.val).count word[left.val] + 1 =
          (word.take left.val ++ [word[left.val]]).count word[left.val] := by
        rw [List.count_append, List.count_singleton_self]
      _ = (word.take (left.val + 1)).count word[left.val] :=
        congrArg (List.count word[left.val]) hstep
  have hsuffixCount := congrArg
    (List.count (tableau.positionRow left)) hsuffix
  simp only [List.count_append] at hsuffixCount
  rw [FixedShapeRowWord.positionColumn,
    FixedShapeRowWord.positionColumn, ← hrow]
  change (word.take left.val).count (tableau.positionRow left) <
    (word.take right.val).count (tableau.positionRow left)
  omega

theorem FixedShapeRowWord.positionCell_injective
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) :
    Function.Injective tableau.positionCell := by
  intro left right hcell
  apply Fin.ext
  have hrow : tableau.positionRow left = tableau.positionRow right :=
    congrArg Sigma.fst hcell
  have hcolumn : tableau.positionColumn left =
      tableau.positionColumn right := by
    have := congrArg (fun cell : YoungCell shape => cell.2.val) hcell
    exact this
  rcases lt_trichotomy left.val right.val with hlt | heq | hgt
  · have hltFin : left < right := hlt
    have := tableau.positionColumn_strictMono_of_sameRow hltFin hrow
    omega
  · exact heq
  · have hgtFin : right < left := hgt
    have := tableau.positionColumn_strictMono_of_sameRow hgtFin hrow.symm
    omega

/-- Every cell occurs at a unique position in a fixed-shape standard row word. -/
noncomputable def FixedShapeRowWord.positionCellEquiv
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) :
    Fin columns ≃ YoungCell shape :=
  Equiv.ofBijective tableau.positionCell
    ((Fintype.bijective_iff_injective_and_card tableau.positionCell).mpr
      ⟨tableau.positionCell_injective, by simp [youngCell_card shape]⟩)

theorem FixedShapeRowWord.count_take_succ_eq_positionColumn_add_one
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) (position : Fin columns) :
    (tableau.1.word.take (position.val + 1)).count
        (tableau.positionRow position) =
      tableau.positionColumn position + 1 := by
  let word := tableau.1.word
  have hposition : position.val < word.length := by
    rw [tableau.1.length_eq]
    exact position.isLt
  have hstep := List.take_concat_get' word position.val hposition
  change (word.take (position.val + 1)).count word[position.val] =
    (word.take position.val).count word[position.val] + 1
  calc
    (word.take (position.val + 1)).count word[position.val] =
        (word.take position.val ++ [word[position.val]]).count word[position.val] :=
      congrArg (List.count word[position.val]) hstep.symm
    _ = (word.take position.val).count word[position.val] + 1 := by
      rw [List.count_append, List.count_singleton_self]

theorem FixedShapeRowWord.prefixCount_antitone
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape)
    {initial : List (Fin (rank + 1))}
    (hprefix : initial <+: tableau.1.word) :
    Antitone fun row : Fin (rank + 1) => initial.count row := by
  rw [Fin.antitone_iff_succ_le]
  intro row
  have hdominant := tableau.1.ballot initial hprefix row
  rw [runPlusWord_eq_add_wordWeight] at hdominant
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, wordWeight_apply] at hdominant
  omega

theorem FixedShapeRowWord.inversePosition_lt_of_sameRow_column_lt
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) {left right : YoungCell shape}
    (hrow : left.1 = right.1) (hcolumn : left.2.val < right.2.val) :
    (tableau.positionCellEquiv.symm left).val <
      (tableau.positionCellEquiv.symm right).val := by
  let leftPosition := tableau.positionCellEquiv.symm left
  let rightPosition := tableau.positionCellEquiv.symm right
  have hleft := tableau.positionCellEquiv.apply_symm_apply left
  have hright := tableau.positionCellEquiv.apply_symm_apply right
  change tableau.positionCell leftPosition = left at hleft
  change tableau.positionCell rightPosition = right at hright
  have hleftRow : tableau.positionRow leftPosition = left.1 :=
    congrArg Sigma.fst hleft
  have hrightRow : tableau.positionRow rightPosition = right.1 :=
    congrArg Sigma.fst hright
  have hleftColumn : tableau.positionColumn leftPosition = left.2.val :=
    congrArg (fun cell : YoungCell shape => cell.2.val) hleft
  have hrightColumn : tableau.positionColumn rightPosition = right.2.val :=
    congrArg (fun cell : YoungCell shape => cell.2.val) hright
  rcases lt_trichotomy leftPosition.val rightPosition.val with hlt | heq | hgt
  · exact hlt
  · have hpositions : leftPosition = rightPosition := Fin.ext heq
    have hcells := congrArg tableau.positionCell hpositions
    rw [hleft, hright] at hcells
    have := congrArg (fun cell : YoungCell shape => cell.2.val) hcells
    omega
  · have hgtFin : rightPosition < leftPosition := hgt
    have hstrict := tableau.positionColumn_strictMono_of_sameRow
      hgtFin (hrightRow.trans (hrow.symm.trans hleftRow.symm))
    omega

theorem FixedShapeRowWord.inversePosition_lt_of_sameColumn_row_lt
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) {upper lower : YoungCell shape}
    (hrow : upper.1.val < lower.1.val)
    (hcolumn : upper.2.val = lower.2.val) :
    (tableau.positionCellEquiv.symm upper).val <
      (tableau.positionCellEquiv.symm lower).val := by
  let upperPosition := tableau.positionCellEquiv.symm upper
  let lowerPosition := tableau.positionCellEquiv.symm lower
  have hupper := tableau.positionCellEquiv.apply_symm_apply upper
  have hlower := tableau.positionCellEquiv.apply_symm_apply lower
  change tableau.positionCell upperPosition = upper at hupper
  change tableau.positionCell lowerPosition = lower at hlower
  have hupperRow : tableau.positionRow upperPosition = upper.1 :=
    congrArg Sigma.fst hupper
  have hlowerRow : tableau.positionRow lowerPosition = lower.1 :=
    congrArg Sigma.fst hlower
  have hupperColumn : tableau.positionColumn upperPosition = upper.2.val :=
    congrArg (fun cell : YoungCell shape => cell.2.val) hupper
  have hlowerColumn : tableau.positionColumn lowerPosition = lower.2.val :=
    congrArg (fun cell : YoungCell shape => cell.2.val) hlower
  by_contra hnot
  have hne : upperPosition ≠ lowerPosition := by
    intro heq
    have hcells := congrArg tableau.positionCell heq
    rw [hupper, hlower] at hcells
    have := congrArg (fun cell : YoungCell shape => cell.1.val) hcells
    omega
  have hlowerUpper : lowerPosition.val < upperPosition.val := by
    omega
  let initial := tableau.1.word.take (lowerPosition.val + 1)
  have hinitialPrefix : initial <+: tableau.1.word :=
    tableau.1.word.take_prefix (lowerPosition.val + 1)
  have hballot := tableau.prefixCount_antitone hinitialPrefix
    (show upper.1 ≤ lower.1 from Fin.mk_le_mk.mpr hrow.le)
  have hlowerCount := tableau.count_take_succ_eq_positionColumn_add_one
    lowerPosition
  have hprefixUpper : initial <+: tableau.1.word.take upperPosition.val := by
    rw [List.take_isPrefix_take]
    exact Or.inl (Nat.succ_le_iff.mpr hlowerUpper)
  obtain ⟨suffix, hsuffix⟩ :=
    List.prefix_iff_exists_append_eq.mp hprefixUpper
  have hsuffixCount := congrArg (List.count upper.1) hsuffix
  simp only [List.count_append] at hsuffixCount
  change initial.count lower.1 ≤ initial.count upper.1 at hballot
  change initial.count (tableau.positionRow lowerPosition) =
    tableau.positionColumn lowerPosition + 1 at hlowerCount
  rw [hlowerRow] at hlowerCount
  change initial.count upper.1 + suffix.count upper.1 =
    (tableau.1.word.take upperPosition.val).count upper.1 at hsuffixCount
  rw [hlowerColumn] at hlowerCount
  have hupperBefore :
      (tableau.1.word.take upperPosition.val).count upper.1 =
        upper.2.val := by
    calc
      (tableau.1.word.take upperPosition.val).count upper.1 =
          (tableau.1.word.take upperPosition.val).count
            (tableau.positionRow upperPosition) := by rw [hupperRow]
      _ = tableau.positionColumn upperPosition := rfl
      _ = upper.2.val := hupperColumn
  omega

noncomputable def FixedShapeRowWord.positionDiagramCellEquiv
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) :
    Fin columns ≃ shape.youngDiagram.cells :=
  tableau.positionCellEquiv.trans (youngCellEquivDiagramCell shape)

/-- The usual standard filling obtained by placing each entry in its row-word cell. -/
noncomputable def FixedShapeRowWord.toSemistandardYoungTableau
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) :
    SemistandardYoungTableau shape.youngDiagram where
  entry row column :=
    if hcell : (row, column) ∈ shape.youngDiagram then
      (tableau.positionDiagramCellEquiv.symm
        ⟨(row, column), by exact hcell⟩).val
    else 0
  row_weak' := by
    intro row leftColumn rightColumn hcolumn hright
    have hleft : (row, leftColumn) ∈ shape.youngDiagram :=
      shape.youngDiagram.up_left_mem (by rfl) hcolumn.le hright
    let leftCell : YoungCell shape :=
      (youngCellEquivDiagramCell shape).symm ⟨(row, leftColumn), hleft⟩
    let rightCell : YoungCell shape :=
      (youngCellEquivDiagramCell shape).symm ⟨(row, rightColumn), hright⟩
    have hrow : leftCell.1 = rightCell.1 := Fin.ext rfl
    have hcolumns : leftCell.2.val < rightCell.2.val := hcolumn
    have hpositions := tableau.inversePosition_lt_of_sameRow_column_lt
      hrow hcolumns
    simpa [FixedShapeRowWord.positionDiagramCellEquiv, leftCell, rightCell,
      hleft, hright] using hpositions.le
  col_strict' := by
    intro upperRow lowerRow column hrow hlower
    have hupper : (upperRow, column) ∈ shape.youngDiagram :=
      shape.youngDiagram.up_left_mem hrow.le (by rfl) hlower
    let upperCell : YoungCell shape :=
      (youngCellEquivDiagramCell shape).symm ⟨(upperRow, column), hupper⟩
    let lowerCell : YoungCell shape :=
      (youngCellEquivDiagramCell shape).symm ⟨(lowerRow, column), hlower⟩
    have hrows : upperCell.1.val < lowerCell.1.val := hrow
    have hcolumns : upperCell.2.val = lowerCell.2.val := rfl
    have hpositions := tableau.inversePosition_lt_of_sameColumn_row_lt
      hrows hcolumns
    simpa [FixedShapeRowWord.positionDiagramCellEquiv, upperCell, lowerCell,
      hupper, hlower] using hpositions
  zeros' := by
    intro row column hcell
    simp [hcell]

@[simp] theorem FixedShapeRowWord.toSemistandardYoungTableau_apply_of_mem
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) {row column : ℕ}
    (hcell : (row, column) ∈ shape.youngDiagram) :
    tableau.toSemistandardYoungTableau row column =
      (tableau.positionCellEquiv.symm
        ((youngCellEquivDiagramCell shape).symm
          ⟨(row, column), hcell⟩)).val := by
  unfold FixedShapeRowWord.toSemistandardYoungTableau
  change (if h : (row, column) ∈ shape.youngDiagram then
      (tableau.positionDiagramCellEquiv.symm
        ⟨(row, column), h⟩).val else 0) = _
  rw [dif_pos hcell]
  rfl

theorem multiset_map_finset_val_eq_map_univ_subtype
    {α β : Type*} [DecidableEq α] (set : Finset α) (function : α → β) :
    set.val.map function =
      (Finset.univ : Finset set).val.map
        (fun element : set => function element.val) := by
  let toOccurrence : set → set.val := fun element =>
    ⟨element.val, ⟨0, by
      have hcount := (Multiset.nodup_iff_count_eq_one.mp set.nodup)
        element.val element.2
      omega⟩⟩
  have toOccurrence_injective : Function.Injective toOccurrence := by
    intro left right heq
    apply Subtype.ext
    exact congrArg Sigma.fst heq
  let membershipEquiv : set ≃ set.val :=
    Equiv.ofBijective toOccurrence
      ((Fintype.bijective_iff_injective_and_card toOccurrence).mpr
        ⟨toOccurrence_injective, by simp⟩)
  calc
    set.val.map function =
        (Finset.univ : Finset set.val).val.map
          (fun element : set.val => function element.1) := by
      rw [Multiset.map_univ]
    _ = ((Finset.univ : Finset set).val.map membershipEquiv).map
          (fun element : set.val => function element.1) := by
      rw [Multiset.map_univ_val_equiv membershipEquiv]
    _ = (Finset.univ : Finset set).val.map
          (fun element : set => function element.val) := by
      rw [Multiset.map_map]
      rfl

theorem fin_univ_val_map_val_eq_range (size : ℕ) :
    (Finset.univ : Finset (Fin size)).val.map Fin.val =
      Multiset.range size := by
  have h := congrArg Finset.val (Fin.map_valEmbedding_univ (n := size))
  rw [Finset.map_val, Nat.Iio_eq_range, Finset.range_val] at h
  exact h

theorem fromCounts_replicate_one_eq_range (size : ℕ) :
    (Multiset.replicate size 1).fromCounts = Multiset.range size := by
  have hsort : (Multiset.replicate size 1).sort (· ≥ ·) =
      List.replicate size 1 := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp
    · intro value hmember
      exact Multiset.eq_of_mem_replicate
        (by simpa only [Multiset.mem_sort] using hmember)
  ext value
  by_cases hvalue : value < size
  · have hcard : value < (Multiset.replicate size 1).card := by
      simpa using hvalue
    calc
      Multiset.count value (Multiset.replicate size 1).fromCounts =
          ((Multiset.replicate size 1).sort (· ≥ ·))[value]'(by simpa using hcard) :=
        Multiset.count_fromCounts hcard
      _ = 1 := by simp only [hsort, List.getElem_replicate]
      _ = Multiset.count value (Multiset.range size) := by
        simp [Multiset.range, List.count_range, hvalue]
  · have hge : value ≥ (Multiset.replicate size 1).card := by
      simpa using Nat.le_of_not_gt hvalue
    have hnot := Multiset.notMem_fromCounts
      (Multiset.replicate size 1) value hge
    rw [Multiset.count_eq_zero.mpr hnot]
    simp [Multiset.range, hvalue]

theorem FixedShapeRowWord.toSemistandardYoungTableau_content
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) :
    tableau.toSemistandardYoungTableau.content =
      (Multiset.replicate columns 1).fromCounts := by
  let cellEquiv := tableau.positionDiagramCellEquiv
  calc
    tableau.toSemistandardYoungTableau.content =
        shape.youngDiagram.cells.val.map
          (fun cell => tableau.toSemistandardYoungTableau cell.1 cell.2) := by
      rfl
    _ = (Finset.univ : Finset shape.youngDiagram.cells).val.map
          (fun cell => tableau.toSemistandardYoungTableau
            cell.val.1 cell.val.2) :=
      multiset_map_finset_val_eq_map_univ_subtype _ _
    _ = (Finset.univ : Finset shape.youngDiagram.cells).val.map
          (fun cell => (cellEquiv.symm cell).val) := by
      apply Multiset.map_congr rfl
      intro cell hcell
      exact tableau.toSemistandardYoungTableau_apply_of_mem cell.2
    _ = ((Finset.univ : Finset shape.youngDiagram.cells).val.map
          cellEquiv.symm).map Fin.val := by
      rw [Multiset.map_map]
      rfl
    _ = (Finset.univ : Finset (Fin columns)).val.map Fin.val := by
      rw [Multiset.map_univ_val_equiv cellEquiv.symm]
    _ = Multiset.range columns := fin_univ_val_map_val_eq_range columns
    _ = (Multiset.replicate columns 1).fromCounts :=
      (fromCounts_replicate_one_eq_range columns).symm

abbrev DistinctContentSSYT
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :=
  {tableau : SemistandardYoungTableau shape.youngDiagram //
    tableau.content = (Multiset.replicate columns 1).fromCounts}

noncomputable instance distinctContentSSYTFintype
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    Fintype (DistinctContentSSYT shape) := by
  let externalType :=
    ↥(SemistandardYoungTableauWithContent shape.youngDiagram
      (Multiset.replicate columns 1))
  let equivalence : externalType ≃ DistinctContentSSYT shape :=
    { toFun := fun tableau => ⟨tableau.1, tableau.2⟩
      invFun := fun tableau => ⟨tableau.1, tableau.2⟩
      left_inv := fun tableau => by apply Subtype.ext; rfl
      right_inv := fun tableau => by apply Subtype.ext; rfl }
  exact Fintype.ofEquiv externalType equivalence

noncomputable def DistinctContentSSYT.entryPosition
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape)
    (cell : shape.youngDiagram.cells) : Fin columns :=
  ⟨tableau.1 cell.val.1 cell.val.2, by
    have hlt := SemistandardYoungTableau.entry_lt_card tableau.2 cell.2
    simpa using hlt⟩

theorem DistinctContentSSYT.content_nodup
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) :
    tableau.1.content.Nodup := by
  rw [tableau.2, fromCounts_replicate_one_eq_range]
  exact Multiset.nodup_range columns

theorem DistinctContentSSYT.entryPosition_injective
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) :
    Function.Injective tableau.entryPosition := by
  intro left right heq
  apply Subtype.ext
  have hentries : tableau.1 left.val.1 left.val.2 =
      tableau.1 right.val.1 right.val.2 := congrArg Fin.val heq
  have hnodup :
      (shape.youngDiagram.cells.val.map
        (fun cell => tableau.1 cell.1 cell.2)).Nodup := by
    exact tableau.content_nodup
  exact Multiset.inj_on_of_nodup_map hnodup left.val left.2
    right.val right.2 hentries

noncomputable def DistinctContentSSYT.entryCellEquiv
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) :
    shape.youngDiagram.cells ≃ Fin columns :=
  Equiv.ofBijective tableau.entryPosition
    ((Fintype.bijective_iff_injective_and_card tableau.entryPosition).mpr
      ⟨tableau.entryPosition_injective, by
        rw [Fintype.card_fin]
        simpa using shape.youngDiagram_card⟩)

noncomputable def DistinctContentSSYT.recoveredRow
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (position : Fin columns) :
    Fin (rank + 1) :=
  ((youngCellEquivDiagramCell shape).symm
    (tableau.entryCellEquiv.symm position)).1

noncomputable def DistinctContentSSYT.recoveredWord
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) : List (Fin (rank + 1)) :=
  List.ofFn tableau.recoveredRow

@[simp] theorem DistinctContentSSYT.recoveredWord_length
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) :
    tableau.recoveredWord.length = columns := by
  simp [DistinctContentSSYT.recoveredWord]

theorem count_take_ofFn_eq_card_positions
    {α : Type*} [DecidableEq α] {size prefixLength : ℕ}
    (function : Fin size → α) (hpref : prefixLength ≤ size) (value : α) :
    (List.ofFn function |>.take prefixLength).count value =
      Fintype.card {position : Fin prefixLength //
        function (Fin.castLE hpref position) = value} := by
  let vector : List.Vector α prefixLength :=
    List.Vector.ofFn (Fin.take prefixLength hpref function)
  have hvectorList : vector.toList =
      (List.ofFn function).take prefixLength := by
    simpa [vector, List.Vector.toList_ofFn] using
      (Fin.ofFn_take_eq_take_ofFn hpref function)
  rw [← hvectorList]
  rw [Fintype.card_subtype]
  rw [← Fin.card_filter_univ_eq_vector_get_eq_count value vector]
  congr 1
  ext position
  simp [vector, Fin.take_apply]

noncomputable def DistinctContentSSYT.recoveredYoungCell
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (position : Fin columns) :
    YoungCell shape :=
  (youngCellEquivDiagramCell shape).symm
    (tableau.entryCellEquiv.symm position)

@[simp] theorem DistinctContentSSYT.recoveredYoungCell_row
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (position : Fin columns) :
    (tableau.recoveredYoungCell position).1 = tableau.recoveredRow position := by
  rfl

noncomputable def DistinctContentSSYT.upperCellForRecovered
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (row : Fin rank)
    (position : Fin columns)
    (hrow : tableau.recoveredRow position = row.succ) : YoungCell shape :=
  ⟨row.castSucc, ⟨(tableau.recoveredYoungCell position).2.val, by
    have hlower : (tableau.recoveredYoungCell position).2.val <
        (shape.1 row.succ).val := by
      have hactual := (tableau.recoveredYoungCell position).2.isLt
      have hcellRow : (tableau.recoveredYoungCell position).1 = row.succ :=
        tableau.recoveredYoungCell_row position |>.trans hrow
      have hshapeLength := congrArg
        (fun actualRow : Fin (rank + 1) => (shape.1 actualRow).val) hcellRow
      omega
    have hpartition := shape.2.1 row
    omega⟩⟩

noncomputable def DistinctContentSSYT.upperPositionForRecovered
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (row : Fin rank)
    (position : Fin columns)
    (hrow : tableau.recoveredRow position = row.succ) : Fin columns :=
  tableau.entryCellEquiv
    (youngCellEquivDiagramCell shape
      (tableau.upperCellForRecovered row position hrow))

theorem DistinctContentSSYT.upperPositionForRecovered_lt
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (row : Fin rank)
    (position : Fin columns)
    (hrow : tableau.recoveredRow position = row.succ) :
    (tableau.upperPositionForRecovered row position hrow).val < position.val := by
  let lowerCell := tableau.recoveredYoungCell position
  let upperCell := tableau.upperCellForRecovered row position hrow
  let lowerDiagramCell := tableau.entryCellEquiv.symm position
  let upperDiagramCell := youngCellEquivDiagramCell shape upperCell
  have hlowerDiagram : youngCellEquivDiagramCell shape lowerCell =
      lowerDiagramCell := by
    exact (youngCellEquivDiagramCell shape).apply_symm_apply lowerDiagramCell
  have hlowerPosition := tableau.entryCellEquiv.apply_symm_apply position
  have hrowValues : upperCell.1.val < lowerCell.1.val := by
    have hlowerRow : lowerCell.1 = row.succ := by
      exact tableau.recoveredYoungCell_row position |>.trans hrow
    change row.castSucc.val < lowerCell.1.val
    rw [hlowerRow]
    simp
  have hcolumnValues : upperCell.2.val = lowerCell.2.val := rfl
  have hentry := tableau.1.col_strict hrowValues
    (show (lowerCell.1.val, lowerCell.2.val) ∈ shape.youngDiagram by
      exact (youngCellEquivDiagramCell shape lowerCell).2)
  have hupperEntry :
      (tableau.upperPositionForRecovered row position hrow).val =
        tableau.1 upperCell.1.val upperCell.2.val := by
    rfl
  have hlowerEntry : position.val =
      tableau.1 lowerCell.1.val lowerCell.2.val := by
    have hvalue := congrArg Fin.val hlowerPosition
    change tableau.1 lowerDiagramCell.val.1 lowerDiagramCell.val.2 =
      position.val at hvalue
    rw [← hlowerDiagram] at hvalue
    exact hvalue.symm
  rw [hupperEntry, hlowerEntry]
  simpa [hcolumnValues] using hentry

abbrev RecoveredRowPosition
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (prefixLength : ℕ)
    (hpref : prefixLength ≤ columns) (row : Fin (rank + 1)) :=
  {position : Fin prefixLength //
    tableau.recoveredRow (Fin.castLE hpref position) = row}

theorem DistinctContentSSYT.recoveredRowPosition_succ_card_le
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (prefixLength : ℕ)
    (hpref : prefixLength ≤ columns) (row : Fin rank) :
    Fintype.card (RecoveredRowPosition tableau prefixLength hpref row.succ) ≤
      Fintype.card
        (RecoveredRowPosition tableau prefixLength hpref row.castSucc) := by
  let liftPosition :
      RecoveredRowPosition tableau prefixLength hpref row.succ →
        RecoveredRowPosition tableau prefixLength hpref row.castSucc :=
    fun lower => by
      let lowerGlobal : Fin columns := Fin.castLE hpref lower.1
      have hlowerRow : tableau.recoveredRow lowerGlobal = row.succ := lower.2
      let upperGlobal := tableau.upperPositionForRecovered row lowerGlobal hlowerRow
      have hupperLower :=
        tableau.upperPositionForRecovered_lt row lowerGlobal hlowerRow
      let upperPrefix : Fin prefixLength :=
        ⟨upperGlobal.val, by
          have hlowerPrefix := lower.1.isLt
          change lowerGlobal.val < prefixLength at hlowerPrefix
          omega⟩
      refine ⟨upperPrefix, ?_⟩
      change tableau.recoveredRow upperGlobal = row.castSucc
      simp [DistinctContentSSYT.recoveredRow,
        DistinctContentSSYT.recoveredYoungCell,
        DistinctContentSSYT.upperPositionForRecovered,
        DistinctContentSSYT.upperCellForRecovered, upperGlobal]
  apply Fintype.card_le_of_injective liftPosition
  intro left right heq
  apply Subtype.ext
  let leftGlobal : Fin columns := Fin.castLE hpref left.1
  let rightGlobal : Fin columns := Fin.castLE hpref right.1
  have hleftRow : tableau.recoveredRow leftGlobal = row.succ := left.2
  have hrightRow : tableau.recoveredRow rightGlobal = row.succ := right.2
  let leftUpper := tableau.upperCellForRecovered row leftGlobal hleftRow
  let rightUpper := tableau.upperCellForRecovered row rightGlobal hrightRow
  have hupperPositions :
      tableau.upperPositionForRecovered row leftGlobal hleftRow =
        tableau.upperPositionForRecovered row rightGlobal hrightRow := by
    apply Fin.ext
    exact congrArg (fun position => position.1.val) heq
  have hupperDiagram :
      youngCellEquivDiagramCell shape leftUpper =
        youngCellEquivDiagramCell shape rightUpper := by
    apply tableau.entryCellEquiv.injective
    exact hupperPositions
  have hupperCells : leftUpper = rightUpper :=
    (youngCellEquivDiagramCell shape).injective hupperDiagram
  have hcolumns : (tableau.recoveredYoungCell leftGlobal).2.val =
      (tableau.recoveredYoungCell rightGlobal).2.val := by
    have hupperColumns :=
      congrArg (fun cell : YoungCell shape => cell.2.val) hupperCells
    change (tableau.recoveredYoungCell leftGlobal).2.val =
      (tableau.recoveredYoungCell rightGlobal).2.val at hupperColumns
    exact hupperColumns
  have hlowerCells : tableau.recoveredYoungCell leftGlobal =
      tableau.recoveredYoungCell rightGlobal := by
    have hrows : (tableau.recoveredYoungCell leftGlobal).1 =
        (tableau.recoveredYoungCell rightGlobal).1 :=
      hleftRow.trans hrightRow.symm
    refine Sigma.ext hrows ?_
    apply (Fin.heq_ext_iff (by rw [hrows])).mpr
    exact hcolumns
  have hlowerDiagram := congrArg (youngCellEquivDiagramCell shape) hlowerCells
  have hinverseCells : tableau.entryCellEquiv.symm leftGlobal =
      tableau.entryCellEquiv.symm rightGlobal := by
    simpa [DistinctContentSSYT.recoveredYoungCell] using hlowerDiagram
  have hglobal : leftGlobal = rightGlobal := by
    exact tableau.entryCellEquiv.symm.injective hinverseCells
  apply Fin.ext
  exact congrArg (fun position : Fin columns => position.val) hglobal

noncomputable def DistinctContentSSYT.toStandardRowWordTableau
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) :
    StandardRowWordTableau rank columns where
  word := tableau.recoveredWord
  length_eq := tableau.recoveredWord_length
  ballot := by
    intro initial hprefix
    have hprefLength : initial.length ≤ columns := by
      have hle := hprefix.length_le
      rw [tableau.recoveredWord_length] at hle
      exact hle
    have hinitial := List.prefix_iff_eq_take.mp hprefix
    rw [runPlusWord_eq_add_wordWeight]
    intro row
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, wordWeight_apply]
    rw [hinitial]
    have hlower := count_take_ofFn_eq_card_positions
      tableau.recoveredRow hprefLength row.succ
    have hupper := count_take_ofFn_eq_card_positions
      tableau.recoveredRow hprefLength row.castSucc
    have hcard := tableau.recoveredRowPosition_succ_card_le
      initial.length hprefLength row
    change (tableau.recoveredWord.take initial.length).count row.succ =
      Fintype.card
        (RecoveredRowPosition tableau initial.length hprefLength row.succ) at hlower
    change (tableau.recoveredWord.take initial.length).count row.castSucc =
      Fintype.card
        (RecoveredRowPosition tableau initial.length hprefLength row.castSucc) at hupper
    omega

noncomputable def DistinctContentSSYT.recoveredPositionCellEquiv
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (row : Fin (rank + 1)) :
    {position : Fin columns // tableau.recoveredRow position = row} ≃
      {cell : YoungCell shape // cell.1 = row} where
  toFun position :=
    ⟨tableau.recoveredYoungCell position.1,
      tableau.recoveredYoungCell_row position.1 |>.trans position.2⟩
  invFun cell := by
    let diagramCell := youngCellEquivDiagramCell shape cell.1
    let position := tableau.entryCellEquiv diagramCell
    refine ⟨position, ?_⟩
    change (tableau.recoveredYoungCell position).1 = row
    have hposition : tableau.entryCellEquiv.symm position = diagramCell :=
      tableau.entryCellEquiv.symm_apply_apply diagramCell
    have hcell : tableau.recoveredYoungCell position = cell.1 := by
      change (youngCellEquivDiagramCell shape).symm
          (tableau.entryCellEquiv.symm position) = cell.1
      rw [hposition]
      exact (youngCellEquivDiagramCell shape).symm_apply_apply cell.1
    rw [hcell]
    exact cell.2
  left_inv position := by
    apply Subtype.ext
    change tableau.entryCellEquiv
        (youngCellEquivDiagramCell shape
          (tableau.recoveredYoungCell position.1)) = position.1
    rw [show youngCellEquivDiagramCell shape
        (tableau.recoveredYoungCell position.1) =
          tableau.entryCellEquiv.symm position.1 by
      exact (youngCellEquivDiagramCell shape).apply_symm_apply _]
    exact tableau.entryCellEquiv.apply_symm_apply position.1
  right_inv cell := by
    apply Subtype.ext
    change (youngCellEquivDiagramCell shape).symm
        (tableau.entryCellEquiv.symm
          (tableau.entryCellEquiv (youngCellEquivDiagramCell shape cell.1))) = cell.1
    rw [tableau.entryCellEquiv.symm_apply_apply]
    exact (youngCellEquivDiagramCell shape).symm_apply_apply cell.1

noncomputable def fixedRowYoungCellEquiv
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) :
    {cell : YoungCell shape // cell.1 = row} ≃ Fin (shape.1 row).val where
  toFun cell :=
    Fin.cast (congrArg (fun actualRow : Fin (rank + 1) => (shape.1 actualRow).val)
      cell.2) cell.1.2
  invFun column := ⟨⟨row, column⟩, rfl⟩
  left_inv cell := by
    apply Subtype.ext
    apply Sigma.ext
    · exact cell.2.symm
    · apply (Fin.heq_ext_iff (by rw [cell.2])).mpr
      rfl
  right_inv column := by
    apply Fin.ext
    rfl

theorem DistinctContentSSYT.recoveredFullRowPosition_card
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (row : Fin (rank + 1)) :
    Fintype.card {position : Fin columns // tableau.recoveredRow position = row} =
      (shape.1 row).val := by
  calc
    Fintype.card {position : Fin columns // tableau.recoveredRow position = row} =
        Fintype.card {cell : YoungCell shape // cell.1 = row} :=
      Fintype.card_congr (tableau.recoveredPositionCellEquiv row)
    _ = Fintype.card (Fin (shape.1 row).val) :=
      Fintype.card_congr (fixedRowYoungCellEquiv shape row)
    _ = (shape.1 row).val := Fintype.card_fin _

theorem DistinctContentSSYT.toStandardRowWordTableau_shape
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) :
    StandardRowWordTableau.shape tableau.toStandardRowWordTableau = shape := by
  apply Subtype.ext
  funext row
  apply Fin.ext
  change tableau.recoveredWord.count row = (shape.1 row).val
  have hcount := count_take_ofFn_eq_card_positions
    tableau.recoveredRow (show columns ≤ columns from le_rfl) row
  have htake : tableau.recoveredWord.take columns = tableau.recoveredWord :=
    (List.take_eq_self_iff tableau.recoveredWord).mpr
      (by rw [tableau.recoveredWord_length])
  change (tableau.recoveredWord.take columns).count row =
    Fintype.card {position : Fin columns //
      tableau.recoveredRow (Fin.castLE le_rfl position) = row} at hcount
  rw [htake] at hcount
  have hcard := tableau.recoveredFullRowPosition_card row
  simpa using hcount.trans hcard

noncomputable def DistinctContentSSYT.toFixedShapeRowWord
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) : FixedShapeRowWord shape :=
  ⟨tableau.toStandardRowWordTableau,
    tableau.toStandardRowWordTableau_shape⟩

theorem DistinctContentSSYT.entryPositionYoungCell_lt_of_sameRow_column_lt
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) {left right : YoungCell shape}
    (hrow : left.1 = right.1) (hcolumn : left.2.val < right.2.val) :
    (tableau.entryCellEquiv (youngCellEquivDiagramCell shape left)).val <
      (tableau.entryCellEquiv (youngCellEquivDiagramCell shape right)).val := by
  let leftDiagram := youngCellEquivDiagramCell shape left
  let rightDiagram := youngCellEquivDiagramCell shape right
  have hweak := tableau.1.row_weak hcolumn rightDiagram.2
  have hrowValue : left.1.val = right.1.val := congrArg Fin.val hrow
  have hne : tableau.entryCellEquiv leftDiagram ≠
      tableau.entryCellEquiv rightDiagram := by
    intro heq
    have hdiagram := tableau.entryCellEquiv.injective heq
    have hcells := (youngCellEquivDiagramCell shape).injective hdiagram
    have := congrArg (fun cell : YoungCell shape => cell.2.val) hcells
    omega
  change tableau.1 left.1.val left.2.val <
    tableau.1 right.1.val right.2.val
  have hvalues : tableau.1 left.1.val left.2.val ≠
      tableau.1 right.1.val right.2.val := by
    intro heq
    apply hne
    apply Fin.ext
    exact heq
  have hleftRewrite : tableau.1 left.1.val left.2.val =
      tableau.1 right.1.val left.2.val := by rw [hrowValue]
  omega

@[simp] theorem DistinctContentSSYT.entryCellEquiv_recoveredYoungCell
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (position : Fin columns) :
    tableau.entryCellEquiv
        (youngCellEquivDiagramCell shape
          (tableau.recoveredYoungCell position)) = position := by
  change tableau.entryCellEquiv
      (youngCellEquivDiagramCell shape
        ((youngCellEquivDiagramCell shape).symm
          (tableau.entryCellEquiv.symm position))) = position
  rw [(youngCellEquivDiagramCell shape).apply_symm_apply,
    tableau.entryCellEquiv.apply_symm_apply]

@[simp] theorem DistinctContentSSYT.recoveredYoungCell_entryCellEquiv
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (cell : YoungCell shape) :
    tableau.recoveredYoungCell
        (tableau.entryCellEquiv (youngCellEquivDiagramCell shape cell)) = cell := by
  change (youngCellEquivDiagramCell shape).symm
      (tableau.entryCellEquiv.symm
        (tableau.entryCellEquiv (youngCellEquivDiagramCell shape cell))) = cell
  rw [tableau.entryCellEquiv.symm_apply_apply,
    (youngCellEquivDiagramCell shape).symm_apply_apply]

theorem DistinctContentSSYT.earlierSameRowPosition_card
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (position : Fin columns) :
    Fintype.card
        (RecoveredRowPosition tableau position.val position.isLt.le
          (tableau.recoveredYoungCell position).1) =
      (tableau.recoveredYoungCell position).2.val := by
  let targetCell := tableau.recoveredYoungCell position
  let hpref : position.val ≤ columns := position.isLt.le
  let earlierPositions := RecoveredRowPosition tableau position.val hpref targetCell.1
  let positionToColumn : earlierPositions → Fin targetCell.2.val := fun earlier => by
    let earlierGlobal : Fin columns := Fin.castLE hpref earlier.1
    let earlierCell := tableau.recoveredYoungCell earlierGlobal
    have hrow : earlierCell.1 = targetCell.1 := earlier.2
    have hearlier : earlierGlobal.val < position.val := by
      exact earlier.1.isLt
    have hcolumn : earlierCell.2.val < targetCell.2.val := by
      rcases lt_trichotomy earlierCell.2.val targetCell.2.val with hlt | heq | hgt
      · exact hlt
      · have hcells : earlierCell = targetCell := by
          refine Sigma.ext hrow ?_
          apply (Fin.heq_ext_iff (by rw [hrow])).mpr
          exact heq
        have hpositions := congrArg
          (fun cell : YoungCell shape =>
            tableau.entryCellEquiv (youngCellEquivDiagramCell shape cell)) hcells
        have hpositions' : earlierGlobal = position := by
          calc
            earlierGlobal = tableau.entryCellEquiv
                (youngCellEquivDiagramCell shape earlierCell) :=
              (tableau.entryCellEquiv_recoveredYoungCell earlierGlobal).symm
            _ = tableau.entryCellEquiv
                (youngCellEquivDiagramCell shape targetCell) := hpositions
            _ = position := tableau.entryCellEquiv_recoveredYoungCell position
        omega
      · have hpositionOrder := tableau.entryPositionYoungCell_lt_of_sameRow_column_lt
          hrow.symm hgt
        have hearlierBack := congrArg Fin.val
          (tableau.entryCellEquiv_recoveredYoungCell earlierGlobal)
        have htargetBack := congrArg Fin.val
          (tableau.entryCellEquiv_recoveredYoungCell position)
        change (tableau.entryCellEquiv
            (youngCellEquivDiagramCell shape earlierCell)).val =
          earlierGlobal.val at hearlierBack
        change (tableau.entryCellEquiv
            (youngCellEquivDiagramCell shape targetCell)).val =
          position.val at htargetBack
        omega
    exact ⟨earlierCell.2.val, hcolumn⟩
  have positionToColumn_injective : Function.Injective positionToColumn := by
    intro left right heq
    apply Subtype.ext
    let leftGlobal : Fin columns := Fin.castLE hpref left.1
    let rightGlobal : Fin columns := Fin.castLE hpref right.1
    let leftCell := tableau.recoveredYoungCell leftGlobal
    let rightCell := tableau.recoveredYoungCell rightGlobal
    have hleftRow : leftCell.1 = targetCell.1 := left.2
    have hrightRow : rightCell.1 = targetCell.1 := right.2
    have hcolumns : leftCell.2.val = rightCell.2.val :=
      congrArg Fin.val heq
    have hcells : leftCell = rightCell := by
      have hrows : leftCell.1 = rightCell.1 := hleftRow.trans hrightRow.symm
      refine Sigma.ext hrows ?_
      apply (Fin.heq_ext_iff (by rw [hrows])).mpr
      exact hcolumns
    have hglobal := congrArg
      (fun cell : YoungCell shape =>
        tableau.entryCellEquiv (youngCellEquivDiagramCell shape cell)) hcells
    have hglobal' : leftGlobal = rightGlobal := by
      calc
        leftGlobal = tableau.entryCellEquiv
            (youngCellEquivDiagramCell shape leftCell) :=
          (tableau.entryCellEquiv_recoveredYoungCell leftGlobal).symm
        _ = tableau.entryCellEquiv
            (youngCellEquivDiagramCell shape rightCell) := hglobal
        _ = rightGlobal := tableau.entryCellEquiv_recoveredYoungCell rightGlobal
    apply Fin.ext
    exact congrArg (fun value : Fin columns => value.val) hglobal'
  have hleForward : Fintype.card earlierPositions ≤ Fintype.card (Fin targetCell.2.val) :=
    Fintype.card_le_of_injective positionToColumn positionToColumn_injective
  let columnToPosition : Fin targetCell.2.val → earlierPositions := fun column => by
    let leftCell : YoungCell shape :=
      ⟨targetCell.1, ⟨column.val, column.isLt.trans targetCell.2.isLt⟩⟩
    let leftGlobal :=
      tableau.entryCellEquiv (youngCellEquivDiagramCell shape leftCell)
    have hleftTarget := tableau.entryPositionYoungCell_lt_of_sameRow_column_lt
      (show leftCell.1 = targetCell.1 from rfl) column.isLt
    have htargetBack := congrArg Fin.val
      (tableau.entryCellEquiv_recoveredYoungCell position)
    change (tableau.entryCellEquiv
        (youngCellEquivDiagramCell shape targetCell)).val =
      position.val at htargetBack
    have hleftTargetPosition : leftGlobal.val < position.val := by omega
    let leftPrefix : Fin position.val := ⟨leftGlobal.val, hleftTargetPosition⟩
    refine ⟨leftPrefix, ?_⟩
    change (tableau.recoveredYoungCell leftGlobal).1 = targetCell.1
    rw [tableau.recoveredYoungCell_entryCellEquiv]
  have columnToPosition_injective : Function.Injective columnToPosition := by
    intro left right heq
    apply Fin.ext
    have hprefixValues := congrArg (fun value => value.1.val) heq
    dsimp only [columnToPosition] at hprefixValues
    change (tableau.entryCellEquiv
        (youngCellEquivDiagramCell shape
          ⟨targetCell.1, ⟨left.val, _⟩⟩)).val =
      (tableau.entryCellEquiv
        (youngCellEquivDiagramCell shape
          ⟨targetCell.1, ⟨right.val, _⟩⟩)).val at hprefixValues
    have hpositions : tableau.entryCellEquiv
        (youngCellEquivDiagramCell shape
          ⟨targetCell.1, ⟨left.val, _⟩⟩) =
      tableau.entryCellEquiv
        (youngCellEquivDiagramCell shape
          ⟨targetCell.1, ⟨right.val, _⟩⟩) := Fin.ext hprefixValues
    have hdiagram := tableau.entryCellEquiv.injective hpositions
    have hcells := (youngCellEquivDiagramCell shape).injective hdiagram
    exact congrArg (fun cell : YoungCell shape => cell.2.val) hcells
  have hleReverse : Fintype.card (Fin targetCell.2.val) ≤ Fintype.card earlierPositions :=
    Fintype.card_le_of_injective columnToPosition columnToPosition_injective
  rw [Fintype.card_fin] at hleForward hleReverse
  change Fintype.card earlierPositions = targetCell.2.val
  omega

theorem DistinctContentSSYT.toFixedShapeRowWord_positionCell
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (position : Fin columns) :
    tableau.toFixedShapeRowWord.positionCell position =
      tableau.recoveredYoungCell position := by
  let targetCell := tableau.recoveredYoungCell position
  have hpositionRow :
      tableau.toFixedShapeRowWord.positionRow position = targetCell.1 := by
    unfold FixedShapeRowWord.positionRow
    change tableau.recoveredWord[position.val]'_ = targetCell.1
    unfold DistinctContentSSYT.recoveredWord
    rw [List.getElem_ofFn]
    exact (tableau.recoveredYoungCell_row position).symm
  have hcount := count_take_ofFn_eq_card_positions
    tableau.recoveredRow position.isLt.le targetCell.1
  change (tableau.recoveredWord.take position.val).count targetCell.1 =
    Fintype.card
      (RecoveredRowPosition tableau position.val position.isLt.le targetCell.1) at hcount
  have hcard := tableau.earlierSameRowPosition_card position
  have hpositionColumn :
      tableau.toFixedShapeRowWord.positionColumn position = targetCell.2.val := by
    change (tableau.recoveredWord.take position.val).count
        (tableau.toFixedShapeRowWord.positionRow position) = targetCell.2.val
    rw [hpositionRow, hcount, hcard]
  refine Sigma.ext hpositionRow ?_
  apply (Fin.heq_ext_iff (congrArg
    (fun row : Fin (rank + 1) => (shape.1 row).val) hpositionRow)).mpr
  exact hpositionColumn

noncomputable def FixedShapeRowWord.toDistinctContentSSYT
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) : DistinctContentSSYT shape :=
  ⟨tableau.toSemistandardYoungTableau,
    tableau.toSemistandardYoungTableau_content⟩

theorem DistinctContentSSYT.toFixedShapeRowWord_positionCellEquiv_symm
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) (cell : YoungCell shape) :
    tableau.toFixedShapeRowWord.positionCellEquiv.symm cell =
      tableau.entryCellEquiv (youngCellEquivDiagramCell shape cell) := by
  apply tableau.toFixedShapeRowWord.positionCellEquiv.injective
  rw [tableau.toFixedShapeRowWord.positionCellEquiv.apply_symm_apply]
  symm
  change tableau.toFixedShapeRowWord.positionCell
      (tableau.entryCellEquiv (youngCellEquivDiagramCell shape cell)) = cell
  rw [tableau.toFixedShapeRowWord_positionCell,
    tableau.recoveredYoungCell_entryCellEquiv]

theorem DistinctContentSSYT.toFixedShapeRowWord_toSemistandardYoungTableau
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) :
    tableau.toFixedShapeRowWord.toSemistandardYoungTableau = tableau.1 := by
  apply SemistandardYoungTableau.ext
  intro row column
  by_cases hcell : (row, column) ∈ shape.youngDiagram
  · let cell : YoungCell shape :=
      (youngCellEquivDiagramCell shape).symm ⟨(row, column), hcell⟩
    rw [tableau.toFixedShapeRowWord.toSemistandardYoungTableau_apply_of_mem hcell]
    rw [tableau.toFixedShapeRowWord_positionCellEquiv_symm cell]
    change (tableau.entryCellEquiv
        (youngCellEquivDiagramCell shape cell)).val = tableau.1 row column
    rfl
  · rw [tableau.toFixedShapeRowWord.toSemistandardYoungTableau.zeros hcell,
      tableau.1.zeros hcell]

theorem DistinctContentSSYT.toFixedShapeRowWord_rightInverse
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : DistinctContentSSYT shape) :
    tableau.toFixedShapeRowWord.toDistinctContentSSYT = tableau := by
  apply Subtype.ext
  exact tableau.toFixedShapeRowWord_toSemistandardYoungTableau

theorem FixedShapeRowWord.toDistinctContentSSYT_entryCellEquiv
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) :
    tableau.toDistinctContentSSYT.entryCellEquiv =
      tableau.positionDiagramCellEquiv.symm := by
  ext cell
  change tableau.toSemistandardYoungTableau cell.val.1 cell.val.2 =
    (tableau.positionDiagramCellEquiv.symm cell).val
  rw [tableau.toSemistandardYoungTableau_apply_of_mem cell.2]
  rfl

theorem FixedShapeRowWord.toDistinctContentSSYT_recoveredYoungCell
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) (position : Fin columns) :
    tableau.toDistinctContentSSYT.recoveredYoungCell position =
      tableau.positionCell position := by
  unfold DistinctContentSSYT.recoveredYoungCell
  rw [tableau.toDistinctContentSSYT_entryCellEquiv]
  change (youngCellEquivDiagramCell shape).symm
      (tableau.positionDiagramCellEquiv position) = tableau.positionCell position
  change (youngCellEquivDiagramCell shape).symm
      (youngCellEquivDiagramCell shape
        (tableau.positionCellEquiv position)) = tableau.positionCell position
  rw [(youngCellEquivDiagramCell shape).symm_apply_apply]
  rfl

theorem FixedShapeRowWord.toDistinctContentSSYT_recoveredRow
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) (position : Fin columns) :
    tableau.toDistinctContentSSYT.recoveredRow position =
      tableau.positionRow position := by
  have hcells := congrArg Sigma.fst
    (tableau.toDistinctContentSSYT_recoveredYoungCell position)
  exact hcells

theorem FixedShapeRowWord.toDistinctContentSSYT_recoveredWord
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) :
    tableau.toDistinctContentSSYT.recoveredWord = tableau.1.word := by
  calc
    tableau.toDistinctContentSSYT.recoveredWord =
        List.ofFn tableau.toDistinctContentSSYT.recoveredRow := by rfl
    _ = List.ofFn tableau.positionRow := by
      exact congrArg List.ofFn
        (funext tableau.toDistinctContentSSYT_recoveredRow)
    _ = tableau.1.word := by
      apply List.ext_get
      · simpa using tableau.1.length_eq.symm
      · intro index hleft hright
        rw [List.get_ofFn]
        unfold FixedShapeRowWord.positionRow
        rfl

theorem FixedShapeRowWord.toDistinctContentSSYT_leftInverse
    {rank columns : ℕ} {shape : BoundedPartition rank columns}
    (tableau : FixedShapeRowWord shape) :
    tableau.toDistinctContentSSYT.toFixedShapeRowWord = tableau := by
  apply Subtype.ext
  apply BallotRowWordFrom.ext
  exact tableau.toDistinctContentSSYT_recoveredWord

noncomputable def fixedShapeRowWordEquivDistinctContentSSYT
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    FixedShapeRowWord shape ≃ DistinctContentSSYT shape where
  toFun := FixedShapeRowWord.toDistinctContentSSYT
  invFun := DistinctContentSSYT.toFixedShapeRowWord
  left_inv := FixedShapeRowWord.toDistinctContentSSYT_leftInverse
  right_inv := DistinctContentSSYT.toFixedShapeRowWord_rightInverse

theorem standardTableauNumber_eq_kostka_replicate_one
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    standardTableauNumber shape =
      kostkaNumber shape.youngDiagram (Multiset.replicate columns 1) := by
  calc
    standardTableauNumber shape = standardRowWordTableauNumber shape :=
      standardTableauNumber_eq_rowWordNumber shape
    _ = Fintype.card (FixedShapeRowWord shape) := rfl
    _ = Fintype.card (DistinctContentSSYT shape) :=
      Fintype.card_congr (fixedShapeRowWordEquivDistinctContentSSYT shape)
    _ = Nat.card (DistinctContentSSYT shape) := Fintype.card_eq_nat_card
    _ = kostkaNumber shape.youngDiagram (Multiset.replicate columns 1) := by
      rw [kostka_eq_card_SSYTWithContent]
      rfl

/-- The manuscript's hook product identity for every bounded partition. -/
theorem hookFormulaStatement
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    HookFormulaStatement shape := by
  unfold HookFormulaStatement
  calc
    standardTableauNumber shape * hookProduct shape =
        (∏ cell ∈ shape.youngDiagram.cells,
          shape.youngDiagram.hookLength cell) *
          kostkaNumber shape.youngDiagram (Multiset.replicate columns 1) := by
      rw [standardTableauNumber_eq_kostka_replicate_one,
        hookProduct_eq_diagram_hookProduct, Nat.mul_comm]
    _ = columns.factorial :=
      hookLength_formula shape.youngDiagram shape.youngDiagram_card

end FibonacciRibbonKernel
