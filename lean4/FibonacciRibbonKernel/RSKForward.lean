import FibonacciRibbonKernel.RSKGrowthDiagram

namespace FibonacciRibbonKernel

open scoped Classical

/-! Row-by-row construction of the forward permutation growth diagram. -/

structure GrowthBoundary (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (processed : ℕ) where
  processed_le : processed ≤ size
  vertices : Fin (size + 1) → GrowthShape (size + 1)
  left_empty : vertices 0 = GrowthShape.empty (size + 1)
  edges : ∀ column : Fin size, GrowthStep (vertices column.castSucc)
  edge_target : ∀ column,
    (edges column).target = vertices column.succ
  edge_stay_iff : ∀ column,
    edges column = GrowthStep.stay ↔
      processed ≤ (permutation.symm column).val
  vertex_card_le : ∀ column, (vertices column).card ≤ processed

noncomputable def initialGrowthBoundary
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) :
    GrowthBoundary size permutation 0 where
  processed_le := by omega
  vertices := fun _ => GrowthShape.empty (size + 1)
  left_empty := rfl
  edges := fun _ => GrowthStep.stay
  edge_target := by intro; rfl
  edge_stay_iff := by simp
  vertex_card_le := by
    intro column
    simp [GrowthShape.card, GrowthShape.empty]

def RowScanStep
    {size : ℕ} {permutation : Equiv.Perm (Fin size)} {processed : ℕ}
    (boundary : GrowthBoundary size permutation processed)
    (hprocessed : processed < size) (column : ℕ) (hcolumn : column ≤ size) :=
  {west : GrowthStep (boundary.vertices ⟨column, by omega⟩) //
    west = GrowthStep.stay ↔
      column ≤ (permutation ⟨processed, hprocessed⟩).val}

theorem rowCellInput
    {size : ℕ} {permutation : Equiv.Perm (Fin size)} {processed : ℕ}
    (boundary : GrowthBoundary size permutation processed)
    (hprocessed : processed < size) (column : Fin size)
    (west : RowScanStep boundary hprocessed column.val (by omega)) :
    GrowthSquareInput (boundary.edges column) west.1
      (permutation ⟨processed, hprocessed⟩ = column) where
  height_pos := by intro; omega
  marked_clear := by
    intro hmarked
    have hinverse : permutation.symm column = ⟨processed, hprocessed⟩ := by
      apply permutation.injective
      rw [permutation.apply_symm_apply]
      exact hmarked.symm
    have hnorth : boundary.edges column = GrowthStep.stay :=
      (boundary.edge_stay_iff column).mpr (by rw [hinverse])
    have hwest : west.1 = GrowthStep.stay := west.2.mpr (by
      have hvalue := congrArg Fin.val hmarked
      omega)
    exact ⟨hnorth, hwest⟩
  repeated_has_next := by
    intro row hnorth hwest hnorthEq hwestEq
    have hrowAddable : (boundary.vertices column.castSucc).Addable row := by
      exact hnorth
    have hrowCard :=
      (boundary.vertices column.castSucc).addable_row_le_card row hrowAddable
    have hcardBound := boundary.vertex_card_le column.castSucc
    omega

noncomputable def rowScan
    {size : ℕ} {permutation : Equiv.Perm (Fin size)} {processed : ℕ}
    (boundary : GrowthBoundary size permutation processed)
    (hprocessed : processed < size) :
    (column : ℕ) → (hcolumn : column ≤ size) →
      RowScanStep boundary hprocessed column hcolumn
  | 0, _ => ⟨GrowthStep.stay, by simp⟩
  | column + 1, hcolumn => by
      let cell : Fin size := ⟨column, by omega⟩
      let west := rowScan boundary hprocessed column (by omega)
      let input := rowCellInput boundary hprocessed cell west
      let output := applyLocalRule (boundary.edges cell) west.1
        (permutation ⟨processed, hprocessed⟩ = cell) input
      let nextWestAtSucc : GrowthStep (boundary.vertices cell.succ) :=
        output.fromNorth.castBase (boundary.edge_target cell)
      let nextColumn : Fin (size + 1) := ⟨column + 1, by omega⟩
      have hnextColumn : cell.succ = nextColumn := Fin.ext rfl
      let nextWest : GrowthStep (boundary.vertices nextColumn) :=
        nextWestAtSucc.castBase (congrArg boundary.vertices hnextColumn)
      refine ⟨nextWest, ?_⟩
      unfold nextWest nextWestAtSucc
      rw [GrowthStep.castBase_eq_stay_iff,
        GrowthStep.castBase_eq_stay_iff,
        applyLocalRule_fromNorth_stay_iff]
      constructor
      · rintro ⟨hwest, hunmarked⟩
        have hle := west.2.mp hwest
        have hne : (permutation ⟨processed, hprocessed⟩).val ≠ column := by
          intro heq
          apply hunmarked
          exact Fin.ext heq
        omega
      · intro hle
        constructor
        · exact west.2.mpr (by omega)
        · intro hmarked
          have hvalue := congrArg Fin.val hmarked
          change (permutation ⟨processed, hprocessed⟩).val = column at hvalue
          omega

noncomputable def rowScanFin
    {size : ℕ} {permutation : Equiv.Perm (Fin size)} {processed : ℕ}
    (boundary : GrowthBoundary size permutation processed)
    (hprocessed : processed < size) (column : Fin (size + 1)) :
    RowScanStep boundary hprocessed column.val (by omega) :=
  rowScan boundary hprocessed column.val (by omega)

noncomputable def rowCellOutput
    {size : ℕ} {permutation : Equiv.Perm (Fin size)} {processed : ℕ}
    (boundary : GrowthBoundary size permutation processed)
    (hprocessed : processed < size) (column : Fin size) :
    GrowthSquareOutput (boundary.edges column)
      (rowScanFin boundary hprocessed column.castSucc).1 := by
  let west := rowScanFin boundary hprocessed column.castSucc
  let input := rowCellInput boundary hprocessed column west
  exact applyLocalRule (boundary.edges column) west.1
    (permutation ⟨processed, hprocessed⟩ = column) input

theorem rowCellOutput_fromWest_stay_iff
    {size : ℕ} {permutation : Equiv.Perm (Fin size)} {processed : ℕ}
    (boundary : GrowthBoundary size permutation processed)
    (hprocessed : processed < size) (column : Fin size) :
    (rowCellOutput boundary hprocessed column).fromWest = GrowthStep.stay ↔
      boundary.edges column = GrowthStep.stay ∧
        ¬ permutation ⟨processed, hprocessed⟩ = column := by
  unfold rowCellOutput
  exact applyLocalRule_fromWest_stay_iff _ _ _ _

theorem rowScan_succ_target
    {size : ℕ} {permutation : Equiv.Perm (Fin size)} {processed : ℕ}
    (boundary : GrowthBoundary size permutation processed)
    (hprocessed : processed < size) (column : Fin size) :
    (rowScanFin boundary hprocessed column.succ).1.target =
      (rowCellOutput boundary hprocessed column).fromNorth.target := by
  have hwest :
      rowScan boundary hprocessed column.val (by omega) =
        rowScanFin boundary hprocessed column.castSucc := by
    apply Subtype.ext
    rfl
  change (rowScan boundary hprocessed (column.val + 1) (by omega)).1.target = _
  rw [rowScan]
  simp only [GrowthStep.target_castBase]
  unfold rowCellOutput
  rw [hwest]

noncomputable def advanceGrowthBoundary
    {size : ℕ} {permutation : Equiv.Perm (Fin size)} {processed : ℕ}
    (boundary : GrowthBoundary size permutation processed)
    (hprocessed : processed < size) :
    GrowthBoundary size permutation (processed + 1) where
  processed_le := by omega
  vertices := fun column =>
    (rowScanFin boundary hprocessed column).1.target
  left_empty := by
    change boundary.vertices 0 = GrowthShape.empty (size + 1)
    exact boundary.left_empty
  edges := fun column => (rowCellOutput boundary hprocessed column).fromWest
  edge_target := by
    intro column
    have hagree := (rowCellOutput boundary hprocessed column).southeast_agrees
    have hscan := rowScan_succ_target boundary hprocessed column
    exact hagree.symm.trans hscan.symm
  edge_stay_iff := by
    intro column
    rw [rowCellOutput_fromWest_stay_iff]
    rw [boundary.edge_stay_iff]
    constructor
    · rintro ⟨hle, hunmarked⟩
      have hstrict : processed < (permutation.symm column).val := by
        by_contra hnot
        have heqVal : (permutation.symm column).val = processed := by omega
        apply hunmarked
        have hinverse : permutation.symm column = ⟨processed, hprocessed⟩ :=
          Fin.ext heqVal
        rw [← hinverse, permutation.apply_symm_apply]
      omega
    · intro hle
      constructor
      · omega
      · intro hmarked
        have hinverse : permutation.symm column = ⟨processed, hprocessed⟩ := by
          apply permutation.injective
          rw [permutation.apply_symm_apply]
          exact hmarked.symm
        have hvalue := congrArg Fin.val hinverse
        change (permutation.symm column).val = processed at hvalue
        omega
  vertex_card_le := by
    intro column
    have hstep :=
      (rowScanFin boundary hprocessed column).1.target_card_le
    have hbase :
        (boundary.vertices ⟨column.val, by omega⟩).card ≤ processed := by
      simpa only using boundary.vertex_card_le column
    omega

noncomputable def growthBoundaryAfter
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) :
    (processed : ℕ) → (hprocessed : processed ≤ size) →
      GrowthBoundary size permutation processed
  | 0, _ => initialGrowthBoundary size permutation
  | processed + 1, hprocessed =>
      advanceGrowthBoundary
        (growthBoundaryAfter size permutation processed (by omega)) (by omega)

theorem growthBoundaryAfter_zero
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) :
    growthBoundaryAfter size permutation 0 (by omega) =
      initialGrowthBoundary size permutation := rfl

theorem growthBoundaryAfter_succ
    (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (processed : ℕ) (hprocessed : processed + 1 ≤ size) :
    growthBoundaryAfter size permutation (processed + 1) hprocessed =
      advanceGrowthBoundary
        (growthBoundaryAfter size permutation processed (by omega)) (by omega) := rfl

noncomputable def forwardPermutationGrowthDiagram
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) :
    PermutationGrowthDiagram size permutation where
  shapes := fun row column =>
    (growthBoundaryAfter size permutation row.val (by omega)).vertices column
  top_empty := by
    intro column
    rfl
  left_empty := by
    intro row
    exact (growthBoundaryAfter size permutation row.val (by omega)).left_empty
  local_rule := by
    intro row column
    let boundary := growthBoundaryAfter size permutation row.val (by omega)
    let west := rowScanFin boundary row.isLt column.castSucc
    let input := rowCellInput boundary row.isLt column west
    let output := applyLocalRule (boundary.edges column) west.1
      (permutation row = column) input
    let rawRule := applyLocalRule_satisfies_relation
      (boundary.edges column) west.1 (permutation row = column) input
    have hnortheast : (boundary.edges column).target =
        boundary.vertices column.succ := boundary.edge_target column
    have hsouthwest : west.1.target =
        (growthBoundaryAfter size permutation row.succ.val (by omega)).vertices
          column.castSucc := by
      change west.1.target =
        (advanceGrowthBoundary boundary row.isLt).vertices column.castSucc
      rfl
    have hsoutheast : output.fromNorth.target =
        (growthBoundaryAfter size permutation row.succ.val (by omega)).vertices
          column.succ := by
      change output.fromNorth.target =
        (advanceGrowthBoundary boundary row.isLt).vertices column.succ
      exact (rowScan_succ_target boundary row.isLt column).symm
    exact rawRule.transport rfl hnortheast hsouthwest hsoutheast

end FibonacciRibbonKernel
