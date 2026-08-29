import FibonacciRibbonKernel.RSKInverse

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def growthDiagramRowBoundary
    {size : ℕ} {permutation : Equiv.Perm (Fin size)}
    (diagram : PermutationGrowthDiagram size permutation)
    (row : Fin (size + 1)) : ShapeBoundary size := by
  by_cases hzero : row.val = 0
  · have hrow : row = 0 := Fin.ext hzero
    subst row
    exact
      { vertices := diagram.shapes 0
        edges := fun _ => GrowthStep.stay
        left_empty := diagram.left_empty 0
        edge_target := by
          intro column
          simp [GrowthStep.target, diagram.top_empty] }
  · let cellRow : Fin size := ⟨row.val - 1, by omega⟩
    have hrow : cellRow.succ = row := by
      apply Fin.ext
      simp [cellRow]
      omega
    let edge : ∀ column : Fin size, GrowthStep (diagram.shapes row column.castSucc) :=
      fun column => by
        let witness := (diagram.local_rule cellRow column).forward_witness
        let forward := applyLocalRule witness.north witness.west
          (permutation cellRow = column) witness.input
        exact forward.fromWest.castBase (by
          rw [← hrow]
          exact witness.southwest_eq)
    exact
      { vertices := diagram.shapes row
        edges := edge
        left_empty := diagram.left_empty row
        edge_target := by
          intro column
          let witness := (diagram.local_rule cellRow column).forward_witness
          let forward := applyLocalRule witness.north witness.west
            (permutation cellRow = column) witness.input
          change (edge column).target = diagram.shapes row column.succ
          unfold edge
          rw [GrowthStep.target_castBase]
          exact forward.southeast_agrees.symm.trans (by
            rw [witness.southeast_eq, hrow]) }

noncomputable def growthDiagramRightEdge
    {size : ℕ} {permutation : Equiv.Perm (Fin size)}
    (diagram : PermutationGrowthDiagram size permutation)
    (row : Fin size) :
    GrowthStep (diagram.shapes row.castSucc (Fin.last size)) := by
  let column : Fin size := ⟨size - 1, by have := row.isLt; omega⟩
  let witness := (diagram.local_rule row column).forward_witness
  let forward := applyLocalRule witness.north witness.west
    (permutation row = column) witness.input
  have hlast : column.succ = Fin.last size := by
    apply Fin.ext
    change (size - 1) + 1 = size
    have hsize := row.isLt
    omega
  exact forward.fromNorth.castBase (by
    exact witness.northeast_eq.trans
      (congrArg (fun index => diagram.shapes row.castSucc index) hlast))

theorem growthDiagramRightEdge_target
    {size : ℕ} {permutation : Equiv.Perm (Fin size)}
    (diagram : PermutationGrowthDiagram size permutation)
    (row : Fin size) :
    (growthDiagramRightEdge diagram row).target =
      diagram.shapes row.succ (Fin.last size) := by
  let column : Fin size := ⟨size - 1, by have := row.isLt; omega⟩
  let witness := (diagram.local_rule row column).forward_witness
  let forward := applyLocalRule witness.north witness.west
    (permutation row = column) witness.input
  have hlast : column.succ = Fin.last size := by
    apply Fin.ext
    change (size - 1) + 1 = size
    have hsize := row.isLt
    omega
  unfold growthDiagramRightEdge
  rw [GrowthStep.target_castBase]
  exact witness.southeast_eq.trans
    (congrArg (fun index => diagram.shapes row.succ index) hlast)

theorem PermutationGrowthDiagram.shapes_unique_of_bottom_right
    {size : ℕ} {leftPermutation rightPermutation : Equiv.Perm (Fin size)}
    (left : PermutationGrowthDiagram size leftPermutation)
    (right : PermutationGrowthDiagram size rightPermutation)
    (hbottom : ∀ column,
      left.shapes (Fin.last size) column = right.shapes (Fin.last size) column)
    (hright : ∀ row,
      left.shapes row (Fin.last size) = right.shapes row (Fin.last size)) :
    left.shapes = right.shapes := by
  funext row column
  let distance := (size - row.val) + (size - column.val)
  have aux : ∀ total : ℕ, ∀ row column : Fin (size + 1),
      (size - row.val) + (size - column.val) = total →
      left.shapes row column = right.shapes row column := by
    intro total
    induction total using Nat.strong_induction_on with
    | h total ih =>
        intro row column htotal
        by_cases hrowLast : row.val = size
        · have hrow : row = Fin.last size := Fin.ext hrowLast
          subst row
          exact hbottom column
        · by_cases hcolumnLast : column.val = size
          · have hcolumn : column = Fin.last size := Fin.ext hcolumnLast
            subst column
            exact hright row
          · let cellRow : Fin size := ⟨row.val, by omega⟩
            let cellColumn : Fin size := ⟨column.val, by omega⟩
            have hrow : cellRow.castSucc = row := Fin.ext rfl
            have hcolumn : cellColumn.castSucc = column := Fin.ext rfl
            have hnortheast := ih
              ((size - cellRow.castSucc.val) + (size - cellColumn.succ.val))
              (by simp [cellRow, cellColumn]; omega)
              cellRow.castSucc cellColumn.succ rfl
            have hsouthwest := ih
              ((size - cellRow.succ.val) + (size - cellColumn.castSucc.val))
              (by simp [cellRow, cellColumn]; omega)
              cellRow.succ cellColumn.castSucc rfl
            have hsoutheast := ih
              ((size - cellRow.succ.val) + (size - cellColumn.succ.val))
              (by simp [cellRow, cellColumn]; omega)
              cellRow.succ cellColumn.succ rfl
            have rightRule :
                LocalGrowthRule (rightPermutation cellRow = cellColumn)
                  (right.shapes cellRow.castSucc cellColumn.castSucc)
                  (left.shapes cellRow.castSucc cellColumn.succ)
                  (left.shapes cellRow.succ cellColumn.castSucc)
                  (left.shapes cellRow.succ cellColumn.succ) :=
              (right.local_rule cellRow cellColumn).transport rfl
                hnortheast.symm hsouthwest.symm hsoutheast.symm
            have hnorthwest :=
              (left.local_rule cellRow cellColumn).northwest_unique rightRule
            simpa [hrow, hcolumn] using hnorthwest
  exact aux distance row column rfl

theorem PermutationGrowthDiagram.marked_iff_of_bottom_right
    {size : ℕ} {leftPermutation rightPermutation : Equiv.Perm (Fin size)}
    (left : PermutationGrowthDiagram size leftPermutation)
    (right : PermutationGrowthDiagram size rightPermutation)
    (hbottom : ∀ column,
      left.shapes (Fin.last size) column = right.shapes (Fin.last size) column)
    (hright : ∀ row,
      left.shapes row (Fin.last size) = right.shapes row (Fin.last size))
    (row column : Fin size) :
    leftPermutation row = column ↔ rightPermutation row = column := by
  have hshapes := left.shapes_unique_of_bottom_right right hbottom hright
  have hnorthwest := congrFun (congrFun hshapes row.castSucc) column.castSucc
  have hnortheast := congrFun (congrFun hshapes row.castSucc) column.succ
  have hsouthwest := congrFun (congrFun hshapes row.succ) column.castSucc
  have hsoutheast := congrFun (congrFun hshapes row.succ) column.succ
  have rightRule :
      LocalGrowthRule (rightPermutation row = column)
        (left.shapes row.castSucc column.castSucc)
        (left.shapes row.castSucc column.succ)
        (left.shapes row.succ column.castSucc)
        (left.shapes row.succ column.succ) :=
    (right.local_rule row column).transport
      hnorthwest.symm hnortheast.symm hsouthwest.symm hsoutheast.symm
  exact (left.local_rule row column).marked_iff rightRule

theorem inverseRSKPermutation_forwardRSK
    {size : ℕ} (permutation : Equiv.Perm (Fin size)) :
    inverseRSKPermutation (forwardRSK size permutation) = permutation := by
  let pair := forwardRSK size permutation
  let forwardDiagram := forwardPermutationGrowthDiagram size permutation
  let inverseDiagram := inversePermutationGrowthDiagram pair
  have hbottom : ∀ column,
      forwardDiagram.shapes (Fin.last size) column =
        inverseDiagram.shapes (Fin.last size) column := by
    intro column
    dsimp [pair, forwardDiagram, inverseDiagram,
      forwardPermutationGrowthDiagram, inversePermutationGrowthDiagram]
    have hzeroBoundary :
        (reverseStage pair (size - size) (by omega)).boundary =
          tableauShapeBoundary pair.insertion :=
      (reverseStage_boundary_congr pair _ _ (by omega)).trans
        (reverseStage_zero_boundary pair)
    rw [hzeroBoundary]
    change (finalGrowthBoundary size permutation).vertices column =
      tableauPrefixShape (finalBoundaryTableau size permutation) column.val
    exact (finalBoundaryTableau_prefixShape size permutation column).symm
  have hinverseShapes := PermutationGrowthDiagram.shapes_unique
    (forwardPermutationGrowthDiagram size permutation.symm)
    forwardDiagram.transpose
  have hright : ∀ row,
      forwardDiagram.shapes row (Fin.last size) =
        inverseDiagram.shapes row (Fin.last size) := by
    intro row
    have htranspose := congrFun (congrFun hinverseShapes (Fin.last size)) row
    change (finalGrowthBoundary size permutation.symm).vertices row =
      forwardDiagram.shapes row (Fin.last size) at htranspose
    change forwardDiagram.shapes row (Fin.last size) =
      (reverseStage pair (size - row.val) (by omega)).boundary.vertices
        (Fin.last size)
    rw [(reverseStage pair (size - row.val) (by omega)).final_vertex]
    have hremaining : size - (size - row.val) = row.val := by
      have hrow := row.isLt
      omega
    rw [hremaining]
    change forwardDiagram.shapes row (Fin.last size) =
      tableauPrefixShape (finalBoundaryTableau size permutation.symm) row.val
    exact htranspose.symm.trans
      (finalBoundaryTableau_prefixShape size permutation.symm row).symm
  apply Equiv.ext
  intro row
  have hmark := forwardDiagram.marked_iff_of_bottom_right
    inverseDiagram hbottom hright row (permutation row)
  exact hmark.mp rfl

noncomputable def rskEquiv (size : ℕ) :
    Equiv.Perm (Fin size) ≃ RSKTableauPair size where
  toFun := forwardRSK size
  invFun := inverseRSKPermutation
  left_inv := inverseRSKPermutation_forwardRSK
  right_inv := forwardRSK_inverseRSKPermutation

end FibonacciRibbonKernel
