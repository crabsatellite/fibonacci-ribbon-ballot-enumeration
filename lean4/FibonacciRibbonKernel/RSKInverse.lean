import FibonacciRibbonKernel.RSKReverse

namespace FibonacciRibbonKernel

open scoped Classical

structure ReverseStage {size : ℕ} (pair : RSKTableauPair size)
    (removed : ℕ) (hremoved : removed ≤ size) where
  boundary : ShapeBoundary size
  final_vertex : boundary.vertices (Fin.last size) =
    tableauPrefixShape pair.recording (size - removed)

noncomputable def reverseStage
    {size : ℕ} (pair : RSKTableauPair size) :
    (removed : ℕ) → (hremoved : removed ≤ size) →
      ReverseStage pair removed hremoved
  | 0, _ => by
      let boundary := tableauShapeBoundary pair.insertion
      refine ⟨boundary, ?_⟩
      change tableauPrefixShape pair.insertion size =
        tableauPrefixShape pair.recording size
      exact tableauPrefixShape_final_eq_of_shape_eq
        pair.insertion pair.recording pair.same_shape
  | removed + 1, hremoved => by
      have hprior : removed ≤ size := by omega
      have hremaining : 0 < size - removed := by omega
      let prior := reverseStage pair removed hprior
      let row : Fin size := ⟨size - removed - 1, by omega⟩
      let rightEdge := tableauBoundaryEdge pair.recording row
      have hrightTarget : rightEdge.target =
          tableauPrefixShape pair.recording (size - removed) := by
        change (tableauBoundaryEdge pair.recording row).target = _
        rw [tableauBoundaryEdge_target]
        congr 1
        simp [row]
        omega
      have hright : rightEdge.target = prior.boundary.vertices (Fin.last size) :=
        hrightTarget.trans prior.final_vertex.symm
      let boundary := reverseBoundary prior.boundary rightEdge hright
      refine ⟨boundary, ?_⟩
      rw [reverseBoundary_final_vertex]
      congr 1

theorem reverseStage_boundary_congr
    {size : ℕ} (pair : RSKTableauPair size)
    {leftRemoved rightRemoved : ℕ}
    (hleft : leftRemoved ≤ size) (hright : rightRemoved ≤ size)
    (heq : leftRemoved = rightRemoved) :
    (reverseStage pair leftRemoved hleft).boundary =
      (reverseStage pair rightRemoved hright).boundary := by
  subst rightRemoved
  rfl

theorem reverseStage_zero_boundary
    {size : ℕ} (pair : RSKTableauPair size) :
    (reverseStage pair 0 (by omega)).boundary =
      tableauShapeBoundary pair.insertion := rfl

noncomputable def inverseRSKMarkByRemoved
    {size : ℕ} (pair : RSKTableauPair size)
    (removed column : Fin size) : Bool := by
  let stage := reverseStage pair removed.val removed.isLt.le
  let row : Fin size := ⟨size - removed.val - 1, by omega⟩
  let rightEdge := tableauBoundaryEdge pair.recording row
  have hrightTarget : rightEdge.target =
      tableauPrefixShape pair.recording (size - removed.val) := by
    change (tableauBoundaryEdge pair.recording row).target = _
    rw [tableauBoundaryEdge_target]
    congr 1
    simp [row]
    omega
  have hright : rightEdge.target = stage.boundary.vertices (Fin.last size) :=
    hrightTarget.trans stage.final_vertex.symm
  exact reverseRowMarks stage.boundary rightEdge hright column

noncomputable def reverseStageMark
    {size : ℕ} (pair : RSKTableauPair size)
    (removed column : Fin size) : Bool :=
  inverseRSKMarkByRemoved pair removed column

noncomputable def inverseRSKRowMarks
    {size : ℕ} (pair : RSKTableauPair size) (row column : Fin size) : Bool :=
  inverseRSKMarkByRemoved pair ⟨size - (row.val + 1), by omega⟩ column

theorem reverseStage_edge_transition
    {size : ℕ} (pair : RSKTableauPair size)
    (removed column : Fin size) :
    (reverseStage pair removed.val removed.isLt.le).boundary.edges column =
        GrowthStep.stay ↔
      (reverseStage pair (removed.val + 1) (by omega)).boundary.edges column =
          GrowthStep.stay ∧
        reverseStageMark pair removed column = false := by
  let stage := reverseStage pair removed.val removed.isLt.le
  let row : Fin size := ⟨size - removed.val - 1, by omega⟩
  let rightEdge := tableauBoundaryEdge pair.recording row
  have hrightTarget : rightEdge.target =
      tableauPrefixShape pair.recording (size - removed.val) := by
    change (tableauBoundaryEdge pair.recording row).target = _
    rw [tableauBoundaryEdge_target]
    congr 1
    simp [row]
    omega
  have hright : rightEdge.target = stage.boundary.vertices (Fin.last size) :=
    hrightTarget.trans stage.final_vertex.symm
  have htransition := reverseBoundary_edge_stay_transition
    stage.boundary rightEdge hright column
  change stage.boundary.edges column = GrowthStep.stay ↔
    (reverseBoundary stage.boundary rightEdge hright).edges column =
        GrowthStep.stay ∧
      reverseRowMarks stage.boundary rightEdge hright column = false at htransition
  change stage.boundary.edges column = GrowthStep.stay ↔
    (reverseStage pair (removed.val + 1) (by omega)).boundary.edges column =
        GrowthStep.stay ∧ reverseStageMark pair removed column = false
  exact htransition

theorem reverseStage_edge_stay_of_marked
    {size : ℕ} (pair : RSKTableauPair size)
    (removed column : Fin size)
    (hmarked : reverseStageMark pair removed column = true) :
    (reverseStage pair (removed.val + 1) (by omega)).boundary.edges column =
      GrowthStep.stay := by
  let stage := reverseStage pair removed.val removed.isLt.le
  let row : Fin size := ⟨size - removed.val - 1, by omega⟩
  let rightEdge := tableauBoundaryEdge pair.recording row
  have hrightTarget : rightEdge.target =
      tableauPrefixShape pair.recording (size - removed.val) := by
    change (tableauBoundaryEdge pair.recording row).target = _
    rw [tableauBoundaryEdge_target]
    congr 1
    simp [row]
    omega
  have hright : rightEdge.target = stage.boundary.vertices (Fin.last size) :=
    hrightTarget.trans stage.final_vertex.symm
  have hstay := reverseBoundary_edge_stay_of_marked
    stage.boundary rightEdge hright column hmarked
  exact hstay

theorem reverseStageMark_existsUnique
    {size : ℕ} (pair : RSKTableauPair size) (column : Fin size) :
    ∃! removed : Fin size, reverseStageMark pair removed column = true := by
  have hinitial :
      (reverseStage pair 0 (by omega)).boundary.edges column ≠ GrowthStep.stay := by
    intro hstay
    change tableauBoundaryEdge pair.insertion column = GrowthStep.stay at hstay
    cases hstay
  have hfinalShape :
      (reverseStage pair size le_rfl).boundary.vertices (Fin.last size) =
        GrowthShape.empty (size + 1) := by
    have hvertex := (reverseStage pair size le_rfl).final_vertex
    rw [show size - size = 0 by omega] at hvertex
    exact hvertex.trans
      (tableauPrefixShape_zero pair.recording)
  have hfinal :
      (reverseStage pair size le_rfl).boundary.edges column = GrowthStep.stay :=
    (reverseStage pair size le_rfl).boundary.edge_stay_of_final_empty
      hfinalShape column
  have hexists : ∃ removed : Fin size,
      reverseStageMark pair removed column = true := by
    by_contra hnone
    push Not at hnone
    have hnonstay : ∀ (removed : ℕ) (hremoved : removed ≤ size),
        (reverseStage pair removed hremoved).boundary.edges column ≠
          GrowthStep.stay := by
      intro removed hremoved
      induction removed with
      | zero => exact hinitial
      | succ removed ih =>
          have hlt : removed < size := by omega
          let index : Fin size := ⟨removed, hlt⟩
          have hmarkFalse : reverseStageMark pair index column = false := by
            cases hmark : reverseStageMark pair index column with
            | false => rfl
            | true => exact (hnone index hmark).elim
          intro hstayNext
          have htransition := (reverseStage_edge_transition pair index column).mpr
            ⟨hstayNext, hmarkFalse⟩
          exact (ih (by omega)) htransition
    exact (hnonstay size le_rfl) hfinal
  obtain ⟨chosen, hchosen⟩ := hexists
  refine ⟨chosen, hchosen, ?_⟩
  intro other hother
  have noTwo : ∀ {left right : Fin size}, left.val < right.val →
      reverseStageMark pair left column = true →
      reverseStageMark pair right column = true → False := by
    intro left right hleftRight hleftMark hrightMark
    have hbase := reverseStage_edge_stay_of_marked pair left column hleftMark
    let P : (removed : ℕ) → left.val + 1 ≤ removed → Prop := fun removed _ =>
      ∀ hremoved : removed ≤ size,
        (reverseStage pair removed hremoved).boundary.edges column = GrowthStep.stay
    have hbaseP : P (left.val + 1) (by omega) := by
      intro hremoved
      simpa only using hbase
    have hstepP : ∀ removed (hleft : left.val + 1 ≤ removed),
        P removed hleft → P (removed + 1) (by omega) := by
      intro removed hleft hinduction hremoved
      have hlt : removed < size := by omega
      let index : Fin size := ⟨removed, hlt⟩
      exact (reverseStage_edge_transition pair index column).mp
        (hinduction (by omega)) |>.1
    have hpropagate : P right.val (by omega) :=
      Nat.le_induction (P := P) hbaseP hstepP right.val (by omega)
    have hrightStay := hpropagate right.isLt.le
    have htransition := (reverseStage_edge_transition pair right column).mp hrightStay
    rw [hrightMark] at htransition
    cases htransition.2
  by_contra hne
  have hvalne : other.val ≠ chosen.val := by
    intro hval
    exact hne (Fin.ext hval)
  rcases lt_or_gt_of_ne hvalne with hlt | hgt
  · exact (noTwo hlt hother hchosen).elim
  · exact (noTwo hgt hchosen hother).elim

theorem reverseStageMark_eq_inverseRSKRowMarks
    {size : ℕ} (pair : RSKTableauPair size) (row column : Fin size) :
    reverseStageMark pair ⟨size - (row.val + 1), by omega⟩ column =
      inverseRSKRowMarks pair row column := by
  rfl

theorem inverseRSKRowMarks_existsUnique
    {size : ℕ} (pair : RSKTableauPair size) (row : Fin size) :
    ∃! column : Fin size, inverseRSKRowMarks pair row column = true := by
  let removed : Fin size := ⟨size - (row.val + 1), by omega⟩
  let stage := reverseStage pair removed.val removed.isLt.le
  let stageRow : Fin size := ⟨size - removed.val - 1, by omega⟩
  let rightEdge := tableauBoundaryEdge pair.recording stageRow
  have hrightTarget : rightEdge.target =
      tableauPrefixShape pair.recording (size - removed.val) := by
    change (tableauBoundaryEdge pair.recording stageRow).target = _
    rw [tableauBoundaryEdge_target]
    congr 1
    simp [stageRow]
    omega
  have hright : rightEdge.target = stage.boundary.vertices (Fin.last size) :=
    hrightTarget.trans stage.final_vertex.symm
  have hnonstay : rightEdge ≠ GrowthStep.stay := by
    dsimp [rightEdge, tableauBoundaryEdge]
    intro heq
    cases heq
  have hexact := reverseRowMarks_existsUnique stage.boundary rightEdge hright hnonstay
  unfold inverseRSKRowMarks inverseRSKMarkByRemoved
  exact hexact

noncomputable def inverseRSKFunction
    {size : ℕ} (pair : RSKTableauPair size) : Fin size → Fin size :=
  fun row => (inverseRSKRowMarks_existsUnique pair row).choose

theorem inverseRSKFunction_marked
    {size : ℕ} (pair : RSKTableauPair size) (row : Fin size) :
    inverseRSKRowMarks pair row (inverseRSKFunction pair row) = true :=
  (inverseRSKRowMarks_existsUnique pair row).choose_spec.1

theorem inverseRSKFunction_eq_of_marked
    {size : ℕ} (pair : RSKTableauPair size) (row column : Fin size)
    (hmarked : inverseRSKRowMarks pair row column = true) :
    column = inverseRSKFunction pair row :=
  (inverseRSKRowMarks_existsUnique pair row).choose_spec.2 column hmarked

theorem inverseRSKFunction_injective
    {size : ℕ} (pair : RSKTableauPair size) :
    Function.Injective (inverseRSKFunction pair) := by
  intro left right heq
  let leftRemoved : Fin size := ⟨size - (left.val + 1), by omega⟩
  let rightRemoved : Fin size := ⟨size - (right.val + 1), by omega⟩
  have hleftMark : reverseStageMark pair leftRemoved (inverseRSKFunction pair left) = true := by
    rw [reverseStageMark_eq_inverseRSKRowMarks]
    exact inverseRSKFunction_marked pair left
  have hrightMark : reverseStageMark pair rightRemoved (inverseRSKFunction pair left) = true := by
    rw [heq]
    rw [reverseStageMark_eq_inverseRSKRowMarks]
    exact inverseRSKFunction_marked pair right
  have hremoved := (reverseStageMark_existsUnique pair
    (inverseRSKFunction pair left)).choose_spec.2
  have hleftEq := hremoved leftRemoved hleftMark
  have hrightEq := hremoved rightRemoved hrightMark
  have hvalues := congrArg Fin.val (hleftEq.trans hrightEq.symm)
  apply Fin.ext
  dsimp [leftRemoved, rightRemoved] at hvalues
  omega

noncomputable def inverseRSKPermutation
    {size : ℕ} (pair : RSKTableauPair size) : Equiv.Perm (Fin size) :=
  Equiv.ofBijective (inverseRSKFunction pair)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨inverseRSKFunction_injective pair, rfl⟩)

@[simp] theorem inverseRSKPermutation_apply
    {size : ℕ} (pair : RSKTableauPair size) (row : Fin size) :
    inverseRSKPermutation pair row = inverseRSKFunction pair row := rfl

theorem inverseRSKPermutation_eq_iff_marked
    {size : ℕ} (pair : RSKTableauPair size) (row column : Fin size) :
    inverseRSKPermutation pair row = column ↔
      inverseRSKRowMarks pair row column = true := by
  constructor
  · intro heq
    rw [inverseRSKPermutation_apply] at heq
    rw [← heq]
    exact inverseRSKFunction_marked pair row
  · intro hmarked
    rw [inverseRSKPermutation_apply]
    exact (inverseRSKFunction_eq_of_marked pair row column hmarked).symm

theorem reverseStage_final_boundary_empty
    {size : ℕ} (pair : RSKTableauPair size)
    (column : Fin (size + 1)) :
    (reverseStage pair size le_rfl).boundary.vertices column =
      GrowthShape.empty (size + 1) := by
  have hfinal :
      (reverseStage pair size le_rfl).boundary.vertices (Fin.last size) =
        GrowthShape.empty (size + 1) := by
    have hvertex := (reverseStage pair size le_rfl).final_vertex
    rw [show size - size = 0 by omega] at hvertex
    exact hvertex.trans (tableauPrefixShape_zero pair.recording)
  exact (reverseStage pair size le_rfl).boundary
    |>.vertex_eq_empty_of_final_empty hfinal column

noncomputable def inverseCellLocalRule
    {size : ℕ} (pair : RSKTableauPair size)
    (row column : Fin size) :
    LocalGrowthRule (inverseRSKPermutation pair row = column)
      ((reverseStage pair (size - row.val) (by omega)).boundary.vertices column.castSucc)
      ((reverseStage pair (size - row.val) (by omega)).boundary.vertices column.succ)
      ((reverseStage pair (size - (row.val + 1)) (by omega)).boundary.vertices column.castSucc)
      ((reverseStage pair (size - (row.val + 1)) (by omega)).boundary.vertices column.succ) := by
  let removed : Fin size := ⟨size - (row.val + 1), by omega⟩
  let stage := reverseStage pair removed.val removed.isLt.le
  let stageRow : Fin size := ⟨size - removed.val - 1, by omega⟩
  let rightEdge := tableauBoundaryEdge pair.recording stageRow
  have hrightTarget : rightEdge.target =
      tableauPrefixShape pair.recording (size - removed.val) := by
    change (tableauBoundaryEdge pair.recording stageRow).target = _
    rw [tableauBoundaryEdge_target]
    congr 1
    simp [stageRow]
    omega
  have hright : rightEdge.target = stage.boundary.vertices (Fin.last size) :=
    hrightTarget.trans stage.final_vertex.symm
  let output := reverseCellOutputAt stage.boundary rightEdge hright column
  have hnextBoundary :
      (reverseStage pair (removed.val + 1) (by omega)).boundary =
        reverseBoundary stage.boundary rightEdge hright := rfl
  have hnorthwest : output.northwest =
      (reverseStage pair (removed.val + 1) (by omega)).boundary.vertices
        column.castSucc := by
    rw [hnextBoundary]
    exact (reverseAtColumn_eq_cell_northwest stage.boundary rightEdge hright column).symm
  have hnortheast :
      (reverseAtColumn stage.boundary rightEdge hright (column.val + 1) (by omega)).1 =
        (reverseStage pair (removed.val + 1) (by omega)).boundary.vertices
          column.succ := by
    rw [hnextBoundary]
    rfl
  have hsoutheast :
      (reverseAtColumn stage.boundary rightEdge hright (column.val + 1) (by omega)).2.1.target =
        stage.boundary.vertices column.succ := by
    rw [(reverseAtColumn stage.boundary rightEdge hright
      (column.val + 1) (by omega)).2.2]
    congr 1
  have hmark : (output.marked = true) ↔
      inverseRSKPermutation pair row = column := by
    rw [inverseRSKPermutation_eq_iff_marked]
    rw [← reverseStageMark_eq_inverseRSKRowMarks]
    rfl
  have rule := output.rule.congr_mark hmark
  have transported := rule.transport hnorthwest hnortheast rfl hsoutheast
  have htop : size - (row.val + 1) + 1 = size - row.val := by omega
  have htopBoundary :
      (reverseStage pair (removed.val + 1) (by omega)).boundary =
        (reverseStage pair (size - row.val) (by omega)).boundary :=
    reverseStage_boundary_congr pair _ _ (by simpa [removed] using htop)
  have hbottomBoundary : stage.boundary =
      (reverseStage pair (size - (row.val + 1)) (by omega)).boundary := by
    rfl
  exact transported.transport
    (congrArg (fun boundary : ShapeBoundary size =>
      boundary.vertices column.castSucc) htopBoundary)
    (congrArg (fun boundary : ShapeBoundary size =>
      boundary.vertices column.succ) htopBoundary)
    (congrArg (fun boundary : ShapeBoundary size =>
      boundary.vertices column.castSucc) hbottomBoundary)
    (congrArg (fun boundary : ShapeBoundary size =>
      boundary.vertices column.succ) hbottomBoundary)

noncomputable def inversePermutationGrowthDiagram
    {size : ℕ} (pair : RSKTableauPair size) :
    PermutationGrowthDiagram size (inverseRSKPermutation pair) where
  shapes := fun row column =>
    (reverseStage pair (size - row.val) (by omega)).boundary.vertices column
  top_empty := by
    intro column
    exact reverseStage_final_boundary_empty pair column
  left_empty := by
    intro row
    exact (reverseStage pair (size - row.val) (by omega)).boundary.left_empty
  local_rule := inverseCellLocalRule pair

theorem forwardRSK_inverseRSKPermutation
    {size : ℕ} (pair : RSKTableauPair size) :
    forwardRSK size (inverseRSKPermutation pair) = pair := by
  let permutation := inverseRSKPermutation pair
  have hforward := PermutationGrowthDiagram.shapes_unique
    (forwardPermutationGrowthDiagram size permutation)
    (inversePermutationGrowthDiagram pair)
  have hinsertion : finalBoundaryTableau size permutation = pair.insertion := by
    apply tableau_eq_of_prefixShape_eq
    intro column
    rw [finalBoundaryTableau_prefixShape]
    have hshape := congrFun (congrFun hforward (Fin.last size)) column
    dsimp [forwardPermutationGrowthDiagram,
      inversePermutationGrowthDiagram] at hshape
    have hzeroBoundary :
        (reverseStage pair (size - size) (by omega)).boundary =
          tableauShapeBoundary pair.insertion :=
      (reverseStage_boundary_congr pair _ _ (by omega)).trans
        (reverseStage_zero_boundary pair)
    rw [hzeroBoundary] at hshape
    change (finalGrowthBoundary size permutation).vertices column =
      tableauPrefixShape pair.insertion column.val
    exact hshape
  have hinverse := PermutationGrowthDiagram.shapes_unique
    (forwardPermutationGrowthDiagram size permutation.symm)
    (inversePermutationGrowthDiagram pair).transpose
  have hrecording : finalBoundaryTableau size permutation.symm = pair.recording := by
    apply tableau_eq_of_prefixShape_eq
    intro column
    rw [finalBoundaryTableau_prefixShape]
    have hshape := congrFun (congrFun hinverse (Fin.last size)) column
    dsimp [forwardPermutationGrowthDiagram,
      inversePermutationGrowthDiagram, PermutationGrowthDiagram.transpose] at hshape
    change (finalGrowthBoundary size permutation.symm).vertices column =
      (reverseStage pair (size - column.val) (by omega)).boundary.vertices
        (Fin.last size) at hshape
    have hvertex :=
      (reverseStage pair (size - column.val) (by omega)).final_vertex
    have hremaining : size - (size - column.val) = column.val := by
      have hcolumn := column.isLt
      omega
    rw [hremaining] at hvertex
    exact hshape.trans hvertex
  apply RSKTableauPair.ext hinsertion hrecording

end FibonacciRibbonKernel
