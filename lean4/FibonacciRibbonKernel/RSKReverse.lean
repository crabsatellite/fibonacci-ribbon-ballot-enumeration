import FibonacciRibbonKernel.RSKReverseLocal
import FibonacciRibbonKernel.RSKTableauBoundary

namespace FibonacciRibbonKernel

open scoped Classical

structure ShapeBoundary (size : ℕ) where
  vertices : Fin (size + 1) → GrowthShape (size + 1)
  edges : ∀ column : Fin size, GrowthStep (vertices column.castSucc)
  left_empty : vertices 0 = GrowthShape.empty (size + 1)
  edge_target : ∀ column, (edges column).target = vertices column.succ

@[ext] theorem ShapeBoundary.ext
    {size : ℕ} {left right : ShapeBoundary size}
    (hvertices : left.vertices = right.vertices) : left = right := by
  cases left with
  | mk leftVertices leftEdges leftEmpty leftTarget =>
      cases right with
      | mk rightVertices rightEdges rightEmpty rightTarget =>
          dsimp at hvertices
          subst rightVertices
          have hedges : leftEdges = rightEdges := by
            funext column
            apply GrowthStep.target_injective
            exact leftTarget column |>.trans (rightTarget column).symm
          subst rightEdges
          rfl

noncomputable def tableauShapeBoundary
    {size : ℕ} (tableau : StandardRowWordTableau size size) :
    ShapeBoundary size where
  vertices := fun column => tableauPrefixShape tableau column.val
  edges := tableauBoundaryEdge tableau
  left_empty := tableauPrefixShape_zero tableau
  edge_target := tableauBoundaryEdge_target tableau

def ReverseVertical
    {size : ℕ} (bottom : ShapeBoundary size) (column : ℕ)
    (hcolumn : column ≤ size) :=
  PSigma fun base : GrowthShape (size + 1) =>
    {step : GrowthStep base //
      step.target = bottom.vertices ⟨column, by omega⟩}

noncomputable def reverseVertical
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size)) :
    (offset : ℕ) → (hoffset : offset ≤ size) →
      ReverseVertical bottom (size - offset) (by omega)
  | 0, _ => ⟨rightBase, rightEdge, by
      change rightEdge.target = bottom.vertices (Fin.last size)
      exact hright⟩
  | offset + 1, hoffset => by
      let column : Fin size := ⟨size - (offset + 1), by omega⟩
      let fromNorth := reverseVertical bottom rightEdge hright offset (by omega)
      have hcolumnNext : size - offset = column.val + 1 := by
        simp [column]
        omega
      have hnorthTarget : fromNorth.2.1.target =
          bottom.vertices column.succ := by
        rw [fromNorth.2.2]
        congr 1
        apply Fin.ext
        simp [hcolumnNext]
      have hagree : fromNorth.2.1.target = (bottom.edges column).target :=
        hnorthTarget.trans (bottom.edge_target column).symm
      let output := reverseLocalRule fromNorth.2.1 (bottom.edges column) hagree
      exact ⟨output.northwest, output.west, by
        exact output.west_target⟩

noncomputable def reverseVerticalFin
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin (size + 1)) :
    ReverseVertical bottom column.val (by omega) := by
  let raw := reverseVertical bottom rightEdge hright
    (size - column.val) (by omega)
  refine ⟨raw.1, raw.2.1, ?_⟩
  rw [raw.2.2]
  congr 1
  apply Fin.ext
  have hcolumn := column.isLt
  change size - (size - column.val) = column.val
  omega

theorem reverseVertical_fst_congr
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    {leftOffset rightOffset : ℕ}
    (hleft : leftOffset ≤ size) (hrightOffset : rightOffset ≤ size)
    (hoffset : leftOffset = rightOffset) :
    (reverseVertical bottom rightEdge hright leftOffset hleft).1 =
      (reverseVertical bottom rightEdge hright rightOffset hrightOffset).1 := by
  subst rightOffset
  rfl

noncomputable def reverseCellOutput
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin size) :
    ReverseSquareOutput
      (reverseVerticalFin bottom rightEdge hright column.succ).1
      (bottom.vertices column.castSucc)
      (reverseVerticalFin bottom rightEdge hright column.succ).2.1.target := by
  let fromNorth := reverseVerticalFin bottom rightEdge hright column.succ
  have hnorthTarget : fromNorth.2.1.target = bottom.vertices column.succ := by
    rw [fromNorth.2.2]
  have hagree : fromNorth.2.1.target = (bottom.edges column).target :=
    hnorthTarget.trans (bottom.edge_target column).symm
  exact reverseLocalRule fromNorth.2.1 (bottom.edges column) hagree

noncomputable def reverseAtColumn
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : ℕ) (hcolumn : column ≤ size) :
    ReverseVertical bottom column hcolumn := by
  by_cases hlast : column = size
  · subst column
    exact ⟨rightBase, rightEdge, by
      change rightEdge.target = bottom.vertices (Fin.last size)
      exact hright⟩
  · have hlt : column < size := by omega
    let cell : Fin size := ⟨column, hlt⟩
    let fromNorth := reverseAtColumn bottom rightEdge hright
      (column + 1) (by omega)
    have hnorthTarget : fromNorth.2.1.target = bottom.vertices cell.succ := by
      rw [fromNorth.2.2]
      congr 1
    have hagree : fromNorth.2.1.target = (bottom.edges cell).target :=
      hnorthTarget.trans (bottom.edge_target cell).symm
    let output := reverseLocalRule fromNorth.2.1 (bottom.edges cell) hagree
    exact ⟨output.northwest, output.west, output.west_target⟩
termination_by size - column
decreasing_by omega

noncomputable def reverseCellOutputAt
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin size) :
    ReverseSquareOutput
      (reverseAtColumn bottom rightEdge hright (column.val + 1) (by omega)).1
      (bottom.vertices column.castSucc)
      (reverseAtColumn bottom rightEdge hright (column.val + 1) (by omega)).2.1.target := by
  let fromNorth := reverseAtColumn bottom rightEdge hright
    (column.val + 1) (by omega)
  have hnorthTarget : fromNorth.2.1.target = bottom.vertices column.succ := by
    rw [fromNorth.2.2]
    congr 1
  have hagree : fromNorth.2.1.target = (bottom.edges column).target :=
    hnorthTarget.trans (bottom.edge_target column).symm
  exact reverseLocalRule fromNorth.2.1 (bottom.edges column) hagree

theorem reverseAtColumn_eq_cell_northwest
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin size) :
    (reverseAtColumn bottom rightEdge hright column.val (by omega)).1 =
      (reverseCellOutputAt bottom rightEdge hright column).northwest := by
  rw [reverseAtColumn]
  simp only [dif_neg (by omega : ¬ column.val = size)]
  rfl

theorem reverseAtColumn_step_eq_cell_west
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin size) :
    (reverseAtColumn bottom rightEdge hright column.val (by omega)).2.1 =
      (reverseCellOutputAt bottom rightEdge hright column).west.castBase
        (reverseAtColumn_eq_cell_northwest bottom rightEdge hright column).symm := by
  apply GrowthStep.target_injective
  rw [GrowthStep.target_castBase]
  exact (reverseAtColumn bottom rightEdge hright column.val (by omega)).2.2.trans
    (reverseCellOutputAt bottom rightEdge hright column).west_target.symm

noncomputable def reverseBoundary
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size)) :
    ShapeBoundary size where
  vertices := fun column =>
    (reverseAtColumn bottom rightEdge hright column.val (by omega)).1
  edges := fun column =>
    (reverseCellOutputAt bottom rightEdge hright column).north.castBase
      (reverseAtColumn_eq_cell_northwest bottom rightEdge hright column).symm
  left_empty := by
    let vertical := reverseAtColumn bottom rightEdge hright 0 (by omega)
    have htarget : vertical.2.1.target = GrowthShape.empty (size + 1) :=
      vertical.2.2.trans bottom.left_empty
    exact vertical.2.1.base_eq_empty_of_target_eq_empty htarget
  edge_target := by
    intro column
    rw [GrowthStep.target_castBase]
    exact (reverseCellOutputAt bottom rightEdge hright column).north_target

theorem reverseBoundary_final_vertex
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size)) :
    (reverseBoundary bottom rightEdge hright).vertices (Fin.last size) = rightBase := by
  change (reverseAtColumn bottom rightEdge hright size (by omega)).1 = rightBase
  rw [reverseAtColumn]
  simp

noncomputable def reverseRowMarks
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size)) :
    Fin size → Bool := fun column =>
  (reverseCellOutputAt bottom rightEdge hright column).marked

theorem reverseBoundary_edge_stay_transition
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin size) :
    bottom.edges column = GrowthStep.stay ↔
      (reverseBoundary bottom rightEdge hright).edges column = GrowthStep.stay ∧
        reverseRowMarks bottom rightEdge hright column = false := by
  let fromNorth := reverseAtColumn bottom rightEdge hright
    (column.val + 1) (by omega)
  have hnorthTarget : fromNorth.2.1.target = bottom.vertices column.succ := by
    rw [fromNorth.2.2]
    congr 1
  have hagree : fromNorth.2.1.target = (bottom.edges column).target :=
    hnorthTarget.trans (bottom.edge_target column).symm
  have hlocal := reverseLocalRule_fromWest_stay_iff
    fromNorth.2.1 (bottom.edges column) hagree
  let output := reverseCellOutputAt bottom rightEdge hright column
  change bottom.edges column = GrowthStep.stay ↔
    output.north = GrowthStep.stay ∧ output.marked = false at hlocal
  have hcast := GrowthStep.castBase_eq_stay_iff
    (reverseAtColumn_eq_cell_northwest bottom rightEdge hright column).symm
    output.north
  change bottom.edges column = GrowthStep.stay ↔
    output.north.castBase
        (reverseAtColumn_eq_cell_northwest bottom rightEdge hright column).symm =
          GrowthStep.stay ∧ output.marked = false
  rw [hcast]
  exact hlocal

theorem reverseBoundary_edge_stay_of_marked
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin size)
    (hmarked : reverseRowMarks bottom rightEdge hright column = true) :
    (reverseBoundary bottom rightEdge hright).edges column = GrowthStep.stay := by
  let fromNorth := reverseAtColumn bottom rightEdge hright
    (column.val + 1) (by omega)
  have hnorthTarget : fromNorth.2.1.target = bottom.vertices column.succ := by
    rw [fromNorth.2.2]
    congr 1
  have hagree : fromNorth.2.1.target = (bottom.edges column).target :=
    hnorthTarget.trans (bottom.edge_target column).symm
  let output := reverseCellOutputAt bottom rightEdge hright column
  have houtputMarked : output.marked = true := hmarked
  have hstay := reverseLocalRule_north_stay_of_marked
    fromNorth.2.1 (bottom.edges column) hagree houtputMarked
  change output.north.castBase
    (reverseAtColumn_eq_cell_northwest bottom rightEdge hright column).symm =
      GrowthStep.stay
  exact (GrowthStep.castBase_eq_stay_iff _ _).mpr hstay

theorem ShapeBoundary.vertex_card_le_final
    {size : ℕ} (boundary : ShapeBoundary size)
    (column : Fin (size + 1)) :
    (boundary.vertices column).card ≤
      (boundary.vertices (Fin.last size)).card := by
  let P : (value : ℕ) → column.val ≤ value → Prop := fun value _ =>
    ∀ hvalue : value ≤ size,
      (boundary.vertices column).card ≤
        (boundary.vertices ⟨value, by omega⟩).card
  have hbase : P column.val le_rfl := by
    intro hcolumn
    have heq : (⟨column.val, by omega⟩ : Fin (size + 1)) = column := Fin.ext rfl
    simp [heq]
  have hstep : ∀ value (hleft : column.val ≤ value),
      P value hleft → P (value + 1) (by omega) := by
    intro value hleft hinduction hvalue
    have hprev : value ≤ size := by omega
    let edge : Fin size := ⟨value, by omega⟩
    have hedge := (boundary.edges edge).base_card_le_target
    rw [boundary.edge_target] at hedge
    have hpast := hinduction hprev
    exact hpast.trans hedge
  have hfinal := Nat.le_induction (P := P) hbase hstep size (by omega) le_rfl
  have hindex : (⟨size, by omega⟩ : Fin (size + 1)) = Fin.last size := Fin.ext rfl
  rw [hindex] at hfinal
  exact hfinal

theorem ShapeBoundary.edge_stay_of_final_empty
    {size : ℕ} (boundary : ShapeBoundary size)
    (hfinal : boundary.vertices (Fin.last size) = GrowthShape.empty (size + 1))
    (column : Fin size) :
    boundary.edges column = GrowthStep.stay := by
  cases hedge : boundary.edges column with
  | stay => rfl
  | add row hadd =>
      have hpositive : 0 < (boundary.vertices column.succ).card := by
        have htarget := boundary.edge_target column
        rw [hedge] at htarget
        have hcard := congrArg GrowthShape.card htarget
        simp at hcard
        omega
      have hmono := boundary.vertex_card_le_final column.succ
      have hfinalCard : (boundary.vertices (Fin.last size)).card = 0 := by
        rw [hfinal]
        simp [GrowthShape.card, GrowthShape.empty]
      rw [hfinalCard] at hmono
      omega

theorem ShapeBoundary.vertex_eq_empty_of_final_empty
    {size : ℕ} (boundary : ShapeBoundary size)
    (hfinal : boundary.vertices (Fin.last size) = GrowthShape.empty (size + 1))
    (column : Fin (size + 1)) :
    boundary.vertices column = GrowthShape.empty (size + 1) := by
  have hmono := boundary.vertex_card_le_final column
  have hfinalCard : (boundary.vertices (Fin.last size)).card = 0 := by
    rw [hfinal]
    simp [GrowthShape.card, GrowthShape.empty]
  rw [hfinalCard] at hmono
  exact (boundary.vertices column).eq_empty_of_card_eq_zero (by omega)

theorem reverseAtColumn_stay_transition
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin size) :
    (reverseAtColumn bottom rightEdge hright (column.val + 1) (by omega)).2.1 =
        GrowthStep.stay ↔
      (reverseAtColumn bottom rightEdge hright column.val (by omega)).2.1 =
          GrowthStep.stay ∧
        reverseRowMarks bottom rightEdge hright column = false := by
  let fromNorth := reverseAtColumn bottom rightEdge hright
    (column.val + 1) (by omega)
  let output := reverseCellOutputAt bottom rightEdge hright column
  have hlocal := reverseLocalRule_fromNorth_stay_iff
    fromNorth.2.1 (bottom.edges column)
      (by
        have hnorth : fromNorth.2.1.target = bottom.vertices column.succ := by
          rw [fromNorth.2.2]
          congr 1
        exact hnorth.trans (bottom.edge_target column).symm)
  have hleft := reverseAtColumn_step_eq_cell_west bottom rightEdge hright column
  have hcast := GrowthStep.castBase_eq_stay_iff
    (reverseAtColumn_eq_cell_northwest bottom rightEdge hright column).symm
    output.west
  change fromNorth.2.1 = GrowthStep.stay ↔ _
  rw [hlocal]
  change output.west = GrowthStep.stay ∧ output.marked = false ↔ _
  rw [← hcast, ← hleft]
  rfl

theorem reverseAtColumn_stay_of_marked
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (column : Fin size)
    (hmarked : reverseRowMarks bottom rightEdge hright column = true) :
    (reverseAtColumn bottom rightEdge hright column.val (by omega)).2.1 =
      GrowthStep.stay := by
  let fromNorth := reverseAtColumn bottom rightEdge hright
    (column.val + 1) (by omega)
  let output := reverseCellOutputAt bottom rightEdge hright column
  have houtputMarked : output.marked = true := hmarked
  have hstay := reverseLocalRule_west_stay_of_marked
    fromNorth.2.1 (bottom.edges column)
      (by
        have hnorth : fromNorth.2.1.target = bottom.vertices column.succ := by
          rw [fromNorth.2.2]
          congr 1
        exact hnorth.trans (bottom.edge_target column).symm)
      houtputMarked
  have hcast := (GrowthStep.castBase_eq_stay_iff
    (reverseAtColumn_eq_cell_northwest bottom rightEdge hright column).symm
    output.west).mpr hstay
  exact (reverseAtColumn_step_eq_cell_west bottom rightEdge hright column).trans hcast

theorem reverseAtColumn_zero_stay
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size)) :
    (reverseAtColumn bottom rightEdge hright 0 (by omega)).2.1 = GrowthStep.stay := by
  have htarget :
      (reverseAtColumn bottom rightEdge hright 0 (by omega)).2.1.target =
        GrowthShape.empty (size + 1) :=
    (reverseAtColumn bottom rightEdge hright 0 (by omega)).2.2.trans bottom.left_empty
  exact GrowthStep.eq_stay_of_target_eq_empty _ htarget

theorem reverseAtColumn_last_base
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size)) :
    (reverseAtColumn bottom rightEdge hright size le_rfl).1 = rightBase := by
  unfold reverseAtColumn
  simp

theorem reverseAtColumn_last_step
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size)) :
    (reverseAtColumn bottom rightEdge hright size le_rfl).2.1 =
      rightEdge.castBase (reverseAtColumn_last_base bottom rightEdge hright).symm := by
  apply GrowthStep.target_injective
  rw [GrowthStep.target_castBase]
  exact (reverseAtColumn bottom rightEdge hright size le_rfl).2.2.trans hright.symm

theorem reverseRowMarks_existsUnique
    {size : ℕ} (bottom : ShapeBoundary size)
    {rightBase : GrowthShape (size + 1)} (rightEdge : GrowthStep rightBase)
    (hright : rightEdge.target = bottom.vertices (Fin.last size))
    (hrightNonstay : rightEdge ≠ GrowthStep.stay) :
    ∃! column : Fin size, reverseRowMarks bottom rightEdge hright column = true := by
  have hexists : ∃ column : Fin size,
      reverseRowMarks bottom rightEdge hright column = true := by
    by_contra hnone
    push Not at hnone
    have hstay : ∀ (column : ℕ) (hcolumn : column ≤ size),
        (reverseAtColumn bottom rightEdge hright column hcolumn).2.1 =
          GrowthStep.stay := by
      intro column hcolumn
      induction column with
      | zero => exact reverseAtColumn_zero_stay bottom rightEdge hright
      | succ column ih =>
          have hlt : column < size := by omega
          let cell : Fin size := ⟨column, hlt⟩
          have hmarkFalse : reverseRowMarks bottom rightEdge hright cell = false := by
            cases hmark : reverseRowMarks bottom rightEdge hright cell with
            | false => rfl
            | true => exact (hnone cell hmark).elim
          exact (reverseAtColumn_stay_transition bottom rightEdge hright cell).mpr
            ⟨ih (by omega), hmarkFalse⟩
    have hlast := hstay size le_rfl
    rw [reverseAtColumn_last_step,
      GrowthStep.castBase_eq_stay_iff] at hlast
    exact hrightNonstay hlast
  obtain ⟨chosen, hchosen⟩ := hexists
  refine ⟨chosen, hchosen, ?_⟩
  intro other hother
  have noTwo : ∀ {left right : Fin size}, left.val < right.val →
      reverseRowMarks bottom rightEdge hright left = true →
      reverseRowMarks bottom rightEdge hright right = true → False := by
    intro left right hleftRight hleftMark hrightMark
    have hbase :
        (reverseAtColumn bottom rightEdge hright (left.val + 1) (by omega)).2.1 ≠
          GrowthStep.stay := by
      intro hstayNext
      have htransition :=
        (reverseAtColumn_stay_transition bottom rightEdge hright left).mp hstayNext
      rw [hleftMark] at htransition
      cases htransition.2
    let P : (column : ℕ) → left.val + 1 ≤ column → Prop := fun column _ =>
      ∀ hcolumn : column ≤ size,
        (reverseAtColumn bottom rightEdge hright column hcolumn).2.1 ≠
          GrowthStep.stay
    have hbaseP : P (left.val + 1) (by omega) := by
      intro hcolumn
      simpa only using hbase
    have hstepP : ∀ column (hleft : left.val + 1 ≤ column),
        P column hleft → P (column + 1) (by omega) := by
      intro column hleft hinduction hupper
      have hcolumnLt : column < size := by omega
      let cell : Fin size := ⟨column, hcolumnLt⟩
      intro hstayNext
      have htransition :=
        (reverseAtColumn_stay_transition bottom rightEdge hright cell).mp hstayNext
      exact (hinduction (by omega)) htransition.1
    have hpropagate : P right.val (by omega) :=
      Nat.le_induction (P := P) hbaseP hstepP right.val (by omega)
    have hrightNonstayAt := hpropagate right.isLt.le
    have hrightStayAt := reverseAtColumn_stay_of_marked
      bottom rightEdge hright right hrightMark
    exact hrightNonstayAt hrightStayAt
  by_contra hne
  have hvalne : other.val ≠ chosen.val := by
    intro hval
    exact hne (Fin.ext hval)
  rcases lt_or_gt_of_ne hvalne with hlt | hgt
  · exact (noTwo hlt hother hchosen).elim
  · exact (noTwo hgt hchosen hother).elim

end FibonacciRibbonKernel
