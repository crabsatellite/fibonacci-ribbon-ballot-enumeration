import FibonacciRibbonKernel.RSKLocalRule
import Mathlib.GroupTheory.Perm.Basic

namespace FibonacciRibbonKernel

/-!
# Symmetric RSK growth diagrams for permutations

The relation below is the complete local rule, stated without an orientation
bias.  Consequently transposing a valid diagram for a permutation gives a
valid diagram for the inverse permutation.  Existence and reverse uniqueness
are proved in the subsequent producer layer.
-/

inductive LocalGrowthRule {height : ℕ} (marked : Prop) :
    GrowthShape height → GrowthShape height →
      GrowthShape height → GrowthShape height → Type where
  | stay (base : GrowthShape height) (hunmarked : ¬ marked) :
      LocalGrowthRule marked base base base base
  | mark (base : GrowthShape height) (hmarked : marked)
      (hheight : 0 < height) :
      LocalGrowthRule marked base base base
        (base.add ⟨0, hheight⟩ (Or.inl rfl))
  | northOnly (base : GrowthShape height) (hunmarked : ¬ marked)
      (row : Fin height) (hadd : base.Addable row) :
      LocalGrowthRule marked base (base.add row hadd) base (base.add row hadd)
  | westOnly (base : GrowthShape height) (hunmarked : ¬ marked)
      (row : Fin height) (hadd : base.Addable row) :
      LocalGrowthRule marked base base (base.add row hadd) (base.add row hadd)
  | distinct (base : GrowthShape height) (hunmarked : ¬ marked)
      (northRow westRow : Fin height)
      (hnorth : base.Addable northRow) (hwest : base.Addable westRow)
      (hne : northRow ≠ westRow) :
      LocalGrowthRule marked base (base.add northRow hnorth)
        (base.add westRow hwest)
        ((base.add northRow hnorth).add westRow
          (base.addable_after_add_of_ne northRow westRow hnorth hwest
            (Ne.symm hne)))
  | distinctWestFirst (base : GrowthShape height) (hunmarked : ¬ marked)
      (northRow westRow : Fin height)
      (hnorth : base.Addable northRow) (hwest : base.Addable westRow)
      (hne : northRow ≠ westRow) :
      LocalGrowthRule marked base (base.add northRow hnorth)
        (base.add westRow hwest)
        ((base.add westRow hwest).add northRow
          (base.addable_after_add_of_ne westRow northRow hwest hnorth hne))
  | repeated (base : GrowthShape height) (hunmarked : ¬ marked)
      (row : Fin height) (hadd : base.Addable row)
      (hnext : row.val + 1 < height) :
      LocalGrowthRule marked base (base.add row hadd) (base.add row hadd)
        ((base.add row hadd).add ⟨row.val + 1, hnext⟩
          (base.next_addable_after_same row hadd hnext))

noncomputable def LocalGrowthRule.congr_mark
    {height : ℕ} {leftMark rightMark : Prop}
    (hmark : leftMark ↔ rightMark)
    {northwest northeast southwest southeast : GrowthShape height}
    (rule : LocalGrowthRule leftMark northwest northeast southwest southeast) :
    LocalGrowthRule rightMark northwest northeast southwest southeast := by
  cases rule with
  | stay hunmarked =>
      exact .stay _ (fun h => hunmarked (hmark.mpr h))
  | mark hmarked hheight =>
      exact .mark _ (hmark.mp hmarked) hheight
  | northOnly hunmarked row hadd =>
      exact .northOnly _ (fun h => hunmarked (hmark.mpr h)) row hadd
  | westOnly hunmarked row hadd =>
      exact .westOnly _ (fun h => hunmarked (hmark.mpr h)) row hadd
  | distinct hunmarked northRow westRow hnorth hwest hne =>
      exact .distinct _ (fun h => hunmarked (hmark.mpr h))
        northRow westRow hnorth hwest hne
  | distinctWestFirst hunmarked northRow westRow hnorth hwest hne =>
      exact .distinctWestFirst _ (fun h => hunmarked (hmark.mpr h))
        northRow westRow hnorth hwest hne
  | repeated hunmarked row hadd hnext =>
      exact .repeated _ (fun h => hunmarked (hmark.mpr h)) row hadd hnext

noncomputable def LocalGrowthRule.transpose
    {height : ℕ} {marked : Prop}
    {northwest northeast southwest southeast : GrowthShape height}
    (rule : LocalGrowthRule marked northwest northeast southwest southeast) :
    LocalGrowthRule marked northwest southwest northeast southeast := by
  cases rule with
  | stay hunmarked => exact .stay _ hunmarked
  | mark hmarked hheight => exact .mark _ hmarked hheight
  | northOnly hunmarked row hadd => exact .westOnly _ hunmarked row hadd
  | westOnly hunmarked row hadd => exact .northOnly _ hunmarked row hadd
  | distinct hunmarked northRow westRow hnorth hwest hne =>
      exact .distinctWestFirst _ hunmarked westRow northRow hwest hnorth (Ne.symm hne)
  | distinctWestFirst hunmarked northRow westRow hnorth hwest hne =>
      exact .distinct _ hunmarked westRow northRow hwest hnorth (Ne.symm hne)
  | repeated hunmarked row hadd hnext =>
      exact .repeated _ hunmarked row hadd hnext

noncomputable def LocalGrowthRule.transport
    {height : ℕ} {marked : Prop}
    {northwest northeast southwest southeast : GrowthShape height}
    {northwest' northeast' southwest' southeast' : GrowthShape height}
    (rule : LocalGrowthRule marked northwest northeast southwest southeast)
    (hnorthwest : northwest = northwest')
    (hnortheast : northeast = northeast')
    (hsouthwest : southwest = southwest')
    (hsoutheast : southeast = southeast') :
    LocalGrowthRule marked northwest' northeast' southwest' southeast' := by
  subst northwest'
  subst northeast'
  subst southwest'
  subst southeast'
  exact rule

noncomputable def applyLocalRule_satisfies_relation
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (input : GrowthSquareInput north west marked) :
    LocalGrowthRule marked base north.target west.target
      (applyLocalRule north west marked input).fromNorth.target := by
  cases north with
  | stay =>
      cases west with
      | stay =>
          by_cases hmarked : marked
          · rw [applyLocalRule_stay_stay_of_marked input hmarked]
            rw [localStayStayMarked_fromNorth_target]
            exact LocalGrowthRule.mark base hmarked (input.height_pos hmarked)
          · rw [applyLocalRule_stay_stay_of_unmarked input hmarked]
            rw [localStayStayUnmarked_fromNorth_target]
            exact LocalGrowthRule.stay base hmarked
      | add westRow hwest =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.2
          exact .westOnly base hunmarked westRow hwest
  | add northRow hnorth =>
      cases west with
      | stay =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          exact .northOnly base hunmarked northRow hnorth
      | add westRow hwest =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          by_cases hrows : northRow = westRow
          · subst westRow
            let hnext := input.repeated_has_next northRow hnorth hwest rfl rfl
            rw [applyLocalRule_repeated]
            rw [localRepeatedAdd_fromNorth_target]
            exact LocalGrowthRule.repeated base hunmarked northRow hnorth
              hnext
          · rw [applyLocalRule_distinct northRow westRow hnorth hwest hrows input]
            rw [localDistinctAdds_fromNorth_target]
            exact LocalGrowthRule.distinct base hunmarked northRow westRow
              hnorth hwest hrows

structure LocalForwardWitness
    {height : ℕ} (marked : Prop)
    (northwest northeast southwest southeast : GrowthShape height) where
  north : GrowthStep northwest
  west : GrowthStep northwest
  northeast_eq : north.target = northeast
  southwest_eq : west.target = southwest
  input : GrowthSquareInput north west marked
  southeast_eq : (applyLocalRule north west marked input).fromNorth.target = southeast

def AdmissibleLocalInput
    {height : ℕ} (marked : Prop) (base : GrowthShape height) :=
  PSigma fun north : GrowthStep base =>
    PSigma fun west : GrowthStep base => GrowthSquareInput north west marked

noncomputable def AdmissibleLocalInput.southeast
    {height : ℕ} {marked : Prop} {base : GrowthShape height}
    (input : AdmissibleLocalInput marked base) : GrowthShape height :=
  (applyLocalRule input.1 input.2.1 marked input.2.2).fromNorth.target

def LocalForwardWitness.toAdmissibleInput
    {height : ℕ} {marked : Prop}
    {northwest northeast southwest southeast : GrowthShape height}
    (witness : LocalForwardWitness marked northwest northeast southwest southeast) :
    AdmissibleLocalInput marked northwest :=
  ⟨witness.north, witness.west, witness.input⟩

noncomputable def LocalGrowthRule.forward_witness
    {height : ℕ} {marked : Prop}
    {northwest northeast southwest southeast : GrowthShape height}
    (rule : LocalGrowthRule marked northwest northeast southwest southeast) :
    LocalForwardWitness marked northwest northeast southwest southeast := by
  cases rule with
  | stay hunmarked =>
      let input := unmarkedGrowthSquareInput
        (GrowthStep.stay : GrowthStep northwest) GrowthStep.stay marked hunmarked
        (by intro row hnorth hwest hnorthEq hwestEq; cases hnorthEq)
      refine ⟨.stay, .stay, rfl, rfl, input, ?_⟩
      rw [applyLocalRule_stay_stay_of_unmarked input hunmarked]
      rfl
  | mark hmarked hheight =>
      let input := markedStayGrowthSquareInput (base := northwest)
        marked hmarked hheight
      refine ⟨.stay, .stay, rfl, rfl, input, ?_⟩
      rw [applyLocalRule_stay_stay_of_marked input hmarked]
      rfl
  | northOnly hunmarked row hadd =>
      let input := unmarkedGrowthSquareInput
        (GrowthStep.add row hadd : GrowthStep northwest) GrowthStep.stay
        marked hunmarked
        (by intro query hnorth hwest hnorthEq hwestEq; cases hwestEq)
      refine ⟨.add row hadd, .stay, rfl, rfl, input, ?_⟩
      rw [applyLocalRule_add_stay]
      rfl
  | westOnly hunmarked row hadd =>
      let input := unmarkedGrowthSquareInput
        (GrowthStep.stay : GrowthStep northwest) (GrowthStep.add row hadd)
        marked hunmarked
        (by intro query hnorth hwest hnorthEq hwestEq; cases hnorthEq)
      refine ⟨.stay, .add row hadd, rfl, rfl, input, ?_⟩
      rw [applyLocalRule_stay_add]
      rfl
  | distinct hunmarked northRow westRow hnorth hwest hne =>
      let input := unmarkedGrowthSquareInput
        (GrowthStep.add northRow hnorth : GrowthStep northwest)
        (GrowthStep.add westRow hwest) marked hunmarked
        (by
          intro query hqueryNorth hqueryWest hnorthEq hwestEq
          cases hnorthEq
          cases hwestEq
          exact (hne rfl).elim)
      refine ⟨.add northRow hnorth, .add westRow hwest,
        rfl, rfl, input, ?_⟩
      rw [applyLocalRule_distinct northRow westRow hnorth hwest hne input]
      rfl
  | distinctWestFirst hunmarked northRow westRow hnorth hwest hne =>
      let input := unmarkedGrowthSquareInput
        (GrowthStep.add northRow hnorth : GrowthStep northwest)
        (GrowthStep.add westRow hwest) marked hunmarked
        (by
          intro query hqueryNorth hqueryWest hnorthEq hwestEq
          cases hnorthEq
          cases hwestEq
          exact (hne rfl).elim)
      refine ⟨.add northRow hnorth, .add westRow hwest,
        rfl, rfl, input, ?_⟩
      rw [applyLocalRule_distinct northRow westRow hnorth hwest hne input,
        localDistinctAdds_fromNorth_target]
      exact northwest.add_comm northRow westRow hnorth hwest hne
  | repeated hunmarked row hadd hnext =>
      let input := unmarkedGrowthSquareInput
        (GrowthStep.add row hadd : GrowthStep northwest)
        (GrowthStep.add row hadd) marked hunmarked
        (by
          intro query hqueryNorth hqueryWest hnorthEq hwestEq
          cases hnorthEq
          exact hnext)
      refine ⟨.add row hadd, .add row hadd, rfl, rfl, input, ?_⟩
      rw [applyLocalRule_repeated]
      rfl

theorem LocalGrowthRule.southeast_unique
    {height : ℕ} {marked : Prop}
    {northwest northeast southwest southeastLeft southeastRight : GrowthShape height}
    (left : LocalGrowthRule marked northwest northeast southwest southeastLeft)
    (right : LocalGrowthRule marked northwest northeast southwest southeastRight) :
    southeastLeft = southeastRight := by
  rcases left.forward_witness with
    ⟨leftNorth, leftWest, leftNorthEq, leftWestEq, leftInput, leftSoutheastEq⟩
  rcases right.forward_witness with
    ⟨rightNorth, rightWest, rightNorthEq, rightWestEq, rightInput, rightSoutheastEq⟩
  have hnorth : leftNorth = rightNorth :=
    GrowthStep.target_injective
      (leftNorthEq.trans rightNorthEq.symm)
  subst rightNorth
  have hwest : leftWest = rightWest :=
    GrowthStep.target_injective
      (leftWestEq.trans rightWestEq.symm)
  subst rightWest
  have hinput : leftInput = rightInput := Subsingleton.elim _ _
  subst rightInput
  exact leftSoutheastEq.symm.trans rightSoutheastEq

theorem LocalGrowthRule.card_balance_of_unmarked
    {height : ℕ} {marked : Prop}
    {northwest northeast southwest southeast : GrowthShape height}
    (rule : LocalGrowthRule marked northwest northeast southwest southeast)
    (hunmarked : ¬ marked) :
    southeast.card + northwest.card = northeast.card + southwest.card := by
  cases rule with
  | stay _ => simp
  | mark hmarked _ => exact (hunmarked hmarked).elim
  | northOnly _ _ _ => simp
  | westOnly _ _ _ => simp; omega
  | distinct _ _ _ _ _ _ => simp; omega
  | distinctWestFirst _ _ _ _ _ _ => simp; omega
  | repeated _ _ _ _ => simp; omega

structure PermutationGrowthDiagram (size : ℕ)
    (permutation : Equiv.Perm (Fin size)) where
  shapes : Fin (size + 1) → Fin (size + 1) → GrowthShape (size + 1)
  top_empty : ∀ column, shapes 0 column = GrowthShape.empty (size + 1)
  left_empty : ∀ row, shapes row 0 = GrowthShape.empty (size + 1)
  local_rule : ∀ row column : Fin size,
    LocalGrowthRule (permutation row = column)
      (shapes row.castSucc column.castSucc)
      (shapes row.castSucc column.succ)
      (shapes row.succ column.castSucc)
      (shapes row.succ column.succ)

noncomputable def PermutationGrowthDiagram.transpose
    {size : ℕ} {permutation : Equiv.Perm (Fin size)}
    (diagram : PermutationGrowthDiagram size permutation) :
    PermutationGrowthDiagram size permutation.symm where
  shapes := fun row column => diagram.shapes column row
  top_empty := diagram.left_empty
  left_empty := diagram.top_empty
  local_rule := by
    intro row column
    have hmark : permutation.symm row = column ↔ permutation column = row := by
      simpa [eq_comm] using
        (permutation.symm_apply_eq : permutation.symm row = column ↔ row = permutation column)
    exact (diagram.local_rule column row).transpose.congr_mark hmark.symm

@[simp] theorem PermutationGrowthDiagram.transpose_transpose_shapes
    {size : ℕ} {permutation : Equiv.Perm (Fin size)}
    (diagram : PermutationGrowthDiagram size permutation)
    (row column : Fin (size + 1)) :
    diagram.transpose.transpose.shapes row column = diagram.shapes row column := rfl

theorem PermutationGrowthDiagram.shapes_unique
    {size : ℕ} {permutation : Equiv.Perm (Fin size)}
    (left right : PermutationGrowthDiagram size permutation) :
    left.shapes = right.shapes := by
  funext row column
  have aux : ∀ total : ℕ, ∀ row column : Fin (size + 1),
      row.val + column.val = total →
      left.shapes row column = right.shapes row column := by
    intro total
    induction total using Nat.strong_induction_on with
    | h total ih =>
        intro row column htotal
        by_cases hrowZero : row.val = 0
        · have hrow : row = 0 := Fin.ext hrowZero
          subst row
          rw [left.top_empty, right.top_empty]
        · by_cases hcolumnZero : column.val = 0
          · have hcolumn : column = 0 := Fin.ext hcolumnZero
            subst column
            rw [left.left_empty, right.left_empty]
          · let cellRow : Fin size := ⟨row.val - 1, by omega⟩
            let cellColumn : Fin size := ⟨column.val - 1, by omega⟩
            have hrow : cellRow.succ = row := by
              apply Fin.ext
              simp [cellRow]
              omega
            have hcolumn : cellColumn.succ = column := by
              apply Fin.ext
              simp [cellColumn]
              omega
            have hnorthwest := ih
              (cellRow.castSucc.val + cellColumn.castSucc.val)
              (by simp [cellRow, cellColumn]; omega)
              cellRow.castSucc cellColumn.castSucc rfl
            have hnortheast := ih
              (cellRow.castSucc.val + cellColumn.succ.val)
              (by simp [cellRow, cellColumn]; omega)
              cellRow.castSucc cellColumn.succ rfl
            have hsouthwest := ih
              (cellRow.succ.val + cellColumn.castSucc.val)
              (by simp [cellRow, cellColumn]; omega)
              cellRow.succ cellColumn.castSucc rfl
            have rightRule :
                LocalGrowthRule (permutation cellRow = cellColumn)
                  (left.shapes cellRow.castSucc cellColumn.castSucc)
                  (left.shapes cellRow.castSucc cellColumn.succ)
                  (left.shapes cellRow.succ cellColumn.castSucc)
                  (right.shapes cellRow.succ cellColumn.succ) := by
              simpa only [hnorthwest, hnortheast, hsouthwest] using
                right.local_rule cellRow cellColumn
            have hsoutheast := LocalGrowthRule.southeast_unique
              (left.local_rule cellRow cellColumn) rightRule
            rw [hrow, hcolumn] at hsoutheast
            exact hsoutheast
  exact aux (row.val + column.val) row column rfl

end FibonacciRibbonKernel
