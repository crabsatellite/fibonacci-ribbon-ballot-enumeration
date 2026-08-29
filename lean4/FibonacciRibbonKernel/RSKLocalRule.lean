import FibonacciRibbonKernel.RSKGrowthShapes

namespace FibonacciRibbonKernel

/-!
# The symmetric local cases of the RSK growth rule

`GrowthStep base` is either a stationary Young-lattice edge or one legal
outer-corner addition.  Each definition below fills the southeast corner of a
growth-diagram square and supplies the two outgoing edges.  These are the five
literal cases of Fomin's symmetric local rule.
-/

inductive GrowthStep {height : ℕ} (base : GrowthShape height) where
  | stay : GrowthStep base
  | add (row : Fin height) (hadd : base.Addable row) : GrowthStep base

noncomputable def GrowthStep.target
    {height : ℕ} {base : GrowthShape height} :
    GrowthStep base → GrowthShape height
  | .stay => base
  | .add row hadd => base.add row hadd

@[simp] theorem GrowthStep.target_stay
    {height : ℕ} (base : GrowthShape height) :
    (GrowthStep.stay : GrowthStep base).target = base := rfl

@[simp] theorem GrowthStep.target_add
    {height : ℕ} (base : GrowthShape height)
    (row : Fin height) (hadd : base.Addable row) :
    (GrowthStep.add row hadd : GrowthStep base).target = base.add row hadd := rfl

theorem GrowthStep.target_injective
    {height : ℕ} {base : GrowthShape height} :
    Function.Injective (@GrowthStep.target height base) := by
  intro left right heq
  cases left with
  | stay =>
      cases right with
      | stay => rfl
      | add row hadd =>
          exact absurd heq.symm (base.add_ne row hadd)
  | add leftRow hleft =>
      cases right with
      | stay =>
          exact absurd heq (base.add_ne leftRow hleft)
      | add rightRow hright =>
          have hrow := base.add_injective_row hleft hright heq
          subst rightRow
          rfl

def GrowthStep.castBase
    {height : ℕ} {left right : GrowthShape height}
    (heq : left = right) (step : GrowthStep left) : GrowthStep right :=
  heq ▸ step

theorem GrowthStep.castBase_eq_stay_iff
    {height : ℕ} {left right : GrowthShape height}
    (heq : left = right) (step : GrowthStep left) :
    step.castBase heq = GrowthStep.stay ↔ step = GrowthStep.stay := by
  subst right
  rfl

def GrowthStep.addedRow?
    {height : ℕ} {base : GrowthShape height} :
    GrowthStep base → Option (Fin height)
  | .stay => none
  | .add row _ => some row

@[simp] theorem GrowthStep.addedRow?_castBase
    {height : ℕ} {left right : GrowthShape height}
    (heq : left = right) (step : GrowthStep left) :
    (step.castBase heq).addedRow? = step.addedRow? := by
  subst right
  rfl

@[simp] theorem GrowthStep.target_castBase
    {height : ℕ} {left right : GrowthShape height}
    (heq : left = right) (step : GrowthStep left) :
    (step.castBase heq).target = step.target := by
  subst right
  rfl

theorem GrowthStep.target_card_le
    {height : ℕ} {base : GrowthShape height}
    (step : GrowthStep base) :
    step.target.card ≤ base.card + 1 := by
  cases step with
  | stay => simp
  | add row hadd => simp

theorem GrowthStep.base_card_le_target
    {height : ℕ} {base : GrowthShape height}
    (step : GrowthStep base) :
    base.card ≤ step.target.card := by
  cases step with
  | stay => simp
  | add row hadd => simp

theorem GrowthStep.base_eq_empty_of_target_eq_empty
    {height : ℕ} {base : GrowthShape height} (step : GrowthStep base)
    (hempty : step.target = GrowthShape.empty height) :
    base = GrowthShape.empty height := by
  cases step with
  | stay => exact hempty
  | add row hadd =>
      have hrow := congrArg (fun shape : GrowthShape height => shape.rows row) hempty
      simp [GrowthShape.empty] at hrow

theorem GrowthStep.eq_stay_of_target_eq_empty
    {height : ℕ} {base : GrowthShape height} (step : GrowthStep base)
    (hempty : step.target = GrowthShape.empty height) :
    step = GrowthStep.stay := by
  cases step with
  | stay => rfl
  | add row hadd =>
      have hrow := congrArg (fun shape : GrowthShape height => shape.rows row) hempty
      simp [GrowthShape.empty] at hrow

structure GrowthSquareOutput
    {height : ℕ} {northwest : GrowthShape height}
    (north west : GrowthStep northwest) where
  fromNorth : GrowthStep north.target
  fromWest : GrowthStep west.target
  southeast_agrees : fromNorth.target = fromWest.target

noncomputable def localStayStayUnmarked
    {height : ℕ} (base : GrowthShape height) :
    GrowthSquareOutput (GrowthStep.stay : GrowthStep base)
      (GrowthStep.stay : GrowthStep base) where
  fromNorth := .stay
  fromWest := .stay
  southeast_agrees := rfl

noncomputable def localStayStayMarked
    {height : ℕ} (base : GrowthShape height) (hheight : 0 < height) :
    GrowthSquareOutput (GrowthStep.stay : GrowthStep base)
      (GrowthStep.stay : GrowthStep base) := by
  let row : Fin height := ⟨0, hheight⟩
  let hadd : base.Addable row := Or.inl rfl
  exact
    { fromNorth := .add row hadd
      fromWest := .add row hadd
      southeast_agrees := rfl }

noncomputable def localAddStay
    {height : ℕ} (base : GrowthShape height)
    (row : Fin height) (hadd : base.Addable row) :
    GrowthSquareOutput (GrowthStep.add row hadd : GrowthStep base)
      (GrowthStep.stay : GrowthStep base) where
  fromNorth := .stay
  fromWest := .add row hadd
  southeast_agrees := rfl

noncomputable def localStayAdd
    {height : ℕ} (base : GrowthShape height)
    (row : Fin height) (hadd : base.Addable row) :
    GrowthSquareOutput (GrowthStep.stay : GrowthStep base)
      (GrowthStep.add row hadd : GrowthStep base) where
  fromNorth := .add row hadd
  fromWest := .stay
  southeast_agrees := rfl

noncomputable def localDistinctAdds
    {height : ℕ} (base : GrowthShape height)
    (northRow westRow : Fin height)
    (hnorth : base.Addable northRow) (hwest : base.Addable westRow)
    (hne : northRow ≠ westRow) :
    GrowthSquareOutput (GrowthStep.add northRow hnorth : GrowthStep base)
      (GrowthStep.add westRow hwest : GrowthStep base) := by
  let hwestAfter : (base.add northRow hnorth).Addable westRow :=
    base.addable_after_add_of_ne northRow westRow hnorth hwest (Ne.symm hne)
  let hnorthAfter : (base.add westRow hwest).Addable northRow :=
    base.addable_after_add_of_ne westRow northRow hwest hnorth hne
  exact
    { fromNorth := .add westRow hwestAfter
      fromWest := .add northRow hnorthAfter
      southeast_agrees := base.add_comm northRow westRow hnorth hwest hne }

noncomputable def localRepeatedAdd
    {height : ℕ} (base : GrowthShape height)
    (row : Fin height) (hadd : base.Addable row)
    (hnext : row.val + 1 < height) :
    GrowthSquareOutput (GrowthStep.add row hadd : GrowthStep base)
      (GrowthStep.add row hadd : GrowthStep base) := by
  let next : Fin height := ⟨row.val + 1, hnext⟩
  let hnextAddable : (base.add row hadd).Addable next :=
    base.next_addable_after_same row hadd hnext
  exact
    { fromNorth := .add next hnextAddable
      fromWest := .add next hnextAddable
      southeast_agrees := rfl }

@[simp] theorem localStayStayUnmarked_fromNorth_target
    {height : ℕ} (base : GrowthShape height) :
    (localStayStayUnmarked base).fromNorth.target = base := rfl

@[simp] theorem localStayStayMarked_fromNorth_target
    {height : ℕ} (base : GrowthShape height) (hheight : 0 < height) :
    (localStayStayMarked base hheight).fromNorth.target =
      base.add ⟨0, hheight⟩ (Or.inl rfl) := rfl

@[simp] theorem localDistinctAdds_fromNorth_target
    {height : ℕ} (base : GrowthShape height)
    (northRow westRow : Fin height)
    (hnorth : base.Addable northRow) (hwest : base.Addable westRow)
    (hne : northRow ≠ westRow) :
    (localDistinctAdds base northRow westRow hnorth hwest hne).fromNorth.target =
      (base.add northRow hnorth).add westRow
        (base.addable_after_add_of_ne northRow westRow hnorth hwest
          (Ne.symm hne)) := rfl

@[simp] theorem localRepeatedAdd_fromNorth_target
    {height : ℕ} (base : GrowthShape height)
    (row : Fin height) (hadd : base.Addable row)
    (hnext : row.val + 1 < height) :
    (localRepeatedAdd base row hadd hnext).fromNorth.target =
      (base.add row hadd).add ⟨row.val + 1, hnext⟩
        (base.next_addable_after_same row hadd hnext) := rfl

/-- Swapping north and west in the distinct-addition case leaves the same
southeast shape. -/
theorem localDistinctAdds_southeast_symmetric
    {height : ℕ} (base : GrowthShape height)
    (northRow westRow : Fin height)
    (hnorth : base.Addable northRow) (hwest : base.Addable westRow)
    (hne : northRow ≠ westRow) :
    (localDistinctAdds base northRow westRow hnorth hwest hne).fromNorth.target =
      (localDistinctAdds base westRow northRow hwest hnorth (Ne.symm hne)).fromNorth.target := by
  let hwestAfter : (base.add northRow hnorth).Addable westRow :=
    base.addable_after_add_of_ne northRow westRow hnorth hwest (Ne.symm hne)
  let hnorthAfter : (base.add westRow hwest).Addable northRow :=
    base.addable_after_add_of_ne westRow northRow hwest hnorth hne
  change (base.add northRow hnorth).add westRow hwestAfter =
    (base.add westRow hwest).add northRow hnorthAfter
  exact base.add_comm northRow westRow hnorth hwest hne

/-- Admissibility conditions supplied by a permutation matrix when a local
square is filled from northwest to southeast. -/
structure GrowthSquareInput
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop) : Prop where
  height_pos : marked → 0 < height
  marked_clear : marked →
    north = GrowthStep.stay ∧ west = GrowthStep.stay
  repeated_has_next : ∀ row hnorth hwest,
    north = GrowthStep.add row hnorth →
    west = GrowthStep.add row hwest →
    row.val + 1 < height

theorem unmarkedGrowthSquareInput
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (hunmarked : ¬ marked)
    (hrepeated : ∀ row hnorth hwest,
      north = GrowthStep.add row hnorth →
      west = GrowthStep.add row hwest →
      row.val + 1 < height) :
    GrowthSquareInput north west marked where
  height_pos h := (hunmarked h).elim
  marked_clear h := (hunmarked h).elim
  repeated_has_next := hrepeated

theorem markedStayGrowthSquareInput
    {height : ℕ} {base : GrowthShape height} (marked : Prop)
    (_hmarked : marked) (hheight : 0 < height) :
    GrowthSquareInput (GrowthStep.stay : GrowthStep base)
      (GrowthStep.stay : GrowthStep base) marked where
  height_pos _ := hheight
  marked_clear _ := ⟨rfl, rfl⟩
  repeated_has_next := by
    intro row hnorth hwest hnorthEq hwestEq
    cases hnorthEq

/-- Deterministic forward local RSK rule. -/
noncomputable def applyLocalRule
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (input : GrowthSquareInput north west marked) :
    GrowthSquareOutput north west := by
  cases north with
  | stay =>
      cases west with
      | stay =>
          by_cases hmarked : marked
          · exact localStayStayMarked base (input.height_pos hmarked)
          · exact localStayStayUnmarked base
      | add westRow hwest =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.2
          exact localStayAdd base westRow hwest
  | add northRow hnorth =>
      cases west with
      | stay =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          exact localAddStay base northRow hnorth
      | add westRow hwest =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          by_cases hrows : northRow = westRow
          · subst westRow
            exact localRepeatedAdd base northRow hnorth
              (input.repeated_has_next northRow hnorth hwest rfl rfl)
          · exact localDistinctAdds base northRow westRow hnorth hwest hrows

theorem applyLocalRule_stay_stay_of_marked
    {height : ℕ} {base : GrowthShape height} {marked : Prop}
    (input : GrowthSquareInput (GrowthStep.stay : GrowthStep base)
      (GrowthStep.stay : GrowthStep base) marked)
    (hmarked : marked) :
    applyLocalRule GrowthStep.stay GrowthStep.stay marked input =
      localStayStayMarked base (input.height_pos hmarked) := by
  unfold applyLocalRule
  simp [hmarked]

theorem applyLocalRule_stay_stay_of_unmarked
    {height : ℕ} {base : GrowthShape height} {marked : Prop}
    (input : GrowthSquareInput (GrowthStep.stay : GrowthStep base)
      (GrowthStep.stay : GrowthStep base) marked)
    (hunmarked : ¬ marked) :
    applyLocalRule GrowthStep.stay GrowthStep.stay marked input =
      localStayStayUnmarked base := by
  unfold applyLocalRule
  simp [hunmarked]

theorem applyLocalRule_add_stay
    {height : ℕ} {base : GrowthShape height} {marked : Prop}
    (row : Fin height) (hadd : base.Addable row)
    (input : GrowthSquareInput (GrowthStep.add row hadd)
      (GrowthStep.stay : GrowthStep base) marked) :
    applyLocalRule (GrowthStep.add row hadd) GrowthStep.stay marked input =
      localAddStay base row hadd := by
  unfold applyLocalRule
  rfl

theorem applyLocalRule_stay_add
    {height : ℕ} {base : GrowthShape height} {marked : Prop}
    (row : Fin height) (hadd : base.Addable row)
    (input : GrowthSquareInput (GrowthStep.stay : GrowthStep base)
      (GrowthStep.add row hadd) marked) :
    applyLocalRule GrowthStep.stay (GrowthStep.add row hadd) marked input =
      localStayAdd base row hadd := by
  unfold applyLocalRule
  rfl

theorem applyLocalRule_repeated
    {height : ℕ} {base : GrowthShape height} {marked : Prop}
    (row : Fin height) (hnorth hwest : base.Addable row)
    (input : GrowthSquareInput (GrowthStep.add row hnorth)
      (GrowthStep.add row hwest) marked) :
    applyLocalRule (GrowthStep.add row hnorth) (GrowthStep.add row hwest)
      marked input =
      localRepeatedAdd base row hnorth
        (input.repeated_has_next row hnorth hwest rfl rfl) := by
  unfold applyLocalRule
  simp

theorem applyLocalRule_distinct
    {height : ℕ} {base : GrowthShape height} {marked : Prop}
    (northRow westRow : Fin height)
    (hnorth : base.Addable northRow) (hwest : base.Addable westRow)
    (hne : northRow ≠ westRow)
    (input : GrowthSquareInput (GrowthStep.add northRow hnorth)
      (GrowthStep.add westRow hwest) marked) :
    applyLocalRule (GrowthStep.add northRow hnorth) (GrowthStep.add westRow hwest)
      marked input =
      localDistinctAdds base northRow westRow hnorth hwest hne := by
  unfold applyLocalRule
  simp [hne]

theorem applyLocalRule_fromNorth_stay_iff
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (input : GrowthSquareInput north west marked) :
    (applyLocalRule north west marked input).fromNorth = GrowthStep.stay ↔
      west = GrowthStep.stay ∧ ¬ marked := by
  cases north with
  | stay =>
      cases west with
      | stay =>
          by_cases hmarked : marked
          · rw [applyLocalRule_stay_stay_of_marked input hmarked]
            simp [localStayStayMarked, hmarked]
          · rw [applyLocalRule_stay_stay_of_unmarked input hmarked]
            simp [localStayStayUnmarked, hmarked]
      | add westRow hwest =>
          rw [applyLocalRule_stay_add]
          simp [localStayAdd]
  | add northRow hnorth =>
      cases west with
      | stay =>
          rw [applyLocalRule_add_stay]
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          simp [localAddStay, hunmarked]
      | add westRow hwest =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          by_cases hrows : northRow = westRow
          · subst westRow
            rw [applyLocalRule_repeated]
            simp [localRepeatedAdd]
          · rw [applyLocalRule_distinct northRow westRow hnorth hwest hrows input]
            simp [localDistinctAdds]

theorem applyLocalRule_fromWest_stay_iff
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (input : GrowthSquareInput north west marked) :
    (applyLocalRule north west marked input).fromWest = GrowthStep.stay ↔
      north = GrowthStep.stay ∧ ¬ marked := by
  cases north with
  | stay =>
      cases west with
      | stay =>
          by_cases hmarked : marked
          · rw [applyLocalRule_stay_stay_of_marked input hmarked]
            simp [localStayStayMarked, hmarked]
          · rw [applyLocalRule_stay_stay_of_unmarked input hmarked]
            simp [localStayStayUnmarked, hmarked]
      | add westRow hwest =>
          rw [applyLocalRule_stay_add]
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.2
          simp [localStayAdd, hunmarked]
  | add northRow hnorth =>
      cases west with
      | stay =>
          rw [applyLocalRule_add_stay]
          simp [localAddStay]
      | add westRow hwest =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          by_cases hrows : northRow = westRow
          · subst westRow
            rw [applyLocalRule_repeated]
            simp [localRepeatedAdd]
          · rw [applyLocalRule_distinct northRow westRow hnorth hwest hrows input]
            simp [localDistinctAdds]

end FibonacciRibbonKernel
