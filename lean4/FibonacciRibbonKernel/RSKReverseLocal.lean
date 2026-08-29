import FibonacciRibbonKernel.RSKGrowthDiagram

namespace FibonacciRibbonKernel

open scoped Classical

structure ReverseSquareOutput
    {height : ℕ} (northeast southwest southeast : GrowthShape height) where
  northwest : GrowthShape height
  north : GrowthStep northwest
  west : GrowthStep northwest
  north_target : north.target = northeast
  west_target : west.target = southwest
  marked : Bool
  rule : LocalGrowthRule (marked = true)
    northwest northeast southwest southeast

structure CompatibleOutgoing
    {height : ℕ} (northBase westBase : GrowthShape height) where
  north : GrowthStep northBase
  west : GrowthStep westBase
  agrees : north.target = west.target

@[ext] theorem CompatibleOutgoing.ext
    {height : ℕ} {northBase westBase : GrowthShape height}
    {left right : CompatibleOutgoing northBase westBase}
    (hnorth : left.north = right.north) (hwest : left.west = right.west) :
    left = right := by
  cases left
  cases right
  simp_all

noncomputable def reverseLocalRule
    {height : ℕ} {northeast southwest : GrowthShape height}
    (fromNorth : GrowthStep northeast) (fromWest : GrowthStep southwest)
    (hagree : fromNorth.target = fromWest.target) :
    ReverseSquareOutput northeast southwest fromNorth.target := by
  cases fromNorth with
  | stay =>
      cases fromWest with
      | stay =>
          have hshape : northeast = southwest := hagree
          let baseRule : LocalGrowthRule ((false : Bool) = true)
              northeast northeast northeast northeast :=
            .stay northeast (by decide)
          exact
            { northwest := northeast
              north := .stay
              west := .stay
              north_target := rfl
              west_target := hshape
              marked := false
              rule := baseRule.transport rfl rfl hshape rfl }
      | add westRow hwest =>
          have hshape : northeast = southwest.add westRow hwest := hagree
          let baseRule : LocalGrowthRule ((false : Bool) = true)
              southwest (southwest.add westRow hwest) southwest
                (southwest.add westRow hwest) :=
            .northOnly southwest (by decide) westRow hwest
          exact
            { northwest := southwest
              north := .add westRow hwest
              west := .stay
              north_target := hshape.symm
              west_target := rfl
              marked := false
              rule := baseRule.transport rfl hshape.symm rfl hshape.symm }
  | add northRow hnorth =>
      cases fromWest with
      | stay =>
          have hshape : northeast.add northRow hnorth = southwest := hagree
          let baseRule : LocalGrowthRule ((false : Bool) = true)
              northeast northeast (northeast.add northRow hnorth)
                (northeast.add northRow hnorth) :=
            .westOnly northeast (by decide) northRow hnorth
          exact
            { northwest := northeast
              north := .stay
              west := .add northRow hnorth
              north_target := rfl
              west_target := hshape
              marked := false
              rule := baseRule.transport rfl rfl hshape rfl }
      | add westRow hwest =>
          have hshape : northeast.add northRow hnorth =
              southwest.add westRow hwest := hagree
          by_cases hrows : northRow = westRow
          · subst westRow
            have hbase : northeast = southwest :=
              northeast.add_cancel southwest northRow hnorth hwest hshape
            by_cases hzero : northRow.val = 0
            · have hrow : northRow = ⟨0, by omega⟩ := Fin.ext hzero
              let zeroRow : Fin height := ⟨0, by omega⟩
              let haddZero : northeast.Addable zeroRow := Or.inl rfl
              let baseRule : LocalGrowthRule ((true : Bool) = true)
                  northeast northeast northeast (northeast.add zeroRow haddZero) :=
                .mark northeast rfl (by omega)
              have hsoutheast : northeast.add zeroRow haddZero =
                  northeast.add northRow hnorth :=
                GrowthShape.add_congr_rows rfl zeroRow northRow hrow.symm
                  haddZero hnorth
              exact
                { northwest := northeast
                  north := .stay
                  west := .stay
                  north_target := rfl
                  west_target := hbase
                  marked := true
                  rule := baseRule.transport rfl rfl hbase hsoutheast }
            · let previous : Fin height := ⟨northRow.val - 1, by omega⟩
              let hremove := northeast.removable_previous_of_addable
                northRow hnorth (by omega)
              let northwest := northeast.remove previous hremove
              let haddPrevious := northeast.remove_addable previous hremove
              have hnorthEq : northwest.add previous haddPrevious = northeast :=
                northeast.add_remove previous hremove
              have hwestEq : northwest.add previous haddPrevious = southwest :=
                hnorthEq.trans hbase
              have hnext : previous.val + 1 < height := by
                dsimp [previous]
                omega
              let baseRule : LocalGrowthRule ((false : Bool) = true)
                  northwest (northwest.add previous haddPrevious)
                    (northwest.add previous haddPrevious)
                    ((northwest.add previous haddPrevious).add
                      ⟨previous.val + 1, hnext⟩
                      (northwest.next_addable_after_same previous haddPrevious hnext)) :=
                .repeated northwest (by decide) previous haddPrevious hnext
              have hsoutheast :
                  ((northwest.add previous haddPrevious).add
                    ⟨previous.val + 1, hnext⟩
                    (northwest.next_addable_after_same previous haddPrevious hnext)) =
                    northeast.add northRow hnorth := by
                have hrowNext : (⟨previous.val + 1, hnext⟩ : Fin height) =
                    northRow := by
                  apply Fin.ext
                  simp [previous]
                  omega
                exact GrowthShape.add_congr_rows hnorthEq
                  ⟨previous.val + 1, hnext⟩ northRow hrowNext _ hnorth
              exact
                { northwest := northwest
                  north := .add previous haddPrevious
                  west := .add previous haddPrevious
                  north_target := hnorthEq
                  west_target := hwestEq
                  marked := false
                  rule := baseRule.transport rfl hnorthEq hwestEq hsoutheast }
          · let hremoveNorth := northeast.removable_of_add_eq_add_of_ne
              southwest northRow westRow hnorth hwest hrows hshape
            let hremoveWest := southwest.removable_of_add_eq_add_of_ne
              northeast westRow northRow hwest hnorth (Ne.symm hrows) hshape.symm
            let northwest := northeast.remove westRow hremoveNorth
            let haddNorth := northeast.remove_addable westRow hremoveNorth
            have hnorthEq : northwest.add westRow haddNorth = northeast :=
              northeast.add_remove westRow hremoveNorth
            have hdiamond := northeast.distinct_diamond_predecessor southwest
              northRow westRow hnorth hwest hrows hshape
            have hnorthwest : northwest = southwest.remove northRow hremoveWest := hdiamond
            let haddWest := southwest.remove_addable northRow hremoveWest
            let haddWestAtNorthwest : northwest.Addable northRow :=
              hnorthwest.symm ▸ haddWest
            have hwestEq : northwest.add northRow haddWestAtNorthwest = southwest := by
              exact (GrowthShape.add_congr hnorthwest northRow
                haddWestAtNorthwest haddWest).trans
                  (southwest.add_remove northRow hremoveWest)
            let baseRule : LocalGrowthRule ((false : Bool) = true)
                northwest (northwest.add westRow haddNorth)
                  (northwest.add northRow haddWestAtNorthwest)
                  ((northwest.add westRow haddNorth).add northRow
                    (northwest.addable_after_add_of_ne westRow northRow
                      haddNorth haddWestAtNorthwest hrows)) :=
              .distinct northwest (by decide) westRow northRow
                haddNorth haddWestAtNorthwest (Ne.symm hrows)
            have hsoutheast :
                ((northwest.add westRow haddNorth).add northRow
                  (northwest.addable_after_add_of_ne westRow northRow
                    haddNorth haddWestAtNorthwest hrows)) =
                  northeast.add northRow hnorth := by
              exact GrowthShape.add_congr hnorthEq northRow _ hnorth
            exact
              { northwest := northwest
                north := .add westRow haddNorth
                west := .add northRow haddWestAtNorthwest
                north_target := hnorthEq
                west_target := hwestEq
                marked := false
                rule := baseRule.transport rfl hnorthEq hwestEq hsoutheast }

theorem reverseLocalRule_fromNorth_stay_iff
    {height : ℕ} {northeast southwest : GrowthShape height}
    (fromNorth : GrowthStep northeast) (fromWest : GrowthStep southwest)
    (hagree : fromNorth.target = fromWest.target) :
    fromNorth = GrowthStep.stay ↔
      (reverseLocalRule fromNorth fromWest hagree).west = GrowthStep.stay ∧
        (reverseLocalRule fromNorth fromWest hagree).marked = false := by
  cases fromNorth with
  | stay =>
      cases fromWest with
      | stay => simp [reverseLocalRule]
      | add westRow hwest => simp [reverseLocalRule]
  | add northRow hnorth =>
      cases fromWest with
      | stay => simp [reverseLocalRule]
      | add westRow hwest =>
          constructor
          · intro himpossible
            cases himpossible
          · rintro ⟨hstay, hmarked⟩
            let output := reverseLocalRule (GrowthStep.add northRow hnorth)
              (GrowthStep.add westRow hwest) hagree
            have hmarked' : output.marked = false := hmarked
            have hunmarked : ¬ (output.marked = true) := by
              rw [hmarked']
              decide
            have hbalance := output.rule.card_balance_of_unmarked hunmarked
            have hwestBase : output.northwest = southwest := by
              have htarget := output.west_target
              rw [hstay] at htarget
              exact htarget
            have hnorthCard :
                (GrowthStep.add northRow hnorth : GrowthStep northeast).target.card =
                  northeast.card + 1 := by simp
            change (GrowthStep.add northRow hnorth : GrowthStep northeast).target.card +
                output.northwest.card = northeast.card + southwest.card at hbalance
            rw [hnorthCard, hwestBase] at hbalance
            omega

theorem reverseLocalRule_west_stay_of_marked
    {height : ℕ} {northeast southwest : GrowthShape height}
    (fromNorth : GrowthStep northeast) (fromWest : GrowthStep southwest)
    (hagree : fromNorth.target = fromWest.target)
    (hmarked : (reverseLocalRule fromNorth fromWest hagree).marked = true) :
    (reverseLocalRule fromNorth fromWest hagree).west = GrowthStep.stay := by
  let output := reverseLocalRule fromNorth fromWest hagree
  let witness := output.rule.forward_witness
  have hwest : witness.west = output.west :=
    GrowthStep.target_injective
      (witness.southwest_eq.trans output.west_target.symm)
  have hclear := witness.input.marked_clear hmarked
  exact hwest ▸ hclear.2

theorem reverseLocalRule_north_stay_of_marked
    {height : ℕ} {northeast southwest : GrowthShape height}
    (fromNorth : GrowthStep northeast) (fromWest : GrowthStep southwest)
    (hagree : fromNorth.target = fromWest.target)
    (hmarked : (reverseLocalRule fromNorth fromWest hagree).marked = true) :
    (reverseLocalRule fromNorth fromWest hagree).north = GrowthStep.stay := by
  let output := reverseLocalRule fromNorth fromWest hagree
  let witness := output.rule.forward_witness
  have hnorth : witness.north = output.north :=
    GrowthStep.target_injective
      (witness.northeast_eq.trans output.north_target.symm)
  have hclear := witness.input.marked_clear hmarked
  exact hnorth ▸ hclear.1

theorem reverseLocalRule_fromWest_stay_iff
    {height : ℕ} {northeast southwest : GrowthShape height}
    (fromNorth : GrowthStep northeast) (fromWest : GrowthStep southwest)
    (hagree : fromNorth.target = fromWest.target) :
    fromWest = GrowthStep.stay ↔
      (reverseLocalRule fromNorth fromWest hagree).north = GrowthStep.stay ∧
        (reverseLocalRule fromNorth fromWest hagree).marked = false := by
  let output := reverseLocalRule fromNorth fromWest hagree
  rcases output.rule.forward_witness with
    ⟨incomingNorth, incomingWest, hnorthTarget, hwestTarget,
      input, hsoutheast⟩
  have hnorth : incomingNorth = output.north :=
    GrowthStep.target_injective
      (hnorthTarget.trans output.north_target.symm)
  have hwest : incomingWest = output.west :=
    GrowthStep.target_injective
      (hwestTarget.trans output.west_target.symm)
  subst incomingNorth
  subst incomingWest
  have hlocal := applyLocalRule_fromWest_stay_iff
    output.north output.west (output.marked = true) input
  have hout : (applyLocalRule output.north output.west
      (output.marked = true) input).fromWest =
        fromWest.castBase output.west_target.symm := by
    apply GrowthStep.target_injective
    have hfromWestTarget :=
      (applyLocalRule output.north output.west
        (output.marked = true) input).southeast_agrees
    rw [GrowthStep.target_castBase]
    exact hfromWestTarget.symm.trans (hsoutheast.trans hagree)
  rw [hout, GrowthStep.castBase_eq_stay_iff] at hlocal
  cases hmarked : output.marked <;> simp [hmarked] at hlocal ⊢
  · exact hlocal
  · exact hlocal

theorem reverseLocalRule_applyLocalRule_northwest
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (input : GrowthSquareInput north west marked) :
    let forward := applyLocalRule north west marked input
    (reverseLocalRule forward.fromNorth forward.fromWest
      forward.southeast_agrees).northwest = base := by
  cases north with
  | stay =>
      cases west with
      | stay =>
          by_cases hmarked : marked
          · rw [applyLocalRule_stay_stay_of_marked input hmarked]
            simp [localStayStayMarked, reverseLocalRule]
          · rw [applyLocalRule_stay_stay_of_unmarked input hmarked]
            simp [localStayStayUnmarked, reverseLocalRule]
      | add westRow hwest =>
          rw [applyLocalRule_stay_add]
          simp [localStayAdd, reverseLocalRule]
  | add northRow hnorth =>
      cases west with
      | stay =>
          rw [applyLocalRule_add_stay]
          simp [localAddStay, reverseLocalRule]
      | add westRow hwest =>
          by_cases hrows : northRow = westRow
          · subst westRow
            rw [applyLocalRule_repeated]
            simp [localRepeatedAdd, reverseLocalRule]
          · rw [applyLocalRule_distinct northRow westRow hnorth hwest hrows input]
            have hrows' : westRow ≠ northRow := Ne.symm hrows
            simp [localDistinctAdds, reverseLocalRule, hrows']

theorem reverseLocalRule_applyLocalRule_marked
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (input : GrowthSquareInput north west marked) :
    let forward := applyLocalRule north west marked input
    ((reverseLocalRule forward.fromNorth forward.fromWest
      forward.southeast_agrees).marked = true ↔ marked) := by
  cases north with
  | stay =>
      cases west with
      | stay =>
          by_cases hmarked : marked
          · rw [applyLocalRule_stay_stay_of_marked input hmarked]
            simp [localStayStayMarked, reverseLocalRule, hmarked]
          · rw [applyLocalRule_stay_stay_of_unmarked input hmarked]
            simp [localStayStayUnmarked, reverseLocalRule, hmarked]
      | add westRow hwest =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.2
          rw [applyLocalRule_stay_add]
          simp [localStayAdd, reverseLocalRule, hunmarked]
  | add northRow hnorth =>
      cases west with
      | stay =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          rw [applyLocalRule_add_stay]
          simp [localAddStay, reverseLocalRule, hunmarked]
      | add westRow hwest =>
          have hunmarked : ¬ marked := by
            intro hmarked
            have hclear := input.marked_clear hmarked
            cases hclear.1
          by_cases hrows : northRow = westRow
          · subst westRow
            rw [applyLocalRule_repeated]
            simp [localRepeatedAdd, reverseLocalRule, hunmarked]
          · rw [applyLocalRule_distinct northRow westRow hnorth hwest hrows input]
            have hrows' : westRow ≠ northRow := Ne.symm hrows
            simp [localDistinctAdds, reverseLocalRule, hrows', hunmarked]

theorem reverseLocalRule_applyLocalRule_north
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (input : GrowthSquareInput north west marked) :
    let forward := applyLocalRule north west marked input
    let reverse := reverseLocalRule forward.fromNorth forward.fromWest
      forward.southeast_agrees
    reverse.north.castBase
      (reverseLocalRule_applyLocalRule_northwest north west marked input) = north := by
  dsimp
  apply GrowthStep.target_injective
  rw [GrowthStep.target_castBase]
  exact (reverseLocalRule
    (applyLocalRule north west marked input).fromNorth
    (applyLocalRule north west marked input).fromWest
    (applyLocalRule north west marked input).southeast_agrees).north_target

theorem reverseLocalRule_applyLocalRule_west
    {height : ℕ} {base : GrowthShape height}
    (north west : GrowthStep base) (marked : Prop)
    (input : GrowthSquareInput north west marked) :
    let forward := applyLocalRule north west marked input
    let reverse := reverseLocalRule forward.fromNorth forward.fromWest
      forward.southeast_agrees
    reverse.west.castBase
      (reverseLocalRule_applyLocalRule_northwest north west marked input) = west := by
  dsimp
  apply GrowthStep.target_injective
  rw [GrowthStep.target_castBase]
  exact (reverseLocalRule
    (applyLocalRule north west marked input).fromNorth
    (applyLocalRule north west marked input).fromWest
    (applyLocalRule north west marked input).southeast_agrees).west_target

theorem reverseLocalRule_castBases_northwest
    {height : ℕ} {northBase northBase' westBase westBase' : GrowthShape height}
    (fromNorth : GrowthStep northBase) (fromWest : GrowthStep westBase)
    (hnorth : northBase = northBase') (hwest : westBase = westBase')
    (hagree : fromNorth.target = fromWest.target)
    (hagree' : (fromNorth.castBase hnorth).target =
      (fromWest.castBase hwest).target) :
    (reverseLocalRule (fromNorth.castBase hnorth) (fromWest.castBase hwest)
      hagree').northwest =
      (reverseLocalRule fromNorth fromWest hagree).northwest := by
  subst northBase'
  subst westBase'
  rfl

theorem reverseLocalRule_castBases_marked
    {height : ℕ} {northBase northBase' westBase westBase' : GrowthShape height}
    (fromNorth : GrowthStep northBase) (fromWest : GrowthStep westBase)
    (hnorth : northBase = northBase') (hwest : westBase = westBase')
    (hagree : fromNorth.target = fromWest.target)
    (hagree' : (fromNorth.castBase hnorth).target =
      (fromWest.castBase hwest).target) :
    (reverseLocalRule (fromNorth.castBase hnorth) (fromWest.castBase hwest)
      hagree').marked =
      (reverseLocalRule fromNorth fromWest hagree).marked := by
  subst northBase'
  subst westBase'
  rfl

theorem LocalGrowthRule.northwest_unique
    {height : ℕ} {leftMarked rightMarked : Prop}
    {leftNorthwest rightNorthwest northeast southwest southeast : GrowthShape height}
    (left : LocalGrowthRule leftMarked leftNorthwest northeast southwest southeast)
    (right : LocalGrowthRule rightMarked rightNorthwest northeast southwest southeast) :
    leftNorthwest = rightNorthwest := by
  rcases left.forward_witness with
    ⟨leftNorth, leftWest, leftNorthEq, leftWestEq, leftInput, leftSoutheastEq⟩
  rcases right.forward_witness with
    ⟨rightNorth, rightWest, rightNorthEq, rightWestEq, rightInput, rightSoutheastEq⟩
  let leftForward := applyLocalRule leftNorth leftWest leftMarked leftInput
  let rightForward := applyLocalRule rightNorth rightWest rightMarked rightInput
  let leftOutNorth : GrowthStep northeast := leftForward.fromNorth.castBase leftNorthEq
  let leftOutWest : GrowthStep southwest := leftForward.fromWest.castBase leftWestEq
  let rightOutNorth : GrowthStep northeast := rightForward.fromNorth.castBase rightNorthEq
  let rightOutWest : GrowthStep southwest := rightForward.fromWest.castBase rightWestEq
  have leftOutNorthTarget : leftOutNorth.target = southeast := by
    rw [GrowthStep.target_castBase]
    exact leftSoutheastEq
  have leftOutWestTarget : leftOutWest.target = southeast := by
    rw [GrowthStep.target_castBase]
    exact leftForward.southeast_agrees.symm.trans leftSoutheastEq
  have rightOutNorthTarget : rightOutNorth.target = southeast := by
    rw [GrowthStep.target_castBase]
    exact rightSoutheastEq
  have rightOutWestTarget : rightOutWest.target = southeast := by
    rw [GrowthStep.target_castBase]
    exact rightForward.southeast_agrees.symm.trans rightSoutheastEq
  have hnorthOut : leftOutNorth = rightOutNorth :=
    GrowthStep.target_injective
      (leftOutNorthTarget.trans rightOutNorthTarget.symm)
  have hwestOut : leftOutWest = rightOutWest :=
    GrowthStep.target_injective
      (leftOutWestTarget.trans rightOutWestTarget.symm)
  have leftCast :
      (reverseLocalRule leftOutNorth leftOutWest
        (leftOutNorthTarget.trans leftOutWestTarget.symm)).northwest =
        (reverseLocalRule leftForward.fromNorth leftForward.fromWest
          leftForward.southeast_agrees).northwest :=
    reverseLocalRule_castBases_northwest _ _ _ _ _ _
  have rightCast :
      (reverseLocalRule rightOutNorth rightOutWest
        (rightOutNorthTarget.trans rightOutWestTarget.symm)).northwest =
        (reverseLocalRule rightForward.fromNorth rightForward.fromWest
          rightForward.southeast_agrees).northwest :=
    reverseLocalRule_castBases_northwest _ _ _ _ _ _
  have leftRecover := reverseLocalRule_applyLocalRule_northwest
    leftNorth leftWest leftMarked leftInput
  have rightRecover := reverseLocalRule_applyLocalRule_northwest
    rightNorth rightWest rightMarked rightInput
  let leftData : CompatibleOutgoing northeast southwest :=
    ⟨leftOutNorth, leftOutWest, leftOutNorthTarget.trans leftOutWestTarget.symm⟩
  let rightData : CompatibleOutgoing northeast southwest :=
    ⟨rightOutNorth, rightOutWest, rightOutNorthTarget.trans rightOutWestTarget.symm⟩
  have hdata : leftData = rightData :=
    CompatibleOutgoing.ext hnorthOut hwestOut
  have hcanonical := congrArg
    (fun data : CompatibleOutgoing northeast southwest =>
      (reverseLocalRule data.north data.west data.agrees).northwest) hdata
  exact leftRecover.symm.trans (leftCast.symm.trans
    (hcanonical.trans (rightCast.trans rightRecover)))

theorem LocalGrowthRule.marked_iff
    {height : ℕ} {leftMarked rightMarked : Prop}
    {leftNorthwest rightNorthwest northeast southwest southeast : GrowthShape height}
    (left : LocalGrowthRule leftMarked leftNorthwest northeast southwest southeast)
    (right : LocalGrowthRule rightMarked rightNorthwest northeast southwest southeast) :
    leftMarked ↔ rightMarked := by
  rcases left.forward_witness with
    ⟨leftNorth, leftWest, leftNorthEq, leftWestEq, leftInput, leftSoutheastEq⟩
  rcases right.forward_witness with
    ⟨rightNorth, rightWest, rightNorthEq, rightWestEq, rightInput, rightSoutheastEq⟩
  let leftForward := applyLocalRule leftNorth leftWest leftMarked leftInput
  let rightForward := applyLocalRule rightNorth rightWest rightMarked rightInput
  let leftOutNorth : GrowthStep northeast := leftForward.fromNorth.castBase leftNorthEq
  let leftOutWest : GrowthStep southwest := leftForward.fromWest.castBase leftWestEq
  let rightOutNorth : GrowthStep northeast := rightForward.fromNorth.castBase rightNorthEq
  let rightOutWest : GrowthStep southwest := rightForward.fromWest.castBase rightWestEq
  have leftOutNorthTarget : leftOutNorth.target = southeast := by
    rw [GrowthStep.target_castBase]
    exact leftSoutheastEq
  have leftOutWestTarget : leftOutWest.target = southeast := by
    rw [GrowthStep.target_castBase]
    exact leftForward.southeast_agrees.symm.trans leftSoutheastEq
  have rightOutNorthTarget : rightOutNorth.target = southeast := by
    rw [GrowthStep.target_castBase]
    exact rightSoutheastEq
  have rightOutWestTarget : rightOutWest.target = southeast := by
    rw [GrowthStep.target_castBase]
    exact rightForward.southeast_agrees.symm.trans rightSoutheastEq
  have hnorthOut : leftOutNorth = rightOutNorth :=
    GrowthStep.target_injective
      (leftOutNorthTarget.trans rightOutNorthTarget.symm)
  have hwestOut : leftOutWest = rightOutWest :=
    GrowthStep.target_injective
      (leftOutWestTarget.trans rightOutWestTarget.symm)
  have leftCast := reverseLocalRule_castBases_marked
    leftForward.fromNorth leftForward.fromWest leftNorthEq leftWestEq
      leftForward.southeast_agrees
      (leftOutNorthTarget.trans leftOutWestTarget.symm)
  have rightCast := reverseLocalRule_castBases_marked
    rightForward.fromNorth rightForward.fromWest rightNorthEq rightWestEq
      rightForward.southeast_agrees
      (rightOutNorthTarget.trans rightOutWestTarget.symm)
  have leftRecover := reverseLocalRule_applyLocalRule_marked
    leftNorth leftWest leftMarked leftInput
  have rightRecover := reverseLocalRule_applyLocalRule_marked
    rightNorth rightWest rightMarked rightInput
  let leftData : CompatibleOutgoing northeast southwest :=
    ⟨leftOutNorth, leftOutWest, leftOutNorthTarget.trans leftOutWestTarget.symm⟩
  let rightData : CompatibleOutgoing northeast southwest :=
    ⟨rightOutNorth, rightOutWest, rightOutNorthTarget.trans rightOutWestTarget.symm⟩
  have hdata : leftData = rightData :=
    CompatibleOutgoing.ext hnorthOut hwestOut
  have hcanonical := congrArg
    (fun data : CompatibleOutgoing northeast southwest =>
      (reverseLocalRule data.north data.west data.agrees).marked) hdata
  have hbool :
      (reverseLocalRule leftForward.fromNorth leftForward.fromWest
        leftForward.southeast_agrees).marked =
      (reverseLocalRule rightForward.fromNorth rightForward.fromWest
        rightForward.southeast_agrees).marked :=
    leftCast.symm.trans (hcanonical.trans rightCast)
  constructor
  · intro hleft
    have hmarkLeft := leftRecover.mpr hleft
    have hmarkRight :
        (reverseLocalRule rightForward.fromNorth rightForward.fromWest
          rightForward.southeast_agrees).marked = true := by
      rw [← hbool]
      exact hmarkLeft
    exact rightRecover.mp hmarkRight
  · intro hright
    have hmarkRight := rightRecover.mpr hright
    have hmarkLeft :
        (reverseLocalRule leftForward.fromNorth leftForward.fromWest
          leftForward.southeast_agrees).marked = true := by
      rw [hbool]
      exact hmarkRight
    exact leftRecover.mp hmarkLeft

end FibonacciRibbonKernel
