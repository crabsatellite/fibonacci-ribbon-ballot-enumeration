import FibonacciRibbonKernel.PathMatchings

namespace FibonacciRibbonKernel

open scoped Classical

def parameterComplementEquiv (rank : ℕ) :
    Fin (rank + 1) ≃ Fin (rank + 1) where
  toFun := parameterComplement
  invFun := parameterComplement
  left_inv := parameterComplement_involutive rank
  right_inv := parameterComplement_involutive rank

set_option linter.unusedVariables false in
/-- Literal alternating parameter choices, retaining each column-validity proof. -/
def ParameterWordFrom (rank : ℕ) :
    Weight rank → Bool → ℕ → Type
  | _, _, 0 => PUnit
  | state, shortPosition, columns + 1 =>
      Σ parameter : Fin (rank + 1),
        {tail : ParameterWordFrom rank
            (state + (parameterColumn shortPosition parameter).weight)
            (!shortPosition) columns //
          (parameterColumn shortPosition parameter).prefixesDominant state}

noncomputable instance parameterWordFromFintype
    (rank : ℕ) (state : Weight rank) (shortPosition : Bool) (columns : ℕ) :
    Fintype (ParameterWordFrom rank state shortPosition columns) := by
  induction columns generalizing state shortPosition with
  | zero =>
      simp only [ParameterWordFrom]
      infer_instance
  | succ columns ih =>
      simp only [ParameterWordFrom]
      letI (parameter : Fin (rank + 1)) :
          Fintype (ParameterWordFrom rank
            (state + (parameterColumn shortPosition parameter).weight)
            (!shortPosition) columns) :=
        ih _ _
      infer_instance

/-- Forget proof fields and read the actual manuscript parameters. -/
def ParameterWordFrom.parameters
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} :
    {columns : ℕ} → ParameterWordFrom rank state shortPosition columns →
      List (Fin (rank + 1))
  | 0, _ => []
  | _ + 1, ⟨parameter, tail⟩ =>
      parameter :: tail.1.parameters

theorem ParameterWordFrom.parameters_length
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} {columns : ℕ}
    (word : ParameterWordFrom rank state shortPosition columns) :
    word.parameters.length = columns := by
  induction columns generalizing state shortPosition with
  | zero => rfl
  | succ columns ih =>
      obtain ⟨parameter, tail⟩ := word
      simp [ParameterWordFrom.parameters, ih tail.1]

@[ext] theorem ParameterWordFrom.ext
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} {columns : ℕ}
    {left right : ParameterWordFrom rank state shortPosition columns}
    (hparameters : left.parameters = right.parameters) : left = right := by
  induction columns generalizing state shortPosition with
  | zero =>
      cases left
      cases right
      rfl
  | succ columns ih =>
      obtain ⟨leftParameter, leftTail⟩ := left
      obtain ⟨rightParameter, rightTail⟩ := right
      simp only [ParameterWordFrom.parameters, List.cons.injEq] at hparameters
      rcases hparameters with ⟨hparameter, htail⟩
      subst rightParameter
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        exact ih htail

theorem ParameterWordFrom.columnsBallot
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} {columns : ℕ}
    (word : ParameterWordFrom rank state shortPosition columns) :
    ColumnsBallotFrom state
      (encodeColumns rank shortPosition word.parameters) := by
  induction columns generalizing state shortPosition with
  | zero => trivial
  | succ columns ih =>
      obtain ⟨parameter, tail⟩ := word
      exact ⟨tail.2, ih tail.1⟩

set_option linter.unusedVariables false in
theorem fintype_card_subtype_const
    {α : Type*} [Fintype α] (proposition : Prop) :
    Fintype.card {element : α // proposition} =
      if proposition then Fintype.card α else 0 := by
  classical
  by_cases h : proposition
  · simp [h]
  · simp [h]

theorem parameterWordFrom_card_eq_mixedPathCount
    (rank : ℕ) {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) (columns : ℕ) :
    Fintype.card (ParameterWordFrom rank state shortPosition columns) =
      mixedPathCount state (alternatingSteps shortPosition columns) := by
  induction columns generalizing state shortPosition with
  | zero => simp [ParameterWordFrom, mixedPathCount, alternatingSteps]
  | succ columns ih =>
      classical
      rw [show Fintype.card
          (ParameterWordFrom rank state shortPosition (columns + 1)) =
            ∑ parameter : Fin (rank + 1),
              Fintype.card
                {tail : ParameterWordFrom rank
                    (state + (parameterColumn shortPosition parameter).weight)
                    (!shortPosition) columns //
                  (parameterColumn shortPosition parameter).prefixesDominant state} by
        change Fintype.card
            (Σ parameter : Fin (rank + 1),
              {tail : ParameterWordFrom rank
                  (state + (parameterColumn shortPosition parameter).weight)
                  (!shortPosition) columns //
                (parameterColumn shortPosition parameter).prefixesDominant state}) = _
        exact Fintype.card_sigma]
      cases shortPosition with
      | true =>
          change (∑ parameter : Fin (rank + 1), _) =
            definingAdjacency
              (fun next => mixedPathCount next
                (alternatingSteps false columns)) state
          unfold definingAdjacency
          apply Finset.sum_congr rfl
          intro parameter hparameter
          have hcriterion := column_prefixesDominant_iff_endpoint
            (state := state) (Column.singleton parameter) hstate
          have hvalidIff :
              (parameterColumn true parameter).prefixesDominant state ↔
                PlusValid state parameter := by
            change (Column.singleton parameter).prefixesDominant state ↔
              Dominant (plusState state parameter)
            simpa [Column.weight, plusState] using hcriterion
          rw [fintype_card_subtype_const, hvalidIff]
          by_cases hvalid : PlusValid state parameter
          · simp only [hvalid, if_true]
            have hstateEq :
                state + (Column.singleton parameter).weight =
                  plusState state parameter := by
              simp [Column.weight, plusState]
            change Fintype.card
                (ParameterWordFrom rank
                  (state + (Column.singleton parameter).weight) false columns) =
              mixedPathCount (plusState state parameter)
                (alternatingSteps false columns)
            rw [hstateEq]
            exact ih hvalid false
          · simp only [hvalid, if_false]
      | false =>
          change (∑ parameter : Fin (rank + 1), _) =
            dualAdjacency
              (fun next => mixedPathCount next
                (alternatingSteps true columns)) state
          unfold dualAdjacency
          apply Fintype.sum_equiv (parameterComplementEquiv rank)
          intro parameter
          dsimp [parameterComplementEquiv, parameterColumn, Column.weight]
          have hcriterion := column_prefixesDominant_iff_endpoint
            (state := state)
            (Column.tall (parameterComplement parameter)) hstate
          have hstateEq :
              state + tallWeight rank (parameterComplement parameter) =
                minusState state (parameterComplement parameter) := by
            simp [minusState,
              tallWeight_eq_neg_letterWeight, sub_eq_add_neg]
          have hvalidIff :
              (parameterColumn false parameter).prefixesDominant state ↔
                MinusValid state (parameterComplement parameter) := by
            change (Column.tall (parameterComplement parameter)).prefixesDominant state ↔
              Dominant (minusState state (parameterComplement parameter))
            rw [← hstateEq]
            exact hcriterion
          by_cases hvalid : MinusValid state (parameterComplement parameter)
          · rw [if_pos hvalid]
            have hprefix :
                (Column.tall (parameterComplement parameter)).prefixesDominant state := by
              apply hvalidIff.mpr hvalid
            let fullType := ParameterWordFrom rank
              (state + tallWeight rank (parameterComplement parameter))
              true columns
            let forgetProof :
                {tail : fullType //
                  (Column.tall (parameterComplement parameter)).prefixesDominant state} ≃
                  fullType :=
              { toFun := fun tail => tail.1
                invFun := fun tail => ⟨tail, hprefix⟩
                left_inv := fun tail => by apply Subtype.ext; rfl
                right_inv := fun tail => rfl }
            calc
              Fintype.card
                  {tail : fullType //
                    (Column.tall (parameterComplement parameter)).prefixesDominant state} =
                  Fintype.card fullType := Fintype.card_congr forgetProof
              _ = mixedPathCount
                    (minusState state (parameterComplement parameter))
                    (alternatingSteps true columns) := by
                  dsimp [fullType]
                  rw [hstateEq]
                  exact ih hvalid true
          · rw [if_neg hvalid]
            have hprefix :
                ¬(Column.tall (parameterComplement parameter)).prefixesDominant state := by
              intro hp
              apply hvalid
              exact hvalidIff.mp hp
            apply Fintype.card_eq_zero_iff.mpr
            exact ⟨fun tail => hprefix tail.2⟩

/-- The actual unrestricted alternating parameter objects in the manuscript. -/
abbrev UnrestrictedParameterWord (rank columns : ℕ) :=
  ParameterWordFrom rank (0 : Weight rank) true columns

theorem unrestrictedParameterWord_card (rank columns : ℕ) :
    Fintype.card (UnrestrictedParameterWord rank columns) =
      unrestrictedCount rank columns := by
  rw [parameterWordFrom_card_eq_mixedPathCount rank (dominant_zero rank)]
  rfl

/-- Fixed-length literal parameter lists with the complete column-ballot condition. -/
structure BallotParameterListFrom (rank : ℕ) (state : Weight rank)
    (shortPosition : Bool) (columns : ℕ) where
  parameters : List (Fin (rank + 1))
  length_eq : parameters.length = columns
  ballot : ColumnsBallotFrom state
    (encodeColumns rank shortPosition parameters)

@[ext] theorem BallotParameterListFrom.ext
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} {columns : ℕ}
    {left right : BallotParameterListFrom rank state shortPosition columns}
    (hparameters : left.parameters = right.parameters) : left = right := by
  cases left
  cases right
  simp_all

def ParameterWordFrom.toBallotParameterList
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} {columns : ℕ}
    (word : ParameterWordFrom rank state shortPosition columns) :
    BallotParameterListFrom rank state shortPosition columns where
  parameters := word.parameters
  length_eq := word.parameters_length
  ballot := word.columnsBallot

def BallotParameterListFrom.toParameterWord
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} :
    (columns : ℕ) → BallotParameterListFrom rank state shortPosition columns →
      ParameterWordFrom rank state shortPosition columns
  | 0, list => PUnit.unit
  | columns + 1, list => by
      have hne : list.parameters ≠ [] := by
        intro hempty
        have hlength := list.length_eq
        rw [hempty] at hlength
        simp at hlength
      let head := list.parameters.head hne
      let tail := list.parameters.tail
      have hdecomp : head :: tail = list.parameters := List.cons_head_tail hne
      have htailLength : tail.length = columns := by
        have hlength := list.length_eq
        rw [← hdecomp] at hlength
        simp at hlength
        exact hlength
      have hballot :
          (parameterColumn shortPosition head).prefixesDominant state ∧
            ColumnsBallotFrom
              (state + (parameterColumn shortPosition head).weight)
              (encodeColumns rank (!shortPosition) tail) := by
        have h := list.ballot
        rw [← hdecomp] at h
        exact h
      let tailList : BallotParameterListFrom rank
          (state + (parameterColumn shortPosition head).weight)
          (!shortPosition) columns :=
        { parameters := tail
          length_eq := htailLength
          ballot := hballot.2 }
      exact ⟨head, ⟨tailList.toParameterWord columns, hballot.1⟩⟩

theorem BallotParameterListFrom.toParameterWord_parameters
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} {columns : ℕ}
    (list : BallotParameterListFrom rank state shortPosition columns) :
    (list.toParameterWord columns).parameters = list.parameters := by
  induction columns generalizing state shortPosition with
  | zero =>
      have hnil : list.parameters = [] :=
        List.length_eq_zero_iff.mp list.length_eq
      simpa [BallotParameterListFrom.toParameterWord,
        ParameterWordFrom.parameters] using hnil.symm
  | succ columns ih =>
      have hne : list.parameters ≠ [] := by
        intro hempty
        have hlength := list.length_eq
        rw [hempty] at hlength
        simp at hlength
      let head := list.parameters.head hne
      let tail := list.parameters.tail
      have hdecomp : head :: tail = list.parameters := List.cons_head_tail hne
      have htailLength : tail.length = columns := by
        have hlength := list.length_eq
        rw [← hdecomp] at hlength
        simp at hlength
        exact hlength
      have hballot :
          (parameterColumn shortPosition head).prefixesDominant state ∧
            ColumnsBallotFrom
              (state + (parameterColumn shortPosition head).weight)
              (encodeColumns rank (!shortPosition) tail) := by
        have h := list.ballot
        rw [← hdecomp] at h
        exact h
      let tailList : BallotParameterListFrom rank
          (state + (parameterColumn shortPosition head).weight)
          (!shortPosition) columns :=
        { parameters := tail
          length_eq := htailLength
          ballot := hballot.2 }
      change head :: (tailList.toParameterWord columns).parameters = list.parameters
      rw [ih tailList, hdecomp]

theorem ParameterWordFrom.toBallotParameterList_toParameterWord
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} {columns : ℕ}
    (word : ParameterWordFrom rank state shortPosition columns) :
    (word.toBallotParameterList.toParameterWord columns) = word := by
  induction columns generalizing state shortPosition with
  | zero => cases word; rfl
  | succ columns ih =>
      obtain ⟨parameter, tail⟩ := word
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Subtype.ext (ih tail.1))

/-- Recursive choices and literal parameter lists are explicitly equivalent. -/
def parameterWordBallotListEquiv
    (rank : ℕ) (state : Weight rank) (shortPosition : Bool) (columns : ℕ) :
    ParameterWordFrom rank state shortPosition columns ≃
      BallotParameterListFrom rank state shortPosition columns where
  toFun := ParameterWordFrom.toBallotParameterList
  invFun := fun list => list.toParameterWord columns
  left_inv := ParameterWordFrom.toBallotParameterList_toParameterWord
  right_inv := by
    intro list
    apply BallotParameterListFrom.ext
    exact BallotParameterListFrom.toParameterWord_parameters list

abbrev UnrestrictedParameterList (rank columns : ℕ) :=
  BallotParameterListFrom rank (0 : Weight rank) true columns

noncomputable instance unrestrictedParameterListFintype (rank columns : ℕ) :
    Fintype (UnrestrictedParameterList rank columns) :=
  Fintype.ofEquiv (UnrestrictedParameterWord rank columns)
    (parameterWordBallotListEquiv rank 0 true columns)

theorem unrestrictedParameterList_card (rank columns : ℕ) :
    Fintype.card (UnrestrictedParameterList rank columns) =
      unrestrictedCount rank columns := by
  rw [← unrestrictedParameterWord_card]
  exact Fintype.card_congr
    (parameterWordBallotListEquiv rank 0 true columns).symm

/-- Total difference displacement of a literal alternating parameter list. -/
def parameterListWeight (rank : ℕ) :
    Bool → List (Fin (rank + 1)) → Weight rank
  | _, [] => 0
  | shortPosition, parameter :: tail =>
      (parameterColumn shortPosition parameter).weight +
        parameterListWeight rank (!shortPosition) tail

def ParameterWordFrom.totalWeight
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} {columns : ℕ}
    (word : ParameterWordFrom rank state shortPosition columns) : Weight rank :=
  parameterListWeight rank shortPosition word.parameters

theorem parameterListWeight_append
    (rank : ℕ) (shortPosition : Bool)
    (left right : List (Fin (rank + 1))) :
    parameterListWeight rank shortPosition (left ++ right) =
      parameterListWeight rank shortPosition left +
        parameterListWeight rank (toggleN shortPosition left.length) right := by
  induction left generalizing shortPosition with
  | nil => simp [parameterListWeight]
  | cons parameter tail ih =>
      simp only [List.cons_append, parameterListWeight, List.length_cons]
      rw [ih]
      simp [add_assoc]

theorem parameterListWeight_badPair
    (rank : ℕ) (shortPosition : Bool) :
    parameterListWeight rank shortPosition
        [0, Fin.last rank] = 0 := by
  cases shortPosition <;>
    simp [parameterListWeight, parameterColumn, parameterComplement,
      Column.weight, oddBadPair_neutral, evenBadPair_neutral]

end FibonacciRibbonKernel
