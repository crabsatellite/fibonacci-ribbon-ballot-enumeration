import FibonacciRibbonKernel.ColumnSequences
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

theorem dominant_add_letterWeight_zero
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) :
    Dominant (state + letterWeight rank 0) := by
  intro i
  have hi := hstate i
  have hsucc : (0 : Fin (rank + 1)) ≠ i.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  rw [Pi.add_apply]
  simp [letterWeight, hsucc]
  split_ifs <;> omega

theorem dominant_add_tallWeight_last
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) :
    Dominant (state + tallWeight rank (Fin.last rank)) := by
  rw [tallWeight_eq_neg_letterWeight]
  intro i
  have hi := hstate i
  have hcast : Fin.last rank ≠ i.castSucc := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  rw [Pi.add_apply]
  simp [letterWeight, hcast]
  split_ifs <;> omega

/-- The two literal columns forced by the forbidden parameter pair. -/
def badPairBlock (rank : ℕ) (shortPosition : Bool) : List (Column rank) :=
  [parameterColumn shortPosition (0 : Fin (rank + 1)),
    parameterColumn (!shortPosition) (Fin.last rank)]

theorem badPairBlock_word (rank : ℕ) (shortPosition : Bool) :
    (badPairBlock rank shortPosition).flatMap Column.word = fullWord rank := by
  simpa [badPairBlock] using badParameterPair_word rank shortPosition

theorem oddBadPairBlock_ballot
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) :
    ColumnsBallotFrom state
      [Column.singleton (0 : Fin (rank + 1)), Column.tall 0] := by
  have hfirst : Dominant (state + letterWeight rank 0) :=
    dominant_add_letterWeight_zero hstate
  have hend :
      Dominant ((state + letterWeight rank 0) + tallWeight rank 0) := by
    rw [add_assoc, oddBadPair_neutral, add_zero]
    exact hstate
  exact ⟨hfirst,
    ⟨(tall_prefixesDominant_iff_endpoint 0 hfirst).mpr hend, trivial⟩⟩

theorem evenBadPairBlock_ballot
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) :
    ColumnsBallotFrom state
      [Column.tall (Fin.last rank), Column.singleton (Fin.last rank)] := by
  have hfirst : Dominant (state + tallWeight rank (Fin.last rank)) :=
    dominant_add_tallWeight_last hstate
  have hend :
      Dominant ((state + tallWeight rank (Fin.last rank)) +
        letterWeight rank (Fin.last rank)) := by
    rw [add_assoc, evenBadPair_neutral, add_zero]
    exact hstate
  exact ⟨(tall_prefixesDominant_iff_endpoint (Fin.last rank) hstate).mpr hfirst,
    ⟨hend, trivial⟩⟩

theorem oddBadPairBlock_run_eq (rank : ℕ) (state : Weight rank) :
    runColumns state
      [Column.singleton (0 : Fin (rank + 1)), Column.tall 0] = state := by
  simp only [runColumns, Column.weight]
  rw [add_assoc, oddBadPair_neutral, add_zero]

theorem evenBadPairBlock_run_eq (rank : ℕ) (state : Weight rank) :
    runColumns state
      [Column.tall (Fin.last rank), Column.singleton (Fin.last rank)] = state := by
  simp only [runColumns, Column.weight]
  rw [add_assoc, evenBadPair_neutral, add_zero]

/-- Every forbidden pair is a ballot-neutral full-alphabet block. -/
theorem badPairBlock_neutral (rank : ℕ) (shortPosition : Bool) :
    NeutralColumnBlock (badPairBlock rank shortPosition) := by
  cases shortPosition with
  | false =>
      constructor
      · intro state hstate
        simpa [badPairBlock, parameterColumn, parameterComplement] using
          (evenBadPairBlock_ballot (rank := rank) hstate)
      · intro state
        simpa [badPairBlock, parameterColumn, parameterComplement] using
          evenBadPairBlock_run_eq rank state
  | true =>
      constructor
      · intro state hstate
        simpa [badPairBlock, parameterColumn, parameterComplement] using
          (oddBadPairBlock_ballot (rank := rank) hstate)
      · intro state
        simpa [badPairBlock, parameterColumn, parameterComplement] using
          oddBadPairBlock_run_eq rank state

/-- Exact arbitrary-position deletion/insertion criterion for one bad pair. -/
theorem badPairBlock_insert_iff
    {rank : ℕ} (shortPosition : Bool)
    {beforeColumns afterColumns : List (Column rank)}
    {state : Weight rank} (hstate : Dominant state) :
    ColumnsBallotFrom state
        (beforeColumns ++ (badPairBlock rank shortPosition ++ afterColumns)) ↔
      ColumnsBallotFrom state (beforeColumns ++ afterColumns) :=
  (badPairBlock_neutral rank shortPosition).insert_iff hstate

end FibonacciRibbonKernel
