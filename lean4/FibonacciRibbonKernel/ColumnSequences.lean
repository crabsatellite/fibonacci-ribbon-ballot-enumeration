import FibonacciRibbonKernel.ColumnWords

namespace FibonacciRibbonKernel

/-- State obtained after reading a list of columns. -/
def runColumns {rank : ℕ} : Weight rank → List (Column rank) → Weight rank
  | state, [] => state
  | state, column :: columns => runColumns (state + column.weight) columns

/-- Every internal prefix of every successive column is ballot. -/
def ColumnsBallotFrom {rank : ℕ} :
    Weight rank → List (Column rank) → Prop
  | _, [] => True
  | state, column :: columns =>
      column.prefixesDominant state ∧
        ColumnsBallotFrom (state + column.weight) columns

theorem Column.endpointDominant_of_prefixes
    {rank : ℕ} {state : Weight rank} {column : Column rank}
    (hcolumn : column.prefixesDominant state) :
    Dominant (state + column.weight) := by
  cases column with
  | singleton letter => exact hcolumn
  | tall omitted =>
      have hend := hcolumn (rank + 1)
      simpa [Column.weight, tallPrefixWeight_at_end] using hend

theorem runColumns_append
    {rank : ℕ} (state : Weight rank)
    (left right : List (Column rank)) :
    runColumns state (left ++ right) =
      runColumns (runColumns state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons column columns ih =>
      simp only [List.cons_append, runColumns]
      exact ih (state + column.weight)

theorem columnsBallotFrom_append_iff
    {rank : ℕ} (state : Weight rank)
    (left right : List (Column rank)) :
    ColumnsBallotFrom state (left ++ right) ↔
      ColumnsBallotFrom state left ∧
        ColumnsBallotFrom (runColumns state left) right := by
  induction left generalizing state with
  | nil => simp [ColumnsBallotFrom, runColumns]
  | cons column columns ih =>
      simp only [List.cons_append, ColumnsBallotFrom, runColumns]
      rw [ih]
      tauto

theorem dominant_runColumns_of_ballot
    {rank : ℕ} {state : Weight rank} {columns : List (Column rank)}
    (hstart : Dominant state)
    (hcolumns : ColumnsBallotFrom state columns) :
    Dominant (runColumns state columns) := by
  induction columns generalizing state with
  | nil => exact hstart
  | cons column columns ih =>
      exact ih (Column.endpointDominant_of_prefixes hcolumns.1) hcolumns.2

/-- A column block that is ballot from every dominant state and returns it. -/
structure NeutralColumnBlock {rank : ℕ} (block : List (Column rank)) : Prop where
  ballot : ∀ {state : Weight rank}, Dominant state →
    ColumnsBallotFrom state block
  run_eq : ∀ state : Weight rank, runColumns state block = state

theorem NeutralColumnBlock.front_iff
    {rank : ℕ} {block suffix : List (Column rank)}
    (hblock : NeutralColumnBlock block)
    {state : Weight rank} (hstate : Dominant state) :
    ColumnsBallotFrom state (block ++ suffix) ↔
      ColumnsBallotFrom state suffix := by
  rw [columnsBallotFrom_append_iff, hblock.run_eq state]
  simp [hblock.ballot hstate]

/--
Insertion or deletion of a neutral block after an arbitrary ballot column
prefix preserves the complete internal-prefix ballot condition.
-/
theorem NeutralColumnBlock.insert_iff
    {rank : ℕ} {block beforeColumns afterColumns : List (Column rank)}
    (hblock : NeutralColumnBlock block)
    {state : Weight rank} (hstate : Dominant state) :
    ColumnsBallotFrom state (beforeColumns ++ (block ++ afterColumns)) ↔
      ColumnsBallotFrom state (beforeColumns ++ afterColumns) := by
  constructor
  · intro h
    have hsplit :=
      (columnsBallotFrom_append_iff state beforeColumns
        (block ++ afterColumns)).mp h
    have hbeforeEnd := dominant_runColumns_of_ballot hstate hsplit.1
    apply (columnsBallotFrom_append_iff state beforeColumns afterColumns).mpr
    exact ⟨hsplit.1, (hblock.front_iff hbeforeEnd).mp hsplit.2⟩
  · intro h
    have hsplit :=
      (columnsBallotFrom_append_iff state beforeColumns afterColumns).mp h
    have hbeforeEnd := dominant_runColumns_of_ballot hstate hsplit.1
    apply (columnsBallotFrom_append_iff state beforeColumns
      (block ++ afterColumns)).mpr
    exact ⟨hsplit.1, (hblock.front_iff hbeforeEnd).mpr hsplit.2⟩

end FibonacciRibbonKernel
