import FibonacciRibbonKernel.UnrestrictedPaths
import Mathlib.Data.List.Infix
import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

open scoped Classical

/-- Difference weight of a finite row word. -/
def wordWeight {rank : ℕ} : List (Fin (rank + 1)) → Weight rank
  | [] => 0
  | letter :: word => letterWeight rank letter + wordWeight word

theorem wordWeight_apply
    {rank : ℕ} (word : List (Fin (rank + 1))) (i : Fin rank) :
    wordWeight word i =
      (word.count i.castSucc : ℤ) - (word.count i.succ : ℤ) := by
  induction word with
  | nil => simp [wordWeight]
  | cons letter word ih =>
      simp only [wordWeight, Pi.add_apply, ih, List.count_cons]
      simp only [letterWeight]
      split_ifs <;> simp_all <;> omega

/-- Read a list of defining letters from a specified state. -/
def runPlusWord {rank : ℕ} :
    Weight rank → List (Fin (rank + 1)) → Weight rank
  | state, [] => state
  | state, letter :: word => runPlusWord (plusState state letter) word

theorem runPlusWord_eq_add_wordWeight
    {rank : ℕ} (state : Weight rank) (word : List (Fin (rank + 1))) :
    runPlusWord state word = state + wordWeight word := by
  induction word generalizing state with
  | nil => simp [runPlusWord, wordWeight]
  | cons letter word ih =>
      rw [runPlusWord, ih]
      simp [plusState, wordWeight, add_assoc]

/-- Forget proof fields and read the row letters of a defining path. -/
def DefiningPathFrom.rowWord
    {rank : ℕ} {state : Weight rank} :
    {columns : ℕ} → DefiningPathFrom state columns →
      List (Fin (rank + 1))
  | 0, _ => []
  | _ + 1, ⟨letter, tail⟩ =>
      letter :: DefiningPathFrom.rowWord tail.1

theorem DefiningPathFrom.rowWord_length
    {rank : ℕ} {state : Weight rank} {columns : ℕ}
    (path : DefiningPathFrom state columns) :
    path.rowWord.length = columns := by
  induction columns generalizing state with
  | zero => rfl
  | succ columns ih =>
      obtain ⟨letter, tail⟩ := path
      simp [DefiningPathFrom.rowWord, ih tail.1]

theorem DefiningPathFrom.endpointDominant
    {rank : ℕ} {state : Weight rank} {columns : ℕ}
    (hstate : Dominant state) (path : DefiningPathFrom state columns) :
    Dominant (runPlusWord state path.rowWord) := by
  induction columns generalizing state with
  | zero => simpa [DefiningPathFrom.rowWord, runPlusWord] using hstate
  | succ columns ih =>
      obtain ⟨letter, tail⟩ := path
      exact ih tail.2 tail.1

/-- Every initial row-word segment of a defining path ends in the cone. -/
theorem DefiningPathFrom.prefixDominant
    {rank : ℕ} {state : Weight rank} {columns : ℕ}
    (hstate : Dominant state) (path : DefiningPathFrom state columns)
    {initial : List (Fin (rank + 1))} (hprefix : initial <+: path.rowWord) :
    Dominant (runPlusWord state initial) := by
  induction columns generalizing state initial with
  | zero =>
      have hempty : initial = [] := List.eq_nil_of_prefix_nil hprefix
      subst initial
      simpa [runPlusWord] using hstate
  | succ columns ih =>
      obtain ⟨letter, tail⟩ := path
      cases initial with
      | nil => simpa [runPlusWord] using hstate
      | cons first remaining =>
          have hcons : first :: remaining <+:
              letter :: DefiningPathFrom.rowWord tail.1 := hprefix
          obtain ⟨rfl, hremaining⟩ := List.cons_prefix_cons.mp hcons
          exact ih tail.2 tail.1 hremaining

/-- Literal prefix-multiplicity formulation of a standard-tableau row word. -/
def StandardRowWord {rank : ℕ} (word : List (Fin (rank + 1))) : Prop :=
  ∀ initial, initial <+: word → ∀ i : Fin rank,
    initial.count i.succ ≤ initial.count i.castSucc

theorem DefiningPathFrom.rowWord_standard
    {rank columns : ℕ}
    (path : DefiningPathFrom (0 : Weight rank) columns) :
    StandardRowWord path.rowWord := by
  intro initial hprefix i
  have hdominant := path.prefixDominant (dominant_zero rank) hprefix i
  rw [runPlusWord_eq_add_wordWeight] at hdominant
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, wordWeight_apply] at hdominant
  omega

/-- Fixed-length row words whose every prefix has weakly decreasing row counts. -/
structure BallotRowWordFrom {rank : ℕ} (state : Weight rank) (columns : ℕ) where
  word : List (Fin (rank + 1))
  length_eq : word.length = columns
  ballot : ∀ initial, initial <+: word →
    Dominant (runPlusWord state initial)

@[ext] theorem BallotRowWordFrom.ext
    {rank : ℕ} {state : Weight rank} {columns : ℕ}
    {left right : BallotRowWordFrom state columns}
    (hword : left.word = right.word) : left = right := by
  cases left
  cases right
  simp_all

def DefiningPathFrom.toBallotRowWord
    {rank : ℕ} {state : Weight rank} {columns : ℕ}
    (hstate : Dominant state) (path : DefiningPathFrom state columns) :
    BallotRowWordFrom state columns where
  word := path.rowWord
  length_eq := path.rowWord_length
  ballot := fun _ hprefix => path.prefixDominant hstate hprefix

/-- Recover the defining path by successively reading a ballot row word. -/
def BallotRowWordFrom.toDefiningPath
    {rank : ℕ} {state : Weight rank} :
    (columns : ℕ) → BallotRowWordFrom state columns →
      DefiningPathFrom state columns
  | 0, _ => PUnit.unit
  | columns + 1, rowWord => by
      have hne : rowWord.word ≠ [] := by
        intro hempty
        have hlength := rowWord.length_eq
        rw [hempty] at hlength
        simp at hlength
      let head := rowWord.word.head hne
      let tail := rowWord.word.tail
      have hdecomp : head :: tail = rowWord.word :=
        List.cons_head_tail hne
      have htailLength : tail.length = columns := by
        have hlength := rowWord.length_eq
        rw [← hdecomp] at hlength
        simp at hlength
        exact hlength
      have hvalid : PlusValid state head := by
        have hone := rowWord.ballot [head] (by
          rw [← hdecomp]
          simp)
        simpa [PlusValid, runPlusWord] using hone
      let tailWord : BallotRowWordFrom (plusState state head) columns :=
        { word := tail
          length_eq := htailLength
          ballot := by
            intro initial hprefix
            have hwhole : head :: initial <+: rowWord.word := by
              rw [← hdecomp]
              exact List.cons_prefix_cons.mpr ⟨rfl, hprefix⟩
            have h := rowWord.ballot (head :: initial) hwhole
            simpa [runPlusWord] using h }
      exact ⟨head, ⟨tailWord.toDefiningPath columns, hvalid⟩⟩

theorem BallotRowWordFrom.toDefiningPath_rowWord
    {rank : ℕ} {state : Weight rank} {columns : ℕ}
    (rowWord : BallotRowWordFrom state columns) :
    (rowWord.toDefiningPath columns).rowWord = rowWord.word := by
  induction columns generalizing state with
  | zero =>
      have hnil : rowWord.word = [] := List.length_eq_zero_iff.mp rowWord.length_eq
      simpa [BallotRowWordFrom.toDefiningPath, DefiningPathFrom.rowWord] using hnil.symm
  | succ columns ih =>
      have hne : rowWord.word ≠ [] := by
        intro hempty
        have hlength := rowWord.length_eq
        rw [hempty] at hlength
        simp at hlength
      let head := rowWord.word.head hne
      let tail := rowWord.word.tail
      have hdecomp : head :: tail = rowWord.word := List.cons_head_tail hne
      have htailLength : tail.length = columns := by
        have hlength := rowWord.length_eq
        rw [← hdecomp] at hlength
        simp at hlength
        exact hlength
      let tailWord : BallotRowWordFrom (plusState state head) columns :=
        { word := tail
          length_eq := htailLength
          ballot := by
            intro initial hprefix
            have hwhole : head :: initial <+: rowWord.word := by
              rw [← hdecomp]
              exact List.cons_prefix_cons.mpr ⟨rfl, hprefix⟩
            simpa [runPlusWord] using rowWord.ballot (head :: initial) hwhole }
      change head :: (tailWord.toDefiningPath columns).rowWord = rowWord.word
      rw [ih tailWord, hdecomp]

theorem DefiningPathFrom.toBallotRowWord_toDefiningPath
    {rank : ℕ} {state : Weight rank} {columns : ℕ}
    (hstate : Dominant state) (path : DefiningPathFrom state columns) :
    (path.toBallotRowWord hstate).toDefiningPath columns = path := by
  induction columns generalizing state with
  | zero =>
      cases path
      rfl
  | succ columns ih =>
      obtain ⟨letter, tail⟩ := path
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Subtype.ext (ih tail.2 tail.1))

/-- Explicit row-word encoding equivalence for standard tableaux. -/
def definingPathBallotRowWordEquiv
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (columns : ℕ) :
    DefiningPathFrom state columns ≃ BallotRowWordFrom state columns where
  toFun := DefiningPathFrom.toBallotRowWord hstate
  invFun := fun rowWord => rowWord.toDefiningPath columns
  left_inv := DefiningPathFrom.toBallotRowWord_toDefiningPath hstate
  right_inv := by
    intro rowWord
    apply BallotRowWordFrom.ext
    exact BallotRowWordFrom.toDefiningPath_rowWord rowWord

/--
Standard Young tableaux with at most `rank + 1` rows, encoded by the row of
each successive entry.  `rowWord_standard` proves this carrier has precisely
the usual row/column condition used in the manuscript proof.
-/
abbrev StandardTableau (rank columns : ℕ) :=
  DefiningPathFrom (0 : Weight rank) columns

/-- A bounded partition of `columns`, stored as its weakly decreasing rows. -/
def BoundedPartition (rank columns : ℕ) :=
  {rows : Fin (rank + 1) → Fin (columns + 1) //
    (∀ i : Fin rank, rows i.succ ≤ rows i.castSucc) ∧
      (∑ row, (rows row : ℕ)) = columns}

noncomputable instance boundedPartitionFintype (rank columns : ℕ) :
    Fintype (BoundedPartition rank columns) := by
  classical
  unfold BoundedPartition
  infer_instance

theorem sum_rowWord_count_eq_length
    {rank : ℕ} (word : List (Fin (rank + 1))) :
    (∑ row : Fin (rank + 1), word.count row) = word.length := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      simp only [List.count_cons]
      rw [Finset.sum_add_distrib, ih]
      simp

/-- Final partition shape of the row-word standard tableau. -/
noncomputable def StandardTableau.shape
    {rank columns : ℕ} (tableau : StandardTableau rank columns) :
    BoundedPartition rank columns := by
  classical
  let word := tableau.rowWord
  let rows : Fin (rank + 1) → Fin (columns + 1) := fun row =>
    ⟨word.count row, by
      have hcount : word.count row ≤ word.length := List.count_le_length
      have hlength : word.length = columns := tableau.rowWord_length
      rw [hlength] at hcount
      omega⟩
  refine ⟨rows, ?_, ?_⟩
  · intro i
    exact tableau.rowWord_standard word (List.prefix_refl word) i
  · simp only [rows]
    have hsum := sum_rowWord_count_eq_length word
    have hlength : word.length = columns := tableau.rowWord_length
    rw [hlength] at hsum
    exact hsum

/-- The usual row-word carrier of standard Young tableaux of bounded height. -/
abbrev StandardRowWordTableau (rank columns : ℕ) :=
  BallotRowWordFrom (0 : Weight rank) columns

noncomputable instance standardRowWordTableauFintype (rank columns : ℕ) :
    Fintype (StandardRowWordTableau rank columns) :=
  Fintype.ofEquiv (StandardTableau rank columns)
    (definingPathBallotRowWordEquiv (dominant_zero rank) columns)

/-- Final partition shape in the usual row-word tableau carrier. -/
noncomputable def StandardRowWordTableau.shape
    {rank columns : ℕ} (tableau : StandardRowWordTableau rank columns) :
    BoundedPartition rank columns := by
  classical
  let rows : Fin (rank + 1) → Fin (columns + 1) := fun row =>
    ⟨tableau.word.count row, by
      have hcount : tableau.word.count row ≤ tableau.word.length :=
        List.count_le_length
      rw [tableau.length_eq] at hcount
      omega⟩
  refine ⟨rows, ?_, ?_⟩
  · intro i
    have hdominant := tableau.ballot tableau.word (List.prefix_refl _) i
    rw [runPlusWord_eq_add_wordWeight] at hdominant
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, wordWeight_apply] at hdominant
    change tableau.word.count i.succ ≤ tableau.word.count i.castSucc
    omega
  · simp only [rows]
    have hsum := sum_rowWord_count_eq_length tableau.word
    rw [tableau.length_eq] at hsum
    exact hsum

theorem StandardTableau.shape_toBallotRowWord
    {rank columns : ℕ} (tableau : StandardTableau rank columns) :
    StandardRowWordTableau.shape
        (tableau.toBallotRowWord (dominant_zero rank)) = tableau.shape := by
  apply Subtype.ext
  funext row
  apply Fin.ext
  rfl

/-- Shape-preserving explicit equivalence with ordinary standard row words. -/
def fixedShapeStandardTableauEquiv
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    {tableau : StandardTableau rank columns // tableau.shape = shape} ≃
      {tableau : StandardRowWordTableau rank columns //
        StandardRowWordTableau.shape tableau = shape} where
  toFun tableau :=
    ⟨tableau.1.toBallotRowWord (dominant_zero rank), by
      rw [StandardTableau.shape_toBallotRowWord, tableau.2]⟩
  invFun tableau :=
    ⟨tableau.1.toDefiningPath columns, by
      have hword := BallotRowWordFrom.toDefiningPath_rowWord tableau.1
      have hshape :
          StandardTableau.shape (tableau.1.toDefiningPath columns) =
            StandardRowWordTableau.shape tableau.1 := by
        apply Subtype.ext
        funext row
        apply Fin.ext
        simpa [StandardTableau.shape, StandardRowWordTableau.shape] using
          congrArg (fun word : List (Fin (rank + 1)) => word.count row) hword
      exact hshape.trans tableau.2⟩
  left_inv tableau := by
    apply Subtype.ext
    exact DefiningPathFrom.toBallotRowWord_toDefiningPath
      (dominant_zero rank) tableau.1
  right_inv tableau := by
    apply Subtype.ext
    apply BallotRowWordFrom.ext
    exact BallotRowWordFrom.toDefiningPath_rowWord tableau.1

/-- The literal `f^λ`: number of standard tableaux with final shape `λ`. -/
noncomputable def standardTableauNumber
    {rank columns : ℕ} (shape : BoundedPartition rank columns) : ℕ :=
  Fintype.card
    {tableau : StandardTableau rank columns // tableau.shape = shape}

/-- The same `f^λ` measured directly on ordinary standard row words. -/
noncomputable def standardRowWordTableauNumber
    {rank columns : ℕ} (shape : BoundedPartition rank columns) : ℕ :=
  Fintype.card
    {tableau : StandardRowWordTableau rank columns //
      StandardRowWordTableau.shape tableau = shape}

theorem standardTableauNumber_eq_rowWordNumber
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    standardTableauNumber shape = standardRowWordTableauNumber shape :=
  Fintype.card_congr (fixedShapeStandardTableauEquiv shape)

/-- Sum of the fixed-shape fibers is the count of all bounded-height tableaux. -/
theorem standardTableau_card_eq_sum_shape_numbers (rank columns : ℕ) :
    Fintype.card (StandardTableau rank columns) =
      ∑ shape : BoundedPartition rank columns,
        standardTableauNumber shape := by
  classical
  unfold standardTableauNumber
  simp_rw [Fintype.card_subtype]
  rw [Fintype.card]
  exact Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (StandardTableau rank columns)))
    (t := (Finset.univ : Finset (BoundedPartition rank columns)))
    (f := StandardTableau.shape)
    (by intro tableau htableau; exact Finset.mem_univ _)

/-- Exact unrestricted formula in bounded-partition/SYT notation. -/
theorem unrestrictedCount_eq_sum_standardTableauNumbers (rank columns : ℕ) :
    unrestrictedCount rank columns =
      ∑ shape : BoundedPartition rank columns,
        standardTableauNumber shape := by
  rw [unrestrictedCount_eq_pureDefiningCount,
    definingIterate_one_eq_card_paths,
    standardTableau_card_eq_sum_shape_numbers]

end FibonacciRibbonKernel
