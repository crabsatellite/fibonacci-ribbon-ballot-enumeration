import FibonacciRibbonKernel.RSKBoundaryTableau

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def tableauPrefixShape
    {size : ℕ} (tableau : StandardRowWordTableau size size)
    (prefixLength : ℕ) : GrowthShape (size + 1) where
  rows := fun row => (tableau.word.take prefixLength).count row
  antitone := by
    intro upper lower hadjacent
    have hupperBound : upper.val < size := by omega
    let index : Fin size := ⟨upper.val, hupperBound⟩
    have hupperEq : index.castSucc = upper := Fin.ext rfl
    have hlowerEq : index.succ = lower := by
      apply Fin.ext
      simpa [index] using hadjacent.symm
    have hdominant := tableau.ballot (tableau.word.take prefixLength)
      (List.take_prefix prefixLength tableau.word) index
    rw [runPlusWord_eq_add_wordWeight] at hdominant
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, wordWeight_apply] at hdominant
    rw [hupperEq, hlowerEq] at hdominant
    omega

noncomputable def tableauBoundaryLetter
    {size : ℕ} (tableau : StandardRowWordTableau size size)
    (column : Fin size) : Fin (size + 1) :=
  tableau.word[column.val]'(by rw [tableau.length_eq]; exact column.isLt)

theorem tableauBoundaryLetter_addable
    {size : ℕ} (tableau : StandardRowWordTableau size size)
    (column : Fin size) :
    (tableauPrefixShape tableau column.val).Addable
      (tableauBoundaryLetter tableau column) := by
  let letter := tableauBoundaryLetter tableau column
  by_cases hzero : letter.val = 0
  · exact Or.inl hzero
  · right
    intro previous hprevious
    have hpreviousNe : previous ≠ letter := by
      intro heq
      have hvalue := congrArg Fin.val heq
      omega
    have hletterAt : tableau.word[column.val]'(by
        rw [tableau.length_eq]; exact column.isLt) = letter := rfl
    have htake := List.take_concat_get (l := tableau.word) (i := column.val)
      (by rw [tableau.length_eq]; exact column.isLt)
    have hdominant := tableau.ballot (tableau.word.take (column.val + 1))
      (List.take_prefix (column.val + 1) tableau.word)
    have hpreviousBound : previous.val < size := by
      have hletterBound := letter.isLt
      omega
    let index : Fin size := ⟨previous.val, hpreviousBound⟩
    have hindexCast : index.castSucc = previous := Fin.ext rfl
    have hindexSucc : index.succ = letter := by
      apply Fin.ext
      simpa [index] using hprevious
    have hdom := hdominant index
    rw [runPlusWord_eq_add_wordWeight] at hdom
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, wordWeight_apply] at hdom
    rw [hindexCast, hindexSucc] at hdom
    rw [← htake, List.concat_eq_append,
      List.count_append, List.count_append,
      List.count_singleton, List.count_singleton, hletterAt] at hdom
    have hreverse : letter ≠ previous := Ne.symm hpreviousNe
    simp [hreverse] at hdom
    change (tableau.word.take column.val).count letter <
      (tableau.word.take column.val).count previous
    omega

noncomputable def tableauBoundaryEdge
    {size : ℕ} (tableau : StandardRowWordTableau size size)
    (column : Fin size) :
    GrowthStep (tableauPrefixShape tableau column.val) :=
  .add (tableauBoundaryLetter tableau column)
    (tableauBoundaryLetter_addable tableau column)

theorem tableauBoundaryEdge_target
    {size : ℕ} (tableau : StandardRowWordTableau size size)
    (column : Fin size) :
    (tableauBoundaryEdge tableau column).target =
      tableauPrefixShape tableau (column.val + 1) := by
  apply GrowthShape.ext
  funext row
  have htake := List.take_concat_get (l := tableau.word) (i := column.val)
    (by rw [tableau.length_eq]; exact column.isLt)
  have hcountNext :
      (tableau.word.take (column.val + 1)).count row =
        (tableau.word.take column.val).count row +
          if row = tableauBoundaryLetter tableau column then 1 else 0 := by
    rw [← htake, List.concat_eq_append, List.count_append,
      List.count_singleton]
    have hletterAt : tableau.word[column.val]'(by
        rw [tableau.length_eq]; exact column.isLt) =
      tableauBoundaryLetter tableau column := rfl
    rw [hletterAt]
    by_cases heq : tableauBoundaryLetter tableau column = row
    · simp [heq]
    · simp [heq, Ne.symm heq]
  change (if row = tableauBoundaryLetter tableau column then
      (tableau.word.take column.val).count row + 1
    else (tableau.word.take column.val).count row) =
      (tableau.word.take (column.val + 1)).count row
  rw [hcountNext]
  by_cases heq : row = tableauBoundaryLetter tableau column
  · simp [heq]
  · simp [heq]

theorem tableauPrefixShape_zero
    {size : ℕ} (tableau : StandardRowWordTableau size size) :
    tableauPrefixShape tableau 0 = GrowthShape.empty (size + 1) := by
  apply GrowthShape.ext
  rfl

theorem tableauPrefixShape_final_eq_of_shape_eq
    {size : ℕ} (left right : StandardRowWordTableau size size)
    (hshape : left.shape = right.shape) :
    tableauPrefixShape left size = tableauPrefixShape right size := by
  apply GrowthShape.ext
  funext row
  have hrows := congrArg
    (fun shape : BoundedPartition size size => (shape.1 row).val) hshape
  change left.word.count row = right.word.count row at hrows
  change (left.word.take size).count row = (right.word.take size).count row
  rw [List.take_of_length_le (by rw [left.length_eq]),
    List.take_of_length_le (by rw [right.length_eq])]
  exact hrows

theorem tableau_eq_of_prefixShape_eq
    {size : ℕ} (left right : StandardRowWordTableau size size)
    (hshape : ∀ column : Fin (size + 1),
      tableauPrefixShape left column.val = tableauPrefixShape right column.val) :
    left = right := by
  apply BallotRowWordFrom.ext
  apply List.ext_getElem
  · rw [left.length_eq, right.length_eq]
  · intro index hleft hright
    let column : Fin size := ⟨index, by simpa [left.length_eq] using hleft⟩
    have hbase : tableauPrefixShape left column.val =
        tableauPrefixShape right column.val := by
      simpa only [Fin.val_castSucc] using hshape column.castSucc
    have hnext : tableauPrefixShape left (column.val + 1) =
        tableauPrefixShape right (column.val + 1) := by
      simpa only [Fin.val_succ] using hshape column.succ
    have hleftTarget := tableauBoundaryEdge_target left column
    have hrightTarget := tableauBoundaryEdge_target right column
    have hsteps : tableauBoundaryEdge left column =
        (tableauBoundaryEdge right column).castBase hbase.symm := by
      apply GrowthStep.target_injective
      rw [GrowthStep.target_castBase, hleftTarget, hrightTarget, hnext]
    have hletters : tableauBoundaryLetter left column =
        tableauBoundaryLetter right column := by
      have hrows := congrArg GrowthStep.addedRow? hsteps
      rw [GrowthStep.addedRow?_castBase] at hrows
      unfold tableauBoundaryEdge GrowthStep.addedRow? at hrows
      change some (tableauBoundaryLetter left column) =
        some (tableauBoundaryLetter right column) at hrows
      exact Option.some.inj hrows
    exact hletters

theorem finalBoundaryTableau_prefixShape
    (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (column : Fin (size + 1)) :
    tableauPrefixShape (finalBoundaryTableau size permutation) column.val =
      (finalGrowthBoundary size permutation).vertices column := by
  apply GrowthShape.ext
  funext row
  change ((List.ofFn (finalBoundaryRow size permutation)).take column.val).count row = _
  rw [List.take_ofFn_eq_ofFn _ column.val (by omega)]
  have hcount := finalBoundary_prefix_count size permutation column.val (by omega) row
  simpa only using hcount

end FibonacciRibbonKernel
