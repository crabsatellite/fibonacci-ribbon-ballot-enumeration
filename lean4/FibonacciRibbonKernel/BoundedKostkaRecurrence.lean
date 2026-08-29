import FibonacciRibbonKernel.BoundedPartitionRemoval
import KostkaNumbers.HookLength.HookLengthFormula
import KostkaNumbers.Kostka.Recursion

namespace FibonacciRibbonKernel

open scoped Classical
open YoungDiagram Kostka

abbrev BoundedPartition.RemovableRowIndex
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :=
  {row : Fin (rank + 1) // shape.RemovableRow row}

noncomputable instance BoundedPartition.removableRowIndexFintype
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    Fintype shape.RemovableRowIndex := by
  unfold BoundedPartition.RemovableRowIndex
  infer_instance

noncomputable def BoundedPartition.removableRowsSubtypeEquiv
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    {row : Fin (rank + 1) // row ∈ shape.removableRows} ≃
      shape.RemovableRowIndex :=
  Equiv.subtypeEquivRight fun row => shape.mem_removableRows_iff row

theorem boundedFactorialDeterminant_corner_recurrence_index
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    (columns : ℚ) * boundedFactorialDeterminant shape =
      ∑ removable : shape.RemovableRowIndex,
        boundedFactorialDeterminant
          (shape.removeRow removable.1 removable.2) := by
  rw [boundedFactorialDeterminant_corner_recurrence]
  rw [Finset.attach_eq_univ]
  let equivalence := shape.removableRowsSubtypeEquiv
  apply Fintype.sum_equiv equivalence
  intro item
  congr 2

theorem BoundedPartition.youngDiagram_rowLen'_eq_zero_of_bound
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : ℕ) (hrow : rank + 1 ≤ row) :
    shape.youngDiagram.rowLen' row = 0 := by
  rw [rowLen'_eq_rowLen]
  apply Nat.eq_zero_of_not_pos
  intro hpositive
  have hmem : (row, 0) ∈ shape.youngDiagram := by
    rw [shape.youngDiagram.mem_iff_lt_rowLen]
    exact hpositive
  obtain ⟨rowFin, hrowFin, hcolumn⟩ :=
    (shape.mem_youngDiagram_iff row 0).mp hmem
  omega

theorem BoundedPartition.subSingle_row_lt_bound
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (removal : SubSingle shape.youngDiagram) :
    removal.1 < rank + 1 := by
  have hpositive : 0 < shape.youngDiagram.rowLen' removal.1 := by
    have hle := removal.2.2 removal.1
    have hone : 1 ≤ shape.youngDiagram.rowLen' removal.1 := by
      simpa [Finsupp.single_apply] using hle
    omega
  by_contra hnot
  have hzero := shape.youngDiagram_rowLen'_eq_zero_of_bound
    removal.1 (by omega)
  omega

/-- A one-row Young-diagram subtraction is exactly an outer-corner row. -/
noncomputable def BoundedPartition.subSingleToRemovableRow
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    SubSingle shape.youngDiagram → shape.RemovableRowIndex :=
  fun removal => by
    let row : Fin (rank + 1) :=
      ⟨removal.1, shape.subSingle_row_lt_bound removal⟩
    refine ⟨row, ?_, ?_⟩
    · have hle := removal.2.2 removal.1
      have hpositive : 0 < shape.youngDiagram.rowLen' removal.1 := by
        have hone : 1 ≤ shape.youngDiagram.rowLen' removal.1 := by
          simpa [Finsupp.single_apply] using hle
        omega
      rw [rowLen'_eq_rowLen, shape.youngDiagram_rowLen row] at hpositive
      exact hpositive
    · intro next hnext
      have hcondition := removal.2.1 removal.1
      have hcurrent : shape.youngDiagram.rowLen' removal.1 =
          (shape.1 row).val := by
        rw [rowLen'_eq_rowLen]
        simpa [row] using shape.youngDiagram_rowLen row
      have hfollowing : shape.youngDiagram.rowLen' (removal.1 + 1) =
          (shape.1 next).val := by
        rw [rowLen'_eq_rowLen]
        have hnextVal : next.val = removal.1 + 1 := by
          simpa [row] using hnext
        rw [← hnextVal]
        exact shape.youngDiagram_rowLen next
      rw [hcurrent, hfollowing] at hcondition
      have hsingle : (Finsupp.single removal.1 1) removal.1 = 1 := by simp
      rw [hsingle] at hcondition
      have hnat : (shape.1 next).val < (shape.1 row).val := by
        have hpositive : 0 < (shape.1 row).val := by
          have hle := removal.2.2 removal.1
          have hone : 1 ≤ shape.youngDiagram.rowLen' removal.1 := by
            simpa [Finsupp.single_apply] using hle
          rw [hcurrent] at hone
          omega
        exact Nat.lt_of_le_sub_one hpositive hcondition
      exact hnat

/-- Every removable bounded row supplies the corresponding `SubSingle`. -/
noncomputable def BoundedPartition.removableRowToSubSingle
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    shape.RemovableRowIndex → SubSingle shape.youngDiagram :=
  fun removable => by
    refine ⟨removable.1.val, ?_, ?_⟩
    · intro index
      simp only [Finsupp.single_apply]
      split_ifs with hindex
      · subst index
        by_cases hnext : removable.1.val + 1 < rank + 1
        · let next : Fin (rank + 1) :=
            ⟨removable.1.val + 1, hnext⟩
          have hstrict := removable.2.2 next rfl
          have hcurrent : shape.youngDiagram.rowLen' removable.1.val =
              (shape.1 removable.1).val := by
            simp [rowLen'_eq_rowLen]
          have hfollowing :
              shape.youngDiagram.rowLen' (removable.1.val + 1) =
                (shape.1 next).val := by
            rw [rowLen'_eq_rowLen]
            simpa [next] using shape.youngDiagram_rowLen next
          rw [hcurrent, hfollowing]
          omega
        · have hzero := shape.youngDiagram_rowLen'_eq_zero_of_bound
            (removable.1.val + 1) (by omega)
          rw [hzero]
          exact Nat.zero_le _
      · rw [Nat.sub_zero]
        exact shape.youngDiagram.rowLen'_anti index.le_succ
    · intro index
      simp only [Finsupp.single_apply]
      split_ifs with hindex
      · subst index
        have hcurrent : shape.youngDiagram.rowLen' removable.1.val =
            (shape.1 removable.1).val := by
          simp [rowLen'_eq_rowLen]
        rw [hcurrent]
        exact removable.2.1
      · exact Nat.zero_le _

noncomputable def BoundedPartition.subSingleRemovableRowEquiv
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    SubSingle shape.youngDiagram ≃ shape.RemovableRowIndex where
  toFun := shape.subSingleToRemovableRow
  invFun := shape.removableRowToSubSingle
  left_inv removal := by
    apply Subtype.ext
    rfl
  right_inv removable := by
    apply Subtype.ext
    apply Fin.ext
    rfl

theorem BoundedPartition.youngDiagram_sub_removableRow
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (row : Fin (rank + 1)) (hremovable : shape.RemovableRow row) :
    shape.youngDiagram.sub (Finsupp.single row.val 1) =
      (shape.removeRow row hremovable).youngDiagram := by
  refine (rowLen'_eq_iff
    (γ := shape.youngDiagram.sub (Finsupp.single row.val 1))
    (γ' := (shape.removeRow row hremovable).youngDiagram)).mp ?_
  apply Finsupp.ext
  intro index
  have hsubCondition :=
    (shape.removableRowToSubSingle ⟨row, hremovable⟩).2.1
  change ∀ current,
      shape.youngDiagram.rowLen' current -
          (Finsupp.single row.val 1) current ≥
        shape.youngDiagram.rowLen' (current + 1) at hsubCondition
  rw [sub_rowLen' (sub_cond hsubCondition)]
  change shape.youngDiagram.rowLen' index -
      (Finsupp.single row.val 1) index =
    (shape.removeRow row hremovable).youngDiagram.rowLen' index
  by_cases hbound : index < rank + 1
  · let candidate : Fin (rank + 1) := ⟨index, hbound⟩
    have hleft : shape.youngDiagram.rowLen' index =
        (shape.1 candidate).val := by
      rw [rowLen'_eq_rowLen]
      simpa [candidate] using shape.youngDiagram_rowLen candidate
    have hright :
        (shape.removeRow row hremovable).youngDiagram.rowLen' index =
          ((shape.removeRow row hremovable).1 candidate).val := by
      rw [rowLen'_eq_rowLen]
      simpa [candidate] using
        (shape.removeRow row hremovable).youngDiagram_rowLen candidate
    rw [hleft, hright, shape.removeRow_value]
    unfold BoundedPartition.decrementedRowValues
    by_cases hcandidate : candidate = row
    · rw [hcandidate]
      have hindex : index = row.val := by
        exact congrArg Fin.val hcandidate
      simp [hindex]
    · have hindexNe : index ≠ row.val := by
        intro heq
        apply hcandidate
        exact Fin.ext heq
      simp [hcandidate, hindexNe]
  · have hindexBound : rank + 1 ≤ index := by omega
    rw [shape.youngDiagram_rowLen'_eq_zero_of_bound index hindexBound]
    have hrightZero :=
      (shape.removeRow row hremovable).youngDiagram_rowLen'_eq_zero_of_bound
        index hindexBound
    rw [hrightZero]
    simp [Finsupp.single_apply]

theorem subSingle_sum_eq_subRowLensType_sum_local
    {diagram : YoungDiagram} :
    ∑ removal : SubSingle diagram,
        kostkaNumber
          (diagram.sub (Finsupp.single removal.1 1))
          (Multiset.replicate (diagram.card - 1) 1) =
      ∑ removal ∈
          {candidate : SubRowLensType diagram |
            ∃ row : ℕ, candidate.1 = Finsupp.single row 1},
        kostkaNumber (diagram.sub removal.1)
          (Multiset.replicate (diagram.card - 1) 1) := by
  let embedding : SubSingle diagram → SubRowLensType diagram :=
    fun ⟨row, hrow⟩ => ⟨Finsupp.single row 1, hrow⟩
  refine Finset.sum_nbij embedding ?_ ?_ ?_ ?_
  · grind
  · intro ⟨left, hleft⟩ _ ⟨right, hright⟩ _
    unfold SubRowLensType
    simp [embedding, Finsupp.single_left_inj]
  · intro ⟨removal, hremoval⟩
    unfold SubRowLensType
    simp [embedding]
    grind
  · simp [embedding]

theorem sum_support_gt_one_local {function : ℕ →₀ ℕ}
    (h : function.support.card ≥ 2 ∨ ∃ row, function row > 1) :
    ∑ row ∈ function.support, function row > 1 := by
  rcases h with hcard | hvalue
  · have hone : function.support.card • 1 > 1 := by lia
    exact lt_of_lt_of_le hone <|
      Finset.card_nsmul_le_sum _ _ 1 (by grind)
  · obtain ⟨row, hrow⟩ := hvalue
    exact lt_of_lt_of_le hrow (Finset.single_le_sum (by lia) (by grind))

theorem kostka_recursion_single_local
    {diagram : YoungDiagram} (hdiagram : diagram.card ≠ 0) :
    kostkaNumber diagram (Multiset.replicate diagram.card 1) =
      ∑ removal : SubSingle diagram,
        kostkaNumber
          (diagram.sub (Finsupp.single removal.1 1))
          (Multiset.replicate (diagram.card - 1) 1) := by
  have hcontent : (Multiset.replicate diagram.card 1).toList ≠ [] := by
    rw [ne_eq, Multiset.toList_eq_nil, Eq.comm, Multiset.eq_replicate]
    simp [hdiagram.symm]
  rw [kostka_recursion hcontent (by simp [Multiset.mem_replicate]) (by simp),
    subSingle_sum_eq_subRowLensType_sum_local]
  symm
  classical refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) ?_ ?_
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter,
      true_and, not_exists]
    intro removal hnotSingle
    refine kostka_ne_card _ _ ?_
    simp only [card_sub (sub_cond removal.2.1) removal.2.2,
      Multiset.replicate_toList, List.min_replicate,
      Multiset.erase_replicate, Multiset.sum_replicate, smul_eq_mul,
      mul_one, ne_eq]
    by_cases! hzero : ∑ row ∈ removal.1.support, removal.1 row = 0
    · lia
    have hsumLe := sum_support_subRowLensType_le_card (f := removal)
    suffices ∑ row ∈ removal.1.support, removal.1 row > 1 by lia
    refine sum_support_gt_one_local ?_
    contrapose! hnotSingle
    obtain ⟨hsupport, hvalue⟩ := hnotSingle
    interval_cases hcard : removal.1.support.card
    · rw [Finset.card_eq_zero, Finsupp.support_eq_empty] at hcard
      simp [hcard] at hzero
    · rw [Finset.card_eq_one] at hcard
      obtain ⟨row, hcard⟩ := hcard
      have hrow : removal.1 row = 1 := by
        have hrowMem : row ∈ removal.1.support := by grind
        grind
      apply subset_of_eq at hcard
      rw [Finsupp.support_subset_singleton, hrow] at hcard
      use row
  · simp [Multiset.erase_replicate]

/-- Fixed-shape standard-tableau numbers satisfy the same corner recurrence. -/
theorem standardTableauNumber_removeRow_recurrence
    {rank columns : ℕ} (shape : BoundedPartition rank columns)
    (hcolumns : 0 < columns) :
    standardTableauNumber shape =
      ∑ removable : shape.RemovableRowIndex,
        standardTableauNumber
          (shape.removeRow removable.1 removable.2) := by
  rw [standardTableauNumber_eq_kostka_replicate_one]
  have hcard : shape.youngDiagram.card ≠ 0 := by
    rw [shape.youngDiagram_card]
    exact Nat.ne_of_gt hcolumns
  have hrecurrence := kostka_recursion_single_local hcard
  rw [shape.youngDiagram_card] at hrecurrence
  let equivalence := shape.subSingleRemovableRowEquiv
  calc
    kostkaNumber shape.youngDiagram (Multiset.replicate columns 1) =
        ∑ removal : SubSingle shape.youngDiagram,
          kostkaNumber
            (shape.youngDiagram.sub (Finsupp.single removal.1 1))
            (Multiset.replicate (columns - 1) 1) := hrecurrence
    _ = ∑ removable : shape.RemovableRowIndex,
        standardTableauNumber
          (shape.removeRow removable.1 removable.2) := by
      apply Fintype.sum_equiv equivalence
      intro removal
      have hrow : (equivalence removal).1.val = removal.1 := rfl
      rw [← hrow]
      rw [shape.youngDiagram_sub_removableRow
        (equivalence removal).1 (equivalence removal).2]
      exact (standardTableauNumber_eq_kostka_replicate_one
        (shape.removeRow (equivalence removal).1
          (equivalence removal).2)).symm

end FibonacciRibbonKernel
