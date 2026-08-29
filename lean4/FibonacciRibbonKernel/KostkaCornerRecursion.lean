import KostkaNumbers.HookLength.HookLengthFormula

namespace FibonacciRibbonKernel

open YoungDiagram Kostka

open Classical in
theorem subSingle_sum_eq_subRowLensType_sum_kernel {diagram : YoungDiagram} :
    (∑ row : SubSingle diagram,
      kostkaNumber (diagram.sub (Finsupp.single row.1 1))
        (Multiset.replicate (diagram.card - 1) 1)) =
    ∑ removal ∈ {candidate : SubRowLensType diagram |
        ∃ row : ℕ, candidate.1 = Finsupp.single row 1},
      kostkaNumber (diagram.sub removal.1)
        (Multiset.replicate (diagram.card - 1) 1) := by
  let embedding : SubSingle diagram → SubRowLensType diagram := fun ⟨row, hrow⟩ =>
    ⟨Finsupp.single row 1, hrow⟩
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

theorem finsupp_sum_support_gt_one_kernel {function : ℕ →₀ ℕ}
    (hlarge : function.support.card ≥ 2 ∨ ∃ row, function row > 1) :
    ∑ row ∈ function.support, function row > 1 := by
  rcases hlarge with hsupport | ⟨row, hrow⟩
  · have hcard : function.support.card • 1 > 1 := by
      rw [nsmul_eq_mul, mul_one]
      exact Nat.lt_of_succ_le hsupport
    exact lt_of_lt_of_le hcard
      (Finset.card_nsmul_le_sum _ _ 1 (by grind))
  · exact lt_of_lt_of_le hrow (Finset.single_le_sum (by omega) (by grind))

/-- Public, project-local copy of the standard-content corner recursion used
by the GNW hook proof.  Every helper is kernel checked in this file. -/
theorem kostkaStandard_corner_recursion
    {diagram : YoungDiagram} (hnonempty : diagram.card ≠ 0) :
    kostkaNumber diagram (Multiset.replicate diagram.card 1) =
      ∑ row : SubSingle diagram,
        kostkaNumber (diagram.sub (Finsupp.single row.1 1))
          (Multiset.replicate (diagram.card - 1) 1) := by
  have hcontent : (Multiset.replicate diagram.card 1).toList ≠ [] := by
    rw [ne_eq, Multiset.toList_eq_nil, Eq.comm, Multiset.eq_replicate]
    simp [hnonempty.symm]
  rw [kostka_recursion hcontent (by simp [Multiset.mem_replicate]) (by simp),
    subSingle_sum_eq_subRowLensType_sum_kernel]
  symm
  classical refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) ?_ ?_
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter,
      true_and, not_exists]
    intro removal hnotSingle
    refine kostka_ne_card _ _ ?_
    simp only [YoungDiagram.card_sub
      (YoungDiagram.sub_cond removal.2.1) removal.2.2,
      Multiset.replicate_toList, List.min_replicate,
      Multiset.erase_replicate, Multiset.sum_replicate,
      smul_eq_mul, mul_one, ne_eq]
    by_cases hzero : ∑ row ∈ removal.1.support, removal.1 row = 0
    · omega
    have hbound := sum_support_subRowLensType_le_card (f := removal)
    suffices ∑ row ∈ removal.1.support, removal.1 row > 1 by omega
    refine finsupp_sum_support_gt_one_kernel ?_
    contrapose! hnotSingle
    obtain ⟨hsupport, hvalues⟩ := hnotSingle
    interval_cases hcard : removal.1.support.card
    · rw [Finset.card_eq_zero, Finsupp.support_eq_empty] at hcard
      simp [hcard] at hzero
    · rw [Finset.card_eq_one] at hcard
      obtain ⟨row, hrow⟩ := hcard
      have hone : removal.1 row = 1 := by
        have hmem : row ∈ removal.1.support := by grind
        grind
      apply subset_of_eq at hrow
      rw [Finsupp.support_subset_singleton, hone] at hrow
      use row
  · simp [Multiset.erase_replicate]

theorem subSingle_sub_cond_kernel
    {diagram : YoungDiagram} {cell : ℕ × ℕ}
    (hcell : cell ∈ diagram.corners) :
    ∀ row : ℕ,
      diagram.rowLen' row - (Finsupp.single cell.1 1) row ≥
        diagram.rowLen' (row + 1) := by
  simp only [YoungDiagram.corners, Finset.mem_filter,
    YoungDiagram.mem_cells] at hcell
  obtain ⟨hmem, hrow, hcolumn⟩ := hcell
  intro row
  rw [Finsupp.single_apply]
  split_ifs with heq
  · rw [YoungDiagram.rowLen'_eq_rowLen, ← heq, ← hrow,
      add_tsub_cancel_right, YoungDiagram.rowLen'_eq_rowLen, hcolumn,
      ge_iff_le, ← Std.not_lt, ← diagram.mem_iff_lt_rowLen,
      diagram.mem_iff_lt_colLen]
    exact Nat.lt_irrefl _
  · simp [diagram.rowLen'_anti row.le_succ]

theorem subSingle_le_rowLen_kernel
    {diagram : YoungDiagram} {cell : ℕ × ℕ}
    (hcell : cell ∈ diagram.corners) :
    ∀ row : ℕ, (Finsupp.single cell.1 1) row ≤ diagram.rowLen' row := by
  simp only [YoungDiagram.corners, Finset.mem_filter,
    YoungDiagram.mem_cells] at hcell
  obtain ⟨hmem, hrow, hcolumn⟩ := hcell
  intro row
  rw [Finsupp.single_apply]
  split_ifs with heq
  · refine Nat.le_of_pred_lt ?_
    rw [YoungDiagram.rowLen'_eq_rowLen, ← heq,
      ← diagram.mem_iff_lt_rowLen]
    exact diagram.up_left_mem (by rfl) zero_le hmem
  · exact zero_le

noncomputable def subSingleCornerEquiv (diagram : YoungDiagram) :
    SubSingle diagram ≃ diagram.corners where
  toFun removal := by
    refine ⟨(removal.1, diagram.rowLen removal.1 - 1), ?_⟩
    simp only [YoungDiagram.corners, Finset.mem_filter,
      YoungDiagram.mem_cells]
    have hbound := removal.2.2 removal.1
    rw [Finsupp.single_eq_same, YoungDiagram.rowLen'_eq_rowLen] at hbound
    constructor
    · rw [diagram.mem_iff_lt_rowLen]
      omega
    constructor
    · omega
    · refine le_antisymm ?_ ?_
      · suffices removal.1 < diagram.colLen (diagram.rowLen removal.1 - 1) by omega
        rw [← diagram.mem_iff_lt_colLen, diagram.mem_iff_lt_rowLen]
        omega
      · rw [← Std.not_lt, ← diagram.mem_iff_lt_colLen,
          diagram.mem_iff_lt_rowLen, Std.not_lt]
        have hcondition := removal.2.1 removal.1
        simpa [YoungDiagram.rowLen'_eq_rowLen] using hcondition
  invFun cell :=
    ⟨cell.1.1,
      ⟨subSingle_sub_cond_kernel cell.2,
        subSingle_le_rowLen_kernel cell.2⟩⟩
  left_inv removal := by
    apply Subtype.ext
    rfl
  right_inv cell := by
    apply Subtype.ext
    simp only
    have hcorner := cell.2
    simp only [YoungDiagram.corners, Finset.mem_filter,
      YoungDiagram.mem_cells] at hcorner
    exact Prod.ext rfl (by omega)

theorem kostkaStandard_corner_recursion_cells
    {diagram : YoungDiagram} (hnonempty : diagram.card ≠ 0) :
    kostkaNumber diagram (Multiset.replicate diagram.card 1) =
      ∑ cell : diagram.corners,
        kostkaNumber (diagram.sub (Finsupp.single cell.1.1 1))
          (Multiset.replicate (diagram.card - 1) 1) := by
  rw [kostkaStandard_corner_recursion hnonempty]
  exact Fintype.sum_equiv (subSingleCornerEquiv diagram)
    (fun removal => kostkaNumber
      (diagram.sub (Finsupp.single removal.1 1))
      (Multiset.replicate (diagram.card - 1) 1))
    (fun cell => kostkaNumber
      (diagram.sub (Finsupp.single cell.1.1 1))
      (Multiset.replicate (diagram.card - 1) 1))
    (by intro; rfl)

end FibonacciRibbonKernel
