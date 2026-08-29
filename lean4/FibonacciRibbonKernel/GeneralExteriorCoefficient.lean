import FibonacciRibbonKernel.GeneralPfaffianAssembly

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

noncomputable def natSelectedValues
    (dimension : ℕ) (selected : List ℕ)
    (hlength : selected.length = dimension) : Fin dimension → ℕ :=
  fun index => selected.get (Fin.cast hlength.symm index)

theorem natSelectedValues_toList
    (dimension : ℕ) (selected : List ℕ)
    (hlength : selected.length = dimension) :
    List.ofFn (natSelectedValues dimension selected hlength) = selected := by
  apply List.ext_get_iff.mpr
  constructor
  · simp [hlength]
  · intro index hleft hright
    simp [natSelectedValues]

theorem natSelectedValues_sum
    (dimension : ℕ) (selected : List ℕ)
    (hlength : selected.length = dimension) :
    (∑ row, natSelectedValues dimension selected hlength row) =
      selected.sum := by
  rw [← List.sum_ofFn, natSelectedValues_toList]

noncomputable def generalNatSelectedDeterminant
    (dimension : ℕ) (selected : List ℕ) : ℚ :=
  if hlength : selected.length = dimension then
    Matrix.det (generalFactorialScalarMatrix
      (natSelectedValues dimension selected hlength))
  else 0

noncomputable def generalNatSelectedSeries
    (dimension : ℕ) (selected : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.monomial selected.sum
    (generalNatSelectedDeterminant dimension selected)

theorem selected_factorial_rows_matrix
    (dimension : ℕ) (selected : List ℕ)
    (hlength : selected.length = dimension) :
    listRowsOfLength
        (selected.map (generalFactorialPowerSeriesRow dimension))
        (by simpa using hlength) =
      generalFactorialPowerSeriesMatrix
        (natSelectedValues dimension selected hlength) := by
  funext row column
  simp [listRowsOfLength, generalFactorialPowerSeriesMatrix,
    natSelectedValues]

theorem generalTopDeterminant_selected_factorial_rows
    (dimension : ℕ) (selected : List ℕ)
    (hlength : selected.length = dimension) :
    generalTopDeterminant (R := ℚ⟦X⟧) dimension
        (exteriorListProduct (R := ℚ⟦X⟧)
          (selected.map (generalFactorialPowerSeriesRow dimension))) =
      generalNatSelectedSeries dimension selected := by
  rw [generalTopDeterminant_exteriorListProduct _ (by simpa using hlength)]
  rw [selected_factorial_rows_matrix dimension selected hlength,
    det_generalFactorialPowerSeriesRows]
  unfold generalNatSelectedSeries generalNatSelectedDeterminant
  rw [dif_pos hlength, natSelectedValues_sum]

theorem generalExteriorTruncation_eq_nat_selected_sum
    (dimension bound : ℕ) :
    generalExteriorTruncation dimension bound =
      (((List.range bound).reverse.sublistsLen dimension).map
        (generalNatSelectedSeries dimension)).sum := by
  unfold generalExteriorTruncation
  rw [generalTopDeterminant_exteriorElementary_eq_sum_sublists]
  rw [sublistsLen_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro selected hselected
  have hlength := List.length_of_sublistsLen hselected
  change generalSelectedDeterminant dimension
      (selected.map (generalFactorialPowerSeriesRow dimension)) =
    generalNatSelectedSeries dimension selected
  unfold generalSelectedDeterminant
  rw [dif_pos (by simpa using hlength)]
  rw [selected_factorial_rows_matrix dimension selected hlength,
    det_generalFactorialPowerSeriesRows]
  unfold generalNatSelectedSeries generalNatSelectedDeterminant
  rw [dif_pos hlength, natSelectedValues_sum]

theorem generalExteriorTruncation_coeff
    (dimension bound degree : ℕ) :
    PowerSeries.coeff degree (generalExteriorTruncation dimension bound) =
      ((((List.range bound).reverse.sublistsLen dimension).map fun selected =>
        if selected.sum = degree then
          generalNatSelectedDeterminant dimension selected else 0).sum) := by
  rw [generalExteriorTruncation_eq_nat_selected_sum]
  induction ((List.range bound).reverse.sublistsLen dimension) with
  | nil => simp
  | cons selected remaining ih =>
      simp only [List.map_cons, List.sum_cons, map_add, ih,
        generalNatSelectedSeries, PowerSeries.coeff_monomial]
      by_cases hdegree : degree = selected.sum
      · simp [hdegree]
      · have hreverse : ¬selected.sum = degree := by omega
        simp [hdegree, hreverse]

theorem generalNatSelectedDeterminant_toList
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    generalNatSelectedDeterminant (rank + 1) tuple.toList =
      Matrix.det (generalFactorialScalarMatrix tuple.values) := by
  unfold generalNatSelectedDeterminant
  rw [dif_pos tuple.toList_length]
  apply congrArg Matrix.det
  apply congrArg generalFactorialScalarMatrix
  apply List.ofFn_injective
  rw [natSelectedValues_toList]
  rfl

theorem selected_sum_ge_staircase
    (rank : ℕ) (selected : List ℕ)
    (hlength : selected.length = rank + 1)
    (hpair : selected.Pairwise (fun left right => left > right)) :
    staircaseWeight rank ≤ selected.sum := by
  let values := natSelectedValues (rank + 1) selected hlength
  have hpairValues : (List.ofFn values).Pairwise
      (fun left right => left > right) := by
    rw [natSelectedValues_toList]
    exact hpair
  have hstrict : StrictAnti values := by
    rw [List.pairwise_ofFn] at hpairValues
    intro left right hleftRight
    exact hpairValues hleftRight
  have hsum : (∑ row : Fin (rank + 1), row.rev.val) ≤
      ∑ row, values row := by
    exact Finset.sum_le_sum fun row _ => strictAnti_staircase_le values hstrict row
  rw [natSelectedValues_sum] at hsum
  exact hsum

theorem general_filtered_selected_sum_eq_strictShifted_sum
    (rank size bound : ℕ)
    (hbound : size + staircaseWeight rank < bound) :
    ∑ selected ∈
        (((List.range bound).reverse.sublistsLen (rank + 1)).toFinset.filter
          fun selected => selected.sum = size + staircaseWeight rank),
        generalNatSelectedDeterminant (rank + 1) selected =
      ∑ tuple : StrictShiftedTuple rank size,
        Matrix.det (generalFactorialScalarMatrix tuple.values) := by
  symm
  refine Finset.sum_nbij
    (fun tuple : StrictShiftedTuple rank size => tuple.toList) ?_ ?_ ?_ ?_
  · intro tuple htuple
    rw [Finset.mem_filter]
    exact ⟨List.mem_toFinset.mpr
        (tuple.toList_mem_sublistsLen_of_bound hbound),
      tuple.toList_sum⟩
  · intro left hleft right hright heq
    apply StrictShiftedTuple.ext
    exact List.ofFn_injective heq
  · intro selected hselected
    change selected ∈
      (((List.range bound).reverse.sublistsLen (rank + 1)).toFinset.filter
        (fun selected => selected.sum = size + staircaseWeight rank)) at hselected
    rw [Finset.mem_filter] at hselected
    obtain ⟨hsource, hsum⟩ := hselected
    have hmember := List.mem_toFinset.mp hsource
    have hlength := List.length_of_sublistsLen hmember
    let values := natSelectedValues (rank + 1) selected hlength
    have hpairSelected :=
      (pairwise_gt_reverse_range_general bound).sublist
        (List.mem_sublistsLen.mp hmember).1
    have hpairValues : (List.ofFn values).Pairwise
        (fun left right => left > right) := by
      rw [natSelectedValues_toList]
      exact hpairSelected
    have hstrictAnti : StrictAnti values := by
      rw [List.pairwise_ofFn] at hpairValues
      intro left right hleftRight
      exact hpairValues hleftRight
    have hstaircase : ∀ row, row.rev.val ≤ values row :=
      strictAnti_staircase_le values hstrictAnti
    have hsumValues : ∑ row, values row = size + staircaseWeight rank := by
      rw [natSelectedValues_sum]
      exact hsum
    let tuple : StrictShiftedTuple rank size :=
      ⟨values, Fin.strictAnti_iff_succ_lt.mp hstrictAnti,
        hstaircase, hsumValues⟩
    refine ⟨tuple, Finset.mem_univ tuple, ?_⟩
    change List.ofFn values = selected
    exact natSelectedValues_toList (rank + 1) selected hlength
  · intro tuple htuple
    exact (generalNatSelectedDeterminant_toList tuple).symm

theorem generalExteriorTruncation_coeff_shifted_of_bound
    (rank size bound : ℕ)
    (hbound : size + staircaseWeight rank < bound) :
    PowerSeries.coeff (size + staircaseWeight rank)
        (generalExteriorTruncation (rank + 1) bound) =
      ∑ tuple : StrictShiftedTuple rank size,
        Matrix.det (generalFactorialScalarMatrix tuple.values) := by
  rw [generalExteriorTruncation_coeff]
  let candidates := (List.range bound).reverse.sublistsLen (rank + 1)
  have hnodup : candidates.Nodup := by
    apply List.nodup_sublistsLen
    exact List.nodup_reverse.mpr List.nodup_range
  rw [← List.sum_toFinset _ hnodup, ← Finset.sum_filter]
  simpa [candidates] using
    general_filtered_selected_sum_eq_strictShifted_sum rank size bound hbound

/-- Uniform coefficientwise bridge from finite exterior truncations to the
actual unrestricted tableau factorial EGF. -/
theorem generalExteriorTruncation_coeff_eq_unrestricted_of_bound
    (rank size bound : ℕ)
    (hbound : size + staircaseWeight rank < bound) :
    PowerSeries.coeff (size + staircaseWeight rank)
        (generalExteriorTruncation (rank + 1) bound) =
      (unrestrictedCount rank size : ℚ) / (size.factorial : ℚ) := by
  rw [generalExteriorTruncation_coeff_shifted_of_bound rank size bound hbound]
  exact (unrestrictedCount_div_factorial_eq_sum_strictShifted rank size).symm

theorem generalExteriorTruncation_coeff_eq_zero_of_lt_staircase
    (rank bound degree : ℕ) (hdegree : degree < staircaseWeight rank) :
    PowerSeries.coeff degree
        (generalExteriorTruncation (rank + 1) bound) = 0 := by
  rw [generalExteriorTruncation_coeff]
  let candidates := (List.range bound).reverse.sublistsLen (rank + 1)
  have hall : ∀ selected ∈ candidates,
      selected.length = rank + 1 ∧
        selected.Pairwise (fun left right => left > right) := by
    intro selected hselected
    constructor
    · exact List.length_of_sublistsLen hselected
    · exact (pairwise_gt_reverse_range_general bound).sublist
        (List.mem_sublistsLen.mp hselected).1
  change ((candidates.map fun selected =>
    if selected.sum = degree then
      generalNatSelectedDeterminant (rank + 1) selected else 0).sum) = 0
  have aux : ∀ list : List (List ℕ),
      (∀ selected ∈ list,
        selected.length = rank + 1 ∧
          selected.Pairwise (fun left right => left > right)) →
      ((list.map fun selected =>
        if selected.sum = degree then
          generalNatSelectedDeterminant (rank + 1) selected else 0).sum) = 0 := by
    intro list hlist
    induction list with
    | nil => simp
    | cons selected remaining ih =>
        have hselected := hlist selected (by simp)
        have hsum := selected_sum_ge_staircase rank selected
          hselected.1 hselected.2
        have hne : ¬selected.sum = degree := by omega
        rw [List.map_cons, List.sum_cons, if_neg hne, zero_add]
        apply ih
        intro current hcurrent
        exact hlist current (by simp [hcurrent])
  exact aux candidates hall

end FibonacciRibbonKernel
