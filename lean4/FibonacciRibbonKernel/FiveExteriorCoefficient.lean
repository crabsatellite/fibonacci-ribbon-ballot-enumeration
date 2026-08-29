import FibonacciRibbonKernel.FiveShiftedPartitions
import FibonacciRibbonKernel.SpecialRankSums

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

noncomputable def fiveSelectedDeterminant : List ℕ → ℚ
  | [a, b, c, d, e] =>
      Matrix.det (fiveFactorialScalarMatrix a b c d e)
  | _ => 0

noncomputable def fiveSelectedSeries (selected : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.monomial selected.sum (fiveSelectedDeterminant selected)

noncomputable def fiveExteriorTruncation (bound : ℕ) : ℚ⟦X⟧ :=
  topFiveDeterminant (R := ℚ⟦X⟧)
    (exteriorElementary 5
      ((List.range bound).reverse.map fiveFactorialPowerSeriesRow))

theorem topFiveDeterminant_selected_factorial_rows
    (selected : List ℕ) (hlength : selected.length = 5) :
    topFiveDeterminant (R := ℚ⟦X⟧)
        (exteriorListProduct (R := ℚ⟦X⟧)
          (selected.map fiveFactorialPowerSeriesRow)) =
      fiveSelectedSeries selected := by
  obtain ⟨a, b, c, d, e, rfl⟩ :=
    exists_five_entries_of_length_eq_five selected hlength
  simp only [List.map_cons, List.map_nil]
  rw [topFiveDeterminant_exteriorListProduct_fiveFactorialRows]
  unfold fiveSelectedSeries fiveSelectedDeterminant
  apply congrArg (fun degree => PowerSeries.monomial degree
    (Matrix.det (fiveFactorialScalarMatrix a b c d e)))
  simp only [List.sum_cons, List.sum_nil, add_zero]
  omega

theorem fiveExteriorTruncation_eq_selected_sum (bound : ℕ) :
    fiveExteriorTruncation bound =
      (((List.range bound).reverse.sublistsLen 5).map
        fiveSelectedSeries).sum := by
  unfold fiveExteriorTruncation
  rw [topFiveDeterminant_exteriorElementary_eq_sum_sublists]
  rw [sublistsLen_map]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro selected hselected
  exact topFiveDeterminant_selected_factorial_rows selected
    (List.length_of_sublistsLen hselected)

theorem fiveExteriorTruncation_coeff (bound degree : ℕ) :
    PowerSeries.coeff degree (fiveExteriorTruncation bound) =
      ((((List.range bound).reverse.sublistsLen 5).map fun selected =>
        if selected.sum = degree then fiveSelectedDeterminant selected else 0).sum) := by
  rw [fiveExteriorTruncation_eq_selected_sum]
  induction ((List.range bound).reverse.sublistsLen 5) with
  | nil => simp
  | cons selected remaining ih =>
      simp only [List.map_cons, List.sum_cons, map_add, ih,
        fiveSelectedSeries, PowerSeries.coeff_monomial]
      by_cases hdegree : degree = selected.sum
      · simp [hdegree]
      · have hreverse : ¬selected.sum = degree := by omega
        simp [hdegree, hreverse]

theorem fiveSelectedDeterminant_toList
    {size : ℕ} (tuple : StrictFiveAt size) :
    fiveSelectedDeterminant tuple.toList =
      Matrix.det
        (fiveFactorialScalarMatrix tuple.a tuple.b tuple.c tuple.d tuple.e) := by
  rfl

theorem five_filtered_selected_sum_eq_strictFive_sum
    (size bound : ℕ) (hbound : size + 5 ≤ bound) :
    ∑ selected ∈
        (((List.range bound).reverse.sublistsLen 5).toFinset.filter
          fun selected => selected.sum = size + 10),
        fiveSelectedDeterminant selected =
      ∑ tuple : StrictFiveAt size,
        Matrix.det
          (fiveFactorialScalarMatrix tuple.a tuple.b tuple.c tuple.d tuple.e) := by
  symm
  refine Finset.sum_nbij (fun tuple : StrictFiveAt size => tuple.toList) ?_ ?_ ?_ ?_
  · intro tuple htuple
    rw [Finset.mem_filter]
    exact ⟨List.mem_toFinset.mpr
        (tuple.toList_mem_sublistsLen_of_bound hbound),
      tuple.toList_sum⟩
  · intro left hleft right hright heq
    have hfields : left.a = right.a ∧ left.b = right.b ∧
        left.c = right.c ∧ left.d = right.d ∧ left.e = right.e := by
      simpa [StrictFiveAt.toList] using heq
    exact StrictFiveAt.ext hfields.1 hfields.2.1 hfields.2.2.1
      hfields.2.2.2.1 hfields.2.2.2.2
  · intro selected hselected
    change selected ∈
      (((List.range bound).reverse.sublistsLen 5).toFinset.filter
        (fun selected => selected.sum = size + 10)) at hselected
    rw [Finset.mem_filter] at hselected
    obtain ⟨hsource, hsum⟩ := hselected
    have hmember := List.mem_toFinset.mp hsource
    have hlength := List.length_of_sublistsLen hmember
    obtain ⟨a, b, c, d, e, hselectedEq⟩ :=
      exists_five_entries_of_length_eq_five selected hlength
    subst selected
    have hsublist := (List.mem_sublistsLen.mp hmember).1
    have hpair := (pairwise_gt_reverse_range bound).sublist hsublist
    have hab : b < a := by
      simpa using hpair.rel_get_of_lt
        (show (0 : Fin 5) < (1 : Fin 5) by decide)
    have hbc : c < b := by
      simpa using hpair.rel_get_of_lt
        (show (1 : Fin 5) < (2 : Fin 5) by decide)
    have hcd : d < c := by
      simpa using hpair.rel_get_of_lt
        (show (2 : Fin 5) < (3 : Fin 5) by decide)
    have hde : e < d := by
      simpa using hpair.rel_get_of_lt
        (show (3 : Fin 5) < (4 : Fin 5) by decide)
    have hsumTuple : a + b + c + d + e = size + 10 := by
      simpa only [List.sum_cons, List.sum_nil, add_zero, add_assoc] using hsum
    let tuple : StrictFiveAt size :=
      ⟨a, b, c, d, e, hab, hbc, hcd, hde, hsumTuple⟩
    refine ⟨tuple, Finset.mem_univ tuple, ?_⟩
    rfl
  · intro tuple htuple
    exact fiveSelectedDeterminant_toList tuple

theorem fiveExteriorTruncation_coeff_shifted (size : ℕ) :
    PowerSeries.coeff (size + 10)
        (fiveExteriorTruncation (size + 5)) =
      ∑ tuple : StrictFiveAt size,
        Matrix.det
          (fiveFactorialScalarMatrix tuple.a tuple.b tuple.c tuple.d tuple.e) := by
  rw [fiveExteriorTruncation_coeff]
  let candidates := (List.range (size + 5)).reverse.sublistsLen 5
  have hnodup : candidates.Nodup := by
    apply List.nodup_sublistsLen
    exact List.nodup_reverse.mpr List.nodup_range
  rw [← List.sum_toFinset _ hnodup]
  rw [← Finset.sum_filter]
  simpa [candidates] using
    five_filtered_selected_sum_eq_strictFive_sum size (size + 5) (by omega)

theorem fiveExteriorTruncation_coeff_shifted_of_bound
    (size bound : ℕ) (hbound : size + 5 ≤ bound) :
    PowerSeries.coeff (size + 10) (fiveExteriorTruncation bound) =
      ∑ tuple : StrictFiveAt size,
        Matrix.det
          (fiveFactorialScalarMatrix tuple.a tuple.b tuple.c tuple.d tuple.e) := by
  rw [fiveExteriorTruncation_coeff]
  let candidates := (List.range bound).reverse.sublistsLen 5
  have hnodup : candidates.Nodup := by
    apply List.nodup_sublistsLen
    exact List.nodup_reverse.mpr List.nodup_range
  rw [← List.sum_toFinset _ hnodup]
  rw [← Finset.sum_filter]
  simpa [candidates] using
    five_filtered_selected_sum_eq_strictFive_sum size bound hbound

theorem fiveExteriorTruncation_coeff_eq_tableaux (size : ℕ) :
    PowerSeries.coeff (size + 10)
        (fiveExteriorTruncation (size + 5)) =
      (heightFiveTableauCount size : ℚ) / (size.factorial : ℚ) := by
  rw [fiveExteriorTruncation_coeff_shifted]
  unfold heightFiveTableauCount
  rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  push_cast
  rw [← (boundedPartitionStrictFiveEquiv size).sum_comp]
  have hfactorial : (size.factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hfactorial).2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro shape hshape
  change Matrix.det
      (fiveFactorialScalarMatrix shape.toStrictFiveAt.a
        shape.toStrictFiveAt.b shape.toStrictFiveAt.c
        shape.toStrictFiveAt.d shape.toStrictFiveAt.e) *
      (size.factorial : ℚ) = (standardTableauNumber shape : ℚ)
  rw [← boundedFactorialDeterminant_eq_strictFiveMatrix shape]
  have hfrobenius :=
    standardTableauNumber_eq_factorial_mul_boundedFactorialDeterminant shape
  rw [hfrobenius]
  ring

theorem fiveExteriorTruncation_coeff_eq_tableaux_of_bound
    (size bound : ℕ) (hbound : size + 5 ≤ bound) :
    PowerSeries.coeff (size + 10) (fiveExteriorTruncation bound) =
      (heightFiveTableauCount size : ℚ) / (size.factorial : ℚ) := by
  rw [fiveExteriorTruncation_coeff_shifted_of_bound size bound hbound]
  unfold heightFiveTableauCount
  rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  push_cast
  rw [← (boundedPartitionStrictFiveEquiv size).sum_comp]
  have hfactorial : (size.factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hfactorial).2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro shape hshape
  change Matrix.det
      (fiveFactorialScalarMatrix shape.toStrictFiveAt.a
        shape.toStrictFiveAt.b shape.toStrictFiveAt.c
        shape.toStrictFiveAt.d shape.toStrictFiveAt.e) *
      (size.factorial : ℚ) = (standardTableauNumber shape : ℚ)
  rw [← boundedFactorialDeterminant_eq_strictFiveMatrix shape]
  rw [standardTableauNumber_eq_factorial_mul_boundedFactorialDeterminant]
  ring

end FibonacciRibbonKernel
