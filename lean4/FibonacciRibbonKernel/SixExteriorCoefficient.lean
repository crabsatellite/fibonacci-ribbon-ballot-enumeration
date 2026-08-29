import FibonacciRibbonKernel.SixShiftedPartitions
import FibonacciRibbonKernel.SpecialRankSums

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

theorem topSixDeterminant_exteriorElementary_eq_sum_sublists
    {R : Type*} [CommRing R] (rows : List (SixRow R)) :
    topSixDeterminant (R := R) (exteriorElementary 6 rows) =
      ((rows.sublistsLen 6).map fun selected =>
        topSixDeterminant (R := R)
          (exteriorListProduct (R := R) selected)).sum := by
  rw [exteriorElementary_eq_sum_sublistsLen]
  simp only [map_list_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro selected hselected
  rfl

noncomputable def sixSelectedDeterminant : List ℕ → ℚ
  | [a, b, c, d, e, f] =>
      Matrix.det (sixFactorialScalarMatrix a b c d e f)
  | _ => 0

noncomputable def sixSelectedSeries (selected : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.monomial selected.sum (sixSelectedDeterminant selected)

noncomputable def sixExteriorTruncation (bound : ℕ) : ℚ⟦X⟧ :=
  topSixDeterminant (R := ℚ⟦X⟧)
    (exteriorElementary 6
      ((List.range bound).reverse.map sixFactorialPowerSeriesRow))

theorem topSixDeterminant_selected_factorial_rows
    (selected : List ℕ) (hlength : selected.length = 6) :
    topSixDeterminant (R := ℚ⟦X⟧)
        (exteriorListProduct (R := ℚ⟦X⟧)
          (selected.map sixFactorialPowerSeriesRow)) =
      sixSelectedSeries selected := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ :=
    exists_six_entries_of_length_eq_six selected hlength
  simp only [List.map_cons, List.map_nil]
  rw [topSixDeterminant_exteriorListProduct_sixFactorialRows]
  unfold sixSelectedSeries sixSelectedDeterminant
  apply congrArg (fun degree => PowerSeries.monomial degree
    (Matrix.det (sixFactorialScalarMatrix a b c d e f)))
  simp only [List.sum_cons, List.sum_nil, add_zero]
  omega

theorem sixExteriorTruncation_eq_selected_sum (bound : ℕ) :
    sixExteriorTruncation bound =
      (((List.range bound).reverse.sublistsLen 6).map
        sixSelectedSeries).sum := by
  unfold sixExteriorTruncation
  rw [topSixDeterminant_exteriorElementary_eq_sum_sublists]
  rw [sublistsLen_map]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro selected hselected
  exact topSixDeterminant_selected_factorial_rows selected
    (List.length_of_sublistsLen hselected)

theorem sixExteriorTruncation_coeff (bound degree : ℕ) :
    PowerSeries.coeff degree (sixExteriorTruncation bound) =
      ((((List.range bound).reverse.sublistsLen 6).map fun selected =>
        if selected.sum = degree then sixSelectedDeterminant selected else 0).sum) := by
  rw [sixExteriorTruncation_eq_selected_sum]
  induction ((List.range bound).reverse.sublistsLen 6) with
  | nil => simp
  | cons selected remaining ih =>
      simp only [List.map_cons, List.sum_cons, map_add, ih,
        sixSelectedSeries, PowerSeries.coeff_monomial]
      by_cases hdegree : degree = selected.sum
      · simp [hdegree]
      · have hreverse : ¬selected.sum = degree := by omega
        simp [hdegree, hreverse]

theorem sixSelectedDeterminant_toList
    {size : ℕ} (tuple : StrictSixAt size) :
    sixSelectedDeterminant tuple.toList =
      Matrix.det
        (sixFactorialScalarMatrix tuple.a tuple.b tuple.c
          tuple.d tuple.e tuple.f) := by
  rfl

theorem six_filtered_selected_sum_eq_strictSix_sum
    (size bound : ℕ) (hbound : size + 6 ≤ bound) :
    ∑ selected ∈
        (((List.range bound).reverse.sublistsLen 6).toFinset.filter
          fun selected => selected.sum = size + 15),
        sixSelectedDeterminant selected =
      ∑ tuple : StrictSixAt size,
        Matrix.det
          (sixFactorialScalarMatrix tuple.a tuple.b tuple.c
            tuple.d tuple.e tuple.f) := by
  symm
  refine Finset.sum_nbij (fun tuple : StrictSixAt size => tuple.toList) ?_ ?_ ?_ ?_
  · intro tuple htuple
    rw [Finset.mem_filter]
    exact ⟨List.mem_toFinset.mpr
        (tuple.toList_mem_sublistsLen_of_bound hbound),
      tuple.toList_sum⟩
  · intro left hleft right hright heq
    have hfields : left.a = right.a ∧ left.b = right.b ∧
        left.c = right.c ∧ left.d = right.d ∧ left.e = right.e ∧
          left.f = right.f := by
      simpa [StrictSixAt.toList] using heq
    exact StrictSixAt.ext hfields.1 hfields.2.1 hfields.2.2.1
      hfields.2.2.2.1 hfields.2.2.2.2.1 hfields.2.2.2.2.2
  · intro selected hselected
    change selected ∈
      (((List.range bound).reverse.sublistsLen 6).toFinset.filter
        (fun selected => selected.sum = size + 15)) at hselected
    rw [Finset.mem_filter] at hselected
    obtain ⟨hsource, hsum⟩ := hselected
    have hmember := List.mem_toFinset.mp hsource
    have hlength := List.length_of_sublistsLen hmember
    obtain ⟨a, b, c, d, e, f, hselectedEq⟩ :=
      exists_six_entries_of_length_eq_six selected hlength
    subst selected
    have hsublist := (List.mem_sublistsLen.mp hmember).1
    have hpair := (pairwise_gt_reverse_range bound).sublist hsublist
    have hab : b < a := by
      simpa using hpair.rel_get_of_lt
        (show (0 : Fin 6) < (1 : Fin 6) by decide)
    have hbc : c < b := by
      simpa using hpair.rel_get_of_lt
        (show (1 : Fin 6) < (2 : Fin 6) by decide)
    have hcd : d < c := by
      simpa using hpair.rel_get_of_lt
        (show (2 : Fin 6) < (3 : Fin 6) by decide)
    have hde : e < d := by
      simpa using hpair.rel_get_of_lt
        (show (3 : Fin 6) < (4 : Fin 6) by decide)
    have hef : f < e := by
      simpa using hpair.rel_get_of_lt
        (show (4 : Fin 6) < (5 : Fin 6) by decide)
    have hsumTuple : a + b + c + d + e + f = size + 15 := by
      simpa only [List.sum_cons, List.sum_nil, add_zero, add_assoc] using hsum
    let tuple : StrictSixAt size :=
      ⟨a, b, c, d, e, f, hab, hbc, hcd, hde, hef, hsumTuple⟩
    refine ⟨tuple, Finset.mem_univ tuple, ?_⟩
    rfl
  · intro tuple htuple
    exact sixSelectedDeterminant_toList tuple

theorem sixExteriorTruncation_coeff_shifted_of_bound
    (size bound : ℕ) (hbound : size + 6 ≤ bound) :
    PowerSeries.coeff (size + 15) (sixExteriorTruncation bound) =
      ∑ tuple : StrictSixAt size,
        Matrix.det
          (sixFactorialScalarMatrix tuple.a tuple.b tuple.c
            tuple.d tuple.e tuple.f) := by
  rw [sixExteriorTruncation_coeff]
  let candidates := (List.range bound).reverse.sublistsLen 6
  have hnodup : candidates.Nodup := by
    apply List.nodup_sublistsLen
    exact List.nodup_reverse.mpr List.nodup_range
  rw [← List.sum_toFinset _ hnodup]
  rw [← Finset.sum_filter]
  simpa [candidates] using
    six_filtered_selected_sum_eq_strictSix_sum size bound hbound

theorem sixExteriorTruncation_coeff_eq_tableaux_of_bound
    (size bound : ℕ) (hbound : size + 6 ≤ bound) :
    PowerSeries.coeff (size + 15) (sixExteriorTruncation bound) =
      (heightSixTableauCount size : ℚ) / (size.factorial : ℚ) := by
  rw [sixExteriorTruncation_coeff_shifted_of_bound size bound hbound]
  unfold heightSixTableauCount
  rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  push_cast
  rw [← (boundedPartitionStrictSixEquiv size).sum_comp]
  have hfactorial : (size.factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hfactorial).2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro shape hshape
  change Matrix.det
      (sixFactorialScalarMatrix shape.toStrictSixAt.a
        shape.toStrictSixAt.b shape.toStrictSixAt.c
        shape.toStrictSixAt.d shape.toStrictSixAt.e shape.toStrictSixAt.f) *
      (size.factorial : ℚ) = (standardTableauNumber shape : ℚ)
  rw [← boundedFactorialDeterminant_eq_strictSixMatrix shape]
  rw [standardTableauNumber_eq_factorial_mul_boundedFactorialDeterminant]
  ring

end FibonacciRibbonKernel
