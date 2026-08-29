import FibonacciRibbonKernel.FourShiftedPartitions
import FibonacciRibbonKernel.FivePfaffianBessel
import FibonacciRibbonKernel.FactorialDifferential

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

noncomputable def heightFourTableauCount (size : ℕ) : ℕ :=
  unrestrictedCount 3 size

theorem topFourDeterminant_exteriorElementary_eq_sum_sublists
    {R : Type*} [CommRing R] (rows : List (FourRow R)) :
    topFourDeterminant (R := R) (exteriorElementary 4 rows) =
      ((rows.sublistsLen 4).map fun selected =>
        topFourDeterminant (R := R)
          (exteriorListProduct (R := R) selected)).sum := by
  rw [exteriorElementary_eq_sum_sublistsLen]
  simp only [map_list_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro selected hselected
  rfl

noncomputable def fourSelectedDeterminant : List ℕ → ℚ
  | [a, b, c, d] => Matrix.det (fourFactorialScalarMatrix a b c d)
  | _ => 0

noncomputable def fourSelectedSeries (selected : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.monomial selected.sum (fourSelectedDeterminant selected)

noncomputable def fourExteriorTruncation (bound : ℕ) : ℚ⟦X⟧ :=
  topFourDeterminant (R := ℚ⟦X⟧)
    (exteriorElementary 4
      ((List.range bound).reverse.map fourFactorialPowerSeriesRow))

theorem topFourDeterminant_selected_factorial_rows
    (selected : List ℕ) (hlength : selected.length = 4) :
    topFourDeterminant (R := ℚ⟦X⟧)
        (exteriorListProduct (R := ℚ⟦X⟧)
          (selected.map fourFactorialPowerSeriesRow)) =
      fourSelectedSeries selected := by
  obtain ⟨a, b, c, d, rfl⟩ :=
    exists_four_entries_of_length_eq_four selected hlength
  simp only [List.map_cons, List.map_nil]
  rw [topFourDeterminant_exteriorListProduct_fourFactorialRows]
  unfold fourSelectedSeries fourSelectedDeterminant
  apply congrArg (fun degree => PowerSeries.monomial degree
    (Matrix.det (fourFactorialScalarMatrix a b c d)))
  simp only [List.sum_cons, List.sum_nil, add_zero]
  omega

theorem fourExteriorTruncation_eq_selected_sum (bound : ℕ) :
    fourExteriorTruncation bound =
      (((List.range bound).reverse.sublistsLen 4).map
        fourSelectedSeries).sum := by
  unfold fourExteriorTruncation
  rw [topFourDeterminant_exteriorElementary_eq_sum_sublists,
    sublistsLen_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro selected hselected
  exact topFourDeterminant_selected_factorial_rows selected
    (List.length_of_sublistsLen hselected)

theorem fourExteriorTruncation_coeff (bound degree : ℕ) :
    PowerSeries.coeff degree (fourExteriorTruncation bound) =
      ((((List.range bound).reverse.sublistsLen 4).map fun selected =>
        if selected.sum = degree then fourSelectedDeterminant selected else 0).sum) := by
  rw [fourExteriorTruncation_eq_selected_sum]
  induction ((List.range bound).reverse.sublistsLen 4) with
  | nil => simp
  | cons selected remaining ih =>
      simp only [List.map_cons, List.sum_cons, map_add, ih,
        fourSelectedSeries, PowerSeries.coeff_monomial]
      by_cases hdegree : degree = selected.sum
      · simp [hdegree]
      · have hreverse : ¬selected.sum = degree := by omega
        simp [hdegree, hreverse]

theorem four_filtered_selected_sum_eq_strictFour_sum
    (size bound : ℕ) (hbound : size + 4 ≤ bound) :
    ∑ selected ∈
        (((List.range bound).reverse.sublistsLen 4).toFinset.filter
          fun selected => selected.sum = size + 6),
        fourSelectedDeterminant selected =
      ∑ tuple : StrictFourAt size,
        Matrix.det (fourFactorialScalarMatrix tuple.a tuple.b tuple.c tuple.d) := by
  symm
  refine Finset.sum_nbij (fun tuple : StrictFourAt size => tuple.toList) ?_ ?_ ?_ ?_
  · intro tuple htuple
    rw [Finset.mem_filter]
    exact ⟨List.mem_toFinset.mpr
        (tuple.toList_mem_sublistsLen_of_bound hbound), tuple.toList_sum⟩
  · intro left hleft right hright heq
    have hfields : left.a = right.a ∧ left.b = right.b ∧
        left.c = right.c ∧ left.d = right.d := by
      simpa [StrictFourAt.toList] using heq
    exact StrictFourAt.ext hfields.1 hfields.2.1
      hfields.2.2.1 hfields.2.2.2
  · intro selected hselected
    change selected ∈
      (((List.range bound).reverse.sublistsLen 4).toFinset.filter
        (fun selected => selected.sum = size + 6)) at hselected
    rw [Finset.mem_filter] at hselected
    obtain ⟨hsource, hsum⟩ := hselected
    have hmember := List.mem_toFinset.mp hsource
    have hlength := List.length_of_sublistsLen hmember
    obtain ⟨a, b, c, d, hselectedEq⟩ :=
      exists_four_entries_of_length_eq_four selected hlength
    subst selected
    have hsublist := (List.mem_sublistsLen.mp hmember).1
    have hpair := (pairwise_gt_reverse_range bound).sublist hsublist
    have hab : b < a := by
      simpa using hpair.rel_get_of_lt
        (show (0 : Fin 4) < (1 : Fin 4) by decide)
    have hbc : c < b := by
      simpa using hpair.rel_get_of_lt
        (show (1 : Fin 4) < (2 : Fin 4) by decide)
    have hcd : d < c := by
      simpa using hpair.rel_get_of_lt
        (show (2 : Fin 4) < (3 : Fin 4) by decide)
    have hsumTuple : a + b + c + d = size + 6 := by
      simpa only [List.sum_cons, List.sum_nil, add_zero, add_assoc] using hsum
    let tuple : StrictFourAt size := ⟨a, b, c, d, hab, hbc, hcd, hsumTuple⟩
    refine ⟨tuple, Finset.mem_univ tuple, ?_⟩
    rfl
  · intro tuple htuple
    rfl

theorem fourExteriorTruncation_coeff_eq_tableaux_of_bound
    (size bound : ℕ) (hbound : size + 4 ≤ bound) :
    PowerSeries.coeff (size + 6) (fourExteriorTruncation bound) =
      (heightFourTableauCount size : ℚ) / (size.factorial : ℚ) := by
  rw [fourExteriorTruncation_coeff]
  let candidates := (List.range bound).reverse.sublistsLen 4
  have hnodup : candidates.Nodup := by
    apply List.nodup_sublistsLen
    exact List.nodup_reverse.mpr List.nodup_range
  rw [← List.sum_toFinset _ hnodup, ← Finset.sum_filter]
  rw [show (∑ selected ∈ candidates.toFinset.filter
      (fun selected => selected.sum = size + 6),
      fourSelectedDeterminant selected) =
      ∑ tuple : StrictFourAt size,
        Matrix.det (fourFactorialScalarMatrix tuple.a tuple.b tuple.c tuple.d) by
    simpa [candidates] using
      four_filtered_selected_sum_eq_strictFour_sum size bound hbound]
  unfold heightFourTableauCount
  rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  push_cast
  rw [← (boundedPartitionStrictFourEquiv size).sum_comp]
  have hfactorial : (size.factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hfactorial).2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro shape hshape
  change Matrix.det (fourFactorialScalarMatrix shape.toStrictFourAt.a
      shape.toStrictFourAt.b shape.toStrictFourAt.c shape.toStrictFourAt.d) *
      (size.factorial : ℚ) = (standardTableauNumber shape : ℚ)
  rw [← boundedFactorialDeterminant_eq_strictFourMatrix shape,
    standardTableauNumber_eq_factorial_mul_boundedFactorialDeterminant]
  ring

noncomputable def fourExteriorLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 6 ≤ degree then
      PowerSeries.coeff degree (fourExteriorTruncation (degree + 1)) else 0

theorem X_six_mul_heightFour_factorialSeries_eq_exteriorLimit :
    X ^ 6 * factorialSeries (fun size => (heightFourTableauCount size : ℚ)) =
      fourExteriorLimitSeries := by
  ext degree
  rw [fourExteriorLimitSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul']
  by_cases hdegree : 6 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree]
    let size := degree - 6
    have hdegreeEq : degree = size + 6 := by dsimp only [size]; omega
    rw [hdegreeEq, Nat.add_sub_cancel, factorialSeries_coeff,
      fourExteriorTruncation_coeff_eq_tableaux_of_bound size
        (size + 6 + 1) (by omega)]
  · rw [if_neg hdegree, if_neg hdegree]

noncomputable def fourTruncatedPfaffian (bound : ℕ) : ℚ⟦X⟧ :=
  let rows := (List.range bound).reverse.map fourFactorialPowerSeriesRow
  pfaffianFour (fourPairSum rows)

set_option maxHeartbeats 1000000 in
theorem fourExteriorTruncation_eq_pfaffian (bound : ℕ) :
    fourExteriorTruncation bound = fourTruncatedPfaffian bound := by
  let rows := (List.range bound).reverse.map fourFactorialPowerSeriesRow
  have hpf := topFourDeterminant_exterior_minor_sum_pfaffian
    (R := ℚ⟦X⟧) rows
  have helem := congrArg (topFourDeterminant (R := ℚ⟦X⟧))
    (exteriorElementary_two_sq (R := ℚ⟦X⟧) rows)
  have hmap : topFourDeterminant (R := ℚ⟦X⟧)
      (2 * exteriorElementary 4 rows) =
      2 * topFourDeterminant (R := ℚ⟦X⟧)
        (exteriorElementary 4 rows) := by
    rw [two_mul, map_add, two_mul]
  rw [hmap] at helem
  change topFourDeterminant (R := ℚ⟦X⟧) (exteriorElementary 2 rows ^ 2) =
      2 * fourExteriorTruncation bound at helem
  change topFourDeterminant (R := ℚ⟦X⟧) (exteriorElementary 2 rows ^ 2) =
      2 * fourTruncatedPfaffian bound at hpf
  have htwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro hzero
    have hcast : (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) := by
      exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm
    rw [hcast] at hzero
    have hC : PowerSeries.C (2 : ℚ) = PowerSeries.C 0 :=
      hzero.trans (map_zero PowerSeries.C).symm
    have := PowerSeries.C_injective hC
    norm_num at this
  apply mul_left_cancel₀ htwo
  rw [← helem, ← hpf]

end FibonacciRibbonKernel
