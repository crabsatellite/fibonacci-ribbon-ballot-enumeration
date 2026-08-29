import FibonacciRibbonKernel.FixedPairFamilies

namespace FibonacciRibbonKernel

open scoped Classical

def AdjacentCycleAt {size : ℕ}
    (permutation : ActualInvolutionOn (Fin size)) (location : ℕ) : Prop :=
  ∃ hright : location + 1 < size,
    permutation.1 ⟨location, by omega⟩ = ⟨location + 1, hright⟩

noncomputable def actualAdjacentLocations
    (size : ℕ) (permutation : ActualInvolutionOn (Fin size)) : Finset ℕ :=
  (Finset.range (size - 1)).filter fun location =>
    AdjacentCycleAt permutation location

noncomputable def actualAdjacentBadEventFinset
    (size location : ℕ) : Finset (ActualInvolutionOn (Fin size)) :=
  Finset.univ.filter fun permutation =>
    location ∈ Finset.range (size - 1) ∧ AdjacentCycleAt permutation location

noncomputable def stableActualInvolutionFinset
    (size : ℕ) : Finset (ActualInvolutionOn (Fin size)) :=
  Finset.univ.filter fun permutation => actualAdjacentLocations size permutation = ∅

noncomputable def stableActualInvolutionNumber (size : ℕ) : ℕ :=
  (stableActualInvolutionFinset size).card

theorem stableActualInvolutionFinset_eq_inf_compl (size : ℕ) :
    stableActualInvolutionFinset size =
      (Finset.range (size - 1)).inf
        (fun location => (actualAdjacentBadEventFinset size location)ᶜ) := by
  classical
  ext permutation
  simp only [stableActualInvolutionFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro hempty
    rw [mem_finset_inf]
    intro location hlocation
    simp only [Finset.mem_compl]
    intro hbad
    have hadjacent : location ∈ actualAdjacentLocations size permutation := by
      simpa [actualAdjacentLocations, actualAdjacentBadEventFinset,
        hlocation] using hbad
    rw [hempty] at hadjacent
    exact Finset.notMem_empty _ hadjacent
  · intro hinf
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨location, hlocation⟩
    have hrange : location ∈ Finset.range (size - 1) := by
      exact (Finset.mem_filter.mp hlocation).1
    have hnot := (mem_finset_inf
      (Finset.range (size - 1))
      (fun edge => (actualAdjacentBadEventFinset size edge)ᶜ)
      permutation).mp hinf location hrange
    simp only [Finset.mem_compl] at hnot
    apply hnot
    simpa [actualAdjacentBadEventFinset] using
      ⟨(by simpa using hrange), (Finset.mem_filter.mp hlocation).2⟩

theorem inf_actualAdjacentBadEventFinset_eq_filter
    (size : ℕ) (locations : Finset ℕ) :
    locations.inf (actualAdjacentBadEventFinset size) =
      Finset.univ.filter
        (fun permutation : ActualInvolutionOn (Fin size) =>
          locations ⊆ actualAdjacentLocations size permutation) := by
  classical
  ext permutation
  rw [mem_finset_inf]
  simp only [actualAdjacentBadEventFinset, actualAdjacentLocations,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hall location hlocation
    have hadjacent := hall location hlocation
    exact Finset.mem_filter.mpr hadjacent
  · intro hsubset location hlocation
    exact Finset.mem_filter.mp (hsubset hlocation)

theorem pathMatching_holdsUnder_iff_locations_subset
    {vertices edges : ℕ} (matching : PathMatching vertices edges)
    (permutation : ActualInvolutionOn (Fin vertices)) :
    matching.HoldsUnder (Function.Embedding.refl _) permutation.1 ↔
      matching.edgePositions ⊆ actualAdjacentLocations vertices permutation := by
  constructor
  · intro hholds location hlocation
    have heq := hholds location hlocation
    simp only [actualAdjacentLocations, Finset.mem_filter]
    refine ⟨matching.edgePositions_subset hlocation, ?_⟩
    refine ⟨(matching.edgeRight location hlocation).isLt, ?_⟩
    simpa [PathMatching.edgeLeft, PathMatching.edgeRight] using heq
  · intro hsubset location hlocation
    have hmem := hsubset hlocation
    simp only [actualAdjacentLocations, Finset.mem_filter] at hmem
    obtain ⟨hrange, hright, heq⟩ := hmem
    simpa [PathMatching.edgeLeft, PathMatching.edgeRight] using heq

theorem inf_actualAdjacentBadEventFinset_card_of_nonAdjacent
    (size : ℕ) (locations : Finset ℕ)
    (hsubset : locations ⊆ Finset.range (size - 1))
    (hnonAdjacent : NonAdjacentEdges locations) :
    (locations.inf (actualAdjacentBadEventFinset size)).card =
      involutionNumber (size - 2 * locations.card) := by
  let actual : ActualPathMatching size locations.card :=
    { edgePositions := locations
      card_eq := rfl
      subset_range := hsubset
      nonAdjacent := hnonAdjacent }
  let canonical := (pathMatchingActualEquiv size locations.card).symm actual
  have hcanonical :
      (pathMatchingActualEquiv size locations.card) canonical = actual :=
    (pathMatchingActualEquiv size locations.card).apply_symm_apply actual
  have hedgePositions : canonical.edgePositions = locations := by
    have h := congrArg (fun matching : ActualPathMatching size locations.card =>
      matching.edgePositions) hcanonical
    simpa [canonical, actual, pathMatchingActualEquiv, PathMatching.toActual] using h
  rw [inf_actualAdjacentBadEventFinset_eq_filter]
  rw [← Fintype.card_subtype]
  let equivalence :
      {permutation : ActualInvolutionOn (Fin size) //
        locations ⊆ actualAdjacentLocations size permutation} ≃
        ActualInvolutionMatchingIntersection canonical :=
    { toFun := fun permutation =>
        ⟨permutation.1, (pathMatching_holdsUnder_iff_locations_subset
          canonical permutation.1).mpr (by
            rw [hedgePositions]
            exact permutation.2)⟩
      invFun := fun permutation =>
        ⟨permutation.1, by
          have := (pathMatching_holdsUnder_iff_locations_subset
            canonical permutation.1).mp permutation.2
          rw [hedgePositions] at this
          exact this⟩
      left_inv := fun permutation => by apply Subtype.ext; rfl
      right_inv := fun permutation => by apply Subtype.ext; rfl }
  rw [Fintype.card_congr equivalence]
  exact actualInvolutionMatchingIntersection_card canonical

theorem inf_actualAdjacentBadEventFinset_eq_empty_of_not_nonAdjacent
    {size : ℕ} (locations : Finset ℕ) (hnot : ¬NonAdjacentEdges locations) :
    locations.inf (actualAdjacentBadEventFinset size) = ∅ := by
  classical
  have hexists : ∃ location,
      location ∈ locations ∧ location + 1 ∈ locations := by
    by_contra hnone
    apply hnot
    intro location hlocation hnext
    exact hnone ⟨location, hlocation, hnext⟩
  obtain ⟨location, hlocation, hnext⟩ := hexists
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨permutation, hpermutation⟩
  have hall := (mem_finset_inf locations
    (actualAdjacentBadEventFinset size) permutation).mp hpermutation
  have hfirst : AdjacentCycleAt permutation location := by
    have hmem : location ∈ Finset.range (size - 1) ∧
        AdjacentCycleAt permutation location := by
      simpa [actualAdjacentBadEventFinset] using hall location hlocation
    exact hmem.2
  have hsecond : AdjacentCycleAt permutation (location + 1) := by
    have hmem : location + 1 ∈ Finset.range (size - 1) ∧
        AdjacentCycleAt permutation (location + 1) := by
      simpa [actualAdjacentBadEventFinset] using hall (location + 1) hnext
    exact hmem.2
  obtain ⟨hfirstBound, hfirstEq⟩ := hfirst
  obtain ⟨hsecondBound, hsecondEq⟩ := hsecond
  have hvalue := congrArg permutation.1 hfirstEq
  rw [permutation.2] at hvalue
  have hmiddle : permutation.1 ⟨location + 1, hfirstBound⟩ =
      ⟨location + 2, hsecondBound⟩ := by
    exact hsecondEq
  rw [hmiddle] at hvalue
  have hval := congrArg Fin.val hvalue
  change location = location + 2 at hval
  omega

theorem stableActualInvolution_inclusion_exclusion (size : ℕ) :
    (stableActualInvolutionNumber size : ℤ) = stableSignedNumber size := by
  unfold stableActualInvolutionNumber stableSignedNumber
  rw [stableActualInvolutionFinset_eq_inf_compl]
  rw [Finset.inclusion_exclusion_card_inf_compl]
  calc
    (∑ locations ∈ (Finset.range (size - 1)).powerset,
        (-1 : ℤ) ^ locations.card *
          ((locations.inf (actualAdjacentBadEventFinset size)).card : ℤ)) =
      ∑ locations ∈ (Finset.range (size - 1)).powerset,
        if NonAdjacentEdges locations then
          (-1 : ℤ) ^ locations.card *
            (involutionNumber (size - 2 * locations.card) : ℤ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro locations hlocations
      have hsubset := Finset.mem_powerset.mp hlocations
      by_cases hnon : NonAdjacentEdges locations
      · rw [if_pos hnon]
        have hcard := inf_actualAdjacentBadEventFinset_card_of_nonAdjacent
          size locations hsubset hnon
        rw [hcard]
      · rw [if_neg hnon,
          inf_actualAdjacentBadEventFinset_eq_empty_of_not_nonAdjacent locations hnon]
        simp
    _ = ∑ edges ∈ Finset.range (size / 2 + 1),
        (Nat.choose (size - edges) edges : ℤ) *
          ((-1 : ℤ) ^ edges *
            (involutionNumber (size - 2 * edges) : ℤ)) :=
      weighted_nonAdjacent_powerset_sum size
        (fun edges => (-1 : ℤ) ^ edges *
          (involutionNumber (size - 2 * edges) : ℤ))
    _ = ∑ edges ∈ Finset.range (size / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (involutionNumber (size - 2 * edges) : ℤ) := by
      apply Finset.sum_congr rfl
      intro edges hedges
      ring

theorem actualAdjacentLocations_nonAdjacent
    {size : ℕ} (permutation : ActualInvolutionOn (Fin size)) :
    NonAdjacentEdges (actualAdjacentLocations size permutation) := by
  intro location hlocation hnext
  have hfirst := (Finset.mem_filter.mp hlocation).2
  have hsecond := (Finset.mem_filter.mp hnext).2
  obtain ⟨hfirstBound, hfirstEq⟩ := hfirst
  obtain ⟨hsecondBound, hsecondEq⟩ := hsecond
  have hvalue := congrArg permutation.1 hfirstEq
  rw [permutation.2] at hvalue
  have hmiddle : permutation.1 ⟨location + 1, hfirstBound⟩ =
      ⟨location + 2, hsecondBound⟩ := hsecondEq
  rw [hmiddle] at hvalue
  have hval := congrArg Fin.val hvalue
  change location = location + 2 at hval
  omega

def AdjacentLocationSelection (size selected : ℕ) :=
  Σ permutation : ActualInvolutionOn (Fin size),
    {locations : Finset ℕ //
      locations ∈ (actualAdjacentLocations size permutation).powersetCard selected}

noncomputable instance adjacentLocationSelectionFintype (size selected : ℕ) :
    Fintype (AdjacentLocationSelection size selected) := by
  unfold AdjacentLocationSelection
  infer_instance

noncomputable def adjacentSelectionToMatching
    {size selected : ℕ} (selection : AdjacentLocationSelection size selected) :
    (Σ matching : PathMatching size selected,
      ActualInvolutionMatchingIntersection matching) := by
    have hmem := selection.2.2
    simp only [Finset.mem_powersetCard] at hmem
    let actual : ActualPathMatching size selected :=
      { edgePositions := selection.2.1
        card_eq := hmem.2
        subset_range := fun location hlocation =>
          (Finset.mem_filter.mp (hmem.1 hlocation)).1
        nonAdjacent := by
          intro location hlocation hnext
          exact actualAdjacentLocations_nonAdjacent selection.1 location
            (hmem.1 hlocation) (hmem.1 hnext) }
    let matching := (pathMatchingActualEquiv size selected).symm actual
    refine ⟨matching, ⟨selection.1, ?_⟩⟩
    apply (pathMatching_holdsUnder_iff_locations_subset matching selection.1).mpr
    have hpositions : matching.edgePositions = selection.2.1 := by
      have h := congrArg (fun value : ActualPathMatching size selected => value.edgePositions)
        ((pathMatchingActualEquiv size selected).apply_symm_apply actual)
      simpa [matching, actual, pathMatchingActualEquiv, PathMatching.toActual] using h
    rw [hpositions]
    exact hmem.1

noncomputable def matchingToAdjacentSelection
    {size selected : ℕ}
    (selection : Σ matching : PathMatching size selected,
      ActualInvolutionMatchingIntersection matching) :
    AdjacentLocationSelection size selected := by
    let locations := selection.1.edgePositions
    refine ⟨selection.2.1, ⟨locations, ?_⟩⟩
    simp only [Finset.mem_powersetCard]
    constructor
    · exact (pathMatching_holdsUnder_iff_locations_subset
        selection.1 selection.2.1).mp selection.2.2
    · exact selection.1.card_edgePositions

noncomputable def adjacentLocationSelectionEquivMatching
    (size selected : ℕ) :
    AdjacentLocationSelection size selected ≃
      (Σ matching : PathMatching size selected,
        ActualInvolutionMatchingIntersection matching) where
  toFun := adjacentSelectionToMatching
  invFun := matchingToAdjacentSelection
  left_inv selection := by
    apply Sigma.ext
    · rfl
    · have hmem := selection.2.2
      simp only [Finset.mem_powersetCard] at hmem
      let actual : ActualPathMatching size selected :=
        { edgePositions := selection.2.1
          card_eq := hmem.2
          subset_range := fun location hlocation =>
            (Finset.mem_filter.mp (hmem.1 hlocation)).1
          nonAdjacent := by
            intro location hlocation hnext
            exact actualAdjacentLocations_nonAdjacent selection.1 location
              (hmem.1 hlocation) (hmem.1 hnext) }
      let matching := (pathMatchingActualEquiv size selected).symm actual
      have hpositions : matching.edgePositions = selection.2.1 := by
        have h := congrArg (fun value : ActualPathMatching size selected => value.edgePositions)
          ((pathMatchingActualEquiv size selected).apply_symm_apply actual)
        simpa [matching, actual, pathMatchingActualEquiv, PathMatching.toActual] using h
      apply heq_of_eq
      apply Subtype.ext
      exact hpositions
  right_inv selection := by
    let locations := selection.1.edgePositions
    let actual : ActualPathMatching size selected :=
      { edgePositions := locations
        card_eq := selection.1.card_edgePositions
        subset_range := selection.1.edgePositions_subset
        nonAdjacent := selection.1.edgePositions_nonAdjacent }
    let matching := (pathMatchingActualEquiv size selected).symm actual
    have hactual : actual = (pathMatchingActualEquiv size selected) selection.1 := by
      apply ActualPathMatching.ext
      rfl
    have hmatching : matching = selection.1 := by
      apply (pathMatchingActualEquiv size selected).injective
      rw [(pathMatchingActualEquiv size selected).apply_symm_apply]
      exact hactual
    have hround :
        (adjacentSelectionToMatching (matchingToAdjacentSelection selection)).1 =
          selection.1 := by
      unfold adjacentSelectionToMatching matchingToAdjacentSelection
      change matching = selection.1
      exact hmatching
    refine Sigma.ext hround ?_
    apply (Subtype.heq_iff_coe_eq (fun permutation => by
      rw [hround])).mpr
    rfl

theorem sum_choose_adjacentCycleCount
    (size selected : ℕ) :
    (∑ permutation : ActualInvolutionOn (Fin size),
        (actualAdjacentLocations size permutation).card.choose selected) =
      Nat.choose (size - selected) selected *
        involutionNumber (size - 2 * selected) := by
  calc
    (∑ permutation : ActualInvolutionOn (Fin size),
        (actualAdjacentLocations size permutation).card.choose selected) =
        Fintype.card (AdjacentLocationSelection size selected) := by
      change _ = Fintype.card
        (Σ permutation : ActualInvolutionOn (Fin size),
          {locations : Finset ℕ //
            locations ∈ (actualAdjacentLocations size permutation).powersetCard selected})
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro permutation hpermutation
      rw [Fintype.card_coe, Finset.card_powersetCard]
    _ = Fintype.card
          (Σ matching : PathMatching size selected,
            ActualInvolutionMatchingIntersection matching) :=
      Fintype.card_congr (adjacentLocationSelectionEquivMatching size selected)
    _ = ∑ matching : PathMatching size selected,
          Fintype.card (ActualInvolutionMatchingIntersection matching) :=
      Fintype.card_sigma
    _ = ∑ _matching : PathMatching size selected,
          involutionNumber (size - 2 * selected) := by
      apply Finset.sum_congr rfl
      intro matching hmatching
      exact actualInvolutionMatchingIntersection_card matching
    _ = Nat.choose (size - selected) selected *
          involutionNumber (size - 2 * selected) := by
      rw [Finset.sum_const, Finset.card_univ, pathMatching_card]
      simp

/-- Numerator form of the factorial-moment identity `eq:factorial-moments`. -/
theorem sum_descFactorial_adjacentCycleCount
    (size selected : ℕ) :
    (∑ permutation : ActualInvolutionOn (Fin size),
        (actualAdjacentLocations size permutation).card.descFactorial selected) =
      selected.factorial * Nat.choose (size - selected) selected *
        involutionNumber (size - 2 * selected) := by
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose,
    ← Finset.mul_sum]
  rw [sum_choose_adjacentCycleCount]
  ring

noncomputable def adjacentCycleFactorialMoment
    (size selected : ℕ) : ℚ :=
  (∑ permutation : ActualInvolutionOn (Fin size),
      ((actualAdjacentLocations size permutation).card.descFactorial selected : ℚ)) /
    involutionNumber size

/-- Exact factorial moment formula for a uniform random involution. -/
theorem adjacentCycleFactorialMoment_formula
    (size selected : ℕ) :
    adjacentCycleFactorialMoment size selected =
      (selected.factorial * Nat.choose (size - selected) selected : ℚ) *
        involutionNumber (size - 2 * selected) / involutionNumber size := by
  unfold adjacentCycleFactorialMoment
  have hsum := sum_descFactorial_adjacentCycleCount size selected
  have hsumQ :
      (∑ permutation : ActualInvolutionOn (Fin size),
          ((actualAdjacentLocations size permutation).card.descFactorial selected : ℚ)) =
        (selected.factorial * Nat.choose (size - selected) selected *
          involutionNumber (size - 2 * selected) : ℕ) := by
    exact_mod_cast hsum
  rw [hsumQ]
  push_cast
  ring

/-- The stable recurrence on the actual no-adjacent-involution carrier. -/
theorem stableActualInvolutionNumber_recurrence
    (size : ℕ) (hsize : 3 ≤ size) :
    (stableActualInvolutionNumber (size + 1) : ℤ) =
      stableActualInvolutionNumber size +
          size * stableActualInvolutionNumber (size - 1) -
        stableActualInvolutionNumber (size - 2) +
          stableActualInvolutionNumber (size - 3) := by
  rw [stableActualInvolution_inclusion_exclusion,
    stableActualInvolution_inclusion_exclusion,
    stableActualInvolution_inclusion_exclusion,
    stableActualInvolution_inclusion_exclusion,
    stableActualInvolution_inclusion_exclusion]
  exact stableSignedNumber_recurrence size hsize

end FibonacciRibbonKernel
