import FibonacciRibbonKernel.MainEnumeration

namespace FibonacciRibbonKernel

open scoped Classical

/-- Unrestricted alternating walks ending at one exact difference weight. -/
def UnrestrictedEndpointObject (rank columns : ℕ) (target : Weight rank) :=
  {word : UnrestrictedParameterList rank columns //
    parameterListWeight rank true word.parameters = target}

noncomputable instance unrestrictedEndpointObjectFintype
    (rank columns : ℕ) (target : Weight rank) :
    Fintype (UnrestrictedEndpointObject rank columns target) := by
  classical
  unfold UnrestrictedEndpointObject
  infer_instance

noncomputable def mixedEndpointMultiplicity
    (rank columns : ℕ) (target : Weight rank) : ℕ :=
  Fintype.card (UnrestrictedEndpointObject rank columns target)

/-- Admissible ribbon words ending at one exact difference weight. -/
def AdmissibleEndpointObject (rank columns : ℕ) (target : Weight rank) :=
  {word : UnrestrictedParameterList rank columns //
    badLocations rank word.parameters = ∅ ∧
      parameterListWeight rank true word.parameters = target}

noncomputable instance admissibleEndpointObjectFintype
    (rank columns : ℕ) (target : Weight rank) :
    Fintype (AdmissibleEndpointObject rank columns target) := by
  classical
  unfold AdmissibleEndpointObject
  infer_instance

noncomputable def ribbonEndpointMultiplicity
    (rank columns : ℕ) (target : Weight rank) : ℕ :=
  Fintype.card (AdmissibleEndpointObject rank columns target)

/-- One matching intersection, restricted to an exact endpoint. -/
def EndpointMatchingIntersection
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) (target : Weight rank) :=
  {intersection : MatchingIntersection rank vertices edges
      ((frontPathMatchingActualEquiv vertices edges) matching) //
    parameterListWeight rank true intersection.1.parameters = target}

noncomputable instance endpointMatchingIntersectionFintype
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) (target : Weight rank) :
    Fintype (EndpointMatchingIntersection rank matching target) := by
  classical
  unfold EndpointMatchingIntersection
  infer_instance

noncomputable def endpointMatchingContractionEquiv
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) (target : Weight rank) :
    EndpointMatchingIntersection rank matching target ≃
      UnrestrictedEndpointObject rank matching.freeVertices target where
  toFun intersection := by
    let contracted :=
      (matchingIntersectionContractionEquiv rank matching) intersection.1
    refine ⟨contracted, ?_⟩
    have hweight := matchingIntersectionContraction_preserves_weight
      rank matching intersection.1
    exact hweight ▸ intersection.2
  invFun contracted := by
    let intersection :=
      (matchingIntersectionContractionEquiv rank matching).symm contracted.1
    refine ⟨intersection, ?_⟩
    have hweight := matchingIntersectionContraction_preserves_weight
      rank matching intersection
    have hright := (matchingIntersectionContractionEquiv rank matching).apply_symm_apply
      contracted.1
    rw [hright] at hweight
    exact hweight.trans contracted.2
  left_inv intersection := by
    apply Subtype.ext
    exact (matchingIntersectionContractionEquiv rank matching).symm_apply_apply
      intersection.1
  right_inv contracted := by
    apply Subtype.ext
    exact (matchingIntersectionContractionEquiv rank matching).apply_symm_apply
      contracted.1

theorem endpointMatchingIntersection_card
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) (target : Weight rank) :
    Fintype.card (EndpointMatchingIntersection rank matching target) =
      mixedEndpointMultiplicity rank (vertices - 2 * edges) target := by
  rw [← matching.freeVertices_eq]
  unfold mixedEndpointMultiplicity
  exact Fintype.card_congr
    (endpointMatchingContractionEquiv rank matching target)

noncomputable def endpointBadEventFinset
    (rank columns : ℕ) (target : Weight rank) (location : ℕ) :
    Finset (UnrestrictedEndpointObject rank columns target) := by
  classical
  exact Finset.univ.filter
    (fun word => location ∈ badLocations rank word.1.parameters)

noncomputable def admissibleEndpointFinset
    (rank columns : ℕ) (target : Weight rank) :
    Finset (UnrestrictedEndpointObject rank columns target) := by
  classical
  exact Finset.univ.filter
    (fun word => badLocations rank word.1.parameters = ∅)

theorem ribbonEndpointMultiplicity_eq_finset_card
    (rank columns : ℕ) (target : Weight rank) :
    ribbonEndpointMultiplicity rank columns target =
      (admissibleEndpointFinset rank columns target).card := by
  classical
  unfold ribbonEndpointMultiplicity AdmissibleEndpointObject
    admissibleEndpointFinset
  let equivalence :
      {word : UnrestrictedParameterList rank columns //
        badLocations rank word.parameters = ∅ ∧
          parameterListWeight rank true word.parameters = target} ≃
      {word : UnrestrictedEndpointObject rank columns target //
        badLocations rank word.1.parameters = ∅} :=
    { toFun := fun word => ⟨⟨word.1, word.2.2⟩, word.2.1⟩
      invFun := fun word => ⟨word.1.1, word.2, word.1.2⟩
      left_inv := fun word => by apply Subtype.ext; rfl
      right_inv := fun word => by apply Subtype.ext; rfl }
  calc
    Fintype.card
        {word : UnrestrictedParameterList rank columns //
          badLocations rank word.parameters = ∅ ∧
            parameterListWeight rank true word.parameters = target} =
      Fintype.card
        {word : UnrestrictedEndpointObject rank columns target //
          badLocations rank word.1.parameters = ∅} :=
        Fintype.card_congr equivalence
    _ = (Finset.univ.filter (fun word : UnrestrictedEndpointObject rank columns target =>
          badLocations rank word.1.parameters = ∅)).card :=
        Fintype.card_subtype _

theorem admissibleEndpointFinset_eq_inf_compl
    (rank columns : ℕ) (target : Weight rank) :
    admissibleEndpointFinset rank columns target =
      (Finset.range (columns - 1)).inf
        (fun location => (endpointBadEventFinset rank columns target location)ᶜ) := by
  classical
  ext word
  simp only [admissibleEndpointFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro hempty
    rw [mem_finset_inf (α := UnrestrictedEndpointObject rank columns target)]
    intro location hlocation
    simp only [Finset.mem_compl]
    intro hmember
    have hbad : location ∈ badLocations rank word.1.parameters := by
      simpa [endpointBadEventFinset] using hmember
    rw [hempty] at hbad
    exact Finset.notMem_empty location hbad
  · intro hinf
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨location, hbad⟩
    have hbound := (mem_badLocations_iff rank word.1.parameters location).mp hbad |>.1
    have hlength := word.1.length_eq
    have hrange : location ∈ Finset.range (columns - 1) := by
      simp only [Finset.mem_range]
      rwa [hlength] at hbound
    have hnot : word ∉ endpointBadEventFinset rank columns target location := by
      have := (mem_finset_inf
        (α := UnrestrictedEndpointObject rank columns target)
        (Finset.range (columns - 1))
        (fun edge => (endpointBadEventFinset rank columns target edge)ᶜ) word).mp
        hinf location hrange
      simpa using this
    apply hnot
    simpa [endpointBadEventFinset] using hbad

theorem ribbonEndpoint_raw_inclusion_exclusion
    (rank columns : ℕ) (target : Weight rank) :
    (ribbonEndpointMultiplicity rank columns target : ℤ) =
      ∑ locations ∈ (Finset.range (columns - 1)).powerset,
        (-1 : ℤ) ^ locations.card *
          ((locations.inf
            (endpointBadEventFinset rank columns target)).card : ℤ) := by
  rw [ribbonEndpointMultiplicity_eq_finset_card,
    admissibleEndpointFinset_eq_inf_compl]
  exact Finset.inclusion_exclusion_card_inf_compl
    (Finset.range (columns - 1))
    (endpointBadEventFinset rank columns target)

theorem inf_endpointBadEventFinset_eq_filter
    (rank columns : ℕ) (target : Weight rank) (locations : Finset ℕ) :
    locations.inf (endpointBadEventFinset rank columns target) =
      Finset.univ.filter
        (fun word : UnrestrictedEndpointObject rank columns target =>
          locations ⊆ badLocations rank word.1.parameters) := by
  classical
  ext word
  rw [mem_finset_inf
    (α := UnrestrictedEndpointObject rank columns target)]
  simp only [endpointBadEventFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hall location hlocation
    exact hall location hlocation
  · intro hsubset location hlocation
    exact hsubset hlocation

theorem inf_endpointBadEventFinset_card_of_nonAdjacent
    (rank columns : ℕ) (target : Weight rank) (locations : Finset ℕ)
    (hsubset : locations ⊆ Finset.range (columns - 1))
    (hnonAdjacent : NonAdjacentEdges locations) :
    (locations.inf (endpointBadEventFinset rank columns target)).card =
      mixedEndpointMultiplicity rank (columns - 2 * locations.card) target := by
  let actual : ActualPathMatching columns locations.card :=
    { edgePositions := locations
      card_eq := rfl
      subset_range := hsubset
      nonAdjacent := hnonAdjacent }
  let canonical := (frontPathMatchingActualEquiv columns locations.card).symm actual
  have hcanonical :
      (frontPathMatchingActualEquiv columns locations.card) canonical = actual :=
    (frontPathMatchingActualEquiv columns locations.card).apply_symm_apply actual
  let equivalence :
      EndpointMatchingIntersection rank canonical target ≃
        {word : UnrestrictedEndpointObject rank columns target //
          locations ⊆ badLocations rank word.1.parameters} :=
    { toFun := fun intersection =>
        ⟨⟨intersection.1.1, intersection.2⟩, by
          have := intersection.1.2
          simpa [canonical, actual, hcanonical] using this⟩
      invFun := fun word =>
        ⟨⟨word.1.1, by
          simpa [canonical, actual, hcanonical] using word.2⟩,
          word.1.2⟩
      left_inv := fun word => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun word => by apply Subtype.ext; apply Subtype.ext; rfl }
  rw [inf_endpointBadEventFinset_eq_filter]
  rw [← Fintype.card_subtype]
  rw [← Fintype.card_congr equivalence]
  exact endpointMatchingIntersection_card rank canonical target

theorem inf_endpointBadEventFinset_eq_empty_of_not_nonAdjacent
    {rank columns : ℕ} (hrank : 1 ≤ rank) (target : Weight rank)
    (locations : Finset ℕ) (hnot : ¬ NonAdjacentEdges locations) :
    locations.inf (endpointBadEventFinset rank columns target) = ∅ := by
  classical
  have hexists : ∃ location,
      location ∈ locations ∧ location + 1 ∈ locations := by
    by_contra hnone
    apply hnot
    intro location hlocation hnext
    apply hnone
    exact ⟨location, hlocation, hnext⟩
  obtain ⟨location, hlocation, hnext⟩ := hexists
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨word, hword⟩
  have hall := (mem_finset_inf
    (α := UnrestrictedEndpointObject rank columns target)
    locations (endpointBadEventFinset rank columns target) word).mp hword
  have hbadMem : location ∈ badLocations rank word.1.parameters := by
    simpa [endpointBadEventFinset] using hall location hlocation
  have hnextMem : location + 1 ∈ badLocations rank word.1.parameters := by
    simpa [endpointBadEventFinset] using hall (location + 1) hnext
  have hbad := (mem_badLocations_iff rank word.1.parameters location).mp hbadMem |>.2
  have hbadNext :=
    (mem_badLocations_iff rank word.1.parameters (location + 1)).mp hnextMem |>.2
  exact badAt_adjacent_impossible hrank hbad hbadNext

theorem inf_endpointBadEventFinset_card_piecewise
    {rank columns : ℕ} (hrank : 1 ≤ rank) (target : Weight rank)
    (locations : Finset ℕ)
    (hsubset : locations ⊆ Finset.range (columns - 1)) :
    ((locations.inf (endpointBadEventFinset rank columns target)).card : ℤ) =
      if NonAdjacentEdges locations then
        (mixedEndpointMultiplicity rank
          (columns - 2 * locations.card) target : ℤ)
      else 0 := by
  classical
  by_cases hnonAdjacent : NonAdjacentEdges locations
  · rw [if_pos hnonAdjacent]
    exact_mod_cast inf_endpointBadEventFinset_card_of_nonAdjacent
      rank columns target locations hsubset hnonAdjacent
  · rw [if_neg hnonAdjacent,
      inf_endpointBadEventFinset_eq_empty_of_not_nonAdjacent
        hrank target locations hnonAdjacent]
    simp

/-- Endpointwise neutral-block inclusion--exclusion. -/
theorem ribbonEndpointMultiplicity_formula
    {rank : ℕ} (hrank : 1 ≤ rank) (columns : ℕ) (target : Weight rank) :
    (ribbonEndpointMultiplicity rank columns target : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (mixedEndpointMultiplicity rank
            (columns - 2 * edges) target : ℤ) := by
  rw [ribbonEndpoint_raw_inclusion_exclusion]
  calc
    (∑ locations ∈ (Finset.range (columns - 1)).powerset,
        (-1 : ℤ) ^ locations.card *
          ((locations.inf
            (endpointBadEventFinset rank columns target)).card : ℤ)) =
      ∑ locations ∈ (Finset.range (columns - 1)).powerset,
        if NonAdjacentEdges locations then
          (-1 : ℤ) ^ locations.card *
            (mixedEndpointMultiplicity rank
              (columns - 2 * locations.card) target : ℤ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro locations hlocations
          have hsubset := Finset.mem_powerset.mp hlocations
          rw [inf_endpointBadEventFinset_card_piecewise
            hrank target locations hsubset]
          by_cases hnon : NonAdjacentEdges locations <;> simp [hnon]
    _ = ∑ edges ∈ Finset.range (columns / 2 + 1),
        (Nat.choose (columns - edges) edges : ℤ) *
          ((-1 : ℤ) ^ edges *
            (mixedEndpointMultiplicity rank
              (columns - 2 * edges) target : ℤ)) :=
          weighted_nonAdjacent_powerset_sum columns
            (fun edges => (-1 : ℤ) ^ edges *
              (mixedEndpointMultiplicity rank
                (columns - 2 * edges) target : ℤ))
    _ = ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (mixedEndpointMultiplicity rank
            (columns - 2 * edges) target : ℤ) := by
          apply Finset.sum_congr rfl
          intro edges hedges
          ring

end FibonacciRibbonKernel
