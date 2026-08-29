import FibonacciRibbonKernel.FrontMatchingContraction
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def badEventFinset (rank columns location : ℕ) :
    Finset (UnrestrictedParameterList rank columns) := by
  classical
  exact Finset.univ.filter
    (fun word => location ∈ badLocations rank word.parameters)

noncomputable def admissibleRibbonFinset (rank columns : ℕ) :
    Finset (UnrestrictedParameterList rank columns) := by
  classical
  exact Finset.univ.filter
    (fun word => badLocations rank word.parameters = ∅)

theorem mem_finset_inf
    {ι α : Type*} [DecidableEq α] [Fintype α]
    (indices : Finset ι) (sets : ι → Finset α) (element : α) :
    element ∈ indices.inf sets ↔
      ∀ index ∈ indices, element ∈ sets index := by
  classical
  induction indices using Finset.cons_induction with
  | empty => simp
  | cons index indices hnot ih => simp [ih]

theorem ribbonCount_eq_admissibleFinset_card (rank columns : ℕ) :
    ribbonCount rank columns = (admissibleRibbonFinset rank columns).card := by
  classical
  unfold ribbonCount AdmissibleRibbonObject admissibleRibbonFinset
  exact Fintype.card_subtype _

theorem admissibleRibbonFinset_eq_inf_compl (rank columns : ℕ) :
    admissibleRibbonFinset rank columns =
      (Finset.range (columns - 1)).inf
        (fun location => (badEventFinset rank columns location)ᶜ) := by
  classical
  ext word
  simp only [admissibleRibbonFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro hempty
    rw [mem_finset_inf (α := UnrestrictedParameterList rank columns)]
    intro location hlocation
    simp only [Finset.mem_compl]
    intro hmember
    have hbad : location ∈ badLocations rank word.parameters := by
      simpa [badEventFinset] using hmember
    rw [hempty] at hbad
    exact Finset.notMem_empty location hbad
  · intro hinf
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨location, hbad⟩
    have hbound := (mem_badLocations_iff rank word.parameters location).mp hbad |>.1
    have hlength := word.length_eq
    have hrange : location ∈ Finset.range (columns - 1) := by
      simp only [Finset.mem_range]
      rwa [hlength] at hbound
    have hnot : word ∉ badEventFinset rank columns location := by
      have := (mem_finset_inf (α := UnrestrictedParameterList rank columns)
        (Finset.range (columns - 1))
        (fun edge => (badEventFinset rank columns edge)ᶜ) word).mp hinf
        location hrange
      simpa using this
    apply hnot
    simpa [badEventFinset] using hbad

/-- Raw inclusion--exclusion on the literal finite bad-adjacency events. -/
theorem ribbonCount_raw_inclusion_exclusion (rank columns : ℕ) :
    (ribbonCount rank columns : ℤ) =
      ∑ locations ∈ (Finset.range (columns - 1)).powerset,
        (-1 : ℤ) ^ locations.card *
          ((locations.inf (badEventFinset rank columns)).card : ℤ) := by
  rw [ribbonCount_eq_admissibleFinset_card,
    admissibleRibbonFinset_eq_inf_compl]
  exact Finset.inclusion_exclusion_card_inf_compl
    (Finset.range (columns - 1)) (badEventFinset rank columns)

theorem inf_badEventFinset_eq_filter
    (rank columns : ℕ) (locations : Finset ℕ) :
    locations.inf (badEventFinset rank columns) =
      Finset.univ.filter (fun word : UnrestrictedParameterList rank columns =>
        locations ⊆ badLocations rank word.parameters) := by
  classical
  ext word
  rw [mem_finset_inf (α := UnrestrictedParameterList rank columns)]
  simp only [badEventFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hall location hlocation
    exact hall location hlocation
  · intro hsubset location hlocation
    exact hsubset hlocation

theorem inf_badEventFinset_card_of_nonAdjacent
    (rank columns : ℕ) (locations : Finset ℕ)
    (hsubset : locations ⊆ Finset.range (columns - 1))
    (hnonAdjacent : NonAdjacentEdges locations) :
    (locations.inf (badEventFinset rank columns)).card =
      unrestrictedCount rank (columns - 2 * locations.card) := by
  let matching : ActualPathMatching columns locations.card :=
    { edgePositions := locations
      card_eq := rfl
      subset_range := hsubset
      nonAdjacent := hnonAdjacent }
  rw [inf_badEventFinset_eq_filter]
  rw [← Fintype.card_subtype]
  change Fintype.card
      (MatchingIntersection rank columns locations.card matching) = _
  exact matchingIntersection_card_actual rank matching

theorem inf_badEventFinset_eq_empty_of_not_nonAdjacent
    {rank columns : ℕ} (hrank : 1 ≤ rank) (locations : Finset ℕ)
    (hnot : ¬ NonAdjacentEdges locations) :
    locations.inf (badEventFinset rank columns) = ∅ := by
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
  have hall : ∀ edge ∈ locations,
      edge ∈ badLocations rank word.parameters := by
    have := (mem_finset_inf (α := UnrestrictedParameterList rank columns)
      locations (badEventFinset rank columns) word).mp hword
    intro edge hedge
    simpa [badEventFinset] using this edge hedge
  have hbad := (mem_badLocations_iff rank word.parameters location).mp
    (hall location hlocation) |>.2
  have hbadNext := (mem_badLocations_iff rank word.parameters (location + 1)).mp
    (hall (location + 1) hnext) |>.2
  exact badAt_adjacent_impossible hrank hbad hbadNext

theorem inf_badEventFinset_card_piecewise
    {rank columns : ℕ} (hrank : 1 ≤ rank) (locations : Finset ℕ)
    (hsubset : locations ⊆ Finset.range (columns - 1)) :
    ((locations.inf (badEventFinset rank columns)).card : ℤ) =
      if NonAdjacentEdges locations then
        (unrestrictedCount rank (columns - 2 * locations.card) : ℤ)
      else 0 := by
  classical
  by_cases hnonAdjacent : NonAdjacentEdges locations
  · rw [if_pos hnonAdjacent]
    exact_mod_cast inf_badEventFinset_card_of_nonAdjacent
      rank columns locations hsubset hnonAdjacent
  · rw [if_neg hnonAdjacent,
      inf_badEventFinset_eq_empty_of_not_nonAdjacent hrank locations hnonAdjacent]
    simp

theorem powersetCard_nonAdjacent_sum
    (columns edges : ℕ) (value : ℕ → ℤ) :
    (∑ locations ∈
        (Finset.range (columns - 1)).powersetCard edges,
      if NonAdjacentEdges locations then value locations.card else 0) =
      (Nat.choose (columns - edges) edges : ℤ) * value edges := by
  classical
  rw [← Finset.sum_filter]
  change (∑ locations ∈ ordinaryPathMatchings columns edges,
      value locations.card) = _
  calc
    (∑ locations ∈ ordinaryPathMatchings columns edges,
        value locations.card) =
        ∑ _location ∈ ordinaryPathMatchings columns edges, value edges := by
          apply Finset.sum_congr rfl
          intro location hlocation
          have hmem := hlocation
          simp only [ordinaryPathMatchings, Finset.mem_filter,
            Finset.mem_powersetCard] at hmem
          rw [hmem.1.2]
    _ = ((ordinaryPathMatchings columns edges).card : ℤ) * value edges := by
          simp
    _ = (Nat.choose (columns - edges) edges : ℤ) * value edges := by
          rw [ordinaryPathMatchings_card]

theorem weighted_nonAdjacent_powerset_sum
    (columns : ℕ) (value : ℕ → ℤ) :
    (∑ locations ∈ (Finset.range (columns - 1)).powerset,
      if NonAdjacentEdges locations then value locations.card else 0) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (Nat.choose (columns - edges) edges : ℤ) * value edges := by
  classical
  rw [Finset.sum_powerset]
  simp_rw [powersetCard_nonAdjacent_sum columns]
  have hgrouped :
      (∑ edges ∈ Finset.range ((Finset.range (columns - 1)).card + 1),
          (Nat.choose (columns - edges) edges : ℤ) * value edges) =
        ∑ edges ∈ Finset.range (columns / 2 + 1),
          (Nat.choose (columns - edges) edges : ℤ) * value edges := by
    by_cases hzero : columns = 0
    · subst columns
      simp
    · have hpositive : 0 < columns := Nat.pos_of_ne_zero hzero
      have hcard : (Finset.range (columns - 1)).card + 1 = columns := by
        simp
        omega
      rw [hcard]
      symm
      apply Finset.sum_subset
      · intro edges hedges
        simp only [Finset.mem_range] at hedges ⊢
        omega
      · intro edges hedges hnotSmall
        simp only [Finset.mem_range] at hedges
        have hlarge : columns / 2 < edges := by
          simpa only [Finset.mem_range, Nat.lt_add_one_iff, not_le] using hnotSmall
        have hlt : columns - edges < edges := by omega
        rw [Nat.choose_eq_zero_of_lt hlt]
        simp
  exact hgrouped

/-- Main inclusion--exclusion formula before substituting the SYT sum. -/
theorem ribbonCount_eq_alternating_unrestricted
    {rank : ℕ} (hrank : 1 ≤ rank) (columns : ℕ) :
    (ribbonCount rank columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (unrestrictedCount rank (columns - 2 * edges) : ℤ) := by
  rw [ribbonCount_raw_inclusion_exclusion]
  calc
    (∑ locations ∈ (Finset.range (columns - 1)).powerset,
        (-1 : ℤ) ^ locations.card *
          ((locations.inf (badEventFinset rank columns)).card : ℤ)) =
      ∑ locations ∈ (Finset.range (columns - 1)).powerset,
        if NonAdjacentEdges locations then
          (-1 : ℤ) ^ locations.card *
            (unrestrictedCount rank (columns - 2 * locations.card) : ℤ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro locations hlocations
          have hsubset := Finset.mem_powerset.mp hlocations
          rw [inf_badEventFinset_card_piecewise hrank locations hsubset]
          by_cases hnon : NonAdjacentEdges locations <;> simp [hnon]
    _ = ∑ edges ∈ Finset.range (columns / 2 + 1),
        (Nat.choose (columns - edges) edges : ℤ) *
          ((-1 : ℤ) ^ edges *
            (unrestrictedCount rank (columns - 2 * edges) : ℤ)) :=
          weighted_nonAdjacent_powerset_sum columns
            (fun edges => (-1 : ℤ) ^ edges *
              (unrestrictedCount rank (columns - 2 * edges) : ℤ))
    _ = ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (unrestrictedCount rank (columns - 2 * edges) : ℤ) := by
          apply Finset.sum_congr rfl
          intro edges hedges
          ring

/-- Complete manuscript formula `thm:main` / `eq:main`. -/
theorem ribbonCount_main_formula
    {rank : ℕ} (hrank : 1 ≤ rank) (columns : ℕ) :
    (ribbonCount rank columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (∑ shape : BoundedPartition rank (columns - 2 * edges),
            (standardTableauNumber shape : ℤ)) := by
  rw [ribbonCount_eq_alternating_unrestricted hrank]
  apply Finset.sum_congr rfl
  intro edges hedges
  rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  simp only [Nat.cast_sum]

end FibonacciRibbonKernel
