import FibonacciRibbonKernel.StandardTableaux
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

/--
Canonical matchings of `j` edges in the path on `vertices` vertices.  For a
path enlarged by two vertices, a matching either omits the last edge or uses
it, in which case the preceding edge is unavailable.
-/
def PathMatching : ℕ → ℕ → Type
  | 0, 0 => PUnit
  | 0, _ + 1 => PEmpty
  | 1, 0 => PUnit
  | 1, _ + 1 => PEmpty
  | _ + 2, 0 => PUnit
  | vertices + 2, edges + 1 =>
      PathMatching (vertices + 1) (edges + 1) ⊕
        PathMatching vertices edges

noncomputable instance pathMatchingFintype (vertices edges : ℕ) :
    Fintype (PathMatching vertices edges) := by
  induction vertices using Nat.twoStepInduction generalizing edges with
  | zero =>
      cases edges <;> simp [PathMatching] <;> infer_instance
  | one =>
      cases edges <;> simp [PathMatching] <;> infer_instance
  | more vertices ih ihSucc =>
      cases edges with
      | zero => simp [PathMatching]; infer_instance
      | succ edges =>
          simp only [PathMatching]
          letI := ihSucc (edges + 1)
          letI := ih edges
          infer_instance

/-- Exact cardinality of size-`j` matchings in a path. -/
theorem pathMatching_card (vertices edges : ℕ) :
    Fintype.card (PathMatching vertices edges) =
      Nat.choose (vertices - edges) edges := by
  induction vertices using Nat.twoStepInduction generalizing edges with
  | zero =>
      cases edges <;> simp [PathMatching]
  | one =>
      cases edges <;> simp [PathMatching]
  | more vertices ih ihSucc =>
      cases edges with
      | zero => simp [PathMatching]
      | succ edges =>
          rw [show Fintype.card (PathMatching (vertices + 2) (edges + 1)) =
              Fintype.card (PathMatching (vertices + 1) (edges + 1)) +
                Fintype.card (PathMatching vertices edges) by
            change Fintype.card
                (PathMatching (vertices + 1) (edges + 1) ⊕
                  PathMatching vertices edges) = _
            exact Fintype.card_sum]
          rw [ihSucc, ih]
          by_cases hedge : edges ≤ vertices
          · have hsub : vertices + 1 - (edges + 1) = vertices - edges := by omega
            have hsub' : vertices + 2 - (edges + 1) = (vertices - edges) + 1 := by
              omega
            rw [hsub, hsub']
            rw [Nat.choose_succ_succ]
            exact Nat.add_comm _ _
          · have hlarge : vertices < edges := Nat.lt_of_not_ge hedge
            have hzero1 : Nat.choose (vertices + 1 - (edges + 1)) (edges + 1) = 0 := by
              apply Nat.choose_eq_zero_of_lt
              omega
            have hzero2 : Nat.choose (vertices - edges) edges = 0 := by
              apply Nat.choose_eq_zero_of_lt
              omega
            have hzero3 : Nat.choose (vertices + 2 - (edges + 1)) (edges + 1) = 0 := by
              apply Nat.choose_eq_zero_of_lt
              omega
            rw [hzero1, hzero2, hzero3]

set_option linter.unusedVariables false in
/-- Concrete edge locations selected by the recursive matching carrier. -/
def PathMatching.edgePositions :
    {vertices edges : ℕ} → PathMatching vertices edges → Finset ℕ
  | 0, 0, _ => ∅
  | 0, _ + 1, matching => nomatch matching
  | 1, 0, _ => ∅
  | 1, _ + 1, matching => nomatch matching
  | _ + 2, 0, _ => ∅
  | vertices + 2, edges + 1, Sum.inl matching => matching.edgePositions
  | vertices + 2, edges + 1, Sum.inr matching =>
      insert vertices matching.edgePositions

theorem PathMatching.edgePositions_subset
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    matching.edgePositions ⊆ Finset.range (vertices - 1) := by
  induction vertices using Nat.twoStepInduction generalizing edges with
  | zero =>
      cases edges with
      | zero => simp [PathMatching.edgePositions]
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => simp [PathMatching.edgePositions]
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => simp [PathMatching.edgePositions]
      | succ edges =>
          cases matching with
          | inl matching =>
              intro location hlocation
              have hbound := ihSucc matching hlocation
              simp only [Finset.mem_range] at hbound ⊢
              omega
          | inr matching =>
              intro location hlocation
              simp only [PathMatching.edgePositions, Finset.mem_insert] at hlocation
              simp only [Finset.mem_range]
              rcases hlocation with rfl | hlocation
              · omega
              · have hbound := ih matching hlocation
                simp only [Finset.mem_range] at hbound
                omega

theorem PathMatching.card_edgePositions
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    matching.edgePositions.card = edges := by
  induction vertices using Nat.twoStepInduction generalizing edges with
  | zero =>
      cases edges with
      | zero => simp [PathMatching.edgePositions]
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => simp [PathMatching.edgePositions]
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => simp [PathMatching.edgePositions]
      | succ edges =>
          cases matching with
          | inl matching =>
              simpa [PathMatching.edgePositions] using ihSucc matching
          | inr matching =>
              have hnot : vertices ∉ matching.edgePositions := by
                intro hmem
                have hbound := matching.edgePositions_subset hmem
                simp only [Finset.mem_range] at hbound
                omega
              simp [PathMatching.edgePositions, hnot, ih matching]

/-- No two selected path-edge locations are consecutive. -/
def NonAdjacentEdges (locations : Finset ℕ) : Prop :=
  ∀ location ∈ locations, location + 1 ∉ locations

theorem PathMatching.edgePositions_nonAdjacent
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    NonAdjacentEdges matching.edgePositions := by
  induction vertices using Nat.twoStepInduction generalizing edges with
  | zero =>
      cases edges with
      | zero => simp [NonAdjacentEdges, PathMatching.edgePositions]
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => simp [NonAdjacentEdges, PathMatching.edgePositions]
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => simp [NonAdjacentEdges, PathMatching.edgePositions]
      | succ edges =>
          cases matching with
          | inl matching =>
              simpa [PathMatching.edgePositions] using ihSucc matching
          | inr matching =>
              intro location hlocation hnext
              simp only [PathMatching.edgePositions, Finset.mem_insert] at hlocation hnext
              rcases hlocation with rfl | hlocation
              · rcases hnext with hfalse | hnext
                · omega
                · have hbound := matching.edgePositions_subset hnext
                  simp only [Finset.mem_range] at hbound
                  omega
              · rcases hnext with hnextEq | hnext
                · have hbound := matching.edgePositions_subset hlocation
                  simp only [Finset.mem_range] at hbound
                  omega
                · exact ih matching location hlocation hnext

/-- Ordinary finite-set presentation of a size-`edges` path matching. -/
structure ActualPathMatching (vertices edges : ℕ) where
  edgePositions : Finset ℕ
  card_eq : edgePositions.card = edges
  subset_range : edgePositions ⊆ Finset.range (vertices - 1)
  nonAdjacent : NonAdjacentEdges edgePositions

@[ext] theorem ActualPathMatching.ext
    {vertices edges : ℕ} {left right : ActualPathMatching vertices edges}
    (hpositions : left.edgePositions = right.edgePositions) : left = right := by
  cases left
  cases right
  simp_all

def PathMatching.toActual
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    ActualPathMatching vertices edges where
  edgePositions := matching.edgePositions
  card_eq := matching.card_edgePositions
  subset_range := matching.edgePositions_subset
  nonAdjacent := matching.edgePositions_nonAdjacent

theorem ActualPathMatching.empty_of_small_vertices
    {vertices edges : ℕ} (matching : ActualPathMatching vertices edges)
    (hvertices : vertices ≤ 1) : matching.edgePositions = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨location, hlocation⟩
  have hbound := matching.subset_range hlocation
  simp only [Finset.mem_range] at hbound
  omega

/-- Recover the canonical last-edge decomposition from an ordinary matching. -/
def ActualPathMatching.toCanonical :
    {vertices edges : ℕ} → ActualPathMatching vertices edges →
      PathMatching vertices edges
  | 0, 0, _ => PUnit.unit
  | 0, edges + 1, matching => by
      have hempty := matching.empty_of_small_vertices (by omega)
      have hcard := matching.card_eq
      rw [hempty] at hcard
      simp at hcard
  | 1, 0, _ => PUnit.unit
  | 1, edges + 1, matching => by
      have hempty := matching.empty_of_small_vertices (by omega)
      have hcard := matching.card_eq
      rw [hempty] at hcard
      simp at hcard
  | vertices + 2, 0, _ => PUnit.unit
  | vertices + 2, edges + 1, matching => by
      by_cases hlast : vertices ∈ matching.edgePositions
      · apply Sum.inr
        let smaller : ActualPathMatching vertices edges :=
          { edgePositions := matching.edgePositions.erase vertices
            card_eq := by
              rw [Finset.card_erase_of_mem hlast, matching.card_eq]
              omega
            subset_range := by
              intro location hlocation
              have hmem := Finset.mem_of_mem_erase hlocation
              have hne := Finset.ne_of_mem_erase hlocation
              have hbound := matching.subset_range hmem
              have hnotPrevious : location + 1 ≠ vertices := by
                intro heq
                exact matching.nonAdjacent location hmem (heq ▸ hlast)
              simp only [Finset.mem_range] at hbound ⊢
              omega
            nonAdjacent := by
              intro location hlocation hnext
              exact matching.nonAdjacent location
                (Finset.mem_of_mem_erase hlocation)
                (Finset.mem_of_mem_erase hnext) }
        exact smaller.toCanonical
      · apply Sum.inl
        let smaller : ActualPathMatching (vertices + 1) (edges + 1) :=
          { edgePositions := matching.edgePositions
            card_eq := matching.card_eq
            subset_range := by
              intro location hlocation
              have hbound := matching.subset_range hlocation
              simp only [Finset.mem_range] at hbound ⊢
              by_contra hnot
              have heq : location = vertices := by omega
              exact hlast (heq ▸ hlocation)
            nonAdjacent := matching.nonAdjacent }
        exact smaller.toCanonical

theorem PathMatching.toActual_toCanonical
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    matching.toActual.toCanonical = matching := by
  induction vertices using Nat.twoStepInduction generalizing edges with
  | zero =>
      cases edges with
      | zero => cases matching; rfl
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => cases matching; rfl
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => cases matching; rfl
      | succ edges =>
          cases matching with
          | inl matching =>
              have hnot : vertices ∉ matching.edgePositions := by
                intro hmem
                have hbound := matching.edgePositions_subset hmem
                simp only [Finset.mem_range] at hbound
                omega
              simp [PathMatching.toActual, ActualPathMatching.toCanonical,
                PathMatching.edgePositions, hnot]
              exact congrArg Sum.inl (ihSucc matching)
          | inr matching =>
              have hnot : vertices ∉ matching.edgePositions := by
                intro hmem
                have hbound := matching.edgePositions_subset hmem
                simp only [Finset.mem_range] at hbound
                omega
              simp [PathMatching.toActual, ActualPathMatching.toCanonical,
                PathMatching.edgePositions, hnot]
              exact congrArg Sum.inr (ih matching)

theorem ActualPathMatching.toCanonical_toActual
    {vertices edges : ℕ} (matching : ActualPathMatching vertices edges) :
    matching.toCanonical.toActual = matching := by
  induction vertices using Nat.twoStepInduction generalizing edges with
  | zero =>
      cases edges with
      | zero =>
          apply ActualPathMatching.ext
          exact (matching.empty_of_small_vertices (by omega)).symm
      | succ edges =>
          have hempty := matching.empty_of_small_vertices (by omega)
          have hcard := matching.card_eq
          rw [hempty] at hcard
          simp at hcard
  | one =>
      cases edges with
      | zero =>
          apply ActualPathMatching.ext
          exact (matching.empty_of_small_vertices (by omega)).symm
      | succ edges =>
          have hempty := matching.empty_of_small_vertices (by omega)
          have hcard := matching.card_eq
          rw [hempty] at hcard
          simp at hcard
  | more vertices ih ihSucc =>
      cases edges with
      | zero =>
          apply ActualPathMatching.ext
          have hcard := matching.card_eq
          exact (Finset.card_eq_zero.mp hcard).symm
      | succ edges =>
          by_cases hlast : vertices ∈ matching.edgePositions
          · let smaller : ActualPathMatching vertices edges :=
              { edgePositions := matching.edgePositions.erase vertices
                card_eq := by
                  rw [Finset.card_erase_of_mem hlast, matching.card_eq]
                  omega
                subset_range := by
                  intro location hlocation
                  have hmem := Finset.mem_of_mem_erase hlocation
                  have hne := Finset.ne_of_mem_erase hlocation
                  have hbound := matching.subset_range hmem
                  have hnotPrevious : location + 1 ≠ vertices := by
                    intro heq
                    exact matching.nonAdjacent location hmem (heq ▸ hlast)
                  simp only [Finset.mem_range] at hbound ⊢
                  omega
                nonAdjacent := by
                  intro location hlocation hnext
                  exact matching.nonAdjacent location
                    (Finset.mem_of_mem_erase hlocation)
                    (Finset.mem_of_mem_erase hnext) }
            apply ActualPathMatching.ext
            simp only [ActualPathMatching.toCanonical, hlast,
              PathMatching.toActual]
            change insert vertices
                (smaller.toCanonical.toActual.edgePositions) =
              matching.edgePositions
            rw [congrArg ActualPathMatching.edgePositions (ih smaller)]
            exact Finset.insert_erase hlast
          · let smaller : ActualPathMatching (vertices + 1) (edges + 1) :=
              { edgePositions := matching.edgePositions
                card_eq := matching.card_eq
                subset_range := by
                  intro location hlocation
                  have hbound := matching.subset_range hlocation
                  simp only [Finset.mem_range] at hbound ⊢
                  by_contra hnot
                  have heq : location = vertices := by omega
                  exact hlast (heq ▸ hlocation)
                nonAdjacent := matching.nonAdjacent }
            apply ActualPathMatching.ext
            simp only [ActualPathMatching.toCanonical, hlast,
              PathMatching.toActual]
            change smaller.toCanonical.toActual.edgePositions =
              matching.edgePositions
            exact congrArg ActualPathMatching.edgePositions (ihSucc smaller)

/-- Exact equivalence between recursive and ordinary finite-set matchings. -/
def pathMatchingActualEquiv (vertices edges : ℕ) :
    PathMatching vertices edges ≃ ActualPathMatching vertices edges where
  toFun := PathMatching.toActual
  invFun := ActualPathMatching.toCanonical
  left_inv := PathMatching.toActual_toCanonical
  right_inv := ActualPathMatching.toCanonical_toActual

/-- Reflect a path-edge location across the midpoint of the path. -/
def reflectPathLocation (vertices location : ℕ) : ℕ :=
  vertices - 2 - location

/-- Reflection of an ordinary path matching. -/
noncomputable def ActualPathMatching.reflect
    {vertices edges : ℕ} (matching : ActualPathMatching vertices edges) :
    ActualPathMatching vertices edges := by
  classical
  let reflected := matching.edgePositions.image (reflectPathLocation vertices)
  refine
    { edgePositions := reflected
      card_eq := ?_
      subset_range := ?_
      nonAdjacent := ?_ }
  · rw [Finset.card_image_of_injOn]
    · exact matching.card_eq
    · intro left hleft right hright heq
      have hleftBound := matching.subset_range hleft
      have hrightBound := matching.subset_range hright
      simp only [Finset.mem_range] at hleftBound hrightBound
      simp only [reflectPathLocation] at heq
      omega
  · intro location hlocation
    simp only [reflected, Finset.mem_image] at hlocation
    obtain ⟨source, hsource, rfl⟩ := hlocation
    have hbound := matching.subset_range hsource
    simp only [Finset.mem_range] at hbound ⊢
    simp only [reflectPathLocation]
    omega
  · intro location hlocation hnext
    simp only [reflected, Finset.mem_image] at hlocation hnext
    obtain ⟨source, hsource, rfl⟩ := hlocation
    obtain ⟨nextSource, hnextSource, heq⟩ := hnext
    have hsourceBound := matching.subset_range hsource
    have hnextBound := matching.subset_range hnextSource
    simp only [Finset.mem_range] at hsourceBound hnextBound
    simp only [reflectPathLocation] at heq
    have hconsecutive : nextSource + 1 = source := by omega
    exact matching.nonAdjacent nextSource hnextSource (hconsecutive ▸ hsource)

theorem ActualPathMatching.reflect_involutive
    {vertices edges : ℕ} (matching : ActualPathMatching vertices edges) :
    matching.reflect.reflect = matching := by
  classical
  apply ActualPathMatching.ext
  ext location
  constructor
  · intro hlocation
    simp only [ActualPathMatching.reflect, Finset.mem_image] at hlocation
    obtain ⟨middle, hmiddle, rfl⟩ := hlocation
    obtain ⟨source, hsource, hmiddleEq⟩ := hmiddle
    subst middle
    have hbound := matching.subset_range hsource
    simp only [Finset.mem_range] at hbound
    have heq : reflectPathLocation vertices
        (reflectPathLocation vertices source) = source := by
      simp [reflectPathLocation]
      omega
    rw [heq]
    exact hsource
  · intro hlocation
    have hbound := matching.subset_range hlocation
    simp only [Finset.mem_range] at hbound
    simp only [ActualPathMatching.reflect, Finset.mem_image]
    refine ⟨reflectPathLocation vertices location, ?_, ?_⟩
    · exact ⟨location, hlocation, rfl⟩
    · simp [reflectPathLocation]
      omega

theorem ActualPathMatching.reflect_edgePositions
    {vertices edges : ℕ} (matching : ActualPathMatching vertices edges) :
    matching.reflect.edgePositions =
      matching.edgePositions.image (reflectPathLocation vertices) := by
  rfl

noncomputable def actualPathMatchingReflectionEquiv (vertices edges : ℕ) :
    ActualPathMatching vertices edges ≃ ActualPathMatching vertices edges where
  toFun := ActualPathMatching.reflect
  invFun := ActualPathMatching.reflect
  left_inv := ActualPathMatching.reflect_involutive
  right_inv := ActualPathMatching.reflect_involutive

/-- Canonical matching interpreted from the first edge rather than the last. -/
noncomputable def frontPathMatchingActualEquiv (vertices edges : ℕ) :
    PathMatching vertices edges ≃ ActualPathMatching vertices edges :=
  (pathMatchingActualEquiv vertices edges).trans
    (actualPathMatchingReflectionEquiv vertices edges)

noncomputable instance actualPathMatchingFintype (vertices edges : ℕ) :
    Fintype (ActualPathMatching vertices edges) :=
  Fintype.ofEquiv (PathMatching vertices edges)
    (frontPathMatchingActualEquiv vertices edges)

noncomputable def ordinaryPathMatchings (vertices edges : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.powersetCard edges (Finset.range (vertices - 1))).filter
    NonAdjacentEdges

noncomputable def actualPathMatchingOrdinaryEquiv (vertices edges : ℕ) :
    ActualPathMatching vertices edges ≃ ordinaryPathMatchings vertices edges where
  toFun matching := by
    refine ⟨matching.edgePositions, ?_⟩
    simp [ordinaryPathMatchings, matching.subset_range,
      matching.card_eq, matching.nonAdjacent]
  invFun matching := by
    have hmem := matching.2
    simp only [ordinaryPathMatchings, Finset.mem_filter,
      Finset.mem_powersetCard] at hmem
    exact
      { edgePositions := matching.1
        card_eq := hmem.1.2
        subset_range := hmem.1.1
        nonAdjacent := hmem.2 }
  left_inv matching := by apply ActualPathMatching.ext; rfl
  right_inv matching := by apply Subtype.ext; rfl

theorem ordinaryPathMatchings_card (vertices edges : ℕ) :
    (ordinaryPathMatchings vertices edges).card =
      Nat.choose (vertices - edges) edges := by
  rw [← Fintype.card_coe]
  rw [← Fintype.card_congr (actualPathMatchingOrdinaryEquiv vertices edges)]
  rw [← Fintype.card_congr (frontPathMatchingActualEquiv vertices edges)]
  exact pathMatching_card vertices edges

theorem frontPathMatchingActualEquiv_apply
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    (frontPathMatchingActualEquiv vertices edges) matching =
      matching.toActual.reflect := rfl

theorem frontPathMatching_inl_positions
    {vertices edges : ℕ}
    (matching : PathMatching (vertices + 1) (edges + 1)) :
    ((frontPathMatchingActualEquiv (vertices + 2) (edges + 1))
        (Sum.inl matching)).edgePositions =
      Finset.image (fun location => location + 1)
        (((frontPathMatchingActualEquiv (vertices + 1) (edges + 1))
          matching).edgePositions) := by
  classical
  rw [frontPathMatchingActualEquiv_apply,
    frontPathMatchingActualEquiv_apply,
    ActualPathMatching.reflect_edgePositions,
    ActualPathMatching.reflect_edgePositions]
  ext location
  simp only [PathMatching.toActual, PathMatching.edgePositions, Finset.mem_image]
  constructor
  · rintro ⟨source, hsource, rfl⟩
    refine ⟨reflectPathLocation (vertices + 1) source, ?_, ?_⟩
    · exact ⟨source, hsource, rfl⟩
    · have hbound := matching.edgePositions_subset hsource
      simp only [Finset.mem_range] at hbound
      simp [reflectPathLocation]
      omega
  · rintro ⟨shifted, ⟨source, hsource, rfl⟩, rfl⟩
    refine ⟨source, hsource, ?_⟩
    have hbound := matching.edgePositions_subset hsource
    simp only [Finset.mem_range] at hbound
    simp [reflectPathLocation]
    omega

theorem frontPathMatching_inr_positions
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    ((frontPathMatchingActualEquiv (vertices + 2) (edges + 1))
        (Sum.inr matching)).edgePositions =
      insert 0
        (((frontPathMatchingActualEquiv vertices edges) matching).edgePositions.image
          (fun location => location + 2)) := by
  classical
  rw [frontPathMatchingActualEquiv_apply,
    frontPathMatchingActualEquiv_apply,
    ActualPathMatching.reflect_edgePositions,
    ActualPathMatching.reflect_edgePositions]
  ext location
  simp only [PathMatching.toActual, PathMatching.edgePositions,
    Finset.mem_image, Finset.mem_insert]
  constructor
  · rintro ⟨source, hsource | hsource, rfl⟩
    · subst source
      left
      simp [reflectPathLocation]
    · right
      refine ⟨reflectPathLocation vertices source, ?_, ?_⟩
      · exact ⟨source, hsource, rfl⟩
      · have hbound := matching.edgePositions_subset hsource
        simp only [Finset.mem_range] at hbound
        simp [reflectPathLocation]
        omega
  · rintro (rfl | ⟨shifted, ⟨source, hsource, rfl⟩, rfl⟩)
    · exact ⟨vertices, by simp, by simp [reflectPathLocation]⟩
    · refine ⟨source, Or.inr hsource, ?_⟩
      have hbound := matching.edgePositions_subset hsource
      simp only [Finset.mem_range] at hbound
      simp [reflectPathLocation]
      omega

end FibonacciRibbonKernel
