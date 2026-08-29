import FibonacciRibbonKernel.BadLocations

namespace FibonacciRibbonKernel

/-- Number of free columns left after contracting all edges of a matching. -/
def PathMatching.freeVertices :
    {vertices edges : ℕ} → PathMatching vertices edges → ℕ
  | 0, 0, _ => 0
  | 0, _ + 1, matching => nomatch matching
  | 1, 0, _ => 1
  | 1, _ + 1, matching => nomatch matching
  | vertices + 2, 0, _ => vertices + 2
  | _ + 2, _ + 1, Sum.inl matching => matching.freeVertices + 1
  | _ + 2, _ + 1, Sum.inr matching => matching.freeVertices

theorem PathMatching.freeVertices_eq
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    matching.freeVertices = vertices - 2 * edges := by
  induction vertices using Nat.twoStepInduction generalizing edges with
  | zero =>
      cases edges with
      | zero => rfl
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => rfl
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => simp [PathMatching.freeVertices]
      | succ edges =>
          cases matching with
          | inl matching =>
              simp only [PathMatching.freeVertices, ihSucc matching]
              have hnonempty : PathMatching (vertices + 1) (edges + 1) := matching
              have hcardPositive :
                  0 < Fintype.card (PathMatching (vertices + 1) (edges + 1)) :=
                Fintype.card_pos_iff.mpr ⟨hnonempty⟩
              rw [pathMatching_card] at hcardPositive
              have hbound : 2 * (edges + 1) ≤ vertices + 1 := by
                by_contra hnot
                have hlt : vertices + 1 - (edges + 1) < edges + 1 := by omega
                rw [Nat.choose_eq_zero_of_lt hlt] at hcardPositive
                omega
              omega
          | inr matching =>
              simp only [PathMatching.freeVertices, ih matching]
              omega

/-- State reached after reading the fixed forbidden pair at the front. -/
def badPairEndState {rank : ℕ} (state : Weight rank)
    (shortPosition : Bool) : Weight rank :=
  state + (parameterColumn shortPosition 0).weight +
    (parameterColumn (!shortPosition) (Fin.last rank)).weight

theorem badPairEndState_eq
    {rank : ℕ} (state : Weight rank) (shortPosition : Bool) :
    badPairEndState state shortPosition = state := by
  cases shortPosition <;>
    simp [badPairEndState, parameterColumn, parameterComplement,
      Column.weight, add_assoc, oddBadPair_neutral, evenBadPair_neutral]

set_option linter.unusedVariables false in
/--
Words in which the front-recursive matching is prescribed to be bad.  The
`inl` branch leaves the first edge unused and chooses one ordinary first
column; the `inr` branch fixes the first two parameters to `(0,last)`.
-/
def FrontSpecifiedWord (rank : ℕ) :
    (state : Weight rank) → (shortPosition : Bool) →
      {vertices edges : ℕ} → PathMatching vertices edges → Type
  | _, _, 0, 0, _ => PUnit
  | _, _, 0, _ + 1, matching => nomatch matching
  | state, shortPosition, 1, 0, _ =>
      ParameterWordFrom rank state shortPosition 1
  | _, _, 1, _ + 1, matching => nomatch matching
  | state, shortPosition, vertices + 2, 0, _ =>
      ParameterWordFrom rank state shortPosition (vertices + 2)
  | state, shortPosition, _ + 2, _ + 1, Sum.inl matching =>
      Σ parameter : Fin (rank + 1),
        {tail : FrontSpecifiedWord rank
            (state + (parameterColumn shortPosition parameter).weight)
            (!shortPosition) matching //
          (parameterColumn shortPosition parameter).prefixesDominant state}
  | state, shortPosition, _ + 2, _ + 1, Sum.inr matching =>
      FrontSpecifiedWord rank (badPairEndState state shortPosition)
        shortPosition matching

noncomputable instance frontSpecifiedWordFintype
    (rank : ℕ) (state : Weight rank) (shortPosition : Bool)
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    Fintype (FrontSpecifiedWord rank state shortPosition matching) := by
  classical
  induction vertices using Nat.twoStepInduction generalizing edges state shortPosition with
  | zero =>
      cases edges with
      | zero => simp [FrontSpecifiedWord]; infer_instance
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => simp [FrontSpecifiedWord]; infer_instance
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => simp [FrontSpecifiedWord]; infer_instance
      | succ edges =>
          cases matching with
          | inl matching =>
              simp only [FrontSpecifiedWord]
              letI (parameter : Fin (rank + 1)) :=
                ihSucc (state :=
                  state + (parameterColumn shortPosition parameter).weight)
                  (shortPosition := !shortPosition) matching
              infer_instance
          | inr matching =>
              simp only [FrontSpecifiedWord]
              exact ih (state := badPairEndState state shortPosition)
                (shortPosition := shortPosition) matching

def parameterWordStateEquiv
    {rank : ℕ} {left right : Weight rank} (hstate : left = right)
    (shortPosition : Bool) (columns : ℕ) :
    ParameterWordFrom rank left shortPosition columns ≃
      ParameterWordFrom rank right shortPosition columns := by
  subst right
  exact Equiv.refl _

theorem parameterWordStateEquiv_parameters
    {rank : ℕ} {left right : Weight rank} (hstate : left = right)
    (shortPosition : Bool) (columns : ℕ)
    (word : ParameterWordFrom rank left shortPosition columns) :
    ((parameterWordStateEquiv hstate shortPosition columns) word).parameters =
      word.parameters := by
  subst right
  rfl

/-- Contract every prescribed bad pair, retaining all free parameters. -/
noncomputable def frontSpecifiedContractionEquiv
    (rank : ℕ) (state : Weight rank) (shortPosition : Bool)
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    FrontSpecifiedWord rank state shortPosition matching ≃
      ParameterWordFrom rank state shortPosition matching.freeVertices := by
  induction vertices using Nat.twoStepInduction generalizing edges state shortPosition with
  | zero =>
      cases edges with
      | zero => exact Equiv.refl _
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => exact Equiv.refl _
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => exact Equiv.refl _
      | succ edges =>
          cases matching with
          | inl matching =>
              let tailEquiv (parameter : Fin (rank + 1)) :=
                ihSucc
                  (state := state +
                    (parameterColumn shortPosition parameter).weight)
                  (shortPosition := !shortPosition) matching
              refine
                { toFun := fun specified =>
                    ⟨specified.1,
                      ⟨tailEquiv specified.1 specified.2.1, specified.2.2⟩⟩
                  invFun := fun contracted =>
                    ⟨contracted.1,
                      ⟨(tailEquiv contracted.1).symm contracted.2.1,
                        contracted.2.2⟩⟩
                  left_inv := ?_
                  right_inv := ?_ }
              · intro specified
                apply Sigma.ext
                · rfl
                · apply heq_of_eq
                  apply Subtype.ext
                  exact (tailEquiv specified.1).left_inv specified.2.1
              · intro contracted
                apply Sigma.ext
                · rfl
                · apply heq_of_eq
                  apply Subtype.ext
                  exact (tailEquiv contracted.1).right_inv contracted.2.1
          | inr matching =>
              exact (ih
                (state := badPairEndState state shortPosition)
                (shortPosition := shortPosition) matching).trans
                (parameterWordStateEquiv
                  (badPairEndState_eq state shortPosition)
                  shortPosition matching.freeVertices)

set_option linter.unusedVariables false in
/-- Front-recursive assertion that every selected edge carries `(0,last)`. -/
def FrontContains (rank : ℕ) :
    {vertices edges : ℕ} → PathMatching vertices edges →
      List (Fin (rank + 1)) → Prop
  | 0, 0, _, _ => True
  | 0, _ + 1, matching, _ => nomatch matching
  | 1, 0, _, _ => True
  | 1, _ + 1, matching, _ => nomatch matching
  | _ + 2, 0, _, _ => True
  | _ + 2, _ + 1, Sum.inl matching, [] => False
  | _ + 2, _ + 1, Sum.inl matching, _ :: tail =>
      FrontContains rank matching tail
  | _ + 2, _ + 1, Sum.inr matching, first :: second :: tail =>
      first = 0 ∧ second = Fin.last rank ∧ FrontContains rank matching tail
  | _ + 2, _ + 1, Sum.inr _, _ => False

/-- Literal full words carrying a front-recursive specified matching. -/
def FrontIntersectionWord (rank : ℕ) (state : Weight rank)
    (shortPosition : Bool) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) :=
  {word : ParameterWordFrom rank state shortPosition vertices //
    FrontContains rank matching word.parameters}

noncomputable instance frontIntersectionWordFintype
    (rank : ℕ) (state : Weight rank) (shortPosition : Bool)
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    Fintype (FrontIntersectionWord rank state shortPosition matching) := by
  classical
  unfold FrontIntersectionWord
  infer_instance

/-- Insert all prescribed front-recursive bad pairs into the free choices. -/
def FrontSpecifiedWord.toFull
    (rank : ℕ) {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) :
    {vertices edges : ℕ} → (matching : PathMatching vertices edges) →
      FrontSpecifiedWord rank state shortPosition matching →
        ParameterWordFrom rank state shortPosition vertices
  | 0, 0, _, _ => PUnit.unit
  | 0, _ + 1, matching, _ => nomatch matching
  | 1, 0, _, specified => specified
  | 1, _ + 1, matching, _ => nomatch matching
  | _ + 2, 0, _, specified => specified
  | vertices + 2, edges + 1, Sum.inl matching, specified => by
      have hnext := Column.endpointDominant_of_prefixes specified.2.2
      exact ⟨specified.1,
        ⟨specified.2.1.toFull rank hnext (!shortPosition) matching,
          specified.2.2⟩⟩
  | vertices + 2, edges + 1, Sum.inr matching, specified => by
      cases shortPosition with
      | false =>
          have hpair : ColumnsBallotFrom state
              [parameterColumn false 0,
                parameterColumn true (Fin.last rank)] := by
            simpa [badPairBlock] using
              (badPairBlock_neutral rank false).ballot hstate
          have htailState : Dominant (badPairEndState state false) := by
            rw [badPairEndState_eq]
            exact hstate
          let tailFull := specified.toFull rank htailState false matching
          exact ⟨0, ⟨⟨Fin.last rank, ⟨tailFull, hpair.2.1⟩⟩, hpair.1⟩⟩
      | true =>
          have hpair : ColumnsBallotFrom state
              [parameterColumn true 0,
                parameterColumn false (Fin.last rank)] := by
            simpa [badPairBlock] using
              (badPairBlock_neutral rank true).ballot hstate
          have htailState : Dominant (badPairEndState state true) := by
            rw [badPairEndState_eq]
            exact hstate
          let tailFull := specified.toFull rank htailState true matching
          exact ⟨0, ⟨⟨Fin.last rank, ⟨tailFull, hpair.2.1⟩⟩, hpair.1⟩⟩

theorem FrontSpecifiedWord.toFull_contains
    (rank : ℕ) {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) {vertices edges : ℕ}
    (matching : PathMatching vertices edges)
    (specified : FrontSpecifiedWord rank state shortPosition matching) :
    FrontContains rank matching
      (specified.toFull rank hstate shortPosition matching).parameters := by
  induction vertices using Nat.twoStepInduction generalizing edges state shortPosition with
  | zero =>
      cases edges with
      | zero => trivial
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => trivial
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => trivial
      | succ edges =>
          cases matching with
          | inl matching =>
              exact ihSucc
                (Column.endpointDominant_of_prefixes specified.2.2)
                (!shortPosition) matching specified.2.1
          | inr matching =>
              cases shortPosition with
              | false =>
                  have htailState : Dominant (badPairEndState state false) := by
                    rw [badPairEndState_eq]
                    exact hstate
                  exact ⟨rfl, rfl,
                    ih htailState false matching specified⟩
              | true =>
                  have htailState : Dominant (badPairEndState state true) := by
                    rw [badPairEndState_eq]
                    exact hstate
                  exact ⟨rfl, rfl,
                    ih htailState true matching specified⟩

/-- Delete the fixed pairs from a full word satisfying `FrontContains`. -/
def FrontIntersectionWord.toSpecified
    (rank : ℕ) (state : Weight rank) (shortPosition : Bool) :
    {vertices edges : ℕ} → (matching : PathMatching vertices edges) →
      FrontIntersectionWord rank state shortPosition matching →
        FrontSpecifiedWord rank state shortPosition matching
  | 0, 0, _, _ => PUnit.unit
  | 0, _ + 1, matching, _ => nomatch matching
  | 1, 0, _, full => full.1
  | 1, _ + 1, matching, _ => nomatch matching
  | _ + 2, 0, _, full => full.1
  | vertices + 2, edges + 1, Sum.inl matching,
      ⟨⟨parameter, tail⟩, hcontains⟩ => by
      change FrontContains rank matching tail.1.parameters at hcontains
      exact ⟨parameter,
        ⟨toSpecified rank
          (state + (parameterColumn shortPosition parameter).weight)
          (!shortPosition) matching ⟨tail.1, hcontains⟩,
          tail.2⟩⟩
  | vertices + 2, edges + 1, Sum.inr matching,
      ⟨⟨first, ⟨⟨second, secondTail⟩, firstValid⟩⟩, hcontains⟩ => by
      have hfirst : first = 0 := hcontains.1
      have hsecond : second = Fin.last rank := hcontains.2.1
      subst first
      subst second
      cases shortPosition with
      | false =>
          exact toSpecified rank (badPairEndState state false)
            false matching ⟨secondTail.1, hcontains.2.2⟩
      | true =>
          exact toSpecified rank (badPairEndState state true)
            true matching ⟨secondTail.1, hcontains.2.2⟩

theorem FrontSpecifiedWord.toFull_toSpecified
    (rank : ℕ) {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) {vertices edges : ℕ}
    (matching : PathMatching vertices edges)
    (specified : FrontSpecifiedWord rank state shortPosition matching) :
    FrontIntersectionWord.toSpecified rank state shortPosition matching
      (⟨specified.toFull rank hstate shortPosition matching,
          specified.toFull_contains rank hstate shortPosition matching⟩ :
        FrontIntersectionWord rank state shortPosition matching) = specified := by
  induction vertices using Nat.twoStepInduction generalizing edges state shortPosition with
  | zero =>
      cases edges with
      | zero => cases specified; rfl
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => rfl
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => rfl
      | succ edges =>
          cases matching with
          | inl matching =>
              apply Sigma.ext
              · rfl
              · apply heq_of_eq
                apply Subtype.ext
                exact ihSucc
                  (Column.endpointDominant_of_prefixes specified.2.2)
                  (!shortPosition) matching specified.2.1
          | inr matching =>
              cases shortPosition with
              | false =>
                  have htailState : Dominant (badPairEndState state false) := by
                    rw [badPairEndState_eq]
                    exact hstate
                  exact ih htailState false matching specified
              | true =>
                  have htailState : Dominant (badPairEndState state true) := by
                    rw [badPairEndState_eq]
                    exact hstate
                  exact ih htailState true matching specified

theorem FrontIntersectionWord.toSpecified_toFull
    (rank : ℕ) {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) {vertices edges : ℕ}
    (matching : PathMatching vertices edges)
    (full : FrontIntersectionWord rank state shortPosition matching) :
    (FrontIntersectionWord.toSpecified rank state shortPosition matching full).toFull
        rank hstate shortPosition matching = full.1 := by
  induction vertices using Nat.twoStepInduction generalizing edges state shortPosition with
  | zero =>
      cases edges with
      | zero => cases full.1; rfl
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => rfl
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => rfl
      | succ edges =>
          cases matching with
          | inl matching =>
              rcases full with ⟨⟨parameter, tail⟩, hcontains⟩
              change FrontContains rank matching tail.1.parameters at hcontains
              apply ParameterWordFrom.ext
              change parameter ::
                  (FrontSpecifiedWord.toFull rank
                    (Column.endpointDominant_of_prefixes tail.2)
                    (!shortPosition) matching
                    (FrontIntersectionWord.toSpecified rank
                      (state + (parameterColumn shortPosition parameter).weight)
                      (!shortPosition) matching ⟨tail.1, hcontains⟩)).parameters =
                parameter :: tail.1.parameters
              exact congrArg (List.cons parameter)
                (congrArg ParameterWordFrom.parameters
                  (ihSucc (Column.endpointDominant_of_prefixes tail.2)
                    (!shortPosition) matching ⟨tail.1, hcontains⟩))
          | inr matching =>
              rcases full with
                ⟨⟨first, ⟨⟨second, secondTail⟩, firstValid⟩⟩, hcontains⟩
              have hfirst : first = 0 := hcontains.1
              have hsecond : second = Fin.last rank := hcontains.2.1
              subst first
              subst second
              cases shortPosition with
              | false =>
                  have htailState : Dominant (badPairEndState state false) := by
                    rw [badPairEndState_eq]
                    exact hstate
                  have htail := ih htailState false matching
                    ⟨secondTail.1, hcontains.2.2⟩
                  apply ParameterWordFrom.ext
                  change (0 : Fin (rank + 1)) :: Fin.last rank ::
                      (FrontSpecifiedWord.toFull rank htailState false matching
                        (FrontIntersectionWord.toSpecified rank
                          (badPairEndState state false) false matching
                          ⟨secondTail.1, hcontains.2.2⟩)).parameters =
                    0 :: Fin.last rank :: secondTail.1.parameters
                  exact congrArg (fun tail =>
                    (0 : Fin (rank + 1)) :: Fin.last rank :: tail)
                    (congrArg ParameterWordFrom.parameters htail)
              | true =>
                  have htailState : Dominant (badPairEndState state true) := by
                    rw [badPairEndState_eq]
                    exact hstate
                  have htail := ih htailState true matching
                    ⟨secondTail.1, hcontains.2.2⟩
                  apply ParameterWordFrom.ext
                  change (0 : Fin (rank + 1)) :: Fin.last rank ::
                      (FrontSpecifiedWord.toFull rank htailState true matching
                        (FrontIntersectionWord.toSpecified rank
                          (badPairEndState state true) true matching
                          ⟨secondTail.1, hcontains.2.2⟩)).parameters =
                    0 :: Fin.last rank :: secondTail.1.parameters
                  exact congrArg (fun tail =>
                    (0 : Fin (rank + 1)) :: Fin.last rank :: tail)
                    (congrArg ParameterWordFrom.parameters htail)

/-- Full specified intersections and recursively fixed bad-pair data agree. -/
noncomputable def frontSpecifiedFullEquiv
    (rank : ℕ) {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) :
    FrontSpecifiedWord rank state shortPosition matching ≃
      FrontIntersectionWord rank state shortPosition matching where
  toFun specified :=
    ⟨specified.toFull rank hstate shortPosition matching,
      specified.toFull_contains rank hstate shortPosition matching⟩
  invFun := FrontIntersectionWord.toSpecified rank state shortPosition matching
  left_inv := FrontSpecifiedWord.toFull_toSpecified
    rank hstate shortPosition matching
  right_inv := by
    intro full
    apply Subtype.ext
    exact FrontIntersectionWord.toSpecified_toFull
      rank hstate shortPosition matching full

theorem frontPathMatching_zero_edges_empty
    {vertices : ℕ} (matching : PathMatching vertices 0) :
    ((frontPathMatchingActualEquiv vertices 0) matching).edgePositions = ∅ := by
  apply Finset.card_eq_zero.mp
  exact ((frontPathMatchingActualEquiv vertices 0) matching).card_eq

/-- `FrontContains` is exactly containment of the ordinary matching locations. -/
theorem frontContains_iff_matching_subset_badLocations
    (rank : ℕ) {state : Weight rank} {shortPosition : Bool}
    {vertices edges : ℕ} (matching : PathMatching vertices edges)
    (word : ParameterWordFrom rank state shortPosition vertices) :
    FrontContains rank matching word.parameters ↔
      ((frontPathMatchingActualEquiv vertices edges) matching).edgePositions ⊆
        badLocations rank word.parameters := by
  induction vertices using Nat.twoStepInduction generalizing edges state shortPosition with
  | zero =>
      cases edges with
      | zero =>
          rw [frontPathMatching_zero_edges_empty]
          cases matching
          simp [FrontContains]
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero =>
          rw [frontPathMatching_zero_edges_empty]
          cases matching
          simp [FrontContains]
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero =>
          rw [frontPathMatching_zero_edges_empty]
          cases matching
          simp [FrontContains]
      | succ edges =>
          cases matching with
          | inl matching =>
              obtain ⟨parameter, tail⟩ := word
              rw [frontPathMatching_inl_positions]
              change FrontContains rank matching tail.1.parameters ↔
                Finset.image (fun location => location + 1)
                    (((frontPathMatchingActualEquiv (vertices + 1) (edges + 1))
                      matching).edgePositions) ⊆
                  badLocations rank (parameter :: tail.1.parameters)
              constructor
              · intro hcontains location hlocation
                obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp hlocation
                rw [mem_badLocations_cons_succ]
                exact (ihSucc matching tail.1).mp hcontains hsource
              · intro hsubset
                apply (ihSucc matching tail.1).mpr
                intro source hsource
                rw [← mem_badLocations_cons_succ rank parameter
                  tail.1.parameters source]
                apply hsubset
                exact Finset.mem_image.mpr ⟨source, hsource, rfl⟩
          | inr matching =>
              rcases word with
                ⟨first, ⟨⟨second, secondTail⟩, firstValid⟩⟩
              rw [frontPathMatching_inr_positions]
              change (first = 0 ∧ second = Fin.last rank ∧
                  FrontContains rank matching secondTail.1.parameters) ↔
                insert 0
                    (Finset.image (fun location => location + 2)
                      (((frontPathMatchingActualEquiv vertices edges)
                        matching).edgePositions)) ⊆
                  badLocations rank (first :: second :: secondTail.1.parameters)
              constructor
              · rintro ⟨hfirst, hsecond, htail⟩ location hlocation
                rcases Finset.mem_insert.mp hlocation with rfl | hlocation
                · rw [zero_mem_badLocations_cons_cons_iff]
                  exact ⟨hfirst, hsecond⟩
                · obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp hlocation
                  rw [mem_badLocations_cons_cons_add_two]
                  exact (ih matching secondTail.1).mp htail hsource
              · intro hsubset
                have hzero := hsubset (Finset.mem_insert_self 0 _)
                have hfirstSecond :=
                  (zero_mem_badLocations_cons_cons_iff rank first second
                    secondTail.1.parameters).mp hzero
                refine ⟨hfirstSecond.1, hfirstSecond.2, ?_⟩
                apply (ih matching secondTail.1).mpr
                intro source hsource
                rw [← mem_badLocations_cons_cons_add_two rank first second
                  secondTail.1.parameters source]
                apply hsubset
                apply Finset.mem_insert_of_mem
                exact Finset.mem_image.mpr ⟨source, hsource, rfl⟩

/-- Recursive full intersections and ordinary matching-event intersections agree. -/
noncomputable def frontIntersectionActualEquiv
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) :
    FrontIntersectionWord rank (0 : Weight rank) true matching ≃
      MatchingIntersection rank vertices edges
        ((frontPathMatchingActualEquiv vertices edges) matching) where
  toFun full := by
    let list := full.1.toBallotParameterList
    refine ⟨list, ?_⟩
    have hsubset :=
      (frontContains_iff_matching_subset_badLocations rank matching full.1).mp full.2
    simpa [list, ParameterWordFrom.toBallotParameterList] using hsubset
  invFun intersection := by
    let word := intersection.1.toParameterWord vertices
    refine ⟨word, ?_⟩
    apply (frontContains_iff_matching_subset_badLocations rank matching word).mpr
    have hparameters :=
      BallotParameterListFrom.toParameterWord_parameters intersection.1
    simpa [word, hparameters] using intersection.2
  left_inv full := by
    apply Subtype.ext
    exact ParameterWordFrom.toBallotParameterList_toParameterWord full.1
  right_inv intersection := by
    apply Subtype.ext
    apply BallotParameterListFrom.ext
    exact BallotParameterListFrom.toParameterWord_parameters intersection.1

/--
Every intersection indexed by a size-`edges` matching contracts bijectively to
an unrestricted parameter list with `vertices - 2*edges` columns.
-/
noncomputable def matchingIntersectionContractionEquiv
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) :
    MatchingIntersection rank vertices edges
        ((frontPathMatchingActualEquiv vertices edges) matching) ≃
      UnrestrictedParameterList rank matching.freeVertices :=
  (frontIntersectionActualEquiv rank matching).symm |>.trans
    ((frontSpecifiedFullEquiv rank (dominant_zero rank) true matching).symm |>.trans
      ((frontSpecifiedContractionEquiv rank 0 true matching).trans
        (parameterWordBallotListEquiv rank 0 true matching.freeVertices)))

theorem matchingIntersection_card
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) :
    Fintype.card
        (MatchingIntersection rank vertices edges
          ((frontPathMatchingActualEquiv vertices edges) matching)) =
      unrestrictedCount rank (vertices - 2 * edges) := by
  rw [← matching.freeVertices_eq]
  rw [← unrestrictedParameterList_card]
  exact Fintype.card_congr (matchingIntersectionContractionEquiv rank matching)

theorem matchingIntersection_card_actual
    (rank : ℕ) {vertices edges : ℕ}
    (matching : ActualPathMatching vertices edges) :
    Fintype.card (MatchingIntersection rank vertices edges matching) =
      unrestrictedCount rank (vertices - 2 * edges) := by
  let canonical :=
    (frontPathMatchingActualEquiv vertices edges).symm matching
  have hcanonical :
      (frontPathMatchingActualEquiv vertices edges) canonical = matching :=
    (frontPathMatchingActualEquiv vertices edges).apply_symm_apply matching
  simpa [canonical, hcanonical] using matchingIntersection_card rank canonical

/-- Free parameters retained by the recursive contraction. -/
def FrontSpecifiedWord.freeParameters
    {rank : ℕ} {state : Weight rank} {shortPosition : Bool} :
    {vertices edges : ℕ} → (matching : PathMatching vertices edges) →
      FrontSpecifiedWord rank state shortPosition matching →
        List (Fin (rank + 1))
  | 0, 0, _, _ => []
  | 0, _ + 1, matching, _ => nomatch matching
  | 1, 0, _, specified => specified.parameters
  | 1, _ + 1, matching, _ => nomatch matching
  | _ + 2, 0, _, specified => specified.parameters
  | _ + 2, _ + 1, Sum.inl matching, specified =>
      specified.1 :: specified.2.1.freeParameters matching
  | _ + 2, _ + 1, Sum.inr matching, specified =>
      specified.freeParameters matching

/-- The contraction equivalence returns exactly `freeParameters`. -/
theorem FrontSpecifiedWord.contraction_parameters
    (rank : ℕ) (state : Weight rank) (shortPosition : Bool)
    {vertices edges : ℕ} (matching : PathMatching vertices edges)
    (specified : FrontSpecifiedWord rank state shortPosition matching) :
    ((frontSpecifiedContractionEquiv rank state shortPosition matching)
        specified).parameters = specified.freeParameters matching := by
  induction vertices using Nat.twoStepInduction generalizing edges state shortPosition with
  | zero =>
      cases edges with
      | zero => cases specified; rfl
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => rfl
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => rfl
      | succ edges =>
          cases matching with
          | inl matching =>
              change specified.1 ::
                  (((frontSpecifiedContractionEquiv rank
                    (state + (parameterColumn shortPosition specified.1).weight)
                    (!shortPosition) matching) specified.2.1).parameters) =
                specified.1 :: specified.2.1.freeParameters matching
              exact congrArg (List.cons specified.1)
                (ihSucc _ _ matching specified.2.1)
          | inr matching =>
              let contracted :=
                (frontSpecifiedContractionEquiv rank
                  (badPairEndState state shortPosition) shortPosition matching) specified
              calc
                (((frontSpecifiedContractionEquiv rank
                    (badPairEndState state shortPosition) shortPosition matching).trans
                      (parameterWordStateEquiv
                        (badPairEndState_eq state shortPosition)
                        shortPosition matching.freeVertices)) specified).parameters =
                    contracted.parameters :=
                      parameterWordStateEquiv_parameters
                        (badPairEndState_eq state shortPosition)
                        shortPosition matching.freeVertices contracted
                _ = specified.freeParameters matching :=
                      ih (badPairEndState state shortPosition)
                        shortPosition matching specified

theorem FrontSpecifiedWord.toFull_weight_eq_free
    (rank : ℕ) {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) {vertices edges : ℕ}
    (matching : PathMatching vertices edges)
    (specified : FrontSpecifiedWord rank state shortPosition matching) :
    parameterListWeight rank shortPosition
        (specified.toFull rank hstate shortPosition matching).parameters =
      parameterListWeight rank shortPosition
        (specified.freeParameters matching) := by
  induction vertices using Nat.twoStepInduction generalizing edges state shortPosition with
  | zero =>
      cases edges with
      | zero => cases matching; cases specified; rfl
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => rfl
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => rfl
      | succ edges =>
          cases matching with
          | inl matching =>
              simp only [FrontSpecifiedWord.toFull, ParameterWordFrom.parameters,
                FrontSpecifiedWord.freeParameters, parameterListWeight]
              rw [ihSucc (Column.endpointDominant_of_prefixes specified.2.2)
                (!shortPosition) matching specified.2.1]
          | inr matching =>
              cases shortPosition with
              | false =>
                  have htailState : Dominant (badPairEndState state false) := by
                    rw [badPairEndState_eq]
                    exact hstate
                  simp only [FrontSpecifiedWord.toFull, ParameterWordFrom.parameters,
                    FrontSpecifiedWord.freeParameters, parameterListWeight]
                  simp only [Bool.not_false, Bool.not_true] at *
                  calc
                    (parameterColumn false 0).weight +
                        ((parameterColumn true (Fin.last rank)).weight +
                          parameterListWeight rank false
                            (specified.toFull rank htailState false matching).parameters) =
                      parameterListWeight rank false
                        (specified.toFull rank htailState false matching).parameters := by
                          rw [← add_assoc]
                          simp [parameterColumn, parameterComplement, Column.weight,
                            evenBadPair_neutral]
                    _ = parameterListWeight rank false
                          (specified.freeParameters matching) :=
                      ih htailState false matching specified
              | true =>
                  have htailState : Dominant (badPairEndState state true) := by
                    rw [badPairEndState_eq]
                    exact hstate
                  simp only [FrontSpecifiedWord.toFull, ParameterWordFrom.parameters,
                    FrontSpecifiedWord.freeParameters, parameterListWeight]
                  simp only [Bool.not_false, Bool.not_true] at *
                  calc
                    (parameterColumn true 0).weight +
                        ((parameterColumn false (Fin.last rank)).weight +
                          parameterListWeight rank true
                            (specified.toFull rank htailState true matching).parameters) =
                      parameterListWeight rank true
                        (specified.toFull rank htailState true matching).parameters := by
                          rw [← add_assoc]
                          simp [parameterColumn, parameterComplement, Column.weight,
                            oddBadPair_neutral]
                    _ = parameterListWeight rank true
                          (specified.freeParameters matching) :=
                      ih htailState true matching specified

theorem matchingIntersectionContraction_preserves_weight
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges)
    (intersection : MatchingIntersection rank vertices edges
      ((frontPathMatchingActualEquiv vertices edges) matching)) :
    parameterListWeight rank true intersection.1.parameters =
      parameterListWeight rank true
        ((matchingIntersectionContractionEquiv rank matching) intersection).parameters := by
  let full := (frontIntersectionActualEquiv rank matching).symm intersection
  let specified := (frontSpecifiedFullEquiv rank (dominant_zero rank) true matching).symm full
  have hfull : specified.toFull rank (dominant_zero rank) true matching = full.1 :=
    (frontSpecifiedFullEquiv rank (dominant_zero rank) true matching).apply_symm_apply full |>
      congrArg Subtype.val
  have hintersection : full.1.toBallotParameterList = intersection.1 :=
    (frontIntersectionActualEquiv rank matching).apply_symm_apply intersection |>
      congrArg Subtype.val
  rw [← hintersection]
  change parameterListWeight rank true full.1.parameters = _
  rw [← hfull]
  rw [specified.toFull_weight_eq_free rank (dominant_zero rank) true matching]
  rw [← specified.contraction_parameters rank 0 true matching]
  rfl

end FibonacciRibbonKernel
