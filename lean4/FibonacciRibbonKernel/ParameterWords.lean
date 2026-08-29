import FibonacciRibbonKernel.BadPairContraction

namespace FibonacciRibbonKernel

/-- Toggle the short/tall parity once for each preceding column. -/
def toggleN (shortPosition : Bool) : ℕ → Bool
  | 0 => shortPosition
  | count + 1 => toggleN (!shortPosition) count

@[simp] theorem toggleN_zero (shortPosition : Bool) :
    toggleN shortPosition 0 = shortPosition := rfl

@[simp] theorem toggleN_succ (shortPosition : Bool) (count : ℕ) :
    toggleN shortPosition (count + 1) = toggleN (!shortPosition) count := rfl

@[simp] theorem toggleN_two (shortPosition : Bool) :
    toggleN shortPosition 2 = shortPosition := by
  cases shortPosition <;> rfl

/-- Encode a parameter list as the literal alternating column list. -/
def encodeColumns (rank : ℕ) :
    Bool → List (Fin (rank + 1)) → List (Column rank)
  | _, [] => []
  | shortPosition, parameter :: parameters =>
      parameterColumn shortPosition parameter ::
        encodeColumns rank (!shortPosition) parameters

theorem encodeColumns_append
    (rank : ℕ) (shortPosition : Bool)
    (left right : List (Fin (rank + 1))) :
    encodeColumns rank shortPosition (left ++ right) =
      encodeColumns rank shortPosition left ++
        encodeColumns rank (toggleN shortPosition left.length) right := by
  induction left generalizing shortPosition with
  | nil => rfl
  | cons parameter parameters ih =>
      simp only [List.cons_append, encodeColumns, List.length_cons]
      rw [ih]
      rfl

theorem encodeColumns_bad_pair
    (rank : ℕ) (shortPosition : Bool)
    (before after : List (Fin (rank + 1))) :
    encodeColumns rank shortPosition
        (before ++ (0 :: Fin.last rank :: after)) =
      encodeColumns rank shortPosition before ++
        (badPairBlock rank (toggleN shortPosition before.length) ++
          encodeColumns rank (toggleN shortPosition before.length) after) := by
  rw [encodeColumns_append]
  simp [encodeColumns, badPairBlock]

theorem dominant_zero (rank : ℕ) : Dominant (0 : Weight rank) := by
  intro i
  simp

/-- Parameter-level single-pair deletion preserves ballot admissibility. -/
theorem encodeColumns_bad_pair_ballot_iff
    (rank : ℕ) (shortPosition : Bool)
    (before after : List (Fin (rank + 1))) :
    ColumnsBallotFrom 0
        (encodeColumns rank shortPosition
          (before ++ (0 :: Fin.last rank :: after))) ↔
      ColumnsBallotFrom 0
        (encodeColumns rank shortPosition (before ++ after)) := by
  rw [encodeColumns_bad_pair, encodeColumns_append]
  exact badPairBlock_insert_iff
    (toggleN shortPosition before.length) (dominant_zero rank)

/-- State-relative form used for simultaneous contraction. -/
theorem encodeColumns_bad_pair_ballot_iff_from
    (rank : ℕ) (shortPosition : Bool)
    {state : Weight rank} (hstate : Dominant state)
    (before after : List (Fin (rank + 1))) :
    ColumnsBallotFrom state
        (encodeColumns rank shortPosition
          (before ++ (0 :: Fin.last rank :: after))) ↔
      ColumnsBallotFrom state
        (encodeColumns rank shortPosition (before ++ after)) := by
  rw [encodeColumns_bad_pair, encodeColumns_append]
  exact badPairBlock_insert_iff
    (toggleN shortPosition before.length) hstate

/-- Fixed left/right lengths around one specified adjacency. -/
structure SplitParameters (rank leftLength rightLength : ℕ) where
  before : List (Fin (rank + 1))
  after : List (Fin (rank + 1))
  before_length : before.length = leftLength
  after_length : after.length = rightLength

def SplitParameters.withBadPair
    {rank leftLength rightLength : ℕ}
    (split : SplitParameters rank leftLength rightLength) :
    List (Fin (rank + 1)) :=
  split.before ++ (0 :: Fin.last rank :: split.after)

def SplitParameters.contracted
    {rank leftLength rightLength : ℕ}
    (split : SplitParameters rank leftLength rightLength) :
    List (Fin (rank + 1)) :=
  split.before ++ split.after

theorem SplitParameters.withBadPair_length
    {rank leftLength rightLength : ℕ}
    (split : SplitParameters rank leftLength rightLength) :
    split.withBadPair.length = leftLength + rightLength + 2 := by
  simp [SplitParameters.withBadPair, split.before_length, split.after_length]
  omega

theorem SplitParameters.contracted_length
    {rank leftLength rightLength : ℕ}
    (split : SplitParameters rank leftLength rightLength) :
    split.contracted.length = leftLength + rightLength := by
  simp [SplitParameters.contracted, split.before_length, split.after_length]

/-- Unrestricted ballot objects carrying a specified bad adjacency. -/
def SpecifiedBadPairObject (rank leftLength rightLength : ℕ) :=
  {split : SplitParameters rank leftLength rightLength //
    ColumnsBallotFrom 0
      (encodeColumns rank true split.withBadPair)}

/-- Contracted unrestricted ballot objects with the same outside parameters. -/
def ContractedPairObject (rank leftLength rightLength : ℕ) :=
  {split : SplitParameters rank leftLength rightLength //
    ColumnsBallotFrom 0
      (encodeColumns rank true split.contracted)}

/--
Literal deletion/insertion bijection for a specified bad adjacency.  The
carrier retains both outside parameter lists, so the inverse inserts exactly
`(0,last)` at the original location.
-/
def specifiedBadPairDeletionEquiv
    (rank leftLength rightLength : ℕ) :
    SpecifiedBadPairObject rank leftLength rightLength ≃
      ContractedPairObject rank leftLength rightLength where
  toFun object :=
    ⟨object.1,
      (encodeColumns_bad_pair_ballot_iff rank true
        object.1.before object.1.after).mp object.2⟩
  invFun object :=
    ⟨object.1,
      (encodeColumns_bad_pair_ballot_iff rank true
        object.1.before object.1.after).mpr object.2⟩
  left_inv object := by
    apply Subtype.ext
    rfl
  right_inv object := by
    apply Subtype.ext
    rfl

/-- Insert one forbidden pair between each two consecutive outside segments. -/
def insertBadPairs (rank : ℕ) :
    List (List (Fin (rank + 1))) → List (Fin (rank + 1))
  | [] => []
  | segment :: [] => segment
  | segment :: nextSegment :: remaining =>
      segment ++ (0 :: Fin.last rank ::
        insertBadPairs rank (nextSegment :: remaining))

/-- Delete all specified pairs, retaining all outside parameter segments. -/
def contractBadPairs {rank : ℕ}
    (segments : List (List (Fin (rank + 1)))) : List (Fin (rank + 1)) :=
  segments.flatten

/-- Number of pair slots represented by a nonempty list of outside segments. -/
def representedPairCount {rank : ℕ}
    (segments : List (List (Fin (rank + 1)))) : ℕ :=
  segments.length - 1

theorem insertBadPairs_length (rank : ℕ)
    (segments : List (List (Fin (rank + 1)))) :
    (insertBadPairs rank segments).length =
      (contractBadPairs segments).length + 2 * representedPairCount segments := by
  induction segments with
  | nil => simp [insertBadPairs, contractBadPairs, representedPairCount]
  | cons segment segments ih =>
      cases segments with
      | nil => simp [insertBadPairs, contractBadPairs, representedPairCount]
      | cons nextSegment remaining =>
          simp only [insertBadPairs, contractBadPairs, List.flatten_cons,
            List.length_append, List.length_cons]
          rw [ih]
          simp [contractBadPairs, representedPairCount]
          omega

/--
Simultaneous deletion of all inserted pairwise-disjoint bad adjacencies
preserves ballot admissibility.  The segments are the parameters outside the
specified pairs; adjacent specified pairs are represented by an empty segment.
-/
theorem encodeColumns_insertBadPairs_ballot_iff_from
    (rank : ℕ) (shortPosition : Bool)
    {state : Weight rank} (hstate : Dominant state)
    (segments : List (List (Fin (rank + 1)))) :
    ColumnsBallotFrom state
        (encodeColumns rank shortPosition (insertBadPairs rank segments)) ↔
      ColumnsBallotFrom state
        (encodeColumns rank shortPosition (contractBadPairs segments)) := by
  induction segments generalizing state shortPosition with
  | nil => rfl
  | cons segment segments ih =>
      cases segments with
      | nil => simp [insertBadPairs, contractBadPairs]
      | cons nextSegment remaining =>
          let tailSegments := nextSegment :: remaining
          let nextPosition := toggleN shortPosition segment.length
          have hinsert :
              encodeColumns rank shortPosition
                  (insertBadPairs rank (segment :: tailSegments)) =
                encodeColumns rank shortPosition segment ++
                  (badPairBlock rank nextPosition ++
                    encodeColumns rank nextPosition
                      (insertBadPairs rank tailSegments)) := by
            simp [tailSegments, insertBadPairs]
            rw [encodeColumns_append]
            simp [encodeColumns, badPairBlock, nextPosition]
          have hcontract :
              encodeColumns rank shortPosition
                  (contractBadPairs (segment :: tailSegments)) =
                encodeColumns rank shortPosition segment ++
                  encodeColumns rank nextPosition
                    (contractBadPairs tailSegments) := by
            simp only [contractBadPairs, List.flatten_cons]
            rw [encodeColumns_append]
          rw [hinsert, hcontract]
          constructor
          · intro h
            have hsplit :=
              (columnsBallotFrom_append_iff state
                (encodeColumns rank shortPosition segment)
                (badPairBlock rank nextPosition ++
                  encodeColumns rank nextPosition
                    (insertBadPairs rank tailSegments))).mp h
            have hnext := dominant_runColumns_of_ballot hstate hsplit.1
            have htailInserted :=
              ((badPairBlock_neutral rank nextPosition).front_iff hnext).mp hsplit.2
            have htailContracted :=
              (ih nextPosition hnext).mp htailInserted
            exact (columnsBallotFrom_append_iff state
              (encodeColumns rank shortPosition segment)
              (encodeColumns rank nextPosition
                (contractBadPairs tailSegments))).mpr
                ⟨hsplit.1, htailContracted⟩
          · intro h
            have hsplit :=
              (columnsBallotFrom_append_iff state
                (encodeColumns rank shortPosition segment)
                (encodeColumns rank nextPosition
                  (contractBadPairs tailSegments))).mp h
            have hnext := dominant_runColumns_of_ballot hstate hsplit.1
            have htailInserted :=
              (ih nextPosition hnext).mpr hsplit.2
            have hwithBlock :=
              ((badPairBlock_neutral rank nextPosition).front_iff hnext).mpr
                htailInserted
            exact (columnsBallotFrom_append_iff state
              (encodeColumns rank shortPosition segment)
              (badPairBlock rank nextPosition ++
                encodeColumns rank nextPosition
                  (insertBadPairs rank tailSegments))).mpr
                ⟨hsplit.1, hwithBlock⟩

theorem encodeColumns_insertBadPairs_ballot_iff
    (rank : ℕ) (segments : List (List (Fin (rank + 1)))) :
    ColumnsBallotFrom 0
        (encodeColumns rank true (insertBadPairs rank segments)) ↔
      ColumnsBallotFrom 0
        (encodeColumns rank true (contractBadPairs segments)) :=
  encodeColumns_insertBadPairs_ballot_iff_from rank true
    (dominant_zero rank) segments

/-- Outside segments together with their prescribed lengths. -/
structure SegmentedParameters (rank : ℕ) (segmentLengths : List ℕ) where
  segments : List (List (Fin (rank + 1)))
  lengths : segments.map List.length = segmentLengths

def SpecifiedBadPairsObject (rank : ℕ) (segmentLengths : List ℕ) :=
  {data : SegmentedParameters rank segmentLengths //
    ColumnsBallotFrom 0
      (encodeColumns rank true (insertBadPairs rank data.segments))}

def ContractedPairsObject (rank : ℕ) (segmentLengths : List ℕ) :=
  {data : SegmentedParameters rank segmentLengths //
    ColumnsBallotFrom 0
      (encodeColumns rank true (contractBadPairs data.segments))}

/-- Explicit simultaneous deletion/insertion bijection for disjoint bad pairs. -/
def specifiedBadPairsDeletionEquiv (rank : ℕ) (segmentLengths : List ℕ) :
    SpecifiedBadPairsObject rank segmentLengths ≃
      ContractedPairsObject rank segmentLengths where
  toFun object :=
    ⟨object.1,
      (encodeColumns_insertBadPairs_ballot_iff rank object.1.segments).mp
        object.2⟩
  invFun object :=
    ⟨object.1,
      (encodeColumns_insertBadPairs_ballot_iff rank object.1.segments).mpr
        object.2⟩
  left_inv object := by
    apply Subtype.ext
    rfl
  right_inv object := by
    apply Subtype.ext
    rfl

end FibonacciRibbonKernel
