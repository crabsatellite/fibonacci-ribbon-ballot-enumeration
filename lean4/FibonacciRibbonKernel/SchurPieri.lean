import FibonacciRibbonKernel.EndpointEnumeration
import Mathlib.Data.Vector.Basic

namespace FibonacciRibbonKernel

open scoped Classical

/-- A normalized dominant partition with `rank + 1` rows and last part zero. -/
def NormalizedPartition (rank : ℕ) :=
  {rows : Fin (rank + 1) → ℕ //
    (∀ row : Fin rank, rows row.succ ≤ rows row.castSucc) ∧
      rows (Fin.last rank) = 0}

/-- Size of a normalized partition. -/
def NormalizedPartition.size
    {rank : ℕ} (partition : NormalizedPartition rank) : ℕ :=
  ∑ row, partition.1 row

/-- Difference weight represented by a normalized partition. -/
def NormalizedPartition.weight
    {rank : ℕ} (partition : NormalizedPartition rank) : Weight rank :=
  fun row => (partition.1 row.castSucc : ℤ) - (partition.1 row.succ : ℤ)

theorem NormalizedPartition.weight_dominant
    {rank : ℕ} (partition : NormalizedPartition rank) :
    Dominant partition.weight := by
  intro row
  have hrow := partition.2.1 row
  simp only [NormalizedPartition.weight]
  omega

/-- One Pieri factor acts on the difference weight. -/
def pieriStepState {rank : ℕ} (state : Weight rank)
    (shortStep : Bool) (parameter : Fin (rank + 1)) : Weight rank :=
  if shortStep then plusState state parameter
  else minusState state (parameterComplement parameter)

/-- Endpoint-valid Pieri branching along a literal step/parameter word. -/
def PieriBallot {rank : ℕ} :
    Weight rank → List Bool → List (Fin (rank + 1)) → Prop
  | _, [], [] => True
  | state, true :: steps, parameter :: parameters =>
      PlusValid state parameter ∧
        PieriBallot (plusState state parameter) steps parameters
  | state, false :: steps, parameter :: parameters =>
      MinusValid state (parameterComplement parameter) ∧
        PieriBallot (minusState state (parameterComplement parameter)) steps parameters
  | _, _, _ => False

/-- Final difference weight of a Pieri step/parameter word. -/
def pieriRun {rank : ℕ} :
    Weight rank → List Bool → List (Fin (rank + 1)) → Weight rank
  | state, [], [] => state
  | state, step :: steps, parameter :: parameters =>
      pieriRun (pieriStepState state step parameter) steps parameters
  | state, _, _ => state

/-- Finite carrier counted by a Schur-basis Pieri coefficient. -/
def PieriPath (rank : ℕ) (state : Weight rank)
    (steps : List Bool) (target : Weight rank) :=
  {parameters : List.Vector (Fin (rank + 1)) steps.length //
    PieriBallot state steps parameters.toList ∧
      pieriRun state steps parameters.toList = target}

noncomputable instance pieriPathFintype
    (rank : ℕ) (state : Weight rank) (steps : List Bool) (target : Weight rank) :
    Fintype (PieriPath rank state steps target) := by
  unfold PieriPath
  infer_instance

/-- A canonical interleaving of `r` factors `p₁` and `s` factors `e_rank`. -/
def pieriSteps : ℕ → ℕ → List Bool
  | 0, dualSteps => List.replicate dualSteps false
  | definingSteps + 1, 0 => List.replicate (definingSteps + 1) true
  | definingSteps + 1, dualSteps + 1 =>
      true :: false :: pieriSteps definingSteps dualSteps

set_option linter.unnecessarySeqFocus false in
@[simp] theorem pieriSteps_length (definingSteps dualSteps : ℕ) :
    (pieriSteps definingSteps dualSteps).length = definingSteps + dualSteps := by
  induction definingSteps, dualSteps using pieriSteps.induct <;>
    simp_all [pieriSteps] <;> omega

theorem alternatingSteps_eq_pieriSteps (columns : ℕ) :
    alternatingSteps true columns =
      pieriSteps ((columns + 1) / 2) (columns / 2) := by
  induction columns using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more columns ih₀ ih₁ =>
      rw [show (columns + 2 + 1) / 2 = (columns + 1) / 2 + 1 by omega]
      rw [show (columns + 2) / 2 = columns / 2 + 1 by omega]
      simp only [alternatingSteps, pieriSteps]
      exact congrArg (true :: false :: ·) ih₀

theorem pieriRun_alternating_eq_parameterListWeight
    (rank : ℕ) (state : Weight rank) (shortPosition : Bool)
    (parameters : List (Fin (rank + 1))) :
    pieriRun state (alternatingSteps shortPosition parameters.length) parameters =
      state + parameterListWeight rank shortPosition parameters := by
  induction parameters generalizing state shortPosition with
  | nil => simp [pieriRun, alternatingSteps, parameterListWeight]
  | cons parameter parameters ih =>
      cases shortPosition <;>
        simp only [List.length_cons, alternatingSteps, parameterListWeight,
          pieriRun, pieriStepState, Bool.false_eq_true, ↓reduceIte]
      · rw [ih]
        simp [parameterColumn, Column.weight, minusState,
          tallWeight_eq_neg_letterWeight, sub_eq_add_neg, add_assoc]
      · rw [ih]
        simp [parameterColumn, Column.weight, plusState, add_assoc]

theorem columnsBallotFrom_encode_iff_pieriBallot
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) (parameters : List (Fin (rank + 1))) :
    ColumnsBallotFrom state (encodeColumns rank shortPosition parameters) ↔
      PieriBallot state (alternatingSteps shortPosition parameters.length) parameters := by
  induction parameters generalizing state shortPosition with
  | nil => simp [encodeColumns, ColumnsBallotFrom, alternatingSteps, PieriBallot]
  | cons parameter parameters ih =>
      cases shortPosition with
      | true =>
          simp only [encodeColumns, ColumnsBallotFrom, List.length_cons,
            alternatingSteps, PieriBallot]
          have hcriterion := column_prefixesDominant_iff_endpoint
            (state := state) (Column.singleton parameter) hstate
          have hhead : (Column.singleton parameter).prefixesDominant state ↔
              PlusValid state parameter := by
            change (Column.singleton parameter).prefixesDominant state ↔
              Dominant (plusState state parameter)
            simpa [Column.weight, plusState] using hcriterion
          constructor
          · rintro ⟨hcolumn, htail⟩
            have hvalid := hhead.mp hcolumn
            exact ⟨hvalid, (ih hvalid false).mp htail⟩
          · rintro ⟨hvalid, htail⟩
            exact ⟨hhead.mpr hvalid, (ih hvalid false).mpr htail⟩
      | false =>
          simp only [encodeColumns, ColumnsBallotFrom, List.length_cons,
            alternatingSteps, PieriBallot]
          let omitted := parameterComplement parameter
          have hcriterion := column_prefixesDominant_iff_endpoint
            (state := state) (Column.tall omitted) hstate
          have hstateEq : state + tallWeight rank omitted =
              minusState state omitted := by
            simp [minusState, tallWeight_eq_neg_letterWeight, sub_eq_add_neg]
          have hcolumnStateEq :
              state + (parameterColumn false parameter).weight =
                minusState state omitted := by
            simp [parameterColumn, Column.weight, omitted, minusState,
              tallWeight_eq_neg_letterWeight, sub_eq_add_neg]
          have hhead : (Column.tall omitted).prefixesDominant state ↔
              MinusValid state omitted := by
            change (Column.tall omitted).prefixesDominant state ↔
              Dominant (minusState state omitted)
            rw [← hstateEq]
            exact hcriterion
          constructor
          · rintro ⟨hcolumn, htail⟩
            have hvalid := hhead.mp hcolumn
            have htail' : ColumnsBallotFrom (minusState state omitted)
                (encodeColumns rank true parameters) := by
              rw [← hcolumnStateEq]
              exact htail
            exact ⟨hvalid, (ih hvalid true).mp htail'⟩
          · rintro ⟨hvalid, htail⟩
            refine ⟨hhead.mpr hvalid, ?_⟩
            have := (ih hvalid true).mpr htail
            rw [hcolumnStateEq]
            exact this

theorem columnsBallotFrom_encode_iff_pieriBallot_of_length
    {rank columns : ℕ} {state : Weight rank} (hstate : Dominant state)
    (shortPosition : Bool) (parameters : List (Fin (rank + 1)))
    (hlength : parameters.length = columns) :
    ColumnsBallotFrom state (encodeColumns rank shortPosition parameters) ↔
      PieriBallot state (alternatingSteps shortPosition columns) parameters := by
  have h := columnsBallotFrom_encode_iff_pieriBallot
    hstate shortPosition parameters
  simpa only [hlength] using h

theorem pieriRun_alternating_eq_parameterListWeight_of_length
    {rank columns : ℕ} (state : Weight rank) (shortPosition : Bool)
    (parameters : List (Fin (rank + 1)))
    (hlength : parameters.length = columns) :
    pieriRun state (alternatingSteps shortPosition columns) parameters =
      state + parameterListWeight rank shortPosition parameters := by
  simpa only [hlength] using pieriRun_alternating_eq_parameterListWeight
    rank state shortPosition parameters

/-- The literal endpoint objects are the Pieri branching paths in alternating order. -/
noncomputable def unrestrictedEndpointPieriEquiv
    (rank columns : ℕ) (target : Weight rank) :
    UnrestrictedEndpointObject rank columns target ≃
      PieriPath rank 0 (alternatingSteps true columns) target where
  toFun word := by
    let parameters : List.Vector (Fin (rank + 1))
        (alternatingSteps true columns).length :=
      ⟨word.1.parameters, by
        rw [alternatingSteps_length]
        exact word.1.length_eq⟩
    refine ⟨parameters, ?_, ?_⟩
    · exact (columnsBallotFrom_encode_iff_pieriBallot_of_length
        (dominant_zero rank) true word.1.parameters word.1.length_eq).mp
          word.1.ballot
    · have hrun := pieriRun_alternating_eq_parameterListWeight_of_length
        (0 : Weight rank) true word.1.parameters word.1.length_eq
      rw [word.2] at hrun
      simpa [parameters] using hrun
  invFun path := by
    have hlength : path.1.toList.length = columns :=
      path.1.toList_length.trans (alternatingSteps_length true columns)
    let parameterList : UnrestrictedParameterList rank columns :=
      { parameters := path.1.toList
        length_eq := hlength
        ballot := (columnsBallotFrom_encode_iff_pieriBallot_of_length
          (dominant_zero rank) true path.1.toList hlength).mpr path.2.1 }
    refine ⟨parameterList, ?_⟩
    have hrun := pieriRun_alternating_eq_parameterListWeight_of_length
      (0 : Weight rank) true path.1.toList hlength
    calc
      parameterListWeight rank true parameterList.parameters =
          pieriRun 0 (alternatingSteps true columns) path.1.toList := by
        simpa [parameterList] using hrun.symm
      _ = target := path.2.2
  left_inv word := by
    apply Subtype.ext
    apply BallotParameterListFrom.ext
    rfl
  right_inv path := by
    apply Subtype.ext
    apply List.Vector.eq
    rfl

/-- Schur-basis coefficient obtained by the literal `p₁`/`e_rank` Pieri rule. -/
noncomputable def schurPieriCoefficient
    (rank definingSteps dualSteps : ℕ)
    (partition : NormalizedPartition rank) : ℕ :=
  Fintype.card
    (PieriPath rank 0 (pieriSteps definingSteps dualSteps) partition.weight)

theorem mixedEndpointMultiplicity_eq_schurPieriCoefficient
    (rank columns : ℕ) (partition : NormalizedPartition rank) :
    mixedEndpointMultiplicity rank columns partition.weight =
      schurPieriCoefficient rank ((columns + 1) / 2) (columns / 2) partition := by
  unfold mixedEndpointMultiplicity schurPieriCoefficient
  calc
    Fintype.card (UnrestrictedEndpointObject rank columns partition.weight) =
        Fintype.card
          (PieriPath rank 0 (alternatingSteps true columns) partition.weight) :=
      Fintype.card_congr
        (unrestrictedEndpointPieriEquiv rank columns partition.weight)
    _ = Fintype.card
          (PieriPath rank 0
            (pieriSteps ((columns + 1) / 2) (columns / 2))
            partition.weight) := by
      rw [alternatingSteps_eq_pieriSteps]

/-- Polynomial degree of a `p₁`/`e_rank` Pieri word. -/
def pieriDegree (rank : ℕ) (steps : List Bool) : ℕ :=
  steps.count true + rank * steps.count false

/-- Row increment of one Pieri factor. -/
def pieriRowIncrement (rank : ℕ) (step : Bool)
    (parameter row : Fin (rank + 1)) : ℕ :=
  if step then if row = parameter then 1 else 0
  else if row = parameterComplement parameter then 0 else 1

/-- Polynomial row lengths accumulated by a Pieri path. -/
def pieriRowCounts (rank : ℕ) :
    List Bool → List (Fin (rank + 1)) → Fin (rank + 1) → ℕ
  | [], [], _ => 0
  | step :: steps, parameter :: parameters, row =>
      pieriRowIncrement rank step parameter row +
        pieriRowCounts rank steps parameters row
  | _, _, _ => 0

/-- Difference weight of a row-count vector. -/
def rowCountsWeight {rank : ℕ}
    (rows : Fin (rank + 1) → ℕ) : Weight rank :=
  fun row => (rows row.castSucc : ℤ) - (rows row.succ : ℤ)

/-- Weight increment of a Pieri word. -/
def pieriWordWeight (rank : ℕ) :
    List Bool → List (Fin (rank + 1)) → Weight rank
  | [], [] => 0
  | true :: steps, parameter :: parameters =>
      letterWeight rank parameter + pieriWordWeight rank steps parameters
  | false :: steps, parameter :: parameters =>
      tallWeight rank (parameterComplement parameter) +
        pieriWordWeight rank steps parameters
  | _, _ => 0

theorem rowCountsWeight_pieriRowIncrement_true
    (rank : ℕ) (parameter : Fin (rank + 1)) :
    rowCountsWeight (pieriRowIncrement rank true parameter) =
      letterWeight rank parameter := by
  funext row
  simp only [rowCountsWeight, pieriRowIncrement, ↓reduceIte, letterWeight]
  split_ifs <;> omega

theorem rowCountsWeight_pieriRowIncrement_false
    (rank : ℕ) (parameter : Fin (rank + 1)) :
    rowCountsWeight (pieriRowIncrement rank false parameter) =
      tallWeight rank (parameterComplement parameter) := by
  rw [tallWeight_eq_neg_letterWeight]
  funext row
  simp only [rowCountsWeight, pieriRowIncrement, Bool.false_eq_true,
    ↓reduceIte, Pi.neg_apply, letterWeight]
  split_ifs <;> omega

theorem rowCountsWeight_add
    {rank : ℕ} (left right : Fin (rank + 1) → ℕ) :
    rowCountsWeight (fun row => left row + right row) =
      rowCountsWeight left + rowCountsWeight right := by
  funext row
  simp only [rowCountsWeight, Pi.add_apply, Nat.cast_add]
  ring

theorem rowCountsWeight_pieriRowCounts
    (rank : ℕ) (steps : List Bool) (parameters : List (Fin (rank + 1)))
    (hlength : parameters.length = steps.length) :
    rowCountsWeight (pieriRowCounts rank steps parameters) =
      pieriWordWeight rank steps parameters := by
  induction steps generalizing parameters with
  | nil =>
      have hnil : parameters = [] := List.length_eq_zero_iff.mp hlength
      subst parameters
      rfl
  | cons step steps ih =>
      cases parameters with
      | nil => simp at hlength
      | cons parameter parameters =>
          have htail : parameters.length = steps.length := by simpa using hlength
          cases step <;>
            simp only [pieriRowCounts, pieriWordWeight]
          · rw [← rowCountsWeight_pieriRowIncrement_false rank parameter, ← ih parameters htail]
            simpa only [pieriRowCounts] using
              rowCountsWeight_add
                (pieriRowIncrement rank false parameter)
                (pieriRowCounts rank steps parameters)
          · rw [← rowCountsWeight_pieriRowIncrement_true rank parameter, ← ih parameters htail]
            simpa only [pieriRowCounts] using
              rowCountsWeight_add
                (pieriRowIncrement rank true parameter)
                (pieriRowCounts rank steps parameters)

theorem pieriRun_eq_add_pieriWordWeight
    (rank : ℕ) (state : Weight rank) (steps : List Bool)
    (parameters : List (Fin (rank + 1)))
    (hlength : parameters.length = steps.length) :
    pieriRun state steps parameters =
      state + pieriWordWeight rank steps parameters := by
  induction steps generalizing state parameters with
  | nil =>
      have hnil : parameters = [] := List.length_eq_zero_iff.mp hlength
      subst parameters
      simp [pieriRun, pieriWordWeight]
  | cons step steps ih =>
      cases parameters with
      | nil => simp at hlength
      | cons parameter parameters =>
          have htail : parameters.length = steps.length := by simpa using hlength
          cases step
          · rw [show pieriRun state (false :: steps) (parameter :: parameters) =
                pieriRun (minusState state (parameterComplement parameter))
                  steps parameters by rfl]
            rw [ih _ parameters htail]
            simp [pieriWordWeight, minusState, tallWeight_eq_neg_letterWeight,
              sub_eq_add_neg, add_assoc]
          · rw [show pieriRun state (true :: steps) (parameter :: parameters) =
                pieriRun (plusState state parameter) steps parameters by rfl]
            rw [ih _ parameters htail]
            simp [pieriWordWeight, plusState, add_assoc]

theorem pieriRowIncrement_sum_true
    (rank : ℕ) (parameter : Fin (rank + 1)) :
    (∑ row, pieriRowIncrement rank true parameter row) = 1 := by
  simp [pieriRowIncrement]

theorem pieriRowIncrement_sum_false
    (rank : ℕ) (parameter : Fin (rank + 1)) :
    (∑ row, pieriRowIncrement rank false parameter row) = rank := by
  classical
  let omitted := parameterComplement parameter
  change (∑ row : Fin (rank + 1), if row = omitted then 0 else 1) = rank
  calc
    (∑ row : Fin (rank + 1), if row = omitted then 0 else 1) =
        ∑ row : Fin (rank + 1), if row ≠ omitted then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro row hrow
      by_cases heq : row = omitted <;> simp [heq]
    _ = ((Finset.univ.filter fun row : Fin (rank + 1) => row ≠ omitted).card) := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = rank := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ omitted)]
      simp

theorem pieriRowCounts_sum_eq_degree
    (rank : ℕ) (steps : List Bool) (parameters : List (Fin (rank + 1)))
    (hlength : parameters.length = steps.length) :
    (∑ row, pieriRowCounts rank steps parameters row) = pieriDegree rank steps := by
  induction steps generalizing parameters with
  | nil =>
      have hnil : parameters = [] := List.length_eq_zero_iff.mp hlength
      subst parameters
      simp [pieriRowCounts, pieriDegree]
  | cons step steps ih =>
      cases parameters with
      | nil => simp at hlength
      | cons parameter parameters =>
          have htail : parameters.length = steps.length := by simpa using hlength
          cases step <;>
            simp only [pieriRowCounts, pieriDegree, List.count_cons,
              Finset.sum_add_distrib]
          · rw [pieriRowIncrement_sum_false, ih parameters htail]
            simp [pieriDegree]
            ring
          · rw [pieriRowIncrement_sum_true, ih parameters htail]
            simp [pieriDegree]
            ring

theorem rows_eq_normalized_add_last
    {rank : ℕ} (partition : NormalizedPartition rank)
    (rows : Fin (rank + 1) → ℕ)
    (hweight : rowCountsWeight rows = partition.weight) :
    ∀ row, rows row = partition.1 row + rows (Fin.last rank) := by
  intro row
  induction row using Fin.reverseInduction with
  | last => simp [partition.2.2]
  | cast row ih =>
      have hcoordinate := congrFun hweight row
      simp only [rowCountsWeight, NormalizedPartition.weight] at hcoordinate
      omega

theorem rows_sum_eq_normalized_size_add_last
    {rank : ℕ} (partition : NormalizedPartition rank)
    (rows : Fin (rank + 1) → ℕ)
    (hweight : rowCountsWeight rows = partition.weight) :
    (∑ row, rows row) =
      partition.size + (rank + 1) * rows (Fin.last rank) := by
  calc
    (∑ row, rows row) =
        ∑ row, (partition.1 row + rows (Fin.last rank)) := by
      apply Finset.sum_congr rfl
      intro row hrow
      exact rows_eq_normalized_add_last partition rows hweight row
    _ = (∑ row, partition.1 row) +
        ∑ _row : Fin (rank + 1), rows (Fin.last rank) :=
      Finset.sum_add_distrib
    _ = partition.size + (rank + 1) * rows (Fin.last rank) := by
      simp [NormalizedPartition.size, Nat.mul_comm]

theorem PieriPath.exists_determinant_shift
    {rank : ℕ} {steps : List Bool} {partition : NormalizedPartition rank}
    (path : PieriPath rank 0 steps partition.weight) :
    ∃ q : ℕ, pieriDegree rank steps =
      partition.size + (rank + 1) * q := by
  let parameters := path.1.toList
  have hlength : parameters.length = steps.length := path.1.toList_length
  have hrun := pieriRun_eq_add_pieriWordWeight
    rank (0 : Weight rank) steps parameters hlength
  rw [path.2.2] at hrun
  have hwordWeight : pieriWordWeight rank steps parameters = partition.weight := by
    simpa using hrun.symm
  have hrowsWeight : rowCountsWeight (pieriRowCounts rank steps parameters) =
      partition.weight :=
    (rowCountsWeight_pieriRowCounts rank steps parameters hlength).trans hwordWeight
  have hsum := pieriRowCounts_sum_eq_degree rank steps parameters hlength
  have hpartition := rows_sum_eq_normalized_size_add_last partition
    (pieriRowCounts rank steps parameters) hrowsWeight
  refine ⟨pieriRowCounts rank steps parameters (Fin.last rank), ?_⟩
  omega

@[simp] theorem pieriSteps_count_true (definingSteps dualSteps : ℕ) :
    (pieriSteps definingSteps dualSteps).count true = definingSteps := by
  induction definingSteps, dualSteps using pieriSteps.induct <;>
    simp_all [pieriSteps, List.count_replicate]

@[simp] theorem pieriSteps_count_false (definingSteps dualSteps : ℕ) :
    (pieriSteps definingSteps dualSteps).count false = dualSteps := by
  induction definingSteps, dualSteps using pieriSteps.induct <;>
    simp_all [pieriSteps, List.count_replicate]

@[simp] theorem pieriDegree_pieriSteps (rank definingSteps dualSteps : ℕ) :
    pieriDegree rank (pieriSteps definingSteps dualSteps) =
      definingSteps + rank * dualSteps := by
  simp [pieriDegree]

/-- An arbitrary polynomial partition with at most `rank + 1` rows. -/
def SchurPartition (rank : ℕ) :=
  {rows : Fin (rank + 1) → ℕ //
    ∀ row : Fin rank, rows row.succ ≤ rows row.castSucc}

def SchurPartition.size
    {rank : ℕ} (partition : SchurPartition rank) : ℕ :=
  ∑ row, partition.1 row

def SchurPartition.weight
    {rank : ℕ} (partition : SchurPartition rank) : Weight rank :=
  rowCountsWeight partition.1

/-- The determinant shift `μ + (q^(rank+1))`. -/
def NormalizedPartition.determinantShift
    {rank : ℕ} (partition : NormalizedPartition rank) (q : ℕ) :
    SchurPartition rank :=
  ⟨fun row => partition.1 row + q,
    fun row => Nat.add_le_add_right (partition.2.1 row) q⟩

@[simp] theorem NormalizedPartition.determinantShift_weight
    {rank : ℕ} (partition : NormalizedPartition rank) (q : ℕ) :
    (partition.determinantShift q).weight = partition.weight := by
  funext row
  simp [SchurPartition.weight, rowCountsWeight,
    NormalizedPartition.determinantShift, NormalizedPartition.weight]

@[simp] theorem NormalizedPartition.determinantShift_size
    {rank : ℕ} (partition : NormalizedPartition rank) (q : ℕ) :
    (partition.determinantShift q).size =
      partition.size + (rank + 1) * q := by
  unfold SchurPartition.size NormalizedPartition.size
  simp_rw [NormalizedPartition.determinantShift, Finset.sum_add_distrib]
  simp [Nat.mul_comm]

/-- Literal coefficient `[p₁^r e_rank^s, s_λ]` via the Schur-basis Pieri rule. -/
noncomputable def schurCoefficientP1Elementary
    (rank definingSteps dualSteps : ℕ) (partition : SchurPartition rank) : ℕ :=
  if partition.size = definingSteps + rank * dualSteps then
    Fintype.card
      (PieriPath rank 0 (pieriSteps definingSteps dualSteps) partition.weight)
  else 0

def determinantShiftCondition
    {rank : ℕ} (definingSteps dualSteps : ℕ)
    (partition : NormalizedPartition rank) : Prop :=
  ∃ q : ℕ, definingSteps + rank * dualSteps =
    partition.size + (rank + 1) * q

/-- The manuscript's case-defined mixed Schur multiplicity `M_{r,s}^{(n)}(μ)`. -/
noncomputable def mixedSchurMultiplicity
    (rank definingSteps dualSteps : ℕ)
    (partition : NormalizedPartition rank) : ℕ :=
  if h : determinantShiftCondition definingSteps dualSteps partition then
    schurCoefficientP1Elementary rank definingSteps dualSteps
      (partition.determinantShift (Nat.find h))
  else 0

theorem schurPieriCoefficient_eq_zero_of_no_shift
    {rank definingSteps dualSteps : ℕ}
    (partition : NormalizedPartition rank)
    (hno : ¬ determinantShiftCondition definingSteps dualSteps partition) :
    schurPieriCoefficient rank definingSteps dualSteps partition = 0 := by
  unfold schurPieriCoefficient
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun path => ?_⟩
  apply hno
  obtain ⟨q, hq⟩ := path.exists_determinant_shift
  exact ⟨q, by simpa using hq⟩

theorem mixedSchurMultiplicity_eq_schurPieriCoefficient
    (rank definingSteps dualSteps : ℕ)
    (partition : NormalizedPartition rank) :
    mixedSchurMultiplicity rank definingSteps dualSteps partition =
      schurPieriCoefficient rank definingSteps dualSteps partition := by
  by_cases hshift : determinantShiftCondition definingSteps dualSteps partition
  · rw [mixedSchurMultiplicity, dif_pos hshift]
    unfold schurCoefficientP1Elementary schurPieriCoefficient
    have hdegree := Nat.find_spec hshift
    rw [if_pos (by simpa using hdegree.symm)]
    simp
  · rw [mixedSchurMultiplicity, dif_neg hshift,
      schurPieriCoefficient_eq_zero_of_no_shift partition hshift]

theorem mixedEndpointMultiplicity_eq_mixedSchurMultiplicity
    (rank columns : ℕ) (partition : NormalizedPartition rank) :
    mixedEndpointMultiplicity rank columns partition.weight =
      mixedSchurMultiplicity rank ((columns + 1) / 2) (columns / 2) partition := by
  rw [mixedEndpointMultiplicity_eq_schurPieriCoefficient,
    mixedSchurMultiplicity_eq_schurPieriCoefficient]

/-- Exact Schur-coefficient form of the manuscript's highest-weight refinement. -/
theorem ribbonEndpointMultiplicity_schur_formula
    {rank : ℕ} (hrank : 1 ≤ rank) (columns : ℕ)
    (partition : NormalizedPartition rank) :
    (ribbonEndpointMultiplicity rank columns partition.weight : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (mixedSchurMultiplicity rank
            ((columns + 1) / 2 - edges) (columns / 2 - edges) partition : ℤ) := by
  rw [ribbonEndpointMultiplicity_formula hrank columns partition.weight]
  apply Finset.sum_congr rfl
  intro edges hedges
  have hedge : edges ≤ columns / 2 := by
    simp only [Finset.mem_range] at hedges
    omega
  have hdefining : (columns - 2 * edges + 1) / 2 =
      (columns + 1) / 2 - edges := by omega
  have hdual : (columns - 2 * edges) / 2 =
      columns / 2 - edges := by omega
  rw [mixedEndpointMultiplicity_eq_mixedSchurMultiplicity
      rank (columns - 2 * edges) partition,
    hdefining, hdual]

end FibonacciRibbonKernel
