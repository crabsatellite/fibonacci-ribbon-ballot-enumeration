import FibonacciRibbonKernel.BadLocations
import Mathlib.Tactic.FinCases

namespace FibonacciRibbonKernel

/-- In rank one, either column parity has the same endpoint increment as its
parameter letter. -/
theorem rankOne_parameterColumn_weight
    (shortPosition : Bool) (parameter : Fin 2) :
    (parameterColumn (rank := 1) shortPosition parameter).weight =
      letterWeight 1 parameter := by
  cases shortPosition with
  | true => simp [parameterColumn, Column.weight]
  | false =>
      simp only [parameterColumn, Bool.false_eq_true, if_false, Column.weight,
        tallWeight_eq_neg_letterWeight]
      by_cases hzero : parameter = 0
      · subst parameter
        funext coordinate
        have hcoordinate : coordinate = 0 := Subsingleton.elim _ _
        subst coordinate
        simp [parameterComplement, letterWeight]
      · have hone : parameter = 1 := by
          apply Fin.ext
          omega
        subst parameter
        funext coordinate
        have hcoordinate : coordinate = 0 := Subsingleton.elim _ _
        subst coordinate
        simp [parameterComplement, letterWeight]

/-- A zero parameter is readable from every rank-one dominant state. -/
theorem rankOne_zero_parameter_prefixesDominant
    (state : Weight 1) (hstate : Dominant state)
    (shortPosition : Bool) :
    (parameterColumn (rank := 1) shortPosition 0).prefixesDominant state := by
  rw [column_prefixesDominant_iff_endpoint _ hstate]
  rw [rankOne_parameterColumn_weight]
  intro coordinate
  have hcoordinate : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  simpa [letterWeight] using add_nonneg (hstate 0) (by omega : (0 : ℤ) ≤ 1)

/-- The all-zero rank-one parameter list satisfies every internal-prefix
ballot condition, independently of the initial column parity. -/
theorem rankOne_replicate_zero_ballot
    (state : Weight 1) (hstate : Dominant state)
    (shortPosition : Bool) (columns : ℕ) :
    ColumnsBallotFrom state
      (encodeColumns 1 shortPosition
        (List.replicate columns (0 : Fin 2))) := by
  induction columns generalizing state shortPosition with
  | zero => simp [encodeColumns, ColumnsBallotFrom]
  | succ columns ih =>
      rw [List.replicate_succ, encodeColumns, ColumnsBallotFrom]
      refine ⟨rankOne_zero_parameter_prefixesDominant state hstate shortPosition, ?_⟩
      have hnext : Dominant
          (state + (parameterColumn (rank := 1) shortPosition 0).weight) :=
        Column.endpointDominant_of_prefixes
          (rankOne_zero_parameter_prefixesDominant state hstate shortPosition)
      exact ih _ hnext (!shortPosition)

/-- Literal all-zero admissible ribbon object on the two-letter alphabet. -/
def rankTwoCanonicalRibbon (columns : ℕ) :
    AdmissibleRibbonObject 1 columns := by
  let word : UnrestrictedParameterList 1 columns :=
    { parameters := List.replicate columns 0
      length_eq := List.length_replicate
      ballot := rankOne_replicate_zero_ballot 0 (dominant_zero 1) true columns }
  refine ⟨word, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro location hlocation
  have hbad := (mem_badLocations_iff 1 word.parameters location).mp hlocation |>.2
  have hindex := hbad.2
  have hmem : (1 : Fin 2) ∈ List.replicate columns 0 :=
    (List.mem_iff_getElem?).mpr ⟨location + 1, hindex⟩
  simp only [List.mem_replicate] at hmem
  exact (by decide : (1 : Fin 2) ≠ 0) hmem.2

/-- A nonempty rank-one ballot parameter list must start with zero. -/
theorem rankOne_ballot_first_parameter_zero
    {columns : ℕ} (word : UnrestrictedParameterList 1 (columns + 1)) :
    word.parameters[0]? = some 0 := by
  have hlength := word.length_eq
  cases hparameters : word.parameters with
  | nil => simp [hparameters] at hlength
  | cons parameter tail =>
      have hballot := word.ballot
      rw [hparameters] at hballot
      simp only [encodeColumns, ColumnsBallotFrom] at hballot
      have hfirst := hballot.1
      have hparameter : parameter = 0 := by
        by_contra hzero
        have hone : parameter = 1 := by
          apply Fin.ext
          change parameter.val = 1
          have hvalne : parameter.val ≠ 0 := by
            intro hval
            apply hzero
            apply Fin.ext
            simpa using hval
          omega
        subst parameter
        simp [parameterColumn, Column.prefixesDominant,
          Dominant, letterWeight] at hfirst
      simp [hparameter]

/-- Once a rank-one list starts at zero, exclusion of the literal bad pair
`(0,1)` forces every later parameter to remain zero. -/
theorem finTwo_list_eq_replicate_zero_of_head_and_no_bad
    (parameters : List (Fin 2)) (hnonempty : parameters ≠ [])
    (hhead : parameters[0]? = some 0)
    (hbad : badLocations 1 parameters = ∅) :
    parameters = List.replicate parameters.length 0 := by
  induction parameters with
  | nil => exact False.elim (hnonempty rfl)
  | cons first tail ih =>
      have hfirst : first = 0 := by simpa using Option.some.inj hhead
      cases tail with
      | nil => simp [hfirst]
      | cons second rest =>
          have hsecond : second = 0 := by
            by_contra hzero
            have hlast : second = Fin.last 1 := by
              apply Fin.ext
              change second.val = 1
              have hvalne : second.val ≠ 0 := by
                intro hval
                apply hzero
                apply Fin.ext
                simpa using hval
              omega
            have hmember :
                0 ∈ badLocations 1 (first :: second :: rest) :=
              (zero_mem_badLocations_cons_cons_iff 1 first second rest).mpr
                ⟨hfirst, hlast⟩
            rw [hbad] at hmember
            exact False.elim (Finset.notMem_empty 0 hmember)
          have htailbad : badLocations 1 (second :: rest) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro location hlocation
            have hlift : location + 1 ∈
                badLocations 1 (first :: second :: rest) :=
              (mem_badLocations_cons_succ 1 first (second :: rest) location).mpr
                hlocation
            rw [hbad] at hlift
            exact Finset.notMem_empty _ hlift
          have htail := ih (by simp) (by simp [hsecond]) htailbad
          calc
            first :: second :: rest = 0 :: (second :: rest) := by rw [hfirst]
            _ = 0 :: List.replicate (second :: rest).length 0 :=
              congrArg (List.cons (0 : Fin 2)) htail
            _ = List.replicate ((second :: rest).length + 1) 0 :=
              (List.replicate_succ (a := (0 : Fin 2))
                (n := (second :: rest).length)).symm
            _ = List.replicate (first :: second :: rest).length 0 := by simp

/-- There is exactly one actual admissible ribbon object in rank one. -/
theorem rankTwo_admissibleRibbonObject_subsingleton (columns : ℕ) :
    Subsingleton (AdmissibleRibbonObject 1 columns) := by
  constructor
  intro left right
  apply Subtype.ext
  apply BallotParameterListFrom.ext
  by_cases hzero : columns = 0
  · subst columns
    exact List.eq_nil_of_length_eq_zero left.1.length_eq
      |>.trans (List.eq_nil_of_length_eq_zero right.1.length_eq).symm
  · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hleftNonempty : left.1.parameters ≠ [] := by
      intro hempty
      have hlength := left.1.length_eq
      rw [hempty] at hlength
      simp at hlength
    have hrightNonempty : right.1.parameters ≠ [] := by
      intro hempty
      have hlength := right.1.length_eq
      rw [hempty] at hlength
      simp at hlength
    have hleftHead := rankOne_ballot_first_parameter_zero left.1
    have hrightHead := rankOne_ballot_first_parameter_zero right.1
    have hleft := finTwo_list_eq_replicate_zero_of_head_and_no_bad
      left.1.parameters hleftNonempty hleftHead left.2
    have hright := finTwo_list_eq_replicate_zero_of_head_and_no_bad
      right.1.parameters hrightNonempty hrightHead right.2
    rw [hleft, hright, left.1.length_eq, right.1.length_eq]

/-- The exact two-letter clause of the fixed-rank theorem: `b_{2,k}=1`. -/
theorem rankTwo_ribbonCount (columns : ℕ) :
    ribbonCount 1 columns = 1 := by
  letI : Unique (AdmissibleRibbonObject 1 columns) :=
    { default := rankTwoCanonicalRibbon columns
      uniq := fun object =>
        (rankTwo_admissibleRibbonObject_subsingleton columns).allEq object _ }
  exact Fintype.card_unique

end FibonacciRibbonKernel
