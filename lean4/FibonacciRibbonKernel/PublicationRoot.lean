import FibonacciRibbonKernel.DefinitionFormulas
import FibonacciRibbonKernel.EndpointEnumeration
import FibonacciRibbonKernel.BesselScales
import FibonacciRibbonKernel.InvolutionCycles
import FibonacciRibbonKernel.HookBridge
import FibonacciRibbonKernel.SchurPieri
import FibonacciRibbonKernel.StableTransform
import FibonacciRibbonKernel.StableInvolutions
import FibonacciRibbonKernel.PoissonDistribution
import FibonacciRibbonKernel.NearStableDefect
import FibonacciRibbonKernel.RSKConsequences
import FibonacciRibbonKernel.TailStrips
import FibonacciRibbonKernel.SpecialRankSums
import FibonacciRibbonKernel.NearStableDefectPolynomial
import FibonacciRibbonKernel.RankTwo
import FibonacciRibbonKernel.HeightFiveBessel
import FibonacciRibbonKernel.DensityLimits
import FibonacciRibbonKernel.SpecialRankConstants
import FibonacciRibbonKernel.HeightSixBessel
import FibonacciRibbonKernel.GesselBesselBridge
import FibonacciRibbonKernel.ExteriorPfaffianFive
import FibonacciRibbonKernel.FrobeniusDeterminant
import FibonacciRibbonKernel.FiveClosedCoordinates
import FibonacciRibbonKernel.FivePairBesselOne
import FibonacciRibbonKernel.FivePairBesselTwo
import FibonacciRibbonKernel.FivePfaffianBessel
import FibonacciRibbonKernel.ExteriorMinorSumSix
import FibonacciRibbonKernel.SixPfaffianBessel
import FibonacciRibbonKernel.HeightFourCatalan
import FibonacciRibbonKernel.FixedRankAsymptotic
import FibonacciRibbonKernel.HeightFourRibbonDfinite
import FibonacciRibbonKernel.HeightFourRibbonRecurrence
import FibonacciRibbonKernel.HeightFourRibbonCharacteristic
import FibonacciRibbonKernel.GeneralBesselReduction
import FibonacciRibbonKernel.GeneralPfaffianAssembly
import FibonacciRibbonKernel.GeneralClosedBridge
import FibonacciRibbonKernel.EulerOperatorTransport
import FibonacciRibbonKernel.RibbonDfinite
import FibonacciRibbonKernel.RegevHookProduct
import FibonacciRibbonKernel.RegevNormalization
import FibonacciRibbonKernel.RegevLocalLimit
import FibonacciRibbonKernel.RegevDomination
import FibonacciRibbonKernel.RegevQuadraticSum
import FibonacciRibbonKernel.RegevQuadraticFullLimit
import FibonacciRibbonKernel.RegevGeneralFullLimit
import FibonacciRibbonKernel.RegevStirlingRenormalization
import FibonacciRibbonKernel.RegevMehtaStandardTarget
import FibonacciRibbonKernel.RankSixAsymptotic
import FibonacciRibbonKernel.GeneralWeylGesselSeries
import FibonacciRibbonKernel.GordonOddDeterminantFactorization
import FibonacciRibbonKernel.AllFixedRankAsymptotic

namespace FibonacciRibbonKernel

open scoped Classical
open PowerSeries
open Filter Asymptotics

theorem publication_general_gessel_actual_bridges :
    (∀ halfDimension : ℕ, 1 ≤ halfDimension →
      GeneralEvenGesselActualBridge halfDimension) ∧
    (∀ halfDimension : ℕ,
      GeneralOddGesselActualBridge halfDimension) := by
  constructor
  · intro halfDimension hhalf
    exact generalEvenGesselActualBridge_all halfDimension hhalf
  · intro halfDimension
    exact generalOddGesselActualBridge_all halfDimension

/-! Kernel-only publication endpoints for the manuscript's complete theorem
and formula surface. -/

theorem publication_fullBlockWeight_eq_zero (rank : ℕ) :
    fullBlockWeight rank = 0 :=
  fullBlockWeight_eq_zero rank

theorem publication_tallWeight_eq_neg_letterWeight
    (rank : ℕ) (omitted : Fin (rank + 1)) :
    tallWeight rank omitted = -letterWeight rank omitted :=
  tallWeight_eq_neg_letterWeight rank omitted

theorem publication_singleton_tall_neutral
    (rank : ℕ) (letter : Fin (rank + 1)) :
    letterWeight rank letter + tallWeight rank letter = 0 :=
  singleton_tall_neutral rank letter

theorem publication_tall_singleton_neutral
    (rank : ℕ) (letter : Fin (rank + 1)) :
    tallWeight rank letter + letterWeight rank letter = 0 :=
  tall_singleton_neutral rank letter

theorem publication_oddBadPair_neutral (rank : ℕ) :
    letterWeight rank 0 + tallWeight rank 0 = 0 :=
  oddBadPair_neutral rank

theorem publication_evenBadPair_neutral (rank : ℕ) :
    tallWeight rank (Fin.last rank) + letterWeight rank (Fin.last rank) = 0 :=
  evenBadPair_neutral rank

theorem publication_fullBlock_internal_prefix
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) (cutoff : ℕ) :
    Dominant (state + fullPrefixWeight rank cutoff) :=
  dominant_add_fullPrefixWeight hstate cutoff

theorem publication_tallColumn_internal_prefix
    {rank : ℕ} {state : Weight rank} (omitted : Fin (rank + 1))
    (hstart : Dominant state)
    (hend : Dominant (state + tallWeight rank omitted))
    (cutoff : ℕ) :
    Dominant (state + tallPrefixWeight rank omitted cutoff) :=
  dominant_add_tallPrefixWeight_of_endpoint omitted hstart hend cutoff

/-- Complete manuscript endpoint for the literal column-walk lemma. -/
theorem publication_column_walk
    {rank : ℕ} {state : Weight rank} (column : Column rank)
    (hstart : Dominant state) :
    column.prefixesDominant state ↔ Dominant (state + column.weight) :=
  column_prefixesDominant_iff_endpoint column hstart

/-- The forbidden parameter pair reads the literal full increasing alphabet. -/
theorem publication_badPair_full_word (rank : ℕ) (shortPosition : Bool) :
    (badPairBlock rank shortPosition).flatMap Column.word = fullWord rank :=
  badPairBlock_word rank shortPosition

/-- One specified bad pair is deleted and reinserted by an actual equivalence. -/
def publication_specifiedBadPair_deletion
    (rank leftLength rightLength : ℕ) :
    SpecifiedBadPairObject rank leftLength rightLength ≃
      ContractedPairObject rank leftLength rightLength :=
  specifiedBadPairDeletionEquiv rank leftLength rightLength

/-- Exact length loss under simultaneous deletion of represented bad pairs. -/
theorem publication_disjointBadPairs_length
    (rank : ℕ) (segments : List (List (Fin (rank + 1)))) :
    (insertBadPairs rank segments).length =
      (contractBadPairs segments).length + 2 * representedPairCount segments :=
  insertBadPairs_length rank segments

/-- Simultaneous deletion/insertion equivalence for pairwise-disjoint bad pairs. -/
def publication_specifiedBadPairs_deletion
    (rank : ℕ) (segmentLengths : List ℕ) :
    SpecifiedBadPairsObject rank segmentLengths ≃
      ContractedPairsObject rank segmentLengths :=
  specifiedBadPairsDeletionEquiv rank segmentLengths

/-- Complete endpoint for Equation `eq:local-obstruction`. -/
theorem publication_local_obstruction
    (rank leftIndex : ℕ)
    (rightParameter leftParameter : Fin (rank + 1)) :
    OriginalAdjacencyAllowed rank leftIndex rightParameter leftParameter ↔
      LocalParameterAdjacencyAllowed rank rightParameter leftParameter :=
  original_adjacency_allowed_iff_local_parameter_allowed
    rank leftIndex rightParameter leftParameter

/-- Pointwise commutation of the manuscript's defining and dual operators. -/
theorem publication_mixed_branching_comm
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (function : Weight rank → ℕ) :
    definingAdjacency (dualAdjacency function) state =
      dualAdjacency (definingAdjacency function) state :=
  definingAdjacency_dualAdjacency_comm hstate function

/-- The manuscript identity `A 1 = B 1` on the dominant cone. -/
theorem publication_mixed_branching_outdegree
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) :
    definingAdjacency (fun _ => 1) state =
      dualAdjacency (fun _ => 1) state :=
  definingAdjacency_one_eq_dualAdjacency_one hstate

/-- The explicit standard-tableau row-word equivalence used in the proof. -/
def publication_standard_tableau_row_word_equiv (rank columns : ℕ) :
    StandardTableau rank columns ≃ StandardRowWordTableau rank columns :=
  definingPathBallotRowWordEquiv (dominant_zero rank) columns

/-- Complete endpoint for `thm:unrestricted` and `eq:unrestricted`. -/
theorem publication_unrestricted_count (rank columns : ℕ) :
    unrestrictedCount rank columns =
      ∑ shape : BoundedPartition rank columns,
        standardTableauNumber shape :=
  unrestrictedCount_eq_sum_standardTableauNumbers rank columns

/-- Each summand is literally the ordinary standard-row-word count `f^λ`. -/
theorem publication_standard_tableau_number_literal
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    standardTableauNumber shape = standardRowWordTableauNumber shape :=
  standardTableauNumber_eq_rowWordNumber shape

/-- Complete endpoint for Equation `eq:path-matchings`. -/
theorem publication_path_matchings (vertices edges : ℕ) :
    Fintype.card (PathMatching vertices edges) =
      Nat.choose (vertices - edges) edges :=
  pathMatching_card vertices edges

/-- The matching carrier selects exactly `edges` nonconsecutive path edges. -/
theorem publication_path_matching_literal
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    matching.edgePositions.card = edges ∧
      matching.edgePositions ⊆ Finset.range (vertices - 1) ∧
      NonAdjacentEdges matching.edgePositions :=
  ⟨matching.card_edgePositions, matching.edgePositions_subset,
    matching.edgePositions_nonAdjacent⟩

/-- Recursive matching carrier is exactly the ordinary finite-set carrier. -/
def publication_path_matching_actual_equiv (vertices edges : ℕ) :
    PathMatching vertices edges ≃ ActualPathMatching vertices edges :=
  pathMatchingActualEquiv vertices edges

/-- Literal unrestricted parameter-list carrier has the operator count. -/
theorem publication_unrestricted_parameter_lists (rank columns : ℕ) :
    Fintype.card (UnrestrictedParameterList rank columns) =
      unrestrictedCount rank columns :=
  unrestrictedParameterList_card rank columns

/-- Every specified actual matching intersection contracts to length `k-2j`. -/
theorem publication_matching_intersection_card
    (rank : ℕ) {vertices edges : ℕ}
    (matching : ActualPathMatching vertices edges) :
    Fintype.card (MatchingIntersection rank vertices edges matching) =
      unrestrictedCount rank (vertices - 2 * edges) :=
  matchingIntersection_card_actual rank matching

/-- Raw literal-event inclusion--exclusion endpoint. -/
theorem publication_raw_inclusion_exclusion (rank columns : ℕ) :
    (ribbonCount rank columns : ℤ) =
      ∑ locations ∈ (Finset.range (columns - 1)).powerset,
        (-1 : ℤ) ^ locations.card *
          ((locations.inf (badEventFinset rank columns)).card : ℤ) :=
  ribbonCount_raw_inclusion_exclusion rank columns

/-- Complete endpoint for `thm:main` and `eq:main` (`rank+1 = n`). -/
theorem publication_main_enumeration
    {rank : ℕ} (hrank : 1 ≤ rank) (columns : ℕ) :
    (ribbonCount rank columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (∑ shape : BoundedPartition rank (columns - 2 * edges),
            (standardTableauNumber shape : ℤ)) :=
  ribbonCount_main_formula hrank columns

/-- The denominator is literally `(1+X²)⁻¹`. -/
theorem publication_substitution_denominator_inverse :
    substitutionDenominator * (1 + PowerSeries.X ^ 2) = 1 :=
  substitutionDenominator_mul_one_add_X_sq

/-- Complete formal-series equality in `eq:substitution`. -/
theorem publication_exact_substitution
    {rank : ℕ} (hrank : 1 ≤ rank) :
    ribbonGeneratingSeries rank =
      substitutionDenominator *
        PowerSeries.subst ribbonSubstitution
          (unrestrictedGeneratingSeries rank) :=
  exact_generating_substitution hrank

/-- Complete endpoint for `thm:substitution`, including the manuscript's
fixed-rank D-finite conclusion on the literal ribbon-count OGF after mapping
its integer coefficients to `ℚ`. -/
theorem publication_exact_substitution_dfinite
    {rank : ℕ} (hrank : 1 ≤ rank) :
    (ribbonGeneratingSeriesQ rank =
        ribbonInverseQuadraticQ *
          PowerSeries.subst ribbonSubstitutionQ
            (generalUnrestrictedOrdinarySeriesQ rank)) ∧
      EulerDFinite (ribbonGeneratingSeriesQ rank) :=
  ⟨exact_generating_substitutionQ hrank,
    ribbonGeneratingSeriesQ_eulerDFinite hrank⟩

/-- `ψ=X C(X²)` has the displayed Catalan odd coefficients. -/
theorem publication_inverse_substitution_coeff_odd (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) inverseRibbonSubstitution =
      (catalan n : ℤ) :=
  inverseRibbonSubstitution_coeff_two_mul_add_one n

theorem publication_inverse_substitution_coeff_even (n : ℕ) :
    PowerSeries.coeff (2 * n) inverseRibbonSubstitution = 0 :=
  inverseRibbonSubstitution_coeff_two_mul n

/-- Both formal substitutions are genuine compositional inverses. -/
theorem publication_substitutions_compose :
    PowerSeries.subst inverseRibbonSubstitution ribbonSubstitution = PowerSeries.X ∧
      PowerSeries.subst ribbonSubstitution inverseRibbonSubstitution = PowerSeries.X :=
  ⟨ribbonSubstitution_subst_inverse,
    inverseRibbonSubstitution_subst_ribbon⟩

/-- Complete endpoint for `eq:inverse-substitution`. -/
theorem publication_inverse_substitution
    {rank : ℕ} (hrank : 1 ≤ rank) :
    unrestrictedGeneratingSeries rank =
      (1 + inverseRibbonSubstitution ^ 2) *
        PowerSeries.subst inverseRibbonSubstitution
          (ribbonGeneratingSeries rank) :=
  inverse_generating_substitution hrank

/-- Complete literal endpoint for `eq:regev-constant`. -/
theorem publication_regev_constant (alphabetSize : ℕ) :
    regevConstant alphabetSize =
      (alphabetSize : ℝ) ^ fixedRankExponent alphabetSize /
          (alphabetSize.factorial : ℝ) *
        ∏ j ∈ Finset.range alphabetSize,
          Real.Gamma (1 + ((j + 1 : ℕ) : ℝ) / 2) /
            Real.Gamma (3 / 2) :=
  regevConstant_formula alphabetSize

/-- Exact low-rank clause of `thm:fixed-rank-asymptotic`: for the two-letter
alphabet the ribbon count is identically one. -/
theorem publication_rank_two_exact (columns : ℕ) :
    ribbonCount 1 columns = 1 :=
  rankTwo_ribbonCount columns

/-- Kernel-checked local substitution geometry used in the fixed-rank
constant transfer. -/
theorem publication_fixed_rank_local_geometry
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonSubstitutionReal (fixedRankPreimage alphabetSize) =
        1 / alphabetSize ∧
      ribbonPrefactorReal (fixedRankPreimage alphabetSize) =
        fixedRankGrowth alphabetSize / alphabetSize ∧
      fixedRankPreimage alphabetSize *
            ribbonSubstitutionDerivativeReal (fixedRankPreimage alphabetSize) /
          (1 / alphabetSize) =
        Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize := by
  exact ⟨ribbonSubstitutionReal_fixedRankPreimage alphabetSize hsize,
    ribbonPrefactorReal_fixedRankPreimage alphabetSize hsize,
    ribbonSubstitutionDerivativeReal_fixedRankPreimage alphabetSize hsize⟩

/-- Complete endpoint for `thm:fixed-rank-asymptotic`: all alphabets at
least three, together with the exact two-letter clause. -/
theorem publication_fixed_rank_asymptotic :
    (∀ alphabetSize : ℕ, 3 ≤ alphabetSize →
      FixedRankRibbonAsymptotic alphabetSize) ∧
    (∀ columns : ℕ, ribbonCount 1 columns = 1) := by
  exact ⟨fixedRankRibbonAsymptotic_all, rankTwo_ribbonCount⟩

/-- Complete all-rank endpoint for `eq:fixed-rank-asymptotic`. -/
theorem publication_fixed_rank_ribbon_asymptotic
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    FixedRankRibbonAsymptotic alphabetSize :=
  fixedRankRibbonAsymptotic_all alphabetSize hsize

/-- Complete all-rank Regev strip endpoint for `eq:regev-leading`. -/
theorem publication_regev_leading
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    FixedRankUnrestrictedAsymptotic alphabetSize :=
  fixedRankUnrestrictedAsymptotic_all_alphabet alphabetSize hsize

/-- Complete endpoint for `eq:fixed-rank-density`. -/
theorem publication_fixed_rank_density
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (fun index : ℕ => finiteRankRibbonDensity alphabetSize index)
      ~[atTop] fixedRankDensityLeadingTerm alphabetSize := by
  exact fixedRankDensityAsymptotic_all alphabetSize hsize

/-- Literal two-stage forward iterated limit in
`eq:noncommuting-limits`. -/
def ForwardIteratedDensityLimit : Prop :=
  (∀ alphabetSize : ℕ, 3 ≤ alphabetSize →
    Tendsto (finiteRankRibbonDensity alphabetSize) atTop (nhds 0)) ∧
  Tendsto (fun _alphabetSize : ℕ => (0 : ℝ)) atTop (nhds 0)

theorem publication_forward_iterated_density_limit :
    ForwardIteratedDensityLimit := by
  constructor
  · intro alphabetSize hsize
    exact fixedRankDensity_tendsto_zero_all alphabetSize hsize
  · exact tendsto_const_nhds

/-- Complete pair of iterated limits in `eq:noncommuting-limits`. -/
theorem publication_noncommuting_limits :
    ForwardIteratedDensityLimit ∧ ReverseIteratedDensityLimit :=
  ⟨publication_forward_iterated_density_limit,
    reverseIteratedDensityLimit⟩

/-- Source-side, premise-free height-five Bessel recurrence.  The distinct
Gessel coefficient bridge to `heightFiveTableauCount` is not folded into this
endpoint. -/
theorem publication_height_five_bessel_recurrence
    (index : ℕ) (hindex : 3 ≤ index) :
    (index + 4 : ℚ) * (index + 6 : ℚ) * heightFiveBesselSequence index -
        (3 * index ^ 2 + 17 * index + 15 : ℚ) *
          heightFiveBesselSequence (index - 1) -
        (index - 1 : ℚ) * (13 * index + 9 : ℚ) *
          heightFiveBesselSequence (index - 2) +
        15 * (index - 1 : ℚ) * (index - 2 : ℚ) *
          heightFiveBesselSequence (index - 3) = 0 :=
  heightFiveBesselSequence_recurrence index hindex

/-- Source-side, premise-free height-six Bessel recurrence, before the
separate Gessel coefficient bridge to the actual tableau carrier. -/
theorem publication_height_six_bessel_recurrence
    (index : ℕ) (hindex : 4 ≤ index) :
    (index + 5 : ℚ) * (index + 8 : ℚ) * (index + 9 : ℚ) *
          heightSixBesselSequence index -
        4 * (5 * index ^ 2 + 46 * index + 84 : ℚ) *
          heightSixBesselSequence (index - 1) -
        4 * (index - 1 : ℚ) *
          (10 * index ^ 2 + 58 * index + 33 : ℚ) *
          heightSixBesselSequence (index - 2) +
        144 * (index - 1 : ℚ) * (index - 2 : ℚ) *
          heightSixBesselSequence (index - 3) +
        144 * (index - 1 : ℚ) * (index - 2 : ℚ) *
          (index - 3 : ℚ) * heightSixBesselSequence (index - 4) = 0 :=
  heightSixBesselSequence_recurrence index hindex

/-- Complete reverse-order half of `eq:noncommuting-limits`. -/
theorem publication_reverse_iterated_density_limit :
    ReverseIteratedDensityLimit :=
  reverseIteratedDensityLimit

/-- Exact special-rank Regev constants and transferred constants appearing in
the three explicit corollaries. -/
theorem publication_special_rank_constants :
    regevConstant 4 = 32 / Real.pi ∧
      regevConstant 5 = 9375 / (8 * Real.pi) ∧
      regevConstant 6 =
        (3 / 4 : ℝ) * 6 ^ (15 / 2 : ℝ) /
          Real.pi ^ (3 / 2 : ℝ) ∧
      transferredFixedRankConstant 4 =
        6 * (2 + Real.sqrt 3) / Real.pi ∧
      transferredFixedRankConstant 5 =
        1323 * fixedRankGrowth 5 / (8 * Real.pi) ∧
      transferredFixedRankConstant 6 =
        3 * 2 ^ (57 / 4 : ℝ) * fixedRankGrowth 6 /
          Real.pi ^ (3 / 2 : ℝ) := by
  exact ⟨regevConstant_four, regevConstant_five, regevConstant_six,
    transferredFixedRankConstant_four, transferredFixedRankConstant_five,
    transferredFixedRankConstant_six⟩

/-- Complete actual-carrier fixed-rank ribbon asymptotics in the three
explicit manuscript dimensions. -/
theorem publication_special_rank_ribbon_asymptotics :
    FixedRankRibbonAsymptotic 4 ∧
      FixedRankRibbonAsymptotic 5 ∧
      FixedRankRibbonAsymptotic 6 :=
  ⟨fixedRankRibbonAsymptotic_four,
    fixedRankRibbonAsymptotic_five,
    fixedRankRibbonAsymptotic_six⟩

/-- The corresponding literal fixed-rank density asymptotics. -/
theorem publication_special_rank_density_asymptotics :
    ((fun index : ℕ =>
      (ribbonCount 3 index : ℝ) / unrestrictedCount 3 index)
        ~[atTop] fixedRankDensityLeadingTerm 4) ∧
    ((fun index : ℕ =>
      (ribbonCount 4 index : ℝ) / unrestrictedCount 4 index)
        ~[atTop] fixedRankDensityLeadingTerm 5) ∧
    ((fun index : ℕ =>
      (ribbonCount 5 index : ℝ) / unrestrictedCount 5 index)
        ~[atTop] fixedRankDensityLeadingTerm 6) := by
  exact ⟨fixedRankDensityAsymptotic_of_leading_asymptotics 4 (by norm_num)
      fixedRankRibbonAsymptotic_four
      (fixedRankUnrestrictedAsymptotic_all 3 (by norm_num)),
    fixedRankDensityAsymptotic_of_leading_asymptotics 5 (by norm_num)
      fixedRankRibbonAsymptotic_five
      (fixedRankUnrestrictedAsymptotic_all 4 (by norm_num)),
    fixedRankDensityAsymptotic_of_leading_asymptotics 6 (by norm_num)
      fixedRankRibbonAsymptotic_six
      (fixedRankUnrestrictedAsymptotic_all 5 (by norm_num))⟩

/-- Forward fixed-rank density limits in the three explicit dimensions. -/
theorem publication_special_rank_density_limits :
    Tendsto (fun index : ℕ =>
      (ribbonCount 3 index : ℝ) / unrestrictedCount 3 index)
        Filter.atTop (nhds 0) ∧
    Tendsto (fun index : ℕ =>
      (ribbonCount 4 index : ℝ) / unrestrictedCount 4 index)
        Filter.atTop (nhds 0) ∧
    Tendsto (fun index : ℕ =>
      (ribbonCount 5 index : ℝ) / unrestrictedCount 5 index)
        Filter.atTop (nhds 0) := by
  exact ⟨fixedRankDensity_tendsto_zero_of_leading_asymptotics 4 (by norm_num)
      fixedRankRibbonAsymptotic_four
      (fixedRankUnrestrictedAsymptotic_all 3 (by norm_num)),
    fixedRankDensity_tendsto_zero_of_leading_asymptotics 5 (by norm_num)
      fixedRankRibbonAsymptotic_five
      (fixedRankUnrestrictedAsymptotic_all 4 (by norm_num)),
    fixedRankDensity_tendsto_zero_of_leading_asymptotics 6 (by norm_num)
      fixedRankRibbonAsymptotic_six
      (fixedRankUnrestrictedAsymptotic_all 5 (by norm_num))⟩

/-- Uniform premise-free analytic Gessel--Weyl identities in both parity
branches.  The corresponding actual bounded-tableau bridges are exposed by
`publication_general_gessel_actual_bridges`. -/
theorem publication_general_weyl_gessel_analytic
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    (evenFormalGesselMatrixR halfDimension).det =
        evenWeylSeriesGeneralR halfDimension ∧
      oddFormalGesselSeriesR halfDimension =
        oddWeylSeriesGeneralR halfDimension :=
  ⟨evenFormalGesselDet_eq_weylSeries hhalf,
    oddFormalGesselSeries_eq_weylSeries hhalf⟩

/-- Complete literal endpoint for `eq:tail-tableaux`. -/
theorem publication_tail_tableaux (tailBound size : ℕ) :
    tailTableauSum tailBound size =
      ∑ shape : BoundedPartition size size,
        if size - shape.firstRow ≤ tailBound then
          standardTableauNumber shape
        else 0 :=
  tailTableauSum_formula tailBound size

/-- Conjugation preserves the fixed-shape standard-tableau count. -/
theorem publication_tableau_conjugation
    {size : ℕ} (shape : BoundedPartition size size) :
    standardTableauNumber shape.conjugate = standardTableauNumber shape :=
  shape.standardTableauNumber_conjugate

/-- Kernel-closed conjugate-tail algebra of `eq:near-stable-defect`; RSK is
the remaining bridge from the all-tableau stable count to `a_k`. -/
theorem publication_near_stable_tableau_defect
    (defect size : ℕ) (hsize : defect + 2 ≤ size) :
    tableauStableSignedNumber size -
        (ribbonCount (size - defect - 1) size : ℤ) =
      ∑ edges ∈ Finset.range ((defect + 1) / 2),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (tailTableauSum (defect - 2 * edges - 1)
            (size - 2 * edges) : ℤ) :=
  tableauStableSignedNumber_sub_ribbonCount defect size hsize

/-- Specified bad-pair contraction preserves every exact endpoint fiber. -/
noncomputable def publication_endpoint_matching_contraction
    (rank : ℕ) {vertices edges : ℕ}
    (matching : PathMatching vertices edges) (target : Weight rank) :
    EndpointMatchingIntersection rank matching target ≃
      UnrestrictedEndpointObject rank matching.freeVertices target :=
  endpointMatchingContractionEquiv rank matching target

/--
Kernel-checked combinatorial core of `thm:highest-weight` /
`eq:highest-weight`; the separate Schur/Pieri identification of the endpoint
multiplicity remains the obligation in `eq:mixed-schur-multiplicity`.
-/
theorem publication_highest_weight_combinatorial
    {rank : ℕ} (hrank : 1 ≤ rank) (columns : ℕ) (target : Weight rank) :
    (ribbonEndpointMultiplicity rank columns target : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (mixedEndpointMultiplicity rank
            (columns - 2 * edges) target : ℤ) :=
  ribbonEndpointMultiplicity_formula hrank columns target

/-- Kernel closure of `eq:mixed-schur-multiplicity` in literal Pieri semantics. -/
theorem publication_mixed_schur_multiplicity
    (rank columns : ℕ) (partition : NormalizedPartition rank) :
    mixedEndpointMultiplicity rank columns partition.weight =
      mixedSchurMultiplicity rank ((columns + 1) / 2) (columns / 2) partition :=
  mixedEndpointMultiplicity_eq_mixedSchurMultiplicity rank columns partition

/-- Kernel closure of `thm:highest-weight` and `eq:highest-weight`. -/
theorem publication_highest_weight_schur
    {rank : ℕ} (hrank : 1 ≤ rank) (columns : ℕ)
    (partition : NormalizedPartition rank) :
    (ribbonEndpointMultiplicity rank columns partition.weight : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (mixedSchurMultiplicity rank
            ((columns + 1) / 2 - edges) (columns / 2 - edges) partition : ℤ) :=
  ribbonEndpointMultiplicity_schur_formula hrank columns partition

/-- Literal factorial-series Bessel derivative producers. -/
theorem publication_bessel_generators :
    PowerSeries.derivative ℚ besselJ0 = 2 * besselJ1 ∧
      PowerSeries.X * PowerSeries.derivative ℚ besselJ1 =
        2 * PowerSeries.X * besselJ0 - besselJ1 :=
  ⟨derivative_besselJ0, X_mul_derivative_besselJ1⟩

/-- Kernel-checked even-rank finite system `X F'=X M₀F+M₁F`. -/
theorem publication_bessel_finite_system
    (degree : ℕ) (index : Fin (degree + 1)) :
    PowerSeries.X *
        PowerSeries.derivative ℚ (besselBasisVector degree index) =
      PowerSeries.X *
          besselM0Action degree (besselBasisVector degree) index +
        besselM1Action degree (besselBasisVector degree) index :=
  bessel_finite_system degree index

theorem publication_odd_bessel_finite_system
    (degree : ℕ) (index : Fin (degree + 1)) :
    PowerSeries.X *
        PowerSeries.derivative ℚ (oddBesselBasisVector degree index) =
      PowerSeries.X *
          oddBesselM0Action degree (oddBesselBasisVector degree) index +
        besselM1Action degree (oddBesselBasisVector degree) index :=
  odd_bessel_finite_system degree index

/-- Complete even/odd factorial-scaled ordinary Bessel systems. -/
theorem publication_bessel_ordinary_system_even
    (degree : ℕ) (index : Fin (degree + 1)) :
    PowerSeries.X *
        (PowerSeries.derivative ℚ (besselOrdinarySeries degree index) -
          PowerSeries.X * besselM0Action degree
            (fun coordinate =>
              PowerSeries.derivative ℚ
                (besselOrdinarySeries degree coordinate)) index) =
      (besselM1Action degree (besselOrdinarySeries degree) index +
          PowerSeries.X * besselM0Action degree
            (besselOrdinarySeries degree) index) -
        PowerSeries.C
          (besselM1CoeffAction degree
            (besselFactorialCoeff degree 0) index) :=
  bessel_ordinary_system degree index

theorem publication_bessel_ordinary_system_odd
    (degree : ℕ) (index : Fin (degree + 1)) :
    PowerSeries.X *
        (PowerSeries.derivative ℚ (oddBesselOrdinarySeries degree index) -
          PowerSeries.X * oddBesselM0Action degree
            (fun coordinate =>
              PowerSeries.derivative ℚ
                (oddBesselOrdinarySeries degree coordinate)) index) =
      (besselM1Action degree (oddBesselOrdinarySeries degree) index +
          PowerSeries.X * oddBesselM0Action degree
            (oddBesselOrdinarySeries degree) index) -
        PowerSeries.C
          (besselM1CoeffAction degree
            (oddBesselFactorialCoeff degree 0) index) :=
  odd_bessel_ordinary_system degree index

/-- Complete scale identities `2d-4r` and `2d+1-4r`. -/
theorem publication_bessel_scales
    (degree scaleIndex : ℕ) (hscale : scaleIndex ≤ degree) :
    besselScaleOperator degree
        (signedBesselPolynomial (degree - scaleIndex) scaleIndex) =
      Polynomial.C (2 * degree - 4 * scaleIndex : ℚ) *
          signedBesselPolynomial (degree - scaleIndex) scaleIndex ∧
    besselScaleOperator degree
          (signedBesselPolynomial (degree - scaleIndex) scaleIndex) +
        signedBesselPolynomial (degree - scaleIndex) scaleIndex =
      Polynomial.C (2 * degree + 1 - 4 * scaleIndex : ℚ) *
          signedBesselPolynomial (degree - scaleIndex) scaleIndex :=
  ⟨signedBesselPolynomial_eigen degree scaleIndex hscale,
    odd_signedBesselPolynomial_eigen degree scaleIndex hscale⟩

/-- Complete displayed convolution `eq:n-five-sum`. -/
theorem publication_height_five_sum (columns : ℕ) :
    (ribbonCount 4 columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (heightFiveTableauCount (columns - 2 * edges) : ℤ) :=
  heightFiveRibbonSum columns

/-- Complete displayed convolution `eq:n-six-sum`. -/
theorem publication_height_six_sum (columns : ℕ) :
    (ribbonCount 5 columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (heightSixTableauCount (columns - 2 * edges) : ℤ) :=
  heightSixRibbonSum columns

/-- Exact simplification of the literal five- and six-row Gessel determinants
to the Bessel series consumed by the recurrence producers. -/
theorem publication_gessel_bessel_determinants :
    gesselHeightFiveSeries = heightFiveBesselSeries ∧
      gesselHeightSixSeries = Matrix.det gesselHeightSixMatrix ∧
      gesselHeightSixSeries = heightSixBesselSeries :=
  ⟨gesselHeightFiveSeries_eq_besselSeries,
    gesselHeightSixSeries_eq_det,
    gesselHeightSixSeries_eq_besselSeries⟩

/-- Finite exterior-algebra minor summation in the exact five-row coordinates
used by the odd-height Gessel bridge. -/
theorem publication_five_row_minor_summation
    (rows : List (FiveRow ℚ)) :
    2 * topFiveDeterminant (R := ℚ) (exteriorElementary 5 rows) =
      2 * borderedPfaffianFive (fivePairSum rows) (fiveRowSum rows) :=
  topFiveDeterminant_exteriorElementary_five_eq_borderedPfaffian rows

/-- Six-row even-height exterior minor-summation core. -/
theorem publication_six_row_exterior_minor_summation
    (rows : List (Fin 6 → ℚ)) :
    exteriorElementary (R := ℚ) 2 rows ^ 3 =
      6 * exteriorElementary 6 rows :=
  exteriorElementary_two_cube rows

theorem publication_six_row_top_minor_summation
    (rows : List (SixRow ℚ)) :
    topSixDeterminant (R := ℚ) (exteriorElementary 2 rows ^ 3) =
      6 * topSixDeterminant (R := ℚ) (exteriorElementary 6 rows) :=
  topSixDeterminant_exterior_minor_sum rows

/-- Complete actual bounded-tableau bridge and manuscript height-six
recurrence. -/
theorem publication_height_six_actual_recurrence
    (index : ℕ) (hindex : 4 ≤ index) :
    (heightSixTableauCount 0 = 1 ∧ heightSixTableauCount 1 = 1 ∧
        heightSixTableauCount 2 = 2 ∧ heightSixTableauCount 3 = 4) ∧
      factorialSeries (fun size => (heightSixTableauCount size : ℚ)) =
        gesselHeightSixSeries ∧
      factorialSeries (fun size => (heightSixTableauCount size : ℚ)) =
        heightSixBesselSeries ∧
      ((index + 5 : ℚ) * (index + 8 : ℚ) * (index + 9 : ℚ) *
            heightSixTableauCount index -
          4 * (5 * index ^ 2 + 46 * index + 84 : ℚ) *
            heightSixTableauCount (index - 1) -
          4 * (index - 1 : ℚ) *
            (10 * index ^ 2 + 58 * index + 33 : ℚ) *
            heightSixTableauCount (index - 2) +
          144 * (index - 1 : ℚ) * (index - 2 : ℚ) *
            heightSixTableauCount (index - 3) +
          144 * (index - 1 : ℚ) * (index - 2 : ℚ) *
            (index - 3 : ℚ) * heightSixTableauCount (index - 4) = 0) :=
  ⟨heightSixTableauCount_initial,
    factorialSeries_heightSixTableauCount_eq_gessel,
    factorialSeries_heightSixTableauCount_eq_bessel,
    heightSixTableauCount_recurrence index hindex⟩

/-- Premise-free Frobenius factorial-determinant formula for every bounded
partition.  This is the fixed-shape producer used by the Gessel bridge. -/
theorem publication_frobenius_factorial_determinant
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    (standardTableauNumber shape : ℚ) =
      (columns.factorial : ℚ) * boundedFactorialDeterminant shape :=
  standardTableauNumber_eq_factorial_mul_boundedFactorialDeterminant shape

/-- Actual five-row bounded-tableau EGF transported through the internally
proved Frobenius determinant and finite exterior minor-summation identity to
the stable bordered-Pfaffian coordinate series. -/
theorem publication_height_five_frobenius_pfaffian_bridge :
    PowerSeries.X ^ 10 *
        factorialSeries (fun size => (heightFiveTableauCount size : ℚ)) =
      fiveClosedPfaffianLimitSeries := by
  rw [X_ten_mul_heightFive_factorialSeries_eq_pfaffianLimit,
    fivePfaffianLimitSeries_eq_closedPfaffianLimit]

/-- First explicit Bessel coordinate of the five-row Pfaffian bridge. -/
theorem publication_height_five_pair_bessel_base :
    fiveClosedPair 3 4 =
      PowerSeries.X * (literalBesselJ 0 + literalBesselJ 1) :=
  fiveClosedPair_three_four_eq_bessel

theorem publication_height_five_pair_bessel_second :
    fiveClosedPair 2 4 =
      PowerSeries.X ^ 2 *
        (literalBesselJ 0 + 2 * literalBesselJ 1 + literalBesselJ 2) :=
  fiveClosedPair_two_four_eq_bessel

/-- Complete actual bounded-tableau coefficient bridge and manuscript
height-five recurrence. -/
theorem publication_height_five_actual_recurrence
    (index : ℕ) (hindex : 3 ≤ index) :
    (heightFiveTableauCount 0 = 1 ∧ heightFiveTableauCount 1 = 1 ∧
        heightFiveTableauCount 2 = 2) ∧
      factorialSeries (fun size => (heightFiveTableauCount size : ℚ)) =
        gesselHeightFiveSeries ∧
      factorialSeries (fun size => (heightFiveTableauCount size : ℚ)) =
        heightFiveBesselSeries ∧
      ((index + 4 : ℚ) * (index + 6 : ℚ) * heightFiveTableauCount index -
          (3 * index ^ 2 + 17 * index + 15 : ℚ) *
            heightFiveTableauCount (index - 1) -
          (index - 1 : ℚ) * (13 * index + 9 : ℚ) *
            heightFiveTableauCount (index - 2) +
          15 * (index - 1 : ℚ) * (index - 2 : ℚ) *
            heightFiveTableauCount (index - 3) = 0) :=
  ⟨heightFiveTableauCount_initial,
    factorialSeries_heightFiveTableauCount_eq_gessel,
    factorialSeries_heightFiveTableauCount_eq_bessel,
    heightFiveTableauCount_recurrence index hindex⟩

/-- Kernel closure of the classical Catalan product formula used in
`cor:n-four`, proved for the actual bounded-tableau count. -/
theorem publication_height_four_catalan (rank : ℕ) :
    heightFourTableauCount (2 * rank) =
        catalan rank * catalan (rank + 1) ∧
      heightFourTableauCount (2 * rank + 1) = catalan (rank + 1) ^ 2 :=
  ⟨heightFourTableauCount_even_catalan rank,
    heightFourTableauCount_odd_catalan rank⟩

/-- Complete exact convolution `eq:n-four-sum`. -/
theorem publication_height_four_sum (columns : ℕ) :
    (ribbonCount 3 columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (heightFourCatalanCount (columns - 2 * edges) : ℤ) :=
  ribbonCount_rankThree_catalan_sum columns

/-- The premise-free differential recurrence that identifies the Catalan
product with the actual height-four tableau sequence. -/
theorem publication_height_four_actual_recurrence
    (index : ℕ) (hindex : 2 ≤ index) :
    heightFourTableauCount index = heightFourCatalanCount index ∧
      ((index + 3 : ℚ) * (index + 4 : ℚ) *
          heightFourTableauCount index -
        (8 * index + 12 : ℚ) * heightFourTableauCount (index - 1) -
        16 * (index : ℚ) * (index - 1 : ℚ) *
          heightFourTableauCount (index - 2) = 0) :=
  ⟨heightFourTableauCount_eq_catalan index,
    heightFourTableauCount_recurrence index hindex⟩

/-- Premise-free four-letter instance of `eq:regev-leading`. -/
theorem publication_regev_leading_four :
    FixedRankUnrestrictedAsymptotic 4 :=
  fixedRankUnrestrictedAsymptotic_four

/-- Explicit homogeneous polynomial differential certificates for both sides
of the exact substitution in the first nontrivial four-letter case. -/
theorem publication_height_four_dfinite_certificates :
    let unrestricted := unrestrictedGeneratingSeries 3
    let ribbon := ribbonGeneratingSeries 3
    (let derivativeOne := PowerSeries.derivative ℤ unrestricted
     let derivativeTwo := PowerSeries.derivative ℤ derivativeOne
     let derivativeThree := PowerSeries.derivative ℤ derivativeTwo
     (X ^ 2 - 16 * X ^ 4) * derivativeThree +
       (10 * X - 8 * X ^ 2 - 128 * X ^ 3) * derivativeTwo +
       (20 - 36 * X - 224 * X ^ 2) * derivativeOne +
       (-20 - 64 * X) * unrestricted = 0) ∧
      heightFourRibbonHomogeneousOperator ribbon = 0 :=
  ⟨unrestrictedGeneratingSeries_three_homogeneous_differential,
    ribbonGeneratingSeries_three_homogeneous_differential⟩

/-- P-recursive coefficient certificate extracted from the four-letter
ribbon OGF equation. -/
theorem publication_height_four_ribbon_recurrence (offset : ℕ) :
    ((offset : ℤ) + 13) * ((offset : ℤ) + 14) *
          ribbonCount 3 (offset + 10) -
        (8 * (offset : ℤ) + 92) * ribbonCount 3 (offset + 9) -
        (14 * (offset : ℤ) ^ 2 + 264 * offset + 1254) *
          ribbonCount 3 (offset + 8) +
        (8 * (offset : ℤ) + 100) * ribbonCount 3 (offset + 7) -
        34 * ((offset : ℤ) + 7) * ribbonCount 3 (offset + 6) +
        (8 * (offset : ℤ) + 12) * ribbonCount 3 (offset + 5) +
        (14 * (offset : ℤ) ^ 2 + 128 * offset + 302) *
          ribbonCount 3 (offset + 4) -
        (8 * (offset : ℤ) + 20) * ribbonCount 3 (offset + 3) -
        (offset : ℤ) * ((offset : ℤ) + 1) *
          ribbonCount 3 (offset + 2) = 0 :=
  ribbonCount_rankThree_recurrence offset

/-- Algebraic characteristic and indicial certificate for the two
equal-modulus four-letter modes: the positive mode has exponent `-3`, while
the negative mode is lower order with exponent `-5`. -/
theorem publication_height_four_characteristic_indicial (exponent : ℝ) :
    heightFourRibbonCharacteristicValue (fixedRankGrowth 4) = 0 ∧
      heightFourRibbonCharacteristicValue (-fixedRankGrowth 4) = 0 ∧
      (heightFourRibbonIndicialValue (fixedRankGrowth 4) exponent = 0 ↔
        exponent = -3) ∧
      (heightFourRibbonIndicialValue (-fixedRankGrowth 4) exponent = 0 ↔
        exponent = -5) :=
  ⟨heightFourRibbonCharacteristic_positive_growth,
    heightFourRibbonCharacteristic_negative_growth,
    heightFourRibbon_positive_indicial_iff exponent,
    heightFourRibbon_negative_indicial_iff exponent⟩

/-- Uniform shifted-row carrier equivalence in every fixed rank. -/
noncomputable def publication_general_shifted_partition_equiv
    (rank size : ℕ) :
    BoundedPartition rank size ≃ StrictShiftedTuple rank size :=
  boundedPartitionStrictShiftedEquiv rank size

/-- Arbitrary-rank Frobenius strict-minor series bridge. -/
theorem publication_general_frobenius_minor_series (rank : ℕ) :
    X ^ staircaseWeight rank * generalUnrestrictedFactorialSeries rank =
        generalStrictMinorSeries rank ∧
      ∀ size,
        PowerSeries.coeff (size + staircaseWeight rank)
            (generalStrictMinorSeries rank) =
          (unrestrictedCount rank size : ℚ) / (size.factorial : ℚ) :=
  ⟨X_staircase_mul_generalUnrestrictedFactorialSeries rank,
    generalStrictMinorSeries_coeff_shifted rank⟩

/-- Arbitrary-dimensional finite exterior minor summation. -/
theorem publication_general_exterior_minor_summation
    (dimension bound : ℕ) :
    generalExteriorTruncation dimension bound =
      ((((List.range bound).reverse.map
          (generalFactorialPowerSeriesRow dimension)).sublistsLen dimension).map
        (generalSelectedDeterminant dimension)).sum :=
  generalExteriorTruncation_eq_selected_sum dimension bound

/-- Uniform adjacent-pair Bessel coordinate and arbitrary-gap monomial
reduction for the general exterior route. -/
theorem publication_general_pair_coordinates
    {rank gap : ℕ} (left right : Fin (rank + 1))
    (hgap : left.rev.val = right.rev.val + gap) :
    generalClosedPair left right =
        X ^ (left.rev.val + right.rev.val) * universalPairQ gap ∧
      universalPairQ 1 = literalBesselJ 0 + literalBesselJ 1 :=
  ⟨generalClosedPair_eq_X_rev_sum_mul_pairQ left right hgap,
    universalPairQ_one_eq_bessel⟩

/-- Complete arbitrary-gap Bessel formula for the universal pair coordinate. -/
theorem publication_general_pair_bessel
    (gap : ℕ) (hgap : 1 ≤ gap) :
    universalPairQ gap =
      (literalBesselJ 0 + literalBesselJ gap +
        2 * ∑ order ∈ Finset.Ico 1 gap, literalBesselJ order) := by
  rw [universalPairQ_eq_generalBesselPairQ gap hgap,
    generalBesselPairQ, if_neg (by omega : gap ≠ 0)]

/-- Complete arbitrary-rank polynomial reduction of every nontrivial pair
coordinate to the manuscript's `J₀,J₁` generators. -/
theorem publication_general_pair_polynomial_reduction
    {rank gap : ℕ} (left right : Fin (rank + 1))
    (hgap : left.rev.val = right.rev.val + gap) (hgapPos : 1 ≤ gap) :
    generalClosedPair left right =
      (X ^ (2 * right.rev.val) * (pairReductionP gap : ℚ⟦X⟧)) *
          literalBesselJ 0 +
        (X ^ (2 * right.rev.val) * (pairReductionQ gap : ℚ⟦X⟧)) *
          literalBesselJ 1 :=
  generalClosedPair_polynomial_bessel_reduction left right hgap hgapPos

/-- Uniform even and odd exterior/Pfaffian assembly, with the exact factorial
normalization in every dimension. -/
theorem publication_general_pfaffian_assembly
    (halfDimension bound : ℕ) :
    ((halfDimension.factorial : ℚ⟦X⟧) *
        generalExteriorTruncation (2 * halfDimension) bound =
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension)
        (exteriorElementary 2
          ((List.range bound).reverse.map
            (generalFactorialPowerSeriesRow (2 * halfDimension))) ^
              halfDimension)) ∧
    ((halfDimension.factorial : ℚ⟦X⟧) *
        generalExteriorTruncation (2 * halfDimension + 1) bound =
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension + 1)
        (exteriorElementary 2
            ((List.range bound).reverse.map
              (generalFactorialPowerSeriesRow (2 * halfDimension + 1))) ^
            halfDimension *
          exteriorElementary 1
            ((List.range bound).reverse.map
              (generalFactorialPowerSeriesRow (2 * halfDimension + 1))))) :=
  ⟨generalExteriorTruncation_even_assembly halfDimension bound,
    generalExteriorTruncation_odd_assembly halfDimension bound⟩

/-- Uniform coefficientwise identification of a sufficiently long finite
exterior truncation with the actual bounded-tableau factorial EGF. -/
theorem publication_general_exterior_coefficient_bridge
    (rank size bound : ℕ)
    (hbound : size + staircaseWeight rank < bound) :
    PowerSeries.coeff (size + staircaseWeight rank)
        (generalExteriorTruncation (rank + 1) bound) =
      (unrestrictedCount rank size : ℚ) / (size.factorial : ℚ) :=
  generalExteriorTruncation_coeff_eq_unrestricted_of_bound
    rank size bound hbound

/-- Coordinate-level finite even/odd assembly before passage to the closed
pair and single series. -/
theorem publication_general_coordinate_assembly
    (halfDimension bound : ℕ) :
    ((halfDimension.factorial : ℚ⟦X⟧) *
        generalExteriorTruncation (2 * halfDimension) bound =
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension)
        (generalTwoForm (fun i j : Fin (2 * halfDimension) =>
          generalPairSum (generalFactorialRows (2 * halfDimension) bound) i j) ^
            halfDimension)) ∧
    ((halfDimension.factorial : ℚ⟦X⟧) *
        generalExteriorTruncation (2 * halfDimension + 1) bound =
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension + 1)
        (generalTwoForm (fun i j : Fin (2 * halfDimension + 1) =>
            generalPairSum
              (generalFactorialRows (2 * halfDimension + 1) bound) i j) ^
            halfDimension *
          generalOneForm (generalRowSum
            (generalFactorialRows (2 * halfDimension + 1) bound)))) :=
  ⟨generalExteriorTruncation_even_coordinate_assembly halfDimension bound,
    generalExteriorTruncation_odd_coordinate_assembly halfDimension bound⟩

/-- Complete arbitrary-rank closed Pfaffian/Bessel bridge to the actual
bounded-tableau factorial EGF. -/
theorem publication_general_closed_bessel_bridge
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    ((halfDimension.factorial : ℚ⟦X⟧) *
        (X ^ staircaseWeight (2 * halfDimension - 1) *
          generalUnrestrictedFactorialSeries (2 * halfDimension - 1)) =
      generalClosedEvenAssembly halfDimension) ∧
    ((halfDimension.factorial : ℚ⟦X⟧) *
        (X ^ staircaseWeight (2 * halfDimension) *
          generalUnrestrictedFactorialSeries (2 * halfDimension)) =
      generalClosedOddAssembly halfDimension) :=
  ⟨generalUnrestrictedFactorialSeries_even_closed halfDimension hhalf,
    generalUnrestrictedFactorialSeries_odd_closed halfDimension⟩

/-- Nonzero scalar polynomial Euler differential equations extracted from
the complete arbitrary-rank closed Pfaffian/Bessel assemblies. -/
theorem publication_general_closed_scalar_ode (halfDimension : ℕ) :
    EulerDFinite (generalClosedEvenAssembly halfDimension) ∧
      EulerDFinite (generalClosedOddAssembly halfDimension) :=
  ⟨(generalClosedEvenAssembly_besselGenerated halfDimension).eulerDFinite,
    (generalClosedOddAssembly_besselGenerated halfDimension).eulerDFinite⟩

/-- The same scalar differential certificates transported to the actual
bounded-tableau factorial EGFs, including their literal staircase shifts. -/
theorem publication_general_factorial_egf_shifted_scalar_ode
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    EulerDFinite
        ((halfDimension.factorial : ℚ⟦X⟧) *
          (X ^ staircaseWeight (2 * halfDimension - 1) *
            generalUnrestrictedFactorialSeries (2 * halfDimension - 1))) ∧
      EulerDFinite
        ((halfDimension.factorial : ℚ⟦X⟧) *
          (X ^ staircaseWeight (2 * halfDimension) *
            generalUnrestrictedFactorialSeries (2 * halfDimension))) := by
  constructor
  · rw [generalUnrestrictedFactorialSeries_even_closed halfDimension hhalf]
    exact (generalClosedEvenAssembly_besselGenerated halfDimension).eulerDFinite
  · rw [generalUnrestrictedFactorialSeries_odd_closed halfDimension]
    exact (generalClosedOddAssembly_besselGenerated halfDimension).eulerDFinite

/-- Nonzero scalar polynomial Euler differential equations for the literal,
unshifted bounded-tableau factorial EGFs in every even and odd dimension. -/
theorem publication_general_factorial_egf_scalar_ode
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    EulerDFinite
        (generalUnrestrictedFactorialSeries (2 * halfDimension - 1)) ∧
      EulerDFinite
        (generalUnrestrictedFactorialSeries (2 * halfDimension)) :=
  ⟨generalUnrestrictedFactorialSeries_even_eulerDFinite
      halfDimension hhalf,
    generalUnrestrictedFactorialSeries_odd_eulerDFinite halfDimension⟩

/-- Exact all-rank Vandermonde/factorial product used in the first line of
Matsumoto's proof of Regev's strip asymptotic. -/
theorem publication_regev_hook_product
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    ((standardTableauNumber shape : ℚ) =
        (size.factorial : ℚ) *
          ((∏ row : Fin (rank + 1),
              ((shape.toStrictShiftedTuple.values row).factorial : ℚ)⁻¹) *
            ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
              ((shape.toStrictShiftedTuple.values row : ℚ) -
                shape.toStrictShiftedTuple.values next))) ∧
      ((standardTableauNumber shape : ℚ) =
        (size.factorial : ℚ) *
          ((∏ row : Fin (rank + 1),
              (((shape.1 row).val + row.rev.val).factorial : ℚ)⁻¹) *
            ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
              (((shape.1 row).val : ℚ) - (shape.1 next).val +
                (next.val : ℚ) - row.val))) :=
  ⟨standardTableauNumber_eq_matsumoto_product shape,
    standardTableauNumber_eq_matsumoto_row_product shape⟩

/-- Exact finite bounded-partition lattice sum before the local-limit and
dominated-convergence steps in the Regev proof. -/
theorem publication_regev_lattice_sum (rank size : ℕ) :
    (unrestrictedCount rank size : ℚ) =
      ∑ shape : BoundedPartition rank size,
        (size.factorial : ℚ) *
          ((∏ row : Fin (rank + 1),
              (((shape.1 row).val + row.rev.val).factorial : ℚ)⁻¹) *
            ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
              (((shape.1 row).val : ℚ) - (shape.1 next).val +
                (next.val : ℚ) - row.val)) :=
  unrestrictedCount_eq_matsumoto_lattice_sum rank size

/-- Exact beta=1 simplification of Matsumoto's Theorem 5.1 normalization to
the manuscript exponent `d(d-1)/4`; the integral value remains explicit. -/
theorem publication_regev_source_normalization
    (dimension index : ℕ) (integral : ℝ)
    (hdimension : 1 ≤ dimension) (hindex : 1 ≤ index) :
    matsumotoBetaOneLeadingTerm dimension index integral =
      matsumotoBetaOneConstant dimension integral *
        (dimension : ℝ) ^ index *
        (index : ℝ) ^ (-fixedRankExponent dimension) :=
  matsumotoBetaOneLeadingTerm_eq_regev_shape
    dimension index integral hdimension hindex

/-- Matsumoto's arbitrary-rank pointwise local limit on the literal bounded
partition carrier, including the exact shifted-factorial and Vandermonde
normalization. -/
theorem publication_regev_local_limit
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Filter.Tendsto sizes Filter.atTop Filter.atTop)
    (hcentered : ∀ row,
      Filter.Tendsto (fun index => regevCenteredRow (shapes index) row)
        Filter.atTop (nhds (limitRows row))) :
    Filter.Tendsto
      (fun index => matsumotoLocalNormalizedTableau (shapes index))
      Filter.atTop
      (nhds (((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
          Real.exp (-(∑ row : Fin (rank + 1),
            limitRows row ^ 2 / 2))) *
        (∏ row : Fin (rank + 1),
          ∏ next ∈ Finset.Ioi row,
            (limitRows row - limitRows next)))) :=
  matsumotoLocalNormalizedTableau_tendsto
    sizes shapes limitRows hsizes hcentered

/-- Explicit fixed-rank polynomial-times-Gaussian domination producers for
Matsumoto's subsequent dominated Riemann-sum argument. -/
theorem publication_regev_domination
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    (((∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 / 2) -
        regevEntropyOffset rank) /
          regevEntropyDenominator rank ≤
      regevShiftedEntropySum shape) ∧
    (regevFactorialNormalized (fun _ => size) (fun _ => shape) 0 ≤
      Real.exp (regevEntropyOffset rank /
          regevEntropyDenominator rank) *
        regevRowEnvelopeProduct shape *
        Real.exp (-(∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 /
            (2 * regevEntropyDenominator rank)))) ∧
    (|∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
        regevCorrectedPair shape row next| ≤
      regevPairEnvelopeProduct shape) :=
  ⟨regevShiftedEntropySum_gaussian_lower shape hsize,
    (regevFactorialNormalized_le_adjustedUpper shape hsize).trans
      (regevAdjustedFactorialUpper_gaussian_bound shape hsize),
    abs_correctedPairProduct_le_envelope shape hsize⟩

/-- The combined polynomial-times-Gaussian majorant for the complete
Matsumoto local summand, on the literal bounded-partition carrier. -/
theorem publication_regev_complete_domination
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    |matsumotoLocalNormalizedTableau shape| ≤
      Real.exp (regevEntropyOffset rank /
          regevEntropyDenominator rank) *
        regevRowEnvelopeProduct shape *
        regevPairEnvelopeProduct shape *
        Real.exp (-(∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 /
            (2 * regevEntropyDenominator rank))) :=
  abs_matsumotoLocalNormalizedTableau_gaussian_bound shape hsize

/-- Exact quadratic-mesh carrier equivalence and the resulting compact-domain
Riemann-sum limit in Matsumoto's proof.  No conditional analytic interface is
inserted: both the reindexing and convergence theorem are premise-free Lean
producers apart from the displayed nonnegative-radius hypothesis. -/
theorem publication_regev_quadratic_truncated_riemann
    (rank : ℕ) (radius : ℝ) (hradius : 0 ≤ radius) :
    (∀ mesh : ℕ, 1 ≤ mesh →
      ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh →
        Nonempty
          (QuadraticTruncatedShape rank mesh radius ≃
            QuadraticTruncatedRiemannPoint rank mesh radius)) ∧
    Filter.Tendsto
      (fun mesh => quadraticTruncatedNormalizedAverage rank mesh radius)
      Filter.atTop
      (nhds (∫ coordinates in regevTruncatedChamber rank radius,
        regevLocalIntegrand rank coordinates)) := by
  constructor
  · intro mesh hmesh hmeshRadius
    exact ⟨quadraticShapePointRiemannEquiv
      rank mesh hmesh radius hradius hmeshRadius⟩
  · exact quadratic_truncated_normalizedAverage_tendsto rank radius hradius

/-- Complete untruncated Regev limit on the exact quadratic mesh.  The endpoint
consumes the literal bounded-partition carrier, the compact Riemann sums, a
kernel proof of global integrability, and a uniform polynomial-times-Gaussian
tail estimate. -/
theorem publication_regev_quadratic_full_limit (rank : ℕ) :
    MeasureTheory.Integrable (regevLocalIntegrand rank) ∧
    Filter.Tendsto
      (fun mesh => quadraticFullNormalizedAverage rank mesh)
      Filter.atTop (nhds (regevFullChamberIntegral rank)) :=
  ⟨integrable_regevLocalIntegrand rank,
    quadratic_full_normalizedAverage_tendsto rank⟩

/-- Complete untruncated all-size Regev limit on the literal bounded-partition
carrier.  This endpoint includes the shifted affine lattice, uniform local
limit, global tails, moving-mesh Riemann convergence, and cutoff removal. -/
theorem publication_regev_all_size_full_limit (rank : ℕ) :
    Filter.Tendsto
      (fun size => generalFullNormalizedAverage rank size)
      Filter.atTop (nhds (regevFullChamberIntegral rank)) :=
  general_full_normalizedAverage_tendsto rank

/-- Regev's unrestricted tableau count on the manuscript scale, with the
remaining constant expressed by the literal traceless chamber integral. -/
theorem publication_regev_integral_coefficient_limit (rank : ℕ) :
    Filter.Tendsto
      (fun size => (unrestrictedCount rank size : ℝ) /
        generalRegevBaseScale rank size)
      Filter.atTop (nhds (regevIntegralLeadingCoefficient rank)) :=
  unrestrictedCount_normalized_tendsto_integralCoefficient rank

/-- The remaining Mehta producer is expressed on the conventional ordered
full-dimensional Gaussian--absolute-Vandermonde chamber.  All traceless-chart,
center-Gaussian, determinant-Jacobian, factorial, and normalization transports
are consumed by this kernel equivalence. -/
theorem publication_regev_mehta_standard_equivalence (rank : ℕ) :
    RegevMehtaChamberEvaluation rank ↔
      StandardMehtaChamberEvaluation rank :=
  RegevMehtaChamberEvaluation_iff_standard rank

/-- Kernel recurrence part of `eq:involution-tableaux`. -/
theorem publication_involution_recurrence (size : ℕ) :
    involutionNumber (size + 1) =
      involutionNumber size + size * involutionNumber (size - 1) :=
  involutionNumber_succ size

/-- Each decoded nontrivial involution cycle has exactly two labels. -/
theorem publication_involution_cycles_are_pairs
    {size : ℕ} (code : InvolutionCode size) :
    ∀ edge ∈ code.cycleEdges, edge.card = 2 :=
  code.cycleEdges_card_two

/-- Complete Robinson--Schensted equivalence used by
`eq:involution-tableaux`. -/
noncomputable def publication_rsk_involution_tableau_equiv (size : ℕ) :
    ActualInvolutionOn (Fin size) ≃ StandardRowWordTableau size size :=
  involutionTableauEquiv size

/-- Complete endpoint for `eq:involution-tableaux`. -/
theorem publication_involution_tableaux (size : ℕ) :
    involutionNumber size =
        ∑ shape : BoundedPartition size size, standardTableauNumber shape ∧
      involutionNumber (size + 1) =
        involutionNumber size + size * involutionNumber (size - 1) :=
  ⟨involutionNumber_eq_sum_standardTableauNumbers size,
    involutionNumber_succ size⟩

/-- Exact formal-series and inclusion--exclusion transform underlying `eq:stable-ie`. -/
theorem publication_stable_transform_ie (size : ℕ) :
    PowerSeries.coeff size stableGeneratingSeries =
      ∑ edges ∈ Finset.range (size / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (involutionNumber (size - 2 * edges) : ℤ) :=
  stableGeneratingSeries_coeff size

/-- Kernel recurrence for the stable inclusion--exclusion transform. -/
theorem publication_stable_transform_recurrence
    (size : ℕ) (hsize : 3 ≤ size) :
    stableSignedNumber (size + 1) =
      stableSignedNumber size + size * stableSignedNumber (size - 1) -
        stableSignedNumber (size - 2) + stableSignedNumber (size - 3) :=
  stableSignedNumber_recurrence size hsize

/-- Actual involutive permutations have the canonical telephone number. -/
theorem publication_actual_involution_card (size : ℕ) :
    Fintype.card (ActualInvolution size) = involutionNumber size :=
  actualInvolutionNumber_eq_involutionNumber size

/-- Kernel closure of the actual no-adjacent-involution formula `eq:stable-ie`. -/
theorem publication_stable_involution_ie (size : ℕ) :
    (stableActualInvolutionNumber size : ℤ) =
      ∑ edges ∈ Finset.range (size / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (involutionNumber (size - 2 * edges) : ℤ) :=
  stableActualInvolution_inclusion_exclusion size

/-- Kernel closure of the actual stable recurrence. -/
theorem publication_stable_involution_recurrence
    (size : ℕ) (hsize : 3 ≤ size) :
    (stableActualInvolutionNumber (size + 1) : ℤ) =
      stableActualInvolutionNumber size +
          size * stableActualInvolutionNumber (size - 1) -
        stableActualInvolutionNumber (size - 2) +
          stableActualInvolutionNumber (size - 3) :=
  stableActualInvolutionNumber_recurrence size hsize

/-- Complete endpoint for `cor:stable` on the manuscript range `n≥k`. -/
theorem publication_stable_range
    (rank columns : ℕ) (hrank : 1 ≤ rank) (hstable : columns ≤ rank + 1) :
    ribbonCount rank columns = stableActualInvolutionNumber columns :=
  ribbonCount_eq_stableActualInvolutionNumber rank columns hrank hstable

/-- Complete displayed identity `eq:near-stable-defect`. -/
theorem publication_near_stable_defect
    (defect size : ℕ) (hsize : defect + 2 ≤ size) :
    (stableActualInvolutionNumber size : ℤ) -
        (ribbonCount (size - defect - 1) size : ℤ) =
      ∑ edges ∈ Finset.range ((defect + 1) / 2),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (tailTableauSum (defect - 2 * edges - 1)
            (size - 2 * edges) : ℤ) :=
  stableActualInvolutionNumber_sub_ribbonCount_tail defect size hsize

/-- First explicit near-stable strip in `eq:first-near-stable-strips`. -/
theorem publication_first_near_stable_strip
    (size : ℕ) (hsize : 3 ≤ size) :
    (stableActualInvolutionNumber size : ℤ) -
      (ribbonCount (size - 2) size : ℤ) = 1 :=
  first_near_stable_strip size hsize

/-- Second explicit near-stable strip in `eq:first-near-stable-strips`. -/
theorem publication_second_near_stable_strip
    (size : ℕ) (hsize : 4 ≤ size) :
    (stableActualInvolutionNumber size : ℤ) -
      (ribbonCount (size - 3) size : ℤ) = size :=
  second_near_stable_strip size hsize

/-- Third explicit near-stable strip in `eq:first-near-stable-strips`. -/
theorem publication_third_near_stable_strip
    (size : ℕ) (hsize : 5 ≤ size) :
    (stableActualInvolutionNumber size : ℤ) -
      (ribbonCount (size - 4) size : ℤ) = (size - 1) * (size - 2) :=
  third_near_stable_strip size hsize

/-- Fourth explicit near-stable strip, in the manuscript's rational form. -/
theorem publication_fourth_near_stable_strip
    (size : ℕ) (hsize : 6 ≤ size) :
    ((stableActualInvolutionNumber size : ℚ) -
      (ribbonCount (size - 5) size : ℚ)) =
        (((size : ℚ) - 2) *
          (2 * (size : ℚ) ^ 2 - 8 * (size : ℚ) + 3)) / 3 :=
  fourth_near_stable_strip size hsize

/-- Complete eventual-polynomial and leading-coefficient assertion in
`cor:near-stable`. -/
theorem publication_near_stable_polynomiality
    (defect : ℕ) (hdefect : 1 ≤ defect) :
    (nearStableDefectPolynomial defect).natDegree = defect - 1 ∧
      (nearStableDefectPolynomial defect).coeff (defect - 1) =
        (involutionNumber (defect - 1) : ℚ) / (defect - 1).factorial ∧
      ∀ᶠ size : ℕ in Filter.atTop,
        (nearStableDefectPolynomial defect).eval (size : ℚ) =
          (stableActualInvolutionNumber size : ℚ) -
            (ribbonCount (size - defect - 1) size : ℚ) :=
  nearStablePolynomiality_with_leading_coefficient defect hdefect

/-- Kernel closure of `eq:factorial-moments`. -/
theorem publication_factorial_moments (size selected : ℕ) :
    adjacentCycleFactorialMoment size selected =
      (selected.factorial * Nat.choose (size - selected) selected : ℚ) *
        involutionNumber (size - 2 * selected) / involutionNumber size :=
  adjacentCycleFactorialMoment_formula size selected

/-- Every fixed-order factorial moment tends to the Poisson(1) value `1`. -/
theorem publication_factorial_moment_limit (selected : ℕ) :
    Filter.Tendsto (fun size : ℕ =>
      adjacentCycleFactorialMomentReal size selected)
      Filter.atTop (nhds 1) :=
  tendsto_adjacentCycleFactorialMomentReal_one selected

/-- Kernel closure of `eq:e-minus-one` on the actual stable carrier. -/
theorem publication_e_minus_one :
    Filter.Tendsto zeroAdjacentCycleProbability Filter.atTop
      (nhds ((Real.exp 1)⁻¹)) :=
  tendsto_zeroAdjacentCycleProbability_e_inv

/--
Kernel closure of `thm:poisson`: every finite CDF of the adjacent-cycle count
converges to the corresponding Poisson(1) CDF.
-/
theorem publication_poisson_distribution : PoissonOneDistributionalLimit :=
  poissonOneDistributionalLimit

/-- Literal hook carrier and integer-safe target for `eq:hook`. -/
theorem publication_hook_carrier
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    Fintype.card (YoungCell shape) = columns ∧
      0 < hookProduct shape ∧
      (HookFormulaStatement shape ↔
        standardTableauNumber shape *
            (∏ cell : YoungCell shape, cell.hookLength) = columns.factorial) :=
  ⟨youngCell_card shape, hookProduct_pos shape,
    hookFormulaStatement_iff shape⟩

/-- Kernel-only closure of the displayed hook formula `eq:hook`. -/
theorem publication_hook_formula
    {rank columns : ℕ} (shape : BoundedPartition rank columns) :
    HookFormulaStatement shape :=
  hookFormulaStatement shape

end FibonacciRibbonKernel
