import FibonacciRibbonKernel.FixedRankLocalGeometry
import FibonacciRibbonKernel.RSKConsequences
import FibonacciRibbonKernel.PoissonZero

namespace FibonacciRibbonKernel

/-- Literal finite-rank ribbon density `b_{n,k}/u_{n,k}` with manuscript
alphabet size `n` (hence internal rank `n-1`). -/
noncomputable def finiteRankRibbonDensity
    (alphabetSize columns : ℕ) : ℝ :=
  (ribbonCount (alphabetSize - 1) columns : ℝ) /
    unrestrictedCount (alphabetSize - 1) columns

theorem unrestrictedCount_eq_involutionNumber_of_stable_height
    (alphabetSize columns : ℕ) (hcolumns : columns ≤ alphabetSize) :
    unrestrictedCount (alphabetSize - 1) columns =
      involutionNumber columns := by
  have hheight : columns ≤ (alphabetSize - 1) + 1 := by omega
  rw [unrestrictedCount_eq_fullTableauSum_of_columns_le_height
    (alphabetSize - 1) columns hheight]
  exact fullTableauSum_eq_involutionNumber columns

/-- For each fixed column number, the finite-rank density is eventually the
actual stable no-adjacent-involution probability. -/
theorem finiteRankRibbonDensity_eventually_eq_stable
    (columns : ℕ) :
    ∀ᶠ alphabetSize : ℕ in Filter.atTop,
      finiteRankRibbonDensity alphabetSize columns =
        zeroAdjacentCycleProbability columns := by
  filter_upwards [Filter.eventually_ge_atTop (max 2 columns)]
    with alphabetSize halphabet
  have htwo : 2 ≤ alphabetSize := le_trans (le_max_left _ _) halphabet
  have hcolumns : columns ≤ alphabetSize :=
    le_trans (le_max_right _ _) halphabet
  have hrank : 1 ≤ alphabetSize - 1 := by omega
  have hstable : columns ≤ (alphabetSize - 1) + 1 := by omega
  rw [finiteRankRibbonDensity, zeroAdjacentCycleProbability,
    ribbonCount_eq_stableActualInvolutionNumber
      (alphabetSize - 1) columns hrank hstable,
    unrestrictedCount_eq_involutionNumber_of_stable_height
      alphabetSize columns hcolumns]

/-- The inner limit in the reverse iterated order is exactly `a_k/I_k`. -/
theorem tendsto_finiteRankRibbonDensity_fixed_columns
    (columns : ℕ) :
    Filter.Tendsto (fun alphabetSize =>
        finiteRankRibbonDensity alphabetSize columns)
      Filter.atTop (nhds (zeroAdjacentCycleProbability columns)) := by
  exact Filter.Tendsto.congr'
    (by
      filter_upwards [finiteRankRibbonDensity_eventually_eq_stable columns]
        with alphabetSize heq
      exact heq.symm)
    tendsto_const_nhds

/-- Exact two-stage formulation of the manuscript's reverse iterated limit. -/
def ReverseIteratedDensityLimit : Prop :=
  (∀ columns : ℕ,
    Filter.Tendsto (fun alphabetSize =>
        finiteRankRibbonDensity alphabetSize columns)
      Filter.atTop (nhds (zeroAdjacentCycleProbability columns))) ∧
  Filter.Tendsto zeroAdjacentCycleProbability Filter.atTop
    (nhds (Real.exp 1)⁻¹)

theorem reverseIteratedDensityLimit : ReverseIteratedDensityLimit := by
  constructor
  · exact tendsto_finiteRankRibbonDensity_fixed_columns
  · exact tendsto_zeroAdjacentCycleProbability_e_inv

theorem fixedRankGrowth_lt_size
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankGrowth alphabetSize < alphabetSize := by
  rw [fixedRankGrowth]
  have hroot := fixedRank_sqrt_lt_size alphabetSize hsize
  nlinarith

theorem fixedRankGrowth_div_size_pos
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    0 < fixedRankGrowth alphabetSize / alphabetSize := by
  exact div_pos (fixedRankGrowth_pos alphabetSize hsize) (by positivity)

theorem fixedRankGrowth_div_size_lt_one
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankGrowth alphabetSize / alphabetSize < 1 := by
  rw [div_lt_one (by positivity : (0 : ℝ) < alphabetSize)]
  exact fixedRankGrowth_lt_size alphabetSize hsize

end FibonacciRibbonKernel
