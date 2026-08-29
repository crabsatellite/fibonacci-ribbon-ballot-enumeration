import FibonacciRibbonKernel.CatalanAsymptotic
import FibonacciRibbonKernel.SpecialRankConstants

namespace FibonacciRibbonKernel

open Filter Asymptotics

/-- Literal right-hand side of `eq:regev-leading`. -/
noncomputable def fixedRankUnrestrictedLeadingTerm
    (alphabetSize index : ℕ) : ℝ :=
  regevConstant alphabetSize * (alphabetSize : ℝ) ^ index *
    (index : ℝ) ^ (-fixedRankExponent alphabetSize)

/-- Literal right-hand side of `eq:fixed-rank-asymptotic`. -/
noncomputable def fixedRankRibbonLeadingTerm
    (alphabetSize index : ℕ) : ℝ :=
  transferredFixedRankConstant alphabetSize *
    fixedRankGrowth alphabetSize ^ index *
    (index : ℝ) ^ (-fixedRankExponent alphabetSize)

/-- Literal right-hand side of `eq:fixed-rank-density`. -/
noncomputable def fixedRankDensityLeadingTerm
    (alphabetSize index : ℕ) : ℝ :=
  fixedRankGrowth alphabetSize / alphabetSize *
    (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
      (fixedRankExponent alphabetSize - 1) *
    (fixedRankGrowth alphabetSize / alphabetSize) ^ index

def FixedRankUnrestrictedAsymptotic (alphabetSize : ℕ) : Prop :=
  (fun index : ℕ => (unrestrictedCount (alphabetSize - 1) index : ℝ))
    ~[atTop] fixedRankUnrestrictedLeadingTerm alphabetSize

def FixedRankRibbonAsymptotic (alphabetSize : ℕ) : Prop :=
  (fun index : ℕ => (ribbonCount (alphabetSize - 1) index : ℝ))
    ~[atTop] fixedRankRibbonLeadingTerm alphabetSize

theorem heightFourRegevLeadingTerm_eventually_eq_manuscript :
    Filter.EventuallyEq atTop heightFourRegevLeadingTerm
      (fixedRankUnrestrictedLeadingTerm 4) := by
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hindexNonneg : (0 : ℝ) ≤ index := by positivity
  unfold heightFourRegevLeadingTerm fixedRankUnrestrictedLeadingTerm
  rw [regevConstant_four, fixedRankExponent_four]
  rw [Real.rpow_neg hindexNonneg]
  field_simp
  norm_num
  ring

/-- Kernel closure of Regev's leading strip asymptotic in the four-letter
case, derived from the actual tableau carrier rather than assumed from a
reference. -/
theorem fixedRankUnrestrictedAsymptotic_four :
    FixedRankUnrestrictedAsymptotic 4 := by
  unfold FixedRankUnrestrictedAsymptotic
  change (fun index : ℕ => (heightFourTableauCount index : ℝ))
    ~[atTop] fixedRankUnrestrictedLeadingTerm 4
  exact heightFourTableau_isEquivalent_regev.congr_right
    heightFourRegevLeadingTerm_eventually_eq_manuscript

theorem regevConstant_pos
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    0 < regevConstant alphabetSize := by
  unfold regevConstant
  have hsizePos : (0 : ℝ) < alphabetSize := by positivity
  have hgammaDenominator : 0 < Real.Gamma (3 / 2 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  apply mul_pos
  · exact div_pos (Real.rpow_pos_of_pos hsizePos _)
      (by positivity)
  · apply Finset.prod_pos
    intro index hindex
    exact div_pos (Real.Gamma_pos_of_pos (by positivity))
      hgammaDenominator

theorem fixedRankLeadingTerm_ratio_eq_density
    (alphabetSize index : ℕ) (hsize : 3 ≤ alphabetSize)
    (hindex : index ≠ 0) :
    fixedRankRibbonLeadingTerm alphabetSize index /
        fixedRankUnrestrictedLeadingTerm alphabetSize index =
      fixedRankDensityLeadingTerm alphabetSize index := by
  have hn : (alphabetSize : ℝ) ≠ 0 := by positivity
  have halpha : fixedRankGrowth alphabetSize ≠ 0 :=
    (fixedRankGrowth_pos alphabetSize hsize).ne'
  have hregev : regevConstant alphabetSize ≠ 0 :=
    (regevConstant_pos alphabetSize hsize).ne'
  have hindexPos : (0 : ℝ) < index := by positivity
  have hpower :
      (index : ℝ) ^ (-fixedRankExponent alphabetSize) ≠ 0 :=
    (Real.rpow_pos_of_pos hindexPos _).ne'
  unfold fixedRankRibbonLeadingTerm fixedRankUnrestrictedLeadingTerm
  unfold fixedRankDensityLeadingTerm transferredFixedRankConstant
  rw [div_pow]
  field_simp

theorem fixedRankDensityAsymptotic_of_leading_asymptotics
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize)
    (hribbon : FixedRankRibbonAsymptotic alphabetSize)
    (hunrestricted : FixedRankUnrestrictedAsymptotic alphabetSize) :
    (fun index : ℕ =>
      (ribbonCount (alphabetSize - 1) index : ℝ) /
        unrestrictedCount (alphabetSize - 1) index)
      ~[atTop] fixedRankDensityLeadingTerm alphabetSize := by
  have hratio := hribbon.div hunrestricted
  apply hratio.congr_right
  filter_upwards [eventually_ne_atTop 0] with index hindex
  exact fixedRankLeadingTerm_ratio_eq_density
    alphabetSize index hsize hindex

theorem fixedRankDensityLeadingTerm_tendsto_zero
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    Tendsto (fixedRankDensityLeadingTerm alphabetSize)
      atTop (nhds 0) := by
  have hn : (0 : ℝ) < alphabetSize := by positivity
  have halphaNonneg :
      0 ≤ fixedRankGrowth alphabetSize / (alphabetSize : ℝ) := by
    exact (div_pos (fixedRankGrowth_pos alphabetSize hsize) hn).le
  have halphaLt :
      fixedRankGrowth alphabetSize / (alphabetSize : ℝ) < 1 := by
    rw [div_lt_one hn]
    exact fixedRankGrowth_lt_size alphabetSize hsize
  unfold fixedRankDensityLeadingTerm
  simpa only [mul_assoc, mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one halphaNonneg halphaLt).const_mul
      (fixedRankGrowth alphabetSize / (alphabetSize : ℝ) *
        (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
          (fixedRankExponent alphabetSize - 1))

theorem fixedRankDensity_tendsto_zero_of_leading_asymptotics
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize)
    (hribbon : FixedRankRibbonAsymptotic alphabetSize)
    (hunrestricted : FixedRankUnrestrictedAsymptotic alphabetSize) :
    Tendsto (fun index : ℕ =>
      (ribbonCount (alphabetSize - 1) index : ℝ) /
        unrestrictedCount (alphabetSize - 1) index)
      atTop (nhds 0) := by
  have hequivalent := fixedRankDensityAsymptotic_of_leading_asymptotics
    alphabetSize hsize hribbon hunrestricted
  exact hequivalent.symm.tendsto_nhds
    (fixedRankDensityLeadingTerm_tendsto_zero alphabetSize hsize)

end FibonacciRibbonKernel
