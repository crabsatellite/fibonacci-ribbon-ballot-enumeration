import FibonacciRibbonKernel.AnalyticMultiplierTransfer

namespace FibonacciRibbonKernel

open PowerSeries
open Filter Asymptotics

/-!
# Analytic-multiplier transfer for both ribbon power--log models

The generic convolution theorem is instantiated here with the literal pair
carrier `(i,j)`, shift `i+2j`, and exact multiplier value from the manuscript.
Both half-integral and integral singular exponents are covered.
-/

theorem halfOddNumerator_pos (order : ℕ) :
    0 < halfOddNumerator order := by
  unfold halfOddNumerator
  apply Finset.prod_pos
  intro index _hindex
  positivity

theorem halfPowerSingularConstant_ne_zero (order : ℕ) :
    halfPowerSingularConstant order ≠ 0 := by
  unfold halfPowerSingularConstant
  have hsign : (-1 : ℝ) ^ order ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnumerator : halfOddNumerator order ≠ 0 :=
    (halfOddNumerator_pos order).ne'
  have hdenominator :
      (2 : ℝ) ^ order * Real.sqrt Real.pi ≠ 0 := by positivity
  exact div_ne_zero (mul_ne_zero hsign hnumerator) hdenominator

theorem integerPowerLogSingularConstant_ne_zero (order : ℕ) :
    (-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ) ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

theorem fixedRankGrowth_gt_one
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    1 < fixedRankGrowth alphabetSize := by
  have hrhoPos := fixedRankPreimage_pos alphabetSize hsize
  have hrhoLt := fixedRankPreimage_lt_one alphabetSize hsize
  have hmul := fixedRankGrowth_mul_preimage alphabetSize hsize
  nlinarith

noncomputable def ribbonTransferRadius (alphabetSize : ℕ) : ℝ :=
  (fixedRankPreimage alphabetSize + 1) / 2

theorem fixedRankPreimage_lt_transferRadius
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankPreimage alphabetSize < ribbonTransferRadius alphabetSize := by
  unfold ribbonTransferRadius
  linarith [fixedRankPreimage_lt_one alphabetSize hsize]

theorem ribbonTransferRadius_lt_one
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonTransferRadius alphabetSize < 1 := by
  unfold ribbonTransferRadius
  linarith [fixedRankPreimage_lt_one alphabetSize hsize]

theorem ribbonTransferRadius_pos
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
  0 < ribbonTransferRadius alphabetSize := by
  unfold ribbonTransferRadius
  linarith [fixedRankPreimage_pos alphabetSize hsize]

theorem ribbonTransferRadius_product_abs_lt_one
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    |fixedRankPreimage alphabetSize * ribbonTransferRadius alphabetSize| < 1 := by
  rw [abs_of_pos (mul_pos (fixedRankPreimage_pos alphabetSize hsize)
    (ribbonTransferRadius_pos alphabetSize hsize))]
  have hmulLt := mul_lt_mul_of_pos_left
    (ribbonTransferRadius_lt_one alphabetSize hsize)
    (fixedRankPreimage_pos alphabetSize hsize)
  have hmulLt' : fixedRankPreimage alphabetSize *
      ribbonTransferRadius alphabetSize < fixedRankPreimage alphabetSize := by
    simpa using hmulLt
  exact hmulLt'.trans (fixedRankPreimage_lt_one alphabetSize hsize)

theorem ribbonMultiplierWeight_hasSum
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    HasSum (fun pair : ℕ × ℕ =>
      ribbonMultiplierPairCoefficient parameter
          (fixedRankPreimage alphabetSize) pair *
        (fixedRankGrowth alphabetSize)⁻¹ ^
          ribbonMultiplierPairShift pair)
      (fixedRankGrowth alphabetSize / alphabetSize *
        (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
          parameter) := by
  have hsum :=
    ribbonMultiplierPairWeighted_at_preimage_localScale_hasSum
      parameter alphabetSize hsize
  convert hsum using 1
  funext pair
  rw [ribbonMultiplierPairWeightedTerm_eq,
    fixedRankPreimage_eq_inv_growth alphabetSize hsize]

theorem ribbonMultiplierWeight_summable_abs_at_transferRadius
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    Summable (fun pair : ℕ × ℕ =>
      |ribbonMultiplierPairCoefficient parameter
          (fixedRankPreimage alphabetSize) pair| *
        ribbonTransferRadius alphabetSize ^ ribbonMultiplierPairShift pair) := by
  have habsolute := ribbonMultiplierPairWeighted_summable_abs parameter
    (fixedRankPreimage alphabetSize) (ribbonTransferRadius alphabetSize)
    (ribbonTransferRadius_product_abs_lt_one alphabetSize hsize)
    (by rw [abs_of_pos (ribbonTransferRadius_pos alphabetSize hsize)]
        exact ribbonTransferRadius_lt_one alphabetSize hsize)
  apply habsolute.congr
  intro pair
  rw [ribbonMultiplierPairWeightedTerm_eq, abs_mul,
    abs_of_pos (pow_pos (ribbonTransferRadius_pos alphabetSize hsize) _)]

noncomputable def ribbonLocalMultiplier
    (parameter : ℝ) (alphabetSize : ℕ) : ℝ :=
  fixedRankGrowth alphabetSize / alphabetSize *
    (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^ parameter

theorem ribbonLocalMultiplier_pos
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    0 < ribbonLocalMultiplier parameter alphabetSize := by
  unfold ribbonLocalMultiplier
  have hgrowth := fixedRankGrowth_pos alphabetSize hsize
  have hsqrt := fixedRank_sqrt_pos alphabetSize hsize
  positivity

theorem ribbonLocalMultiplier_ne_zero
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonLocalMultiplier parameter alphabetSize ≠ 0 :=
  (ribbonLocalMultiplier_pos parameter alphabetSize hsize).ne'

theorem halfPowerSeries_coeff_isEquivalent
    (order : ℕ) (growth : ℝ) :
    (fun index : ℕ => PowerSeries.coeff index
      (halfPowerSeries order growth)) ~[atTop]
      powerExponentialTerm (halfPowerSingularConstant order)
        growth ((order : ℝ) + 1 / 2) := by
  have heq : (fun index : ℕ => PowerSeries.coeff index
      (halfPowerSeries order growth)) =
      halfPowerClosedCoefficient order growth := by
    funext index
    exact halfPowerSeries_coeff_closed order growth index
  rw [heq]
  change halfPowerClosedCoefficient order growth ~[atTop]
    halfPowerRpowLeadingCoefficient order growth
  exact halfPowerClosedCoefficient_isEquivalent_rpow order growth

theorem integerPowerLogSeries_coeff_isEquivalent
    (order : ℕ) (growth : ℝ) :
    (fun index : ℕ => PowerSeries.coeff index
      (integerPowerLogSeries order growth)) ~[atTop]
      powerExponentialTerm
        ((-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ))
        growth (order + 1 : ℕ) := by
  have heq : (fun index : ℕ => PowerSeries.coeff index
      (integerPowerLogSeries order growth)) =ᶠ[atTop]
      integerPowerLogClosedCoefficient order growth := by
    filter_upwards [eventually_ge_atTop (order + 1)] with index hindex
    exact integerPowerLogSeries_coeff_closed order growth index (by omega)
  have hclosed := integerPowerLogClosedCoefficient_isEquivalent_rpow
    order growth
  have hleading : integerPowerLogRpowLeadingCoefficient order growth =
      powerExponentialTerm
        ((-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ))
        growth (order + 1 : ℕ) := by
    funext index
    unfold integerPowerLogRpowLeadingCoefficient powerExponentialTerm
    push_cast
    ring
  rw [← hleading]
  exact heq.isEquivalent.trans hclosed

theorem halfPowerRibbonConvolutionRatio_tendsto
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    Tendsto
      (weightedShiftedConvolutionRatio
        (ribbonMultiplierPairCoefficient ((order : ℝ) - 1 / 2)
          (fixedRankPreimage alphabetSize))
        ribbonMultiplierPairShift
        (fun index : ℕ => PowerSeries.coeff index
          (halfPowerSeries order (fixedRankGrowth alphabetSize)))
        (powerExponentialTerm (halfPowerSingularConstant order)
          (fixedRankGrowth alphabetSize) ((order : ℝ) + 1 / 2)))
      atTop
      (nhds (fixedRankGrowth alphabetSize / alphabetSize *
        (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
          ((order : ℝ) - 1 / 2))) := by
  apply weightedShiftedConvolutionRatio_tendsto_multiplier
    (radius := ribbonTransferRadius alphabetSize)
  · exact halfPowerSeries_coeff_isEquivalent order
      (fixedRankGrowth alphabetSize)
  · exact halfPowerSingularConstant_ne_zero order
  · exact fixedRankGrowth_gt_one alphabetSize hsize
  · positivity
  · rw [← fixedRankPreimage_eq_inv_growth alphabetSize hsize]
    exact fixedRankPreimage_lt_transferRadius alphabetSize hsize
  · exact ribbonMultiplierWeight_hasSum
      ((order : ℝ) - 1 / 2) alphabetSize hsize
  · exact ribbonMultiplierWeight_summable_abs_at_transferRadius
      ((order : ℝ) - 1 / 2) alphabetSize hsize

theorem integerPowerLogRibbonConvolutionRatio_tendsto
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    Tendsto
      (weightedShiftedConvolutionRatio
        (ribbonMultiplierPairCoefficient order
          (fixedRankPreimage alphabetSize))
        ribbonMultiplierPairShift
        (fun index : ℕ => PowerSeries.coeff index
          (integerPowerLogSeries order (fixedRankGrowth alphabetSize)))
        (powerExponentialTerm
          ((-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ))
          (fixedRankGrowth alphabetSize) (order + 1 : ℕ)))
      atTop
      (nhds (fixedRankGrowth alphabetSize / alphabetSize *
        (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
          (order : ℝ))) := by
  apply weightedShiftedConvolutionRatio_tendsto_multiplier
    (radius := ribbonTransferRadius alphabetSize)
  · exact integerPowerLogSeries_coeff_isEquivalent order
      (fixedRankGrowth alphabetSize)
  · exact integerPowerLogSingularConstant_ne_zero order
  · exact fixedRankGrowth_gt_one alphabetSize hsize
  · positivity
  · rw [← fixedRankPreimage_eq_inv_growth alphabetSize hsize]
    exact fixedRankPreimage_lt_transferRadius alphabetSize hsize
  · exact ribbonMultiplierWeight_hasSum order alphabetSize hsize
  · exact ribbonMultiplierWeight_summable_abs_at_transferRadius
      order alphabetSize hsize

theorem halfPowerRibbonConvolution_isEquivalent
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    scaledWeightedShiftedConvolution
        (ribbonMultiplierPairCoefficient ((order : ℝ) - 1 / 2)
          (fixedRankPreimage alphabetSize))
        ribbonMultiplierPairShift
        (fun index : ℕ => PowerSeries.coeff index
          (halfPowerSeries order (fixedRankGrowth alphabetSize)))
        (powerExponentialTerm (halfPowerSingularConstant order)
          (fixedRankGrowth alphabetSize) ((order : ℝ) + 1 / 2)) ~[atTop]
      (fun index => ribbonLocalMultiplier ((order : ℝ) - 1 / 2)
          alphabetSize *
        powerExponentialTerm (halfPowerSingularConstant order)
          (fixedRankGrowth alphabetSize) ((order : ℝ) + 1 / 2) index) := by
  apply scaledWeightedShiftedConvolution_isEquivalent
    (radius := ribbonTransferRadius alphabetSize)
  · exact halfPowerSeries_coeff_isEquivalent order
      (fixedRankGrowth alphabetSize)
  · exact halfPowerSingularConstant_ne_zero order
  · exact fixedRankGrowth_gt_one alphabetSize hsize
  · positivity
  · rw [← fixedRankPreimage_eq_inv_growth alphabetSize hsize]
    exact fixedRankPreimage_lt_transferRadius alphabetSize hsize
  · exact ribbonMultiplierWeight_hasSum
      ((order : ℝ) - 1 / 2) alphabetSize hsize
  · exact ribbonMultiplierWeight_summable_abs_at_transferRadius
      ((order : ℝ) - 1 / 2) alphabetSize hsize
  · exact ribbonLocalMultiplier_ne_zero
      ((order : ℝ) - 1 / 2) alphabetSize hsize

theorem integerPowerLogRibbonConvolution_isEquivalent
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    scaledWeightedShiftedConvolution
        (ribbonMultiplierPairCoefficient order
          (fixedRankPreimage alphabetSize))
        ribbonMultiplierPairShift
        (fun index : ℕ => PowerSeries.coeff index
          (integerPowerLogSeries order (fixedRankGrowth alphabetSize)))
        (powerExponentialTerm
          ((-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ))
          (fixedRankGrowth alphabetSize) (order + 1 : ℕ)) ~[atTop]
      (fun index => ribbonLocalMultiplier order alphabetSize *
        powerExponentialTerm
          ((-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ))
          (fixedRankGrowth alphabetSize) (order + 1 : ℕ) index) := by
  apply scaledWeightedShiftedConvolution_isEquivalent
    (radius := ribbonTransferRadius alphabetSize)
  · exact integerPowerLogSeries_coeff_isEquivalent order
      (fixedRankGrowth alphabetSize)
  · exact integerPowerLogSingularConstant_ne_zero order
  · exact fixedRankGrowth_gt_one alphabetSize hsize
  · positivity
  · rw [← fixedRankPreimage_eq_inv_growth alphabetSize hsize]
    exact fixedRankPreimage_lt_transferRadius alphabetSize hsize
  · exact ribbonMultiplierWeight_hasSum order alphabetSize hsize
  · exact ribbonMultiplierWeight_summable_abs_at_transferRadius
      order alphabetSize hsize
  · exact ribbonLocalMultiplier_ne_zero order alphabetSize hsize

end FibonacciRibbonKernel
