import FibonacciRibbonKernel.RibbonPairCoefficient

namespace FibonacciRibbonKernel

open PowerSeries
open Filter Asymptotics

/-!
# Coefficient asymptotics of the pulled leading models

This file identifies the abstract Tannery convolution with the literal
coefficient of the formal-series product.  It closes the analytic-multiplier
transfer for both power--logarithm parities.
-/

theorem halfPower_model_product_coeff_isEquivalent
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (fun index : ℕ => PowerSeries.coeff index
      (halfPowerSeries order (fixedRankGrowth alphabetSize) *
        ribbonSingularAnalyticMultiplier ((order : ℝ) - 1 / 2)
          alphabetSize)) ~[atTop]
      (fun index => ribbonLocalMultiplier ((order : ℝ) - 1 / 2)
          alphabetSize *
        powerExponentialTerm (halfPowerSingularConstant order)
          (fixedRankGrowth alphabetSize) ((order : ℝ) + 1 / 2) index) := by
  let comparison := powerExponentialTerm (halfPowerSingularConstant order)
    (fixedRankGrowth alphabetSize) ((order : ℝ) + 1 / 2)
  have hcomparisonNe : ∀ᶠ index : ℕ in atTop, comparison index ≠ 0 := by
    filter_upwards [eventually_ne_atTop 0] with index hindex
    dsimp only [comparison]
    unfold powerExponentialTerm
    exact mul_ne_zero (mul_ne_zero (halfPowerSingularConstant_ne_zero order)
      (pow_ne_zero _ (fixedRankGrowth_pos alphabetSize hsize).ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  have heq :
      (fun index : ℕ => PowerSeries.coeff index
        (halfPowerSeries order (fixedRankGrowth alphabetSize) *
          ribbonSingularAnalyticMultiplier ((order : ℝ) - 1 / 2)
            alphabetSize)) =ᶠ[atTop]
        scaledWeightedShiftedConvolution
          (ribbonMultiplierPairCoefficient ((order : ℝ) - 1 / 2)
            (fixedRankPreimage alphabetSize))
          ribbonMultiplierPairShift
          (fun index : ℕ => PowerSeries.coeff index
            (halfPowerSeries order (fixedRankGrowth alphabetSize)))
          comparison := by
    filter_upwards [hcomparisonNe] with index hindex
    rw [coeff_model_mul_ribbonMultiplier]
    exact (scaledRibbonPairConvolution_eq_finite
      (fun degree => PowerSeries.coeff degree
        (halfPowerSeries order (fixedRankGrowth alphabetSize)))
      comparison ((order : ℝ) - 1 / 2)
      (fixedRankPreimage alphabetSize) index hindex).symm
  exact heq.isEquivalent.trans
    (halfPowerRibbonConvolution_isEquivalent order alphabetSize hsize)

theorem integerPowerLog_model_product_coeff_isEquivalent
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (fun index : ℕ => PowerSeries.coeff index
      (integerPowerLogSeries order (fixedRankGrowth alphabetSize) *
        ribbonSingularAnalyticMultiplier order alphabetSize)) ~[atTop]
      (fun index => ribbonLocalMultiplier order alphabetSize *
        powerExponentialTerm
          ((-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ))
          (fixedRankGrowth alphabetSize) (order + 1 : ℕ) index) := by
  let comparison := powerExponentialTerm
    ((-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ))
    (fixedRankGrowth alphabetSize) (order + 1 : ℕ)
  have hcomparisonNe : ∀ᶠ index : ℕ in atTop, comparison index ≠ 0 := by
    filter_upwards [eventually_ne_atTop 0] with index hindex
    dsimp only [comparison]
    unfold powerExponentialTerm
    exact mul_ne_zero (mul_ne_zero
      (integerPowerLogSingularConstant_ne_zero order)
      (pow_ne_zero _ (fixedRankGrowth_pos alphabetSize hsize).ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  have heq :
      (fun index : ℕ => PowerSeries.coeff index
        (integerPowerLogSeries order (fixedRankGrowth alphabetSize) *
          ribbonSingularAnalyticMultiplier order alphabetSize)) =ᶠ[atTop]
        scaledWeightedShiftedConvolution
          (ribbonMultiplierPairCoefficient order
            (fixedRankPreimage alphabetSize))
          ribbonMultiplierPairShift
          (fun index : ℕ => PowerSeries.coeff index
            (integerPowerLogSeries order (fixedRankGrowth alphabetSize)))
          comparison := by
    filter_upwards [hcomparisonNe] with index hindex
    rw [coeff_model_mul_ribbonMultiplier]
    exact (scaledRibbonPairConvolution_eq_finite
      (fun degree => PowerSeries.coeff degree
        (integerPowerLogSeries order (fixedRankGrowth alphabetSize)))
      comparison order (fixedRankPreimage alphabetSize)
      index hindex).symm
  exact heq.isEquivalent.trans
    (integerPowerLogRibbonConvolution_isEquivalent order alphabetSize hsize)

noncomputable def ribbonPulledHalfPower
    (order alphabetSize : ℕ) : ℝ⟦X⟧ :=
  realSubstitutionDenominator *
    formalBinomialPow ((order : ℝ) - 1 / 2)
      (-(PowerSeries.C (alphabetSize : ℝ) * realRibbonSubstitution))

theorem ribbonPulledHalfPower_factorization
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonPulledHalfPower order alphabetSize =
      halfPowerSeries order (fixedRankGrowth alphabetSize) *
        ribbonSingularAnalyticMultiplier ((order : ℝ) - 1 / 2)
          alphabetSize := by
  unfold ribbonPulledHalfPower halfPowerSeries
  exact ribbonPulledBinomial_factorization
    ((order : ℝ) - 1 / 2) alphabetSize hsize

theorem ribbonPulledHalfPower_coeff_isEquivalent
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (fun index : ℕ => PowerSeries.coeff index
      (ribbonPulledHalfPower order alphabetSize)) ~[atTop]
      (fun index => ribbonLocalMultiplier ((order : ℝ) - 1 / 2)
          alphabetSize *
        powerExponentialTerm (halfPowerSingularConstant order)
          (fixedRankGrowth alphabetSize) ((order : ℝ) + 1 / 2) index) := by
  rw [ribbonPulledHalfPower_factorization order alphabetSize hsize]
  exact halfPower_model_product_coeff_isEquivalent
    order alphabetSize hsize

end FibonacciRibbonKernel
