import FibonacciRibbonKernel.FormalLogMultiplicative

namespace FibonacciRibbonKernel

open PowerSeries

/-!
# Exact logarithmic ribbon pullback

This file handles the integral-exponent branch of the manuscript's
power--logarithm transfer.  The pulled logarithm is split into its leading
`log(1-alpha X)` term and a rigorously identified analytic remainder.
-/

theorem logOf_linearUnit_eq_formalLogOneSub (scale : ℝ) :
    PowerSeries.logOf
        (1 - PowerSeries.C scale * PowerSeries.X : ℝ⟦X⟧) =
      formalLogOneSub scale := by
  have hdeviation :
      (1 - PowerSeries.C scale * PowerSeries.X : ℝ⟦X⟧) - 1 =
        -(PowerSeries.C scale * PowerSeries.X) := by ring
  rw [PowerSeries.logOf_eq, hdeviation]
  have hsmul :
      (-scale : ℝ) • (PowerSeries.X : ℝ⟦X⟧) =
        -(PowerSeries.C scale * PowerSeries.X) := by
    simp [smul_eq_C_mul]
  rw [← hsmul, ← PowerSeries.rescale_eq_subst]
  ext index
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_log]
  cases index with
  | zero => simp
  | succ index =>
      rw [formalLogOneSub_coeff_succ]
      simp only [Nat.succ_ne_zero, if_false]
      norm_num
      rw [neg_pow]
      have hsign :
          (-1 : ℝ) ^ (index + 1) * (-1 : ℝ) ^ (index + 2) = -1 := by
        rw [← pow_add]
        rw [show (index + 1) + (index + 2) = 2 * (index + 1) + 1 by omega,
          pow_succ, pow_mul]
        norm_num
      field_simp
      linear_combination scale ^ (index + 1) * hsign

theorem formalBinomialPow_nat_parameter
    (order : ℕ) {deviation : ℝ⟦X⟧}
    (hsubst : PowerSeries.HasSubst deviation) :
    formalBinomialPow (order : ℝ) deviation = (1 + deviation) ^ order := by
  unfold formalBinomialPow
  rw [PowerSeries.binomialSeries_nat, PowerSeries.subst_pow hsubst]
  congr 1
  rw [PowerSeries.subst_add hsubst]
  change PowerSeries.subst deviation (PowerSeries.C (R := ℝ) 1) +
      PowerSeries.subst deviation PowerSeries.X = 1 + deviation
  rw [PowerSeries.subst_C, PowerSeries.subst_X hsubst]
  simp

noncomputable def ribbonPulledIntegerPowerLog
    (order alphabetSize : ℕ) : ℝ⟦X⟧ :=
  realSubstitutionDenominator *
    ((1 - PowerSeries.C (alphabetSize : ℝ) *
        realRibbonSubstitution) ^ order *
      PowerSeries.logOf
        (1 - PowerSeries.C (alphabetSize : ℝ) *
          realRibbonSubstitution))

noncomputable def ribbonIntegerLogAnalyticRemainder
    (order alphabetSize : ℕ) : ℝ⟦X⟧ :=
  (1 - PowerSeries.C (fixedRankGrowth alphabetSize) *
      PowerSeries.X) ^ order *
    ribbonSingularAnalyticMultiplier order alphabetSize *
      (PowerSeries.logOf
          (1 - PowerSeries.C (fixedRankPreimage alphabetSize) *
            PowerSeries.X) +
        PowerSeries.logOf realSubstitutionDenominator)

theorem pulledLeadingUnit_log_decomposition
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    PowerSeries.logOf
        (1 - PowerSeries.C (alphabetSize : ℝ) *
          realRibbonSubstitution) =
      PowerSeries.logOf
          (1 - PowerSeries.C (fixedRankGrowth alphabetSize) *
            PowerSeries.X) +
        PowerSeries.logOf
          (1 - PowerSeries.C (fixedRankPreimage alphabetSize) *
            PowerSeries.X) +
        PowerSeries.logOf realSubstitutionDenominator := by
  let leading := 1 - PowerSeries.C (fixedRankGrowth alphabetSize) *
    PowerSeries.X
  let secondary := 1 - PowerSeries.C (fixedRankPreimage alphabetSize) *
    PowerSeries.X
  have hleading : PowerSeries.constantCoeff leading = 1 := by
    simp [leading]
  have hsecondary : PowerSeries.constantCoeff secondary = 1 := by
    simp [secondary]
  have hdenominator :
      PowerSeries.constantCoeff realSubstitutionDenominator = 1 :=
    realSubstitutionDenominator_constantCoeff
  have hfactor := one_sub_size_mul_realRibbonSubstitution alphabetSize hsize
  change PowerSeries.logOf
      (1 - PowerSeries.C (alphabetSize : ℝ) * realRibbonSubstitution) = _
  rw [hfactor, logOf_mul (by rw [map_mul, hleading, hsecondary, one_mul])
    hdenominator, logOf_mul hleading hsecondary]

/-- Exact split of the pulled integral power--log model into the leading
integer power--log series times the analytic multiplier, plus an analytic
remainder. -/
theorem ribbonPulledIntegerPowerLog_decomposition
    (order alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonPulledIntegerPowerLog order alphabetSize =
      integerPowerLogSeries order (fixedRankGrowth alphabetSize) *
          ribbonSingularAnalyticMultiplier order alphabetSize +
        ribbonIntegerLogAnalyticRemainder order alphabetSize := by
  have hpulledDeviationZero :
      PowerSeries.constantCoeff
        (-(PowerSeries.C (alphabetSize : ℝ) * realRibbonSubstitution)) = 0 := by
    rw [map_neg, map_mul, PowerSeries.constantCoeff_C,
      realRibbonSubstitution_constantCoeff, mul_zero, neg_zero]
  have hpower := formalBinomialPow_ribbonLeadingProduct
    (order : ℝ) alphabetSize hsize
  rw [formalBinomialPow_nat_parameter order
      (PowerSeries.HasSubst.of_constantCoeff_zero' hpulledDeviationZero),
    formalBinomialPow_nat_parameter order
      (PowerSeries.HasSubst.of_constantCoeff_zero'
        (leadingLinearDeviation_constantCoeff alphabetSize)),
    formalBinomialPow_nat_parameter order
      (PowerSeries.HasSubst.of_constantCoeff_zero'
        (secondaryLinearDeviation_constantCoeff alphabetSize)),
    formalBinomialPow_nat_parameter order denominatorUnitDeviation_hasSubst]
    at hpower
  have hpower' :
      (1 - PowerSeries.C (alphabetSize : ℝ) *
          realRibbonSubstitution) ^ order =
        (1 - PowerSeries.C (fixedRankGrowth alphabetSize) *
            PowerSeries.X) ^ order *
          (1 - PowerSeries.C (fixedRankPreimage alphabetSize) *
            PowerSeries.X) ^ order *
          realSubstitutionDenominator ^ order := by
    simpa [leadingLinearDeviation, secondaryLinearDeviation,
      denominatorUnitDeviation, sub_eq_add_neg] using hpower
  have hlog := pulledLeadingUnit_log_decomposition alphabetSize hsize
  unfold ribbonPulledIntegerPowerLog
  rw [hpower', hlog]
  rw [logOf_linearUnit_eq_formalLogOneSub]
  unfold integerPowerLogSeries
  unfold ribbonIntegerLogAnalyticRemainder
  unfold ribbonSingularAnalyticMultiplier
  rw [formalBinomialPow_nat_parameter order
      (PowerSeries.HasSubst.of_constantCoeff_zero'
        (secondaryLinearDeviation_constantCoeff alphabetSize)),
    formalBinomialPow_nat_parameter order denominatorUnitDeviation_hasSubst]
  unfold secondaryLinearDeviation
  unfold denominatorUnitDeviation
  ring

end FibonacciRibbonKernel
