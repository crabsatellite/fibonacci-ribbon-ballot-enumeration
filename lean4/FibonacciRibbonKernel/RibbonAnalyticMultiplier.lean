import FibonacciRibbonKernel.RibbonSingularPullback

namespace FibonacciRibbonKernel

open PowerSeries

/-!
# Explicit analytic multiplier in the ribbon pullback

The secondary factor and the denominator factor from
`ribbonPulledBinomial_factorization` are converted here into literal
generalized-binomial series.  This exposes their coefficient radius and their
value at the leading preimage for the subsequent convolution theorem.
-/

theorem formalBinomialPow_add_parameters
    (left right : ℝ) {deviation : ℝ⟦X⟧}
    (hsubst : PowerSeries.HasSubst deviation) :
    formalBinomialPow (left + right) deviation =
      formalBinomialPow left deviation * formalBinomialPow right deviation := by
  unfold formalBinomialPow
  rw [PowerSeries.binomialSeries_add,
    PowerSeries.subst_mul hsubst]

theorem formalBinomialPow_zero_parameter
    {deviation : ℝ⟦X⟧} (_hsubst : PowerSeries.HasSubst deviation) :
    formalBinomialPow 0 deviation = 1 := by
  unfold formalBinomialPow
  rw [PowerSeries.binomialSeries_zero]
  change PowerSeries.subst deviation (PowerSeries.C (R := ℝ) 1) = 1
  simpa using PowerSeries.subst_C (a := deviation) (1 : ℝ)

theorem formalBinomialPow_zero_deviation (parameter : ℝ) :
    formalBinomialPow parameter (0 : ℝ⟦X⟧) = 1 := by
  unfold formalBinomialPow
  rw [PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem formalBinomialPow_one_parameter
    {deviation : ℝ⟦X⟧} (hsubst : PowerSeries.HasSubst deviation) :
    formalBinomialPow 1 deviation = 1 + deviation := by
  unfold formalBinomialPow
  rw [show (1 : ℝ) = (1 : ℕ) by norm_num,
    PowerSeries.binomialSeries_nat, pow_one]
  rw [PowerSeries.subst_add hsubst]
  change PowerSeries.subst deviation (PowerSeries.C (R := ℝ) 1) +
      PowerSeries.subst deviation PowerSeries.X = 1 + deviation
  rw [PowerSeries.subst_C, PowerSeries.subst_X hsubst]
  simp

theorem formalBinomialPow_mul_neg
    (parameter : ℝ) {deviation : ℝ⟦X⟧}
    (hsubst : PowerSeries.HasSubst deviation) :
    formalBinomialPow parameter deviation *
        formalBinomialPow (-parameter) deviation = 1 := by
  rw [← formalBinomialPow_add_parameters parameter (-parameter) hsubst]
  rw [add_neg_cancel, formalBinomialPow_zero_parameter hsubst]

theorem formalBinomialPow_neg_mul
    (parameter : ℝ) {deviation : ℝ⟦X⟧}
    (hsubst : PowerSeries.HasSubst deviation) :
    formalBinomialPow (-parameter) deviation *
        formalBinomialPow parameter deviation = 1 := by
  rw [mul_comm, formalBinomialPow_mul_neg parameter hsubst]

theorem right_inverse_unique {left right unit : ℝ⟦X⟧}
    (hleft : left * unit = 1) (hright : right * unit = 1) :
    left = right := by
  calc
    left = left * 1 := by ring
    _ = left * (unit * right) := by rw [mul_comm unit right, hright]
    _ = (left * unit) * right := by ring
    _ = right := by rw [hleft, one_mul]

theorem X_sq_hasSubst :
    PowerSeries.HasSubst (PowerSeries.X ^ 2 : ℝ⟦X⟧) :=
  PowerSeries.HasSubst.X_pow (by omega)

theorem realSubstitutionDenominator_eq_formalBinomialPow_neg_one :
    realSubstitutionDenominator =
      formalBinomialPow (-1) (PowerSeries.X ^ 2 : ℝ⟦X⟧) := by
  apply right_inverse_unique
    (unit := (1 + PowerSeries.X ^ 2 : ℝ⟦X⟧))
  · exact realSubstitutionDenominator_mul_one_add_X_sq
  · rw [← formalBinomialPow_one_parameter X_sq_hasSubst]
    exact formalBinomialPow_neg_mul 1 X_sq_hasSubst

theorem denominatorUnitDeviation_product_X_sq :
    productDeviation denominatorUnitDeviation
        (PowerSeries.X ^ 2 : ℝ⟦X⟧) = 0 := by
  unfold productDeviation denominatorUnitDeviation
  have hunit := realSubstitutionDenominator_mul_one_add_X_sq
  linear_combination hunit

theorem denominatorUnitDeviation_hasSubst :
    PowerSeries.HasSubst denominatorUnitDeviation :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    denominatorUnitDeviation_constantCoeff

theorem formalBinomialPow_denominatorUnit
    (parameter : ℝ) :
    formalBinomialPow parameter denominatorUnitDeviation =
      formalBinomialPow (-parameter) (PowerSeries.X ^ 2 : ℝ⟦X⟧) := by
  have hproduct := formalBinomialPow_product parameter
    denominatorUnitDeviation_constantCoeff
      (by simp : PowerSeries.constantCoeff (PowerSeries.X ^ 2 : ℝ⟦X⟧) = 0)
  rw [denominatorUnitDeviation_product_X_sq,
    formalBinomialPow_zero_deviation] at hproduct
  apply right_inverse_unique
    (unit := formalBinomialPow parameter (PowerSeries.X ^ 2 : ℝ⟦X⟧))
  · exact hproduct.symm
  · exact formalBinomialPow_neg_mul parameter X_sq_hasSubst

theorem formalBinomialPow_X_sq_eq_subst_binomial
    (parameter : ℝ) :
    formalBinomialPow parameter (PowerSeries.X ^ 2 : ℝ⟦X⟧) =
      PowerSeries.subst (PowerSeries.X ^ 2)
        (PowerSeries.binomialSeries ℝ parameter) := rfl

theorem formalBinomialPow_secondaryLinear
    (parameter : ℝ) (alphabetSize : ℕ) :
    formalBinomialPow parameter (secondaryLinearDeviation alphabetSize) =
      rescaledBinomialSeries parameter (fixedRankPreimage alphabetSize) := by
  unfold secondaryLinearDeviation
  exact formalBinomialPow_linearDeviation parameter
    (fixedRankPreimage alphabetSize)

/-- Fully explicit analytic multiplier:
`(1-rho X)^parameter (1+X^2)^(-(parameter+1))`. -/
theorem ribbonSingularAnalyticMultiplier_explicit
    (parameter : ℝ) (alphabetSize : ℕ) :
    ribbonSingularAnalyticMultiplier parameter alphabetSize =
      rescaledBinomialSeries parameter (fixedRankPreimage alphabetSize) *
        PowerSeries.subst (PowerSeries.X ^ 2)
          (PowerSeries.binomialSeries ℝ (-(parameter + 1))) := by
  unfold ribbonSingularAnalyticMultiplier
  rw [formalBinomialPow_secondaryLinear,
    formalBinomialPow_denominatorUnit,
    realSubstitutionDenominator_eq_formalBinomialPow_neg_one]
  rw [← formalBinomialPow_X_sq_eq_subst_binomial]
  have hcombine :=
    formalBinomialPow_add_parameters (-1) (-parameter) X_sq_hasSubst
  rw [show (-1 : ℝ) + -parameter = -(parameter + 1) by ring] at hcombine
  rw [hcombine]
  ring

end FibonacciRibbonKernel
