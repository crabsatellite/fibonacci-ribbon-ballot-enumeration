import FibonacciRibbonKernel.FormalBinomialMultiplicative

namespace FibonacciRibbonKernel

open PowerSeries

/-!
# Exact formal factorization of the ribbon singular pullback

This file transports the integral substitution series from `ℤ` to `ℝ` and
proves the literal factorization

`1 - n w(X) = (1-alpha X)(1-rho X)/(1+X^2)`

inside the formal power-series ring.  It then feeds that factorization into
the kernel proof of formal-binomial base multiplicativity.
-/

noncomputable def realSubstitutionDenominator : ℝ⟦X⟧ :=
  PowerSeries.map (Int.castRingHom ℝ) substitutionDenominator

noncomputable def realRibbonSubstitution : ℝ⟦X⟧ :=
  PowerSeries.X * realSubstitutionDenominator

theorem realSubstitutionDenominator_mul_one_add_X_sq :
    realSubstitutionDenominator * (1 + PowerSeries.X ^ 2) = 1 := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℝ))
    substitutionDenominator_mul_one_add_X_sq
  simpa [realSubstitutionDenominator, map_mul, map_add,
    PowerSeries.map_X] using hmap

theorem realSubstitutionDenominator_constantCoeff :
    PowerSeries.constantCoeff realSubstitutionDenominator = 1 := by
  have hunit := realSubstitutionDenominator_mul_one_add_X_sq
  have hconstant := congrArg PowerSeries.constantCoeff hunit
  simpa using hconstant

theorem realRibbonSubstitution_constantCoeff :
    PowerSeries.constantCoeff realRibbonSubstitution = 0 := by
  simp [realRibbonSubstitution]

theorem realRibbonSubstitution_hasSubst :
    PowerSeries.HasSubst realRibbonSubstitution :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    realRibbonSubstitution_constantCoeff

/-- Formal version of the leading factorization used in the manuscript. -/
theorem one_sub_size_mul_realRibbonSubstitution
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    1 - PowerSeries.C (alphabetSize : ℝ) * realRibbonSubstitution =
      (1 - PowerSeries.C (fixedRankGrowth alphabetSize) * PowerSeries.X) *
        (1 - PowerSeries.C (fixedRankPreimage alphabetSize) * PowerSeries.X) *
          realSubstitutionDenominator := by
  let alpha := fixedRankGrowth alphabetSize
  let rho := fixedRankPreimage alphabetSize
  have hsum : alpha + rho = (alphabetSize : ℝ) :=
    fixedRankGrowth_add_preimage alphabetSize
  have hmul : alpha * rho = 1 :=
    fixedRankGrowth_mul_preimage alphabetSize hsize
  have hCsum :
      PowerSeries.C (alphabetSize : ℝ) =
        PowerSeries.C alpha + PowerSeries.C rho := by
    rw [← map_add, hsum]
  have hCmul : PowerSeries.C alpha * PowerSeries.C rho = 1 := by
    rw [← map_mul, hmul, map_one]
  rw [realRibbonSubstitution]
  calc
    1 - PowerSeries.C (alphabetSize : ℝ) *
          (PowerSeries.X * realSubstitutionDenominator) =
        realSubstitutionDenominator * (1 + PowerSeries.X ^ 2) -
          PowerSeries.C (alphabetSize : ℝ) * PowerSeries.X *
            realSubstitutionDenominator := by
              rw [realSubstitutionDenominator_mul_one_add_X_sq]
              ring
    _ = (1 - PowerSeries.C alpha * PowerSeries.X) *
        (1 - PowerSeries.C rho * PowerSeries.X) *
          realSubstitutionDenominator := by
            rw [hCsum]
            linear_combination
              -PowerSeries.X ^ 2 * realSubstitutionDenominator * hCmul

/-- Deviation of the leading linear factor. -/
noncomputable def leadingLinearDeviation (alphabetSize : ℕ) : ℝ⟦X⟧ :=
  -(PowerSeries.C (fixedRankGrowth alphabetSize) * PowerSeries.X)

/-- Deviation of the secondary equal-modulus factor. -/
noncomputable def secondaryLinearDeviation (alphabetSize : ℕ) : ℝ⟦X⟧ :=
  -(PowerSeries.C (fixedRankPreimage alphabetSize) * PowerSeries.X)

/-- Deviation of the rational denominator unit. -/
noncomputable def denominatorUnitDeviation : ℝ⟦X⟧ :=
  realSubstitutionDenominator - 1

theorem leadingLinearDeviation_constantCoeff (alphabetSize : ℕ) :
    PowerSeries.constantCoeff (leadingLinearDeviation alphabetSize) = 0 := by
  simp [leadingLinearDeviation]

theorem secondaryLinearDeviation_constantCoeff (alphabetSize : ℕ) :
    PowerSeries.constantCoeff (secondaryLinearDeviation alphabetSize) = 0 := by
  simp [secondaryLinearDeviation]

theorem denominatorUnitDeviation_constantCoeff :
    PowerSeries.constantCoeff denominatorUnitDeviation = 0 := by
  simp [denominatorUnitDeviation, realSubstitutionDenominator_constantCoeff]

noncomputable def ribbonLeadingProductDeviation
    (alphabetSize : ℕ) : ℝ⟦X⟧ :=
  productDeviation
    (productDeviation (leadingLinearDeviation alphabetSize)
      (secondaryLinearDeviation alphabetSize))
    denominatorUnitDeviation

theorem ribbonLeadingProductDeviation_eq
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonLeadingProductDeviation alphabetSize =
      -(PowerSeries.C (alphabetSize : ℝ) * realRibbonSubstitution) := by
  have hfactor := one_sub_size_mul_realRibbonSubstitution alphabetSize hsize
  unfold ribbonLeadingProductDeviation productDeviation
  unfold leadingLinearDeviation secondaryLinearDeviation
  unfold denominatorUnitDeviation
  linear_combination -hfactor

/-- Exact three-factor formal-binomial decomposition of the pulled-back
leading singular model. -/
theorem formalBinomialPow_ribbonLeadingProduct
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    formalBinomialPow parameter
        (-(PowerSeries.C (alphabetSize : ℝ) * realRibbonSubstitution)) =
      formalBinomialPow parameter (leadingLinearDeviation alphabetSize) *
      formalBinomialPow parameter (secondaryLinearDeviation alphabetSize) *
          formalBinomialPow parameter denominatorUnitDeviation := by
  rw [← ribbonLeadingProductDeviation_eq alphabetSize hsize]
  unfold ribbonLeadingProductDeviation
  rw [formalBinomialPow_product parameter
    (productDeviation_constantCoeff
      (leadingLinearDeviation_constantCoeff alphabetSize)
      (secondaryLinearDeviation_constantCoeff alphabetSize))
    denominatorUnitDeviation_constantCoeff]
  rw [formalBinomialPow_product parameter
    (leadingLinearDeviation_constantCoeff alphabetSize)
    (secondaryLinearDeviation_constantCoeff alphabetSize)]

theorem formalBinomialPow_linearDeviation
    (parameter scale : ℝ) :
    formalBinomialPow parameter
        (-(PowerSeries.C scale * PowerSeries.X)) =
      rescaledBinomialSeries parameter scale := by
  unfold formalBinomialPow rescaledBinomialSeries
  rw [PowerSeries.rescale_eq_subst]
  congr 1
  simp [smul_eq_C_mul]

noncomputable def ribbonSingularAnalyticMultiplier
    (parameter : ℝ) (alphabetSize : ℕ) : ℝ⟦X⟧ :=
  realSubstitutionDenominator *
    formalBinomialPow parameter (secondaryLinearDeviation alphabetSize) *
      formalBinomialPow parameter denominatorUnitDeviation

/-- Exact factorization into the leading singular binomial series and a
multiplier analytic at the leading preimage. -/
theorem ribbonPulledBinomial_factorization
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
      realSubstitutionDenominator *
        formalBinomialPow parameter
          (-(PowerSeries.C (alphabetSize : ℝ) * realRibbonSubstitution)) =
      rescaledBinomialSeries parameter (fixedRankGrowth alphabetSize) *
        ribbonSingularAnalyticMultiplier parameter alphabetSize := by
  rw [formalBinomialPow_ribbonLeadingProduct parameter alphabetSize hsize]
  unfold leadingLinearDeviation
  rw [formalBinomialPow_linearDeviation]
  unfold ribbonSingularAnalyticMultiplier
  ring

end FibonacciRibbonKernel
