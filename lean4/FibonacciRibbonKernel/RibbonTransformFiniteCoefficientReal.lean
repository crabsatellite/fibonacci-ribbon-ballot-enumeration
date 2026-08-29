import FibonacciRibbonKernel.FibonacciKernelSeriesReal

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators

theorem coeff_ribbonSubstitutionR_pow_eq_zero_of_lt
    {degree coefficient : ℕ} (hlt : coefficient < degree) :
    PowerSeries.coeff coefficient (ribbonSubstitutionR ^ degree) = 0 := by
  rw [ribbonSubstitutionR_eq, mul_pow,
    PowerSeries.coeff_X_pow_mul']
  simp [hlt.not_ge]

theorem coeff_subst_ribbonSubstitutionR_eq_sum_range
    (series : ℝ⟦X⟧) {coefficient bound : ℕ} (hbound : coefficient ≤ bound) :
    PowerSeries.coeff coefficient
        (PowerSeries.subst ribbonSubstitutionR series) =
      ∑ degree ∈ Finset.range (bound + 1),
        PowerSeries.coeff degree series *
          PowerSeries.coeff coefficient (ribbonSubstitutionR ^ degree) := by
  rw [PowerSeries.coeff_subst' ribbonSubstitutionR_hasSubst]
  have hsupport : Function.support (fun degree : ℕ =>
      PowerSeries.coeff degree series •
        PowerSeries.coeff coefficient (ribbonSubstitutionR ^ degree)) ⊆
      (Finset.range (bound + 1) : Set ℕ) := by
    intro degree hdegree
    simp only [Function.mem_support, smul_eq_mul] at hdegree
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hnot
    have hlt : coefficient < degree := by omega
    rw [coeff_ribbonSubstitutionR_pow_eq_zero_of_lt hlt, mul_zero] at hdegree
    exact hdegree rfl
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  rfl

noncomputable def ribbonTransformBasisWeightR
    (coefficient degree : ℕ) : ℝ :=
  PowerSeries.coeff coefficient
    (ribbonInverseQuadraticR * ribbonSubstitutionR ^ degree)

theorem coeff_ribbonTransformR
    (series : ℝ⟦X⟧) (coefficient : ℕ) :
    PowerSeries.coeff coefficient
        (ribbonInverseQuadraticR *
          PowerSeries.subst ribbonSubstitutionR series) =
      ∑ degree ∈ Finset.range (coefficient + 1),
        PowerSeries.coeff degree series *
          ribbonTransformBasisWeightR coefficient degree := by
  rw [PowerSeries.coeff_mul]
  have hrewrite : ∀ pair : ℕ × ℕ,
      pair ∈ (Finset.HasAntidiagonal.antidiagonal coefficient :
        Finset (ℕ × ℕ)) →
      PowerSeries.coeff pair.2
          (PowerSeries.subst ribbonSubstitutionR series) =
        ∑ degree ∈ Finset.range (coefficient + 1),
          PowerSeries.coeff degree series *
            PowerSeries.coeff pair.2 (ribbonSubstitutionR ^ degree) := by
    intro pair hpair
    apply coeff_subst_ribbonSubstitutionR_eq_sum_range
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    omega
  rw [Finset.sum_congr rfl (fun pair hpair => by rw [hrewrite pair hpair])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro degree _hdegree
  unfold ribbonTransformBasisWeightR
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair _hpair
  ring

theorem fibonacciScaleKernel_eq_finite_transform
    (scale : ℝ) (coefficient : ℕ) :
    fibonacciScaleKernel scale coefficient =
      ∑ degree ∈ Finset.range (coefficient + 1),
        scale ^ degree * ribbonTransformBasisWeightR coefficient degree := by
  have hcoeff := congrArg (PowerSeries.coeff coefficient)
    (ribbonTransform_geometricScaleSeriesR scale)
  rw [fibonacciScaleSeriesR_coeff, coeff_ribbonTransformR] at hcoeff
  simpa only [geometricScaleSeriesR_coeff] using hcoeff.symm

end FibonacciRibbonKernel
