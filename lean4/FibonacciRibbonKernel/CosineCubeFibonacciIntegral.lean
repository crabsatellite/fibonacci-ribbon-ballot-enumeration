import FibonacciRibbonKernel.RibbonTransformFiniteCoefficientReal

namespace FibonacciRibbonKernel

open MeasureTheory PowerSeries
open scoped BigOperators

noncomputable def cosineCubeFibonacciIntegrand
    (plusPower minusPower power : ℕ)
    (angles : Fin (plusPower + minusPower) → ℝ) : ℝ :=
  fibonacciScaleKernel (cosineCubeScale angles) power *
    cosineCubeWeight plusPower minusPower angles

noncomputable def cosineCubeFibonacciIntegral
    (plusPower minusPower power : ℕ) : ℝ :=
  (1 / Real.pi) ^ (plusPower + minusPower) *
    ∫ angles : Fin (plusPower + minusPower) → ℝ,
      cosineCubeFibonacciIntegrand plusPower minusPower power angles
      ∂cosineCubeProductMeasure (plusPower + minusPower)

noncomputable def cosineCubeMomentSeriesR
    (plusPower minusPower : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk (cosineCubeIntegralMoment plusPower minusPower)

@[simp] theorem cosineCubeMomentSeriesR_coeff
    (plusPower minusPower power : ℕ) :
    PowerSeries.coeff power (cosineCubeMomentSeriesR plusPower minusPower) =
      cosineCubeIntegralMoment plusPower minusPower power := by
  simp [cosineCubeMomentSeriesR]

noncomputable def cosineCubeFibonacciTerm
    (plusPower minusPower power degree : ℕ)
    (angles : Fin (plusPower + minusPower) → ℝ) : ℝ :=
  ribbonTransformBasisWeightR power degree *
    cosineCubeRawIntegrand plusPower minusPower degree angles

theorem integrable_cosineCubeFibonacciTerm
    (plusPower minusPower power degree : ℕ) :
    Integrable (cosineCubeFibonacciTerm plusPower minusPower power degree)
      (cosineCubeProductMeasure (plusPower + minusPower)) := by
  unfold cosineCubeFibonacciTerm
  exact (integrable_cosineCubeRawIntegrand
    plusPower minusPower degree).const_mul _

theorem cosineCubeFibonacciIntegrand_eq_finite_sum
    (plusPower minusPower power : ℕ)
    (angles : Fin (plusPower + minusPower) → ℝ) :
    cosineCubeFibonacciIntegrand plusPower minusPower power angles =
      ∑ degree ∈ Finset.range (power + 1),
        cosineCubeFibonacciTerm plusPower minusPower power degree angles := by
  unfold cosineCubeFibonacciIntegrand
  rw [fibonacciScaleKernel_eq_finite_transform]
  unfold cosineCubeFibonacciTerm cosineCubeRawIntegrand
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro degree _hdegree
  ring

theorem cosineCubeFibonacciIntegral_eq_finite_transform
    (plusPower minusPower power : ℕ) :
    cosineCubeFibonacciIntegral plusPower minusPower power =
      ∑ degree ∈ Finset.range (power + 1),
        cosineCubeIntegralMoment plusPower minusPower degree *
          ribbonTransformBasisWeightR power degree := by
  unfold cosineCubeFibonacciIntegral cosineCubeIntegralMoment
  calc
    (1 / Real.pi) ^ (plusPower + minusPower) *
        (∫ angles : Fin (plusPower + minusPower) → ℝ,
          cosineCubeFibonacciIntegrand plusPower minusPower power angles
          ∂cosineCubeProductMeasure (plusPower + minusPower)) =
      (1 / Real.pi) ^ (plusPower + minusPower) *
        (∫ angles : Fin (plusPower + minusPower) → ℝ,
          ∑ degree ∈ Finset.range (power + 1),
            cosineCubeFibonacciTerm plusPower minusPower power degree angles
          ∂cosineCubeProductMeasure (plusPower + minusPower)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with angles
      exact cosineCubeFibonacciIntegrand_eq_finite_sum
        plusPower minusPower power angles
    _ = (1 / Real.pi) ^ (plusPower + minusPower) *
        ∑ degree ∈ Finset.range (power + 1),
          ∫ angles : Fin (plusPower + minusPower) → ℝ,
            cosineCubeFibonacciTerm plusPower minusPower power degree angles
            ∂cosineCubeProductMeasure (plusPower + minusPower) := by
      congr 1
      rw [integral_finsetSum]
      intro degree _hdegree
      exact integrable_cosineCubeFibonacciTerm
        plusPower minusPower power degree
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro degree _hdegree
      unfold cosineCubeFibonacciTerm
      rw [integral_const_mul]
      ring

theorem cosineCubeFibonacciIntegral_eq_ribbonTransformCoeff
    (plusPower minusPower power : ℕ) :
    cosineCubeFibonacciIntegral plusPower minusPower power =
      PowerSeries.coeff power
        (ribbonInverseQuadraticR *
          PowerSeries.subst ribbonSubstitutionR
            (cosineCubeMomentSeriesR plusPower minusPower)) := by
  rw [cosineCubeFibonacciIntegral_eq_finite_transform,
    coeff_ribbonTransformR]
  simp only [cosineCubeMomentSeriesR_coeff]

end FibonacciRibbonKernel
