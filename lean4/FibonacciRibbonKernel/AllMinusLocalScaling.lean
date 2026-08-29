import FibonacciRibbonKernel.CosineCubeReflection

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable def allMinusAngleLocalNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (anglePositiveLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        allMinusAngleWeight dimension angles)
    angles

noncomputable def allMinusAngleLocalNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    allMinusAngleLocalNormalizedIntegrand dimension index angles

theorem continuous_allMinusAngleWeight (dimension : ℕ) :
    Continuous (allMinusAngleWeight dimension) := by
  unfold allMinusAngleWeight
  apply continuous_finsetProd
  intro coordinate _hcoordinate
  exact continuous_const.sub (Real.continuous_cos.comp
    (continuous_apply coordinate))

theorem stronglyMeasurable_allMinusAngleLocalNormalizedIntegrand
    (dimension index : ℕ) :
    StronglyMeasurable
      (allMinusAngleLocalNormalizedIntegrand dimension index) := by
  unfold allMinusAngleLocalNormalizedIntegrand
  exact (((continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale dimension)).div_const _)).mul
        (continuous_allMinusAngleWeight dimension)).stronglyMeasurable.indicator
          (measurableSet_anglePositiveLocalDomain dimension))

theorem allMinusAngleWeight_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    allMinusAngleWeight dimension
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      allMinusScaledWeight dimension index coordinates := by
  rw [coordinateInverseSqrt_apply]
  unfold allMinusAngleWeight allMinusScaledWeight
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  simp

theorem allMinusAngleLocalNormalizedIntegrand_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    allMinusAngleLocalNormalizedIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      allMinusLocalRescaledIntegrand dimension index coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [allMinusAngleLocalNormalizedIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff
          dimension index coordinates).2 hdomain),
      allMinusLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt, allMinusAngleWeight_inverseSqrt]
    unfold normalizedFibonacciCosineKernel
    rfl
  · rw [allMinusAngleLocalNormalizedIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff
          dimension index coordinates).1 hdomain),
      allMinusLocalRescaledIntegrand, Set.indicator_of_notMem hdomain]

theorem allMinusLocalScalingIntegral_identity
    (dimension index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ dimension *
        allMinusAngleLocalNormalizedIntegral dimension index =
      ∫ coordinates : Fin dimension → ℝ,
        allMinusLocalRescaledIntegrand dimension index coordinates := by
  let scaleMap := coordinateScalarLinearMap dimension
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := allMinusAngleLocalNormalizedIntegrand dimension index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension _).aemeasurable
      (stronglyMeasurable_allMinusAngleLocalNormalizedIntegrand
        dimension index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume] at hmap
  rw [integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ dimension := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold allMinusAngleLocalNormalizedIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      allMinusAngleLocalNormalizedIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      allMinusLocalRescaledIntegrand dimension index by
    funext coordinates
    exact allMinusAngleLocalNormalizedIntegrand_inverseSqrt
      dimension index coordinates] at hmap
  exact hmap

theorem tendsto_allMinusAngleLocalNormalizedIntegral
    (dimension : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    Tendsto
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          allMinusAngleLocalNormalizedIntegral dimension index)
      atTop (nhds 0) := by
  rw [show
    (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        allMinusAngleLocalNormalizedIntegral dimension index) =
      fun index : ℕ => ∫ coordinates,
        allMinusLocalRescaledIntegrand dimension index coordinates by
    funext index
    exact allMinusLocalScalingIntegral_identity dimension index]
  exact tendsto_integral_allMinusLocalRescaledIntegrand dimension hdimension

end FibonacciRibbonKernel
