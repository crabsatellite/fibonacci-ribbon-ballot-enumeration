import FibonacciRibbonKernel.GeneralOddGeometricLimit
import FibonacciRibbonKernel.RankSixEvenFullLimit

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

noncomputable def generalEvenAngleLocalIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (anglePositiveLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        evenWeylAngleWeight dimension angles)
    angles

noncomputable def generalEvenAngleLocalIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenAngleLocalIntegrand dimension index angles

theorem generalEvenAngleWeight_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    evenWeylAngleWeight dimension
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      evenScaledWeylWeight dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) := by
  have hscale := evenScaledWeylWeight_eq dimension index coordinates
  have hnonzero : (index + 1 : ℝ) ^ (dimension * (dimension - 1)) ≠ 0 := by
    positivity
  apply (eq_div_iff hnonzero).2
  rw [hscale]
  ring

theorem generalEvenAngleLocalIntegrand_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    generalEvenAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      generalEvenWeylLocalRescaledIntegrand dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [generalEvenAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).2
          hdomain),
      generalEvenWeylLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt, generalEvenAngleWeight_inverseSqrt]
    unfold normalizedFibonacciCosineKernel
    ring
  · rw [generalEvenAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).1
          hdomain),
      generalEvenWeylLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem stronglyMeasurable_generalEvenAngleLocalIntegrand
    (dimension index : ℕ) :
    StronglyMeasurable (generalEvenAngleLocalIntegrand dimension index) := by
  unfold generalEvenAngleLocalIntegrand
  exact (((continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale dimension)).div_const _)).mul
        (continuous_evenWeylAngleWeight dimension)).stronglyMeasurable.indicator
          (measurableSet_anglePositiveLocalDomain dimension))

theorem generalEvenLocalScalingIntegral_identity
    (dimension index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenAngleLocalIntegral dimension index =
      ∫ coordinates : Fin dimension → ℝ,
        generalEvenWeylLocalRescaledIntegrand dimension index coordinates := by
  let scaleMap := coordinateScalarLinearMap dimension
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := generalEvenAngleLocalIntegrand dimension index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension _).aemeasurable
      (stronglyMeasurable_generalEvenAngleLocalIntegrand
        dimension index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ dimension := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold generalEvenAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      generalEvenAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
    fun coordinates =>
      generalEvenWeylLocalRescaledIntegrand dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) by
      funext coordinates
      exact generalEvenAngleLocalIntegrand_inverseSqrt
        dimension index coordinates] at hmap
  rw [integral_div] at hmap
  have hnonzero : (index + 1 : ℝ) ^
      (dimension * (dimension - 1)) ≠ 0 := by positivity
  field_simp [hnonzero] at hmap ⊢
  exact hmap

theorem tendsto_generalEvenAngleLocalIntegral
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenAngleLocalIntegral dimension index)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalEvenWeylLocalLimitIntegrand dimension coordinates)) := by
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenAngleLocalIntegral dimension index) =
    fun index => ∫ coordinates : Fin dimension → ℝ,
      generalEvenWeylLocalRescaledIntegrand dimension index coordinates by
      funext index
      exact generalEvenLocalScalingIntegral_identity dimension index]
  exact tendsto_integral_generalEvenWeylLocalRescaledIntegrand dimension (by
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    linarith)

noncomputable def generalEvenMinusScaledWeight
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  scaledCosineVandermondeWeight dimension index coordinates *
    allMinusScaledWeight dimension index coordinates

noncomputable def generalEvenMinusLocalRescaledIntegrand
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  (positiveLocalScaledDomain dimension index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        normalizedFibonacciCosineKernel coordinates index *
        generalEvenMinusScaledWeight dimension index coordinates)
    coordinates

theorem generalEvenMinusScaledWeight_nonneg
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    0 ≤ generalEvenMinusScaledWeight dimension index coordinates := by
  unfold generalEvenMinusScaledWeight scaledCosineVandermondeWeight
  exact mul_nonneg (by positivity)
    (allMinusScaledWeight_nonneg dimension index coordinates)

theorem generalEvenMinusScaledWeight_le_global
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    generalEvenMinusScaledWeight dimension index coordinates ≤
      (2 : ℝ) ^ dimension *
        weylGlobalPolynomial dimension coordinates ^
          (weylSeparableExponent dimension 0) := by
  unfold generalEvenMinusScaledWeight weylSeparableExponent
  have hv := scaledCosineVandermondeWeight_le_global
    dimension index coordinates
  have hm := allMinusScaledWeight_le_two_pow dimension index coordinates
  have hmNonneg := allMinusScaledWeight_nonneg dimension index coordinates
  have h := mul_le_mul hv hm hmNonneg
    (pow_nonneg (le_trans (by norm_num)
      (one_le_weylGlobalPolynomial dimension coordinates)) _)
  simpa [Nat.add_zero, mul_comm] using h

theorem tendsto_generalEvenMinusLocalRescaledIntegrand_zero
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      generalEvenMinusLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds 0) := by
  have hdimensionPos : 0 < dimension := by omega
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain (by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith) coordinates horthant
    have hkernel := tendsto_normalizedFibonacciCosineKernel (by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith) coordinates
    have hweight : Tendsto (fun index =>
        generalEvenMinusScaledWeight dimension index coordinates)
        atTop (nhds 0) := by
      unfold generalEvenMinusScaledWeight
      simpa using (tendsto_scaledCosineVandermondeWeight
        dimension coordinates).mul
          (tendsto_allMinusScaledWeight hdimensionPos coordinates)
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    simpa only [mul_zero] using hproduct.congr' (by
      filter_upwards [hlocal] with index hindex
      rw [generalEvenMinusLocalRescaledIntegrand,
        Set.indicator_of_mem hindex])
  · have hnot : ∃ coordinate : Fin dimension,
        coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _ => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveLocalScaledDomain dimension index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    rw [show (fun index : ℕ =>
        generalEvenMinusLocalRescaledIntegrand dimension index coordinates) =
      fun _ => 0 by
        funext index
        rw [generalEvenMinusLocalRescaledIntegrand,
          Set.indicator_of_notMem (houtside index)]]
    exact tendsto_const_nhds

theorem aestronglyMeasurable_generalEvenMinusLocalRescaledIntegrand
    (dimension index : ℕ) (hdimension : 2 ≤ dimension) :
    AEStronglyMeasurable
      (generalEvenMinusLocalRescaledIntegrand dimension index) := by
  unfold generalEvenMinusLocalRescaledIntegrand generalEvenMinusScaledWeight
  exact (((continuous_const.mul
    (continuous_normalizedFibonacciCosineKernel dimension index (by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith))).mul
      ((continuous_scaledCosineVandermondeWeight dimension index).mul
        (continuous_allMinusScaledWeight dimension index))).stronglyMeasurable.indicator
          (measurableSet_positiveLocalScaledDomain dimension index)).aestronglyMeasurable

theorem norm_generalEvenMinusLocalRescaledIntegrand_le
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖generalEvenMinusLocalRescaledIntegrand dimension index coordinates‖ ≤
      generalEvenWeylLocalDominating dimension coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [generalEvenMinusLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, Real.norm_eq_abs, abs_of_nonneg]
    · have hcoordinate : ∀ coordinate,
          |coordinates coordinate| ≤
            Real.pi * Real.sqrt (index + 1 : ℝ) := by
        intro coordinate
        have hmem := hdomain.1 coordinate (Set.mem_univ coordinate)
        rw [abs_of_pos hmem.1]
        exact hmem.2
      have hdimreal : 2 < (2 * dimension : ℝ) := by
        have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
        linarith
      have hkernel := normalizedFibonacciCosineKernel_le_local_gaussian
        hdimreal coordinates hcoordinate hdomain.2
      have hweight := generalEvenMinusScaledWeight_le_global
        dimension index coordinates
      have hkernelNonneg := normalizedFibonacciCosineKernel_nonneg
        hdimreal coordinates
        ((cosineScaleMidpoint_gt_two hdimreal).trans_le hdomain.2)
      have hweightNonneg := generalEvenMinusScaledWeight_nonneg
        dimension index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg
        (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ dimension by positivity)
      calc
        (1 / Real.pi) ^ dimension *
            normalizedFibonacciCosineKernel coordinates index *
              generalEvenMinusScaledWeight dimension index coordinates ≤
          (1 / Real.pi) ^ dimension *
            ((Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
                Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4) *
              Real.exp (-(4 / (Real.pi ^ 2 *
                Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
                  ∑ coordinate, coordinates coordinate ^ 2)) *
              ((2 : ℝ) ^ dimension *
                weylGlobalPolynomial dimension coordinates ^
                  (weylSeparableExponent dimension 0))) := by
                    simpa only [mul_assoc] using hscaled
        _ = generalEvenWeylLocalDominating dimension coordinates := by
          unfold generalEvenWeylLocalDominating
            generalEvenWeylDominatingConstant weylSeparableDominating
            allPlusGaussianCoefficient
          rw [← gaussianGlobalPolynomial_eq_separable]
          ring
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (normalizedFibonacciCosineKernel_nonneg (by
            have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
            linarith) coordinates
            ((cosineScaleMidpoint_gt_two (by
              have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
              linarith)).trans_le hdomain.2)))
        (generalEvenMinusScaledWeight_nonneg dimension index coordinates)
  · rw [generalEvenMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold generalEvenWeylLocalDominating weylSeparableDominating
      generalEvenWeylDominatingConstant
    have hdimreal : 2 < (2 * dimension : ℝ) := by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith
    have hroot : 0 < Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
      apply Real.sqrt_pos.2
      nlinarith
    have hmid := cosineScaleMidpoint_gt_two hdimreal
    have hmidRoot : 0 < Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4) := by
      apply Real.sqrt_pos.2
      nlinarith
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _)
          (div_nonneg hroot.le hmidRoot.le))
        (pow_nonneg (by norm_num) _)
    · apply Finset.prod_nonneg
      intro coordinate hcoordinate
      unfold weylCoordinateDominating
      positivity

theorem tendsto_integral_generalEvenMinusLocalRescaled_zero
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index => ∫ coordinates : Fin dimension → ℝ,
      generalEvenMinusLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds 0) := by
  simpa using tendsto_integral_of_dominated_convergence
    (generalEvenWeylLocalDominating dimension)
    (fun index =>
      aestronglyMeasurable_generalEvenMinusLocalRescaledIntegrand
        dimension index hdimension)
    (integrable_generalEvenWeylLocalDominating dimension (by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith))
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_generalEvenMinusLocalRescaledIntegrand_le
        hdimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_generalEvenMinusLocalRescaledIntegrand_zero
        hdimension coordinates)

noncomputable def generalEvenMinusAngleLocalIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (anglePositiveLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        (cosineVandermondeWeight dimension angles *
          allMinusAngleWeight dimension angles))
    angles

noncomputable def generalEvenMinusAngleLocalIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenMinusAngleLocalIntegrand dimension index angles

theorem generalEvenMinusAngleWeight_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    cosineVandermondeWeight dimension
          (coordinateScalarLinearMap dimension
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) *
        allMinusAngleWeight dimension
          (coordinateScalarLinearMap dimension
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      generalEvenMinusScaledWeight dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) := by
  have hscale := scaledCosineVandermondeWeight_eq
    dimension index coordinates
  rw [weylPairScalingExponent_eq] at hscale
  unfold generalEvenMinusScaledWeight
  rw [allMinusAngleWeight_inverseSqrt]
  have hnonzero : (index + 1 : ℝ) ^
      (dimension * (dimension - 1)) ≠ 0 := by positivity
  apply (eq_div_iff hnonzero).2
  rw [hscale]
  ring

theorem generalEvenMinusAngleLocalIntegrand_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    generalEvenMinusAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      generalEvenMinusLocalRescaledIntegrand dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [generalEvenMinusAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).2
          hdomain),
      generalEvenMinusLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt,
      generalEvenMinusAngleWeight_inverseSqrt]
    unfold normalizedFibonacciCosineKernel
    ring
  · rw [generalEvenMinusAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).1
          hdomain),
      generalEvenMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem stronglyMeasurable_generalEvenMinusAngleLocalIntegrand
    (dimension index : ℕ) :
    StronglyMeasurable
      (generalEvenMinusAngleLocalIntegrand dimension index) := by
  unfold generalEvenMinusAngleLocalIntegrand
  exact (((continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale dimension)).div_const _)).mul
      ((continuous_cosineVandermondeWeight dimension).mul
        (continuous_allMinusAngleWeight dimension))).stronglyMeasurable.indicator
          (measurableSet_anglePositiveLocalDomain dimension))

theorem generalEvenMinusLocalScalingIntegral_identity
    (dimension index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenMinusAngleLocalIntegral dimension index =
      ∫ coordinates : Fin dimension → ℝ,
        generalEvenMinusLocalRescaledIntegrand dimension index coordinates := by
  let scaleMap := coordinateScalarLinearMap dimension
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := generalEvenMinusAngleLocalIntegrand dimension index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension _).aemeasurable
      (stronglyMeasurable_generalEvenMinusAngleLocalIntegrand
        dimension index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ dimension := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold generalEvenMinusAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      generalEvenMinusAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
    fun coordinates =>
      generalEvenMinusLocalRescaledIntegrand dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) by
      funext coordinates
      exact generalEvenMinusAngleLocalIntegrand_inverseSqrt
        dimension index coordinates] at hmap
  rw [integral_div] at hmap
  have hnonzero : (index + 1 : ℝ) ^
      (dimension * (dimension - 1)) ≠ 0 := by positivity
  field_simp [hnonzero] at hmap ⊢
  exact hmap

theorem tendsto_generalEvenMinusAngleLocalIntegral_zero
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenMinusAngleLocalIntegral dimension index)
      atTop (nhds 0) := by
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenMinusAngleLocalIntegral dimension index) =
    fun index => ∫ coordinates : Fin dimension → ℝ,
      generalEvenMinusLocalRescaledIntegrand dimension index coordinates by
      funext index
      exact generalEvenMinusLocalScalingIntegral_identity dimension index]
  exact tendsto_integral_generalEvenMinusLocalRescaled_zero dimension hdimension

noncomputable def generalEvenFullNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (1 / Real.pi) ^ dimension *
    (fibonacciScaleKernel (cosineCubeScale angles) index /
      (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
    evenWeylAngleWeight dimension angles

noncomputable def generalEvenPositiveProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (positiveSpectralLocalDomain dimension).indicator
    (generalEvenFullNormalizedIntegrand dimension index) angles

noncomputable def generalEvenNegativeProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (negativeSpectralLocalDomain dimension).indicator
    (generalEvenFullNormalizedIntegrand dimension index) angles

noncomputable def generalEvenMiddleProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (middleOpenSpectralDomain dimension).indicator
    (generalEvenFullNormalizedIntegrand dimension index) angles

noncomputable def generalEvenMinusPositiveIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (positiveSpectralLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        (cosineVandermondeWeight dimension angles *
          allMinusAngleWeight dimension angles))
    angles

noncomputable def generalEvenFullNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenFullNormalizedIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

noncomputable def generalEvenNegativeIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenNegativeProductIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

noncomputable def generalEvenMiddleIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenMiddleProductIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

theorem integrable_generalEvenFullNormalizedIntegrand
    (dimension index : ℕ) :
    Integrable (generalEvenFullNormalizedIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
  apply integrable_continuous_cosineCube
  unfold generalEvenFullNormalizedIntegrand
  exact (continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale dimension)).div_const _)).mul
        (continuous_evenWeylAngleWeight dimension)

theorem generalEvenFullIntegrand_partition
    (dimension index : ℕ) (angles : Fin dimension → ℝ) :
    generalEvenFullNormalizedIntegrand dimension index angles =
      generalEvenPositiveProductIntegrand dimension index angles +
        (generalEvenNegativeProductIntegrand dimension index angles +
          generalEvenMiddleProductIntegrand dimension index angles) := by
  have hmidPos : 0 < cosineScaleMidpoint dimension := by
    unfold cosineScaleMidpoint
    positivity
  by_cases hpositive : angles ∈ positiveSpectralLocalDomain dimension
  · have hnegative : angles ∉ negativeSpectralLocalDomain dimension := by
      intro hnegative
      change cosineScaleMidpoint dimension ≤ cosineCubeScale angles at hpositive
      change cosineCubeScale angles ≤ -cosineScaleMidpoint dimension at hnegative
      linarith
    have hmiddle : angles ∉ middleOpenSpectralDomain dimension := by
      intro hmiddle
      exact (not_lt_of_ge hpositive) hmiddle.2
    rw [generalEvenPositiveProductIntegrand, Set.indicator_of_mem hpositive,
      generalEvenNegativeProductIntegrand, Set.indicator_of_notMem hnegative,
      generalEvenMiddleProductIntegrand, Set.indicator_of_notMem hmiddle,
      zero_add, add_zero]
  · have hpositiveLt : cosineCubeScale angles < cosineScaleMidpoint dimension := by
      change ¬cosineScaleMidpoint dimension ≤ cosineCubeScale angles at hpositive
      exact lt_of_not_ge hpositive
    by_cases hnegative : angles ∈ negativeSpectralLocalDomain dimension
    · have hmiddle : angles ∉ middleOpenSpectralDomain dimension := by
        intro hmiddle
        exact (not_lt_of_ge hnegative) hmiddle.1
      rw [generalEvenPositiveProductIntegrand, Set.indicator_of_notMem hpositive,
        generalEvenNegativeProductIntegrand, Set.indicator_of_mem hnegative,
        generalEvenMiddleProductIntegrand, Set.indicator_of_notMem hmiddle,
        zero_add, add_zero]
    · have hnegativeLt : -cosineScaleMidpoint dimension <
          cosineCubeScale angles := by
        change ¬cosineCubeScale angles ≤ -cosineScaleMidpoint dimension at hnegative
        exact lt_of_not_ge hnegative
      have hmiddle : angles ∈ middleOpenSpectralDomain dimension :=
        ⟨hnegativeLt, hpositiveLt⟩
      rw [generalEvenPositiveProductIntegrand, Set.indicator_of_notMem hpositive,
        generalEvenNegativeProductIntegrand, Set.indicator_of_notMem hnegative,
        generalEvenMiddleProductIntegrand, Set.indicator_of_mem hmiddle,
        zero_add]
      simp

theorem generalEvenPositiveIntegral_eq_angleLocal
    (dimension index : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      generalEvenPositiveProductIntegrand dimension index angles
      ∂cosineCubeProductMeasure dimension) =
      generalEvenAngleLocalIntegral dimension index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin dimension =>
      Set.Ioc (0 : ℝ) Real.pi) = anglePositiveCube dimension by rfl]
  rw [← integral_indicator (show MeasurableSet (anglePositiveCube dimension) by
    unfold anglePositiveCube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold generalEvenAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube dimension
  · by_cases hlocal : angles ∈ positiveSpectralLocalDomain dimension
    · have hangle : angles ∈ anglePositiveLocalDomain dimension := ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube, generalEvenPositiveProductIntegrand,
        Set.indicator_of_mem hlocal, generalEvenAngleLocalIntegrand,
        Set.indicator_of_mem hangle]
      unfold generalEvenFullNormalizedIntegrand
      rfl
    · rw [Set.indicator_of_mem hcube, generalEvenPositiveProductIntegrand,
        Set.indicator_of_notMem hlocal, generalEvenAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube, generalEvenAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem generalEvenMinusPositiveIntegral_eq_angleLocal
    (dimension index : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      generalEvenMinusPositiveIntegrand dimension index angles
      ∂cosineCubeProductMeasure dimension) =
      generalEvenMinusAngleLocalIntegral dimension index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin dimension =>
      Set.Ioc (0 : ℝ) Real.pi) = anglePositiveCube dimension by rfl]
  rw [← integral_indicator (show MeasurableSet (anglePositiveCube dimension) by
    unfold anglePositiveCube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold generalEvenMinusAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube dimension
  · by_cases hlocal : angles ∈ positiveSpectralLocalDomain dimension
    · have hangle : angles ∈ anglePositiveLocalDomain dimension := ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube, generalEvenMinusPositiveIntegrand,
        Set.indicator_of_mem hlocal, generalEvenMinusAngleLocalIntegrand,
        Set.indicator_of_mem hangle]
    · rw [Set.indicator_of_mem hcube, generalEvenMinusPositiveIntegrand,
        Set.indicator_of_notMem hlocal, generalEvenMinusAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube, generalEvenMinusAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem generalEvenNegativeIntegral_eq
    (dimension index : ℕ) :
    generalEvenNegativeIntegral dimension index =
      (-1 : ℝ) ^ index * generalEvenMinusAngleLocalIntegral dimension index := by
  unfold generalEvenNegativeIntegral generalEvenNegativeProductIntegrand
  rw [← (measurePreserving_angleReflectionEquiv dimension).integral_comp'
    ((negativeSpectralLocalDomain dimension).indicator
      (generalEvenFullNormalizedIntegrand dimension index))]
  rw [show (fun angles : Fin dimension → ℝ =>
      (negativeSpectralLocalDomain dimension).indicator
        (generalEvenFullNormalizedIntegrand dimension index)
        (angleReflectionEquiv dimension angles)) =
    fun angles => (-1 : ℝ) ^ index *
      generalEvenMinusPositiveIntegrand dimension index angles by
    funext angles
    have hscale := cosineCubeScale_angleReflection dimension angles
    by_cases hlocal : angles ∈ positiveSpectralLocalDomain dimension
    · have hreflected : angleReflectionEquiv dimension angles ∈
          negativeSpectralLocalDomain dimension := by
        change cosineCubeScale (angleReflectionEquiv dimension angles) ≤
          -cosineScaleMidpoint dimension
        rw [hscale]
        exact neg_le_neg hlocal
      rw [Set.indicator_of_mem hreflected, generalEvenMinusPositiveIntegrand,
        Set.indicator_of_mem hlocal, generalEvenFullNormalizedIntegrand,
        hscale, fibonacciScaleKernel_neg, evenWeylAngleWeight_reflection]
      ring
    · have hreflected : angleReflectionEquiv dimension angles ∉
          negativeSpectralLocalDomain dimension := by
        intro hreflected
        apply hlocal
        change cosineCubeScale (angleReflectionEquiv dimension angles) ≤
          -cosineScaleMidpoint dimension at hreflected
        rw [hscale] at hreflected
        change cosineScaleMidpoint dimension ≤ cosineCubeScale angles
        linarith
      rw [Set.indicator_of_notMem hreflected,
        generalEvenMinusPositiveIntegrand, Set.indicator_of_notMem hlocal,
        mul_zero], integral_const_mul,
    generalEvenMinusPositiveIntegral_eq_angleLocal]

theorem tendsto_generalEvenNegativeIntegral_zero
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenNegativeIntegral dimension index)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ‖Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenMinusAngleLocalIntegral dimension index‖)
  · intro index
    rw [generalEvenNegativeIntegral_eq]
    simp [norm_mul]
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_generalEvenMinusAngleLocalIntegral_zero dimension hdimension

noncomputable def generalEvenMiddleGrowthConstant (dimension : ℕ) : ℝ :=
  (1 / Real.pi) ^ dimension *
    Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
    ((4 : ℝ) ^ weylPairCount dimension * (2 : ℝ) ^ dimension)

theorem norm_generalEvenMiddleProductIntegrand_le
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (index : ℕ) (angles : Fin dimension → ℝ) :
    ‖generalEvenMiddleProductIntegrand dimension index angles‖ ≤
      generalEvenMiddleGrowthConstant dimension *
        fibonacciMiddleGrowthRatio dimension ^ (index + 1) := by
  by_cases hmiddle : angles ∈ middleOpenSpectralDomain dimension
  · rw [generalEvenMiddleProductIntegrand, Set.indicator_of_mem hmiddle,
      generalEvenFullNormalizedIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
      abs_of_nonneg (evenWeylAngleWeight_nonneg dimension angles)]
    have hdimreal : 4 ≤ (2 * dimension : ℝ) := by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith
    have hkernel := abs_middle_normalized_kernel_le
      (dimension := dimension) (index := index) hdimreal
      (middleOpen_abs_scale_le hmiddle)
    have hweight := evenWeylAngleWeight_le_constant dimension angles
    have hrightNonneg : 0 ≤ (1 / Real.pi) ^ dimension *
        (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
          fibonacciMiddleGrowthRatio dimension ^ (index + 1)) :=
      mul_nonneg (pow_nonneg (by positivity) _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg (fibonacciMiddleGrowthRatio_pos hdimreal).le _))
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left hkernel (pow_nonneg (by positivity) _))
      hweight (evenWeylAngleWeight_nonneg dimension angles)
      hrightNonneg).trans_eq (by
        unfold generalEvenMiddleGrowthConstant
        ring)
  · rw [generalEvenMiddleProductIntegrand, Set.indicator_of_notMem hmiddle,
      norm_zero]
    unfold generalEvenMiddleGrowthConstant
    have hdimreal : 4 ≤ (2 * dimension : ℝ) := by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith
    exact mul_nonneg (by positivity)
      (pow_nonneg (fibonacciMiddleGrowthRatio_pos hdimreal).le _)

theorem tendsto_generalEvenMiddleIntegral_zero
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenMiddleIntegral dimension index)
      atTop (nhds 0) := by
  let exponent := dimension * (dimension - 1) + dimension
  have hdimreal : 4 ≤ (2 * dimension : ℝ) := by
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    linarith
  have hgeom := tendsto_pow_const_mul_const_pow_of_abs_lt_one exponent
    (by rw [abs_of_pos (fibonacciMiddleGrowthRatio_pos hdimreal)]
        exact fibonacciMiddleGrowthRatio_lt_one hdimreal)
  have hshift := hgeom.comp (tendsto_add_atTop_nat 1)
  have hpolyGeom : Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ exponent *
        fibonacciMiddleGrowthRatio dimension ^ (index + 1))
      atTop (nhds 0) := by
    rw [show (fun index : ℕ =>
        (index + 1 : ℝ) ^ exponent *
          fibonacciMiddleGrowthRatio dimension ^ (index + 1)) =
      (fun index : ℕ => (index : ℝ) ^ exponent *
        fibonacciMiddleGrowthRatio dimension ^ index) ∘
          (fun index : ℕ => index + 1) by
        funext index
        simp [Function.comp_apply]]
    exact hshift
  let constant := generalEvenMiddleGrowthConstant dimension *
    (cosineCubeProductMeasure dimension).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ exponent *
        fibonacciMiddleGrowthRatio dimension ^ (index + 1)) * constant)
  · intro index
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _),
      abs_of_nonneg (pow_nonneg (by positivity) _)]
    have hintegral : ‖generalEvenMiddleIntegral dimension index‖ ≤
        (generalEvenMiddleGrowthConstant dimension *
          fibonacciMiddleGrowthRatio dimension ^ (index + 1)) *
          (cosineCubeProductMeasure dimension).real Set.univ := by
      unfold generalEvenMiddleIntegral
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall
          (norm_generalEvenMiddleProductIntegrand_le hdimension index))
    have hsqrt : Real.sqrt (index + 1 : ℝ) ≤ (index + 1 : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
    have hsqrtPow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt dimension
    have hpoly : Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) ≤
        (index + 1 : ℝ) ^ exponent := by
      calc
        _ ≤ (index + 1 : ℝ) ^ dimension *
            (index + 1 : ℝ) ^ (dimension * (dimension - 1)) :=
          mul_le_mul_of_nonneg_right hsqrtPow (by positivity)
        _ = _ := by unfold exponent; rw [← pow_add]; congr 1; omega
    calc
      Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
            ‖generalEvenMiddleIntegral dimension index‖ ≤
        (index + 1 : ℝ) ^ exponent *
          ‖generalEvenMiddleIntegral dimension index‖ :=
        mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hintegral (by positivity)
      _ = _ := by ring
  · simpa only [zero_mul] using hpolyGeom.mul_const constant

theorem generalEvenFullNormalizedIntegral_partition
    (dimension index : ℕ) :
    generalEvenFullNormalizedIntegral dimension index =
      generalEvenAngleLocalIntegral dimension index +
        (generalEvenNegativeIntegral dimension index +
          generalEvenMiddleIntegral dimension index) := by
  unfold generalEvenFullNormalizedIntegral generalEvenNegativeIntegral
    generalEvenMiddleIntegral
  rw [show (fun angles : Fin dimension → ℝ =>
      generalEvenFullNormalizedIntegrand dimension index angles) =
    fun angles => generalEvenPositiveProductIntegrand dimension index angles +
      (generalEvenNegativeProductIntegrand dimension index angles +
        generalEvenMiddleProductIntegrand dimension index angles) by
      funext angles
      exact generalEvenFullIntegrand_partition dimension index angles]
  have hfull := integrable_generalEvenFullNormalizedIntegrand dimension index
  have hpositive := hfull.indicator
    (measurableSet_positiveSpectralLocalDomain dimension)
  have hnegative := hfull.indicator
    (measurableSet_negativeSpectralLocalDomain dimension)
  have hmiddle := hfull.indicator
    (measurableSet_middleOpenSpectralDomain dimension)
  change Integrable (generalEvenPositiveProductIntegrand dimension index)
    (cosineCubeProductMeasure dimension) at hpositive
  change Integrable (generalEvenNegativeProductIntegrand dimension index)
    (cosineCubeProductMeasure dimension) at hnegative
  change Integrable (generalEvenMiddleProductIntegrand dimension index)
    (cosineCubeProductMeasure dimension) at hmiddle
  calc
    (∫ angles : Fin dimension → ℝ,
      generalEvenPositiveProductIntegrand dimension index angles +
        (generalEvenNegativeProductIntegrand dimension index angles +
          generalEvenMiddleProductIntegrand dimension index angles)
      ∂cosineCubeProductMeasure dimension) =
      (∫ angles : Fin dimension → ℝ,
        generalEvenPositiveProductIntegrand dimension index angles
        ∂cosineCubeProductMeasure dimension) +
      ∫ angles : Fin dimension → ℝ,
        (generalEvenNegativeProductIntegrand dimension index angles +
          generalEvenMiddleProductIntegrand dimension index angles)
        ∂cosineCubeProductMeasure dimension :=
      integral_add hpositive (hnegative.add hmiddle)
    _ = (∫ angles : Fin dimension → ℝ,
          generalEvenPositiveProductIntegrand dimension index angles
          ∂cosineCubeProductMeasure dimension) +
        ((∫ angles : Fin dimension → ℝ,
            generalEvenNegativeProductIntegrand dimension index angles
            ∂cosineCubeProductMeasure dimension) +
          ∫ angles : Fin dimension → ℝ,
            generalEvenMiddleProductIntegrand dimension index angles
            ∂cosineCubeProductMeasure dimension) := by
      rw [integral_add hnegative hmiddle]
    _ = _ := by rw [generalEvenPositiveIntegral_eq_angleLocal]

theorem tendsto_generalEvenFullNormalizedIntegral
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenFullNormalizedIntegral dimension index)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalEvenWeylLocalLimitIntegrand dimension coordinates)) := by
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenFullNormalizedIntegral dimension index) =
    fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenAngleLocalIntegral dimension index +
      (Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
            generalEvenNegativeIntegral dimension index +
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
            generalEvenMiddleIntegral dimension index) by
      funext index
      rw [generalEvenFullNormalizedIntegral_partition]
      ring]
  simpa using (tendsto_generalEvenAngleLocalIntegral dimension hdimension).add
    ((tendsto_generalEvenNegativeIntegral_zero dimension hdimension).add
      (tendsto_generalEvenMiddleIntegral_zero dimension hdimension))

theorem generalEvenFullNormalizedIntegral_eq_weylMoment
    (dimension index : ℕ) :
    generalEvenFullNormalizedIntegral dimension index =
      (1 / Real.pi) ^ dimension *
        (evenWeylFibonacciMoment dimension index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) := by
  unfold generalEvenFullNormalizedIntegral generalEvenFullNormalizedIntegrand
    evenWeylFibonacciMoment weightedCosineCubeFibonacciMoment
    weightedCosineCubeFibonacciIntegrand
  rw [show (fun angles : Fin dimension → ℝ =>
      (1 / Real.pi) ^ dimension *
          (fibonacciScaleKernel (cosineCubeScale angles) index /
            (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
              Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        evenWeylAngleWeight dimension angles) =
    fun angles => ((1 / Real.pi) ^ dimension /
      (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
      (fibonacciScaleKernel (cosineCubeScale angles) index *
        evenWeylAngleWeight dimension angles) by
      funext angles
      ring]
  rw [integral_const_mul]
  ring

theorem generalEvenFullNormalizedIntegral_eq_ribbonCount
    (dimension : ℕ) (hdimension : 1 ≤ dimension) (index : ℕ) :
    generalEvenFullNormalizedIntegral dimension index =
      (1 / Real.pi) ^ dimension / evenWeylNormalization dimension *
      ((ribbonCount (2 * dimension - 1) index : ℝ) /
        (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) := by
  rw [generalEvenFullNormalizedIntegral_eq_weylMoment,
    generalEvenRibbonCount_eq_normalizedWeylMoment dimension hdimension]
  have hnorm : evenWeylNormalization dimension ≠ 0 := by
    unfold evenWeylNormalization
    positivity
  field_simp [hnorm]

theorem tendsto_generalEvenRibbonNormalizedIntegralConstant
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
      ((ribbonCount (2 * dimension - 1) index : ℝ) /
        (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))))
      atTop (nhds ((evenWeylNormalization dimension * Real.pi ^ dimension) *
        (∫ coordinates : Fin dimension → ℝ,
          generalEvenWeylLocalLimitIntegrand dimension coordinates))) := by
  have h := (tendsto_generalEvenFullNormalizedIntegral dimension hdimension).const_mul
    (evenWeylNormalization dimension * Real.pi ^ dimension)
  apply h.congr'
  filter_upwards with index
  rw [generalEvenFullNormalizedIntegral_eq_ribbonCount dimension
    (by omega) index]
  have hnorm : evenWeylNormalization dimension ≠ 0 := by
    unfold evenWeylNormalization
    positivity
  have hpiCancel : Real.pi ^ dimension *
      (1 / Real.pi) ^ dimension = 1 := by
    rw [← mul_pow]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hcoefficient : evenWeylNormalization dimension * Real.pi ^ dimension *
      ((1 / Real.pi) ^ dimension / evenWeylNormalization dimension) = 1 := by
    rw [show evenWeylNormalization dimension * Real.pi ^ dimension *
        ((1 / Real.pi) ^ dimension / evenWeylNormalization dimension) =
      (Real.pi ^ dimension * (1 / Real.pi) ^ dimension) *
        (evenWeylNormalization dimension / evenWeylNormalization dimension) by
      ring, hpiCancel, div_self hnorm, one_mul]
  calc
    evenWeylNormalization dimension * Real.pi ^ dimension *
        (Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
            ((1 / Real.pi) ^ dimension / evenWeylNormalization dimension *
              ((ribbonCount (2 * dimension - 1) index : ℝ) /
                (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
                  Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))))) =
      (evenWeylNormalization dimension * Real.pi ^ dimension *
        ((1 / Real.pi) ^ dimension / evenWeylNormalization dimension)) *
        (Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
            ((ribbonCount (2 * dimension - 1) index : ℝ) /
              (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
                Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)))) := by ring
    _ = _ := by rw [hcoefficient, one_mul]

end FibonacciRibbonKernel
