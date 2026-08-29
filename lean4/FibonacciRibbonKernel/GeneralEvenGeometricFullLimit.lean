import FibonacciRibbonKernel.GeneralEvenGeometricLimit

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

noncomputable def generalEvenGeometricMinusLocalRescaledIntegrand
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  (positiveLocalScaledDomain dimension index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        generalEvenNormalizedGeometricKernel dimension coordinates index *
        generalEvenMinusScaledWeight dimension index coordinates)
    coordinates

theorem tendsto_generalEvenGeometricMinusLocalRescaledIntegrand_zero
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      generalEvenGeometricMinusLocalRescaledIntegrand
        dimension index coordinates)
      atTop (nhds 0) := by
  have hdimensionPos : 0 < dimension := by omega
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain (by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith) coordinates horthant
    have hkernel := tendsto_generalEvenNormalizedGeometricKernel
      (show 1 ≤ dimension by omega) coordinates
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
      rw [generalEvenGeometricMinusLocalRescaledIntegrand,
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
        generalEvenGeometricMinusLocalRescaledIntegrand
          dimension index coordinates) = fun _ => 0 by
        funext index
        rw [generalEvenGeometricMinusLocalRescaledIntegrand,
          Set.indicator_of_notMem (houtside index)]]
    exact tendsto_const_nhds

theorem aestronglyMeasurable_generalEvenGeometricMinusLocalRescaledIntegrand
    (dimension index : ℕ) :
    AEStronglyMeasurable
      (generalEvenGeometricMinusLocalRescaledIntegrand dimension index) := by
  unfold generalEvenGeometricMinusLocalRescaledIntegrand
    generalEvenMinusScaledWeight
  exact (((continuous_const.mul
    (continuous_generalEvenNormalizedGeometricKernel dimension index)).mul
      ((continuous_scaledCosineVandermondeWeight dimension index).mul
        (continuous_allMinusScaledWeight dimension index))).stronglyMeasurable.indicator
          (measurableSet_positiveLocalScaledDomain dimension index)).aestronglyMeasurable

theorem norm_generalEvenGeometricMinusLocalRescaledIntegrand_le
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖generalEvenGeometricMinusLocalRescaledIntegrand
        dimension index coordinates‖ ≤
      generalEvenGeometricLocalDominating dimension coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [generalEvenGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, Real.norm_eq_abs, abs_of_nonneg]
    · have hkernel := generalEvenNormalizedGeometricKernel_le_gaussian
        hdimension index coordinates hdomain.1 hdomain.2
      have hweight := generalEvenMinusScaledWeight_le_global
        dimension index coordinates
      have hkernelNonneg := generalEvenNormalizedGeometricKernel_nonneg
        ((show (0 : ℝ) < cosineScaleMidpoint dimension by
          unfold cosineScaleMidpoint
          positivity).le.trans hdomain.2)
      have hweightNonneg := generalEvenMinusScaledWeight_nonneg
        dimension index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg
        (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ dimension by positivity)
      calc
        (1 / Real.pi) ^ dimension *
            generalEvenNormalizedGeometricKernel
              dimension coordinates index *
              generalEvenMinusScaledWeight dimension index coordinates ≤
          (1 / Real.pi) ^ dimension *
            ((Real.exp 1 *
              Real.exp (-generalEvenGeometricGaussianCoefficient dimension *
                ∑ coordinate, coordinates coordinate ^ 2)) *
              ((2 : ℝ) ^ dimension *
                weylGlobalPolynomial dimension coordinates ^
                  (weylSeparableExponent dimension 0))) := by
                    simpa only [mul_assoc] using hscaled
        _ = generalEvenGeometricLocalDominating dimension coordinates := by
          unfold generalEvenGeometricLocalDominating weylSeparableDominating
          rw [← gaussianGlobalPolynomial_eq_separable]
          ring
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (generalEvenNormalizedGeometricKernel_nonneg
            ((show (0 : ℝ) < cosineScaleMidpoint dimension by
              unfold cosineScaleMidpoint
              positivity).le.trans hdomain.2)))
        (generalEvenMinusScaledWeight_nonneg dimension index coordinates)
  · rw [generalEvenGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold generalEvenGeometricLocalDominating weylSeparableDominating
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro coordinate hcoordinate
    unfold weylCoordinateDominating
    positivity

theorem tendsto_integral_generalEvenGeometricMinusLocalRescaled_zero
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index => ∫ coordinates : Fin dimension → ℝ,
      generalEvenGeometricMinusLocalRescaledIntegrand
        dimension index coordinates)
      atTop (nhds 0) := by
  simpa using tendsto_integral_of_dominated_convergence
    (generalEvenGeometricLocalDominating dimension)
    (fun index =>
      aestronglyMeasurable_generalEvenGeometricMinusLocalRescaledIntegrand
        dimension index)
    (integrable_generalEvenGeometricLocalDominating hdimension)
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_generalEvenGeometricMinusLocalRescaledIntegrand_le
        hdimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_generalEvenGeometricMinusLocalRescaledIntegrand_zero
        hdimension coordinates)

noncomputable def generalEvenGeometricMinusAngleLocalIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (anglePositiveLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (cosineCubeScale angles / (2 * dimension : ℝ)) ^ index *
        (cosineVandermondeWeight dimension angles *
          allMinusAngleWeight dimension angles))
    angles

noncomputable def generalEvenGeometricMinusAngleLocalIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenGeometricMinusAngleLocalIntegrand dimension index angles

theorem generalEvenGeometricMinusAngleLocalIntegrand_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    generalEvenGeometricMinusAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      generalEvenGeometricMinusLocalRescaledIntegrand
          dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [generalEvenGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).2
          hdomain),
      generalEvenGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt,
      generalEvenMinusAngleWeight_inverseSqrt]
    unfold generalEvenNormalizedGeometricKernel
    ring
  · rw [generalEvenGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).1
          hdomain),
      generalEvenGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem stronglyMeasurable_generalEvenGeometricMinusAngleLocalIntegrand
    (dimension index : ℕ) :
    StronglyMeasurable
      (generalEvenGeometricMinusAngleLocalIntegrand dimension index) := by
  unfold generalEvenGeometricMinusAngleLocalIntegrand
  exact (((continuous_const.mul
    (((continuous_cosineCubeScale dimension).div_const _).pow index)).mul
      ((continuous_cosineVandermondeWeight dimension).mul
        (continuous_allMinusAngleWeight dimension))).stronglyMeasurable.indicator
          (measurableSet_anglePositiveLocalDomain dimension))

theorem generalEvenGeometricMinusLocalScalingIntegral_identity
    (dimension index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricMinusAngleLocalIntegral dimension index =
      ∫ coordinates : Fin dimension → ℝ,
        generalEvenGeometricMinusLocalRescaledIntegrand
          dimension index coordinates := by
  let scaleMap := coordinateScalarLinearMap dimension
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := generalEvenGeometricMinusAngleLocalIntegrand dimension index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension _).aemeasurable
      (stronglyMeasurable_generalEvenGeometricMinusAngleLocalIntegrand
        dimension index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ dimension := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold generalEvenGeometricMinusAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      generalEvenGeometricMinusAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
    fun coordinates =>
      generalEvenGeometricMinusLocalRescaledIntegrand
          dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) by
      funext coordinates
      exact generalEvenGeometricMinusAngleLocalIntegrand_inverseSqrt
        dimension index coordinates] at hmap
  rw [integral_div] at hmap
  have hnonzero : (index + 1 : ℝ) ^
      (dimension * (dimension - 1)) ≠ 0 := by positivity
  field_simp [hnonzero] at hmap ⊢
  exact hmap

theorem tendsto_generalEvenGeometricMinusAngleLocalIntegral_zero
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricMinusAngleLocalIntegral dimension index)
      atTop (nhds 0) := by
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricMinusAngleLocalIntegral dimension index) =
    fun index => ∫ coordinates : Fin dimension → ℝ,
      generalEvenGeometricMinusLocalRescaledIntegrand
        dimension index coordinates by
      funext index
      exact generalEvenGeometricMinusLocalScalingIntegral_identity
        dimension index]
  exact tendsto_integral_generalEvenGeometricMinusLocalRescaled_zero
    dimension hdimension

noncomputable def generalEvenGeometricFullIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (1 / Real.pi) ^ dimension *
    (cosineCubeScale angles / (2 * dimension : ℝ)) ^ index *
    evenWeylAngleWeight dimension angles

noncomputable def generalEvenGeometricPositiveProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (positiveSpectralLocalDomain dimension).indicator
    (generalEvenGeometricFullIntegrand dimension index) angles

noncomputable def generalEvenGeometricNegativeProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (negativeSpectralLocalDomain dimension).indicator
    (generalEvenGeometricFullIntegrand dimension index) angles

noncomputable def generalEvenGeometricMiddleProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (middleOpenSpectralDomain dimension).indicator
    (generalEvenGeometricFullIntegrand dimension index) angles

noncomputable def generalEvenGeometricMinusPositiveIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (positiveSpectralLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (cosineCubeScale angles / (2 * dimension : ℝ)) ^ index *
        (cosineVandermondeWeight dimension angles *
          allMinusAngleWeight dimension angles))
    angles

noncomputable def generalEvenGeometricFullIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenGeometricFullIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

noncomputable def generalEvenGeometricNegativeIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenGeometricNegativeProductIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

noncomputable def generalEvenGeometricMiddleIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenGeometricMiddleProductIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

theorem integrable_generalEvenGeometricFullIntegrand
    (dimension index : ℕ) :
    Integrable (generalEvenGeometricFullIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
  apply integrable_continuous_cosineCube
  unfold generalEvenGeometricFullIntegrand
  exact (continuous_const.mul
    (((continuous_cosineCubeScale dimension).div_const _).pow index)).mul
      (continuous_evenWeylAngleWeight dimension)

theorem generalEvenGeometricFullIntegrand_partition
    (dimension index : ℕ) (angles : Fin dimension → ℝ) :
    generalEvenGeometricFullIntegrand dimension index angles =
      generalEvenGeometricPositiveProductIntegrand dimension index angles +
        (generalEvenGeometricNegativeProductIntegrand dimension index angles +
          generalEvenGeometricMiddleProductIntegrand
            dimension index angles) := by
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
    rw [generalEvenGeometricPositiveProductIntegrand,
      Set.indicator_of_mem hpositive,
      generalEvenGeometricNegativeProductIntegrand,
      Set.indicator_of_notMem hnegative,
      generalEvenGeometricMiddleProductIntegrand,
      Set.indicator_of_notMem hmiddle, zero_add, add_zero]
  · have hpositiveLt : cosineCubeScale angles <
        cosineScaleMidpoint dimension := by
      change ¬cosineScaleMidpoint dimension ≤ cosineCubeScale angles at hpositive
      exact lt_of_not_ge hpositive
    by_cases hnegative : angles ∈ negativeSpectralLocalDomain dimension
    · have hmiddle : angles ∉ middleOpenSpectralDomain dimension := by
        intro hmiddle
        exact (not_lt_of_ge hnegative) hmiddle.1
      rw [generalEvenGeometricPositiveProductIntegrand,
        Set.indicator_of_notMem hpositive,
        generalEvenGeometricNegativeProductIntegrand,
        Set.indicator_of_mem hnegative,
        generalEvenGeometricMiddleProductIntegrand,
        Set.indicator_of_notMem hmiddle, zero_add, add_zero]
    · have hnegativeLt : -cosineScaleMidpoint dimension <
          cosineCubeScale angles := by
        change ¬cosineCubeScale angles ≤
          -cosineScaleMidpoint dimension at hnegative
        exact lt_of_not_ge hnegative
      have hmiddle : angles ∈ middleOpenSpectralDomain dimension :=
        ⟨hnegativeLt, hpositiveLt⟩
      rw [generalEvenGeometricPositiveProductIntegrand,
        Set.indicator_of_notMem hpositive,
        generalEvenGeometricNegativeProductIntegrand,
        Set.indicator_of_notMem hnegative,
        generalEvenGeometricMiddleProductIntegrand,
        Set.indicator_of_mem hmiddle, zero_add]
      simp

theorem generalEvenGeometricPositiveIntegral_eq_angleLocal
    (dimension index : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      generalEvenGeometricPositiveProductIntegrand dimension index angles
      ∂cosineCubeProductMeasure dimension) =
      generalEvenGeometricAngleLocalIntegral dimension index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin dimension =>
      Set.Ioc (0 : ℝ) Real.pi) = anglePositiveCube dimension by rfl]
  rw [← integral_indicator (show MeasurableSet (anglePositiveCube dimension) by
    unfold anglePositiveCube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold generalEvenGeometricAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube dimension
  · by_cases hlocal : angles ∈ positiveSpectralLocalDomain dimension
    · have hangle : angles ∈ anglePositiveLocalDomain dimension :=
        ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        generalEvenGeometricPositiveProductIntegrand,
        Set.indicator_of_mem hlocal,
        generalEvenGeometricAngleLocalIntegrand,
        Set.indicator_of_mem hangle]
      unfold generalEvenGeometricFullIntegrand
      rfl
    · rw [Set.indicator_of_mem hcube,
        generalEvenGeometricPositiveProductIntegrand,
        Set.indicator_of_notMem hlocal,
        generalEvenGeometricAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      generalEvenGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem generalEvenGeometricMinusPositiveIntegral_eq_angleLocal
    (dimension index : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      generalEvenGeometricMinusPositiveIntegrand dimension index angles
      ∂cosineCubeProductMeasure dimension) =
      generalEvenGeometricMinusAngleLocalIntegral dimension index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin dimension =>
      Set.Ioc (0 : ℝ) Real.pi) = anglePositiveCube dimension by rfl]
  rw [← integral_indicator (show MeasurableSet (anglePositiveCube dimension) by
    unfold anglePositiveCube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold generalEvenGeometricMinusAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube dimension
  · by_cases hlocal : angles ∈ positiveSpectralLocalDomain dimension
    · have hangle : angles ∈ anglePositiveLocalDomain dimension :=
        ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        generalEvenGeometricMinusPositiveIntegrand,
        Set.indicator_of_mem hlocal,
        generalEvenGeometricMinusAngleLocalIntegrand,
        Set.indicator_of_mem hangle]
    · rw [Set.indicator_of_mem hcube,
        generalEvenGeometricMinusPositiveIntegrand,
        Set.indicator_of_notMem hlocal,
        generalEvenGeometricMinusAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      generalEvenGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem generalEvenGeometricNegativeIntegral_eq
    (dimension index : ℕ) :
    generalEvenGeometricNegativeIntegral dimension index =
      (-1 : ℝ) ^ index *
        generalEvenGeometricMinusAngleLocalIntegral dimension index := by
  unfold generalEvenGeometricNegativeIntegral
    generalEvenGeometricNegativeProductIntegrand
  rw [← (measurePreserving_angleReflectionEquiv dimension).integral_comp'
    ((negativeSpectralLocalDomain dimension).indicator
      (generalEvenGeometricFullIntegrand dimension index))]
  rw [show (fun angles : Fin dimension → ℝ =>
      (negativeSpectralLocalDomain dimension).indicator
        (generalEvenGeometricFullIntegrand dimension index)
        (angleReflectionEquiv dimension angles)) =
    fun angles => (-1 : ℝ) ^ index *
      generalEvenGeometricMinusPositiveIntegrand dimension index angles by
    funext angles
    have hscale := cosineCubeScale_angleReflection dimension angles
    by_cases hlocal : angles ∈ positiveSpectralLocalDomain dimension
    · have hreflected : angleReflectionEquiv dimension angles ∈
          negativeSpectralLocalDomain dimension := by
        change cosineCubeScale (angleReflectionEquiv dimension angles) ≤
          -cosineScaleMidpoint dimension
        rw [hscale]
        exact neg_le_neg hlocal
      rw [Set.indicator_of_mem hreflected,
        generalEvenGeometricMinusPositiveIntegrand,
        Set.indicator_of_mem hlocal,
        generalEvenGeometricFullIntegrand,
        hscale, evenWeylAngleWeight_reflection]
      rw [neg_div, neg_pow]
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
        generalEvenGeometricMinusPositiveIntegrand,
        Set.indicator_of_notMem hlocal, mul_zero],
    integral_const_mul,
    generalEvenGeometricMinusPositiveIntegral_eq_angleLocal]

theorem tendsto_generalEvenGeometricNegativeIntegral_zero
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricNegativeIntegral dimension index)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ‖Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricMinusAngleLocalIntegral dimension index‖)
  · intro index
    rw [generalEvenGeometricNegativeIntegral_eq]
    simp [norm_mul]
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_generalEvenGeometricMinusAngleLocalIntegral_zero
      dimension hdimension

end FibonacciRibbonKernel
