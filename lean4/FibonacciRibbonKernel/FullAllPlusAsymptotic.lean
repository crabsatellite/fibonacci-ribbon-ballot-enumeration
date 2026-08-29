import FibonacciRibbonKernel.MiddleOpenIntegral

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def allPlusFullNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (1 / Real.pi) ^ dimension *
    (fibonacciScaleKernel (cosineCubeScale angles) index /
      (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
    cosineCubeWeight dimension 0 angles

noncomputable def allPlusFullNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    allPlusFullNormalizedIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

noncomputable def allPlusPositiveLocalNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (positiveSpectralLocalDomain dimension).indicator
    (allPlusFullNormalizedIntegrand dimension index) angles

theorem measurableSet_negativeSpectralLocalDomain (dimension : ℕ) :
    MeasurableSet (negativeSpectralLocalDomain dimension) := by
  unfold negativeSpectralLocalDomain
  exact measurableSet_Iic.preimage
    (continuous_cosineCubeScale dimension).measurable

theorem measurableSet_middleOpenSpectralDomain (dimension : ℕ) :
    MeasurableSet (middleOpenSpectralDomain dimension) := by
  unfold middleOpenSpectralDomain
  exact (measurableSet_Ioi.preimage
    (continuous_cosineCubeScale dimension).measurable).inter
      (measurableSet_Iio.preimage
        (continuous_cosineCubeScale dimension).measurable)

theorem integrable_allPlusFullNormalizedIntegrand
    (dimension index : ℕ) :
    Integrable (allPlusFullNormalizedIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
  have hraw : Integrable (cosineCubeFibonacciIntegrand dimension 0 index)
      (cosineCubeProductMeasure dimension) := by
    change Integrable (fun angles : Fin dimension → ℝ =>
      cosineCubeFibonacciIntegrand dimension 0 index angles)
      (cosineCubeProductMeasure dimension)
    rw [show (fun angles : Fin dimension → ℝ =>
      cosineCubeFibonacciIntegrand dimension 0 index angles) =
      fun angles => ∑ degree ∈ Finset.range (index + 1),
        cosineCubeFibonacciTerm dimension 0 index degree angles by
      funext angles
      exact cosineCubeFibonacciIntegrand_eq_finite_sum
        dimension 0 index angles]
    exact integrable_finsetSum (Finset.range (index + 1))
      (fun degree _hdegree =>
      integrable_cosineCubeFibonacciTerm dimension 0 index degree
      )
  change Integrable (fun angles : Fin dimension → ℝ =>
    allPlusFullNormalizedIntegrand dimension index angles)
    (cosineCubeProductMeasure dimension)
  rw [show (fun angles : Fin dimension → ℝ =>
      allPlusFullNormalizedIntegrand dimension index angles) =
      fun angles =>
        ((1 / Real.pi) ^ dimension /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
          cosineCubeFibonacciIntegrand dimension 0 index angles by
    funext angles
    unfold allPlusFullNormalizedIntegrand cosineCubeFibonacciIntegrand
    ring]
  exact hraw.const_mul _

theorem integrable_allPlusPositiveLocalNormalizedIntegrand
    (dimension index : ℕ) :
    Integrable (allPlusPositiveLocalNormalizedIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
  unfold allPlusPositiveLocalNormalizedIntegrand
  exact (integrable_allPlusFullNormalizedIntegrand dimension index).indicator
    (measurableSet_positiveSpectralLocalDomain dimension)

theorem integrable_allPlusNegativeLocalNormalizedIntegrand
    (dimension index : ℕ) :
    Integrable (allPlusNegativeLocalNormalizedIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
  unfold allPlusNegativeLocalNormalizedIntegrand
  exact (integrable_allPlusFullNormalizedIntegrand dimension index).indicator
    (measurableSet_negativeSpectralLocalDomain dimension)

theorem integrable_allPlusMiddleOpenNormalizedIntegrand
    (dimension index : ℕ) :
    Integrable (allPlusMiddleOpenNormalizedIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
  unfold allPlusMiddleOpenNormalizedIntegrand
  exact (integrable_allPlusFullNormalizedIntegrand dimension index).indicator
    (measurableSet_middleOpenSpectralDomain dimension)

theorem fullNormalizedIntegrand_partition
    {dimension : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ))
    (index : ℕ) (angles : Fin dimension → ℝ) :
    allPlusFullNormalizedIntegrand dimension index angles =
      allPlusPositiveLocalNormalizedIntegrand dimension index angles +
        (allPlusNegativeLocalNormalizedIntegrand dimension index angles +
          allPlusMiddleOpenNormalizedIntegrand dimension index angles) := by
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
      change cosineScaleMidpoint dimension ≤ cosineCubeScale angles at hpositive
      exact (not_lt_of_ge hpositive) hmiddle.2
    rw [allPlusPositiveLocalNormalizedIntegrand,
      indicator_of_mem hpositive,
      allPlusNegativeLocalNormalizedIntegrand,
      indicator_of_notMem hnegative,
      allPlusMiddleOpenNormalizedIntegrand,
      indicator_of_notMem hmiddle, zero_add, add_zero]
  · have hpositiveLt : cosineCubeScale angles <
        cosineScaleMidpoint dimension := by
      change ¬ cosineScaleMidpoint dimension ≤ cosineCubeScale angles at hpositive
      exact lt_of_not_ge hpositive
    by_cases hnegative : angles ∈ negativeSpectralLocalDomain dimension
    · have hmiddle : angles ∉ middleOpenSpectralDomain dimension := by
        intro hmiddle
        change cosineCubeScale angles ≤ -cosineScaleMidpoint dimension at hnegative
        exact (not_lt_of_ge hnegative) hmiddle.1
      rw [allPlusPositiveLocalNormalizedIntegrand,
        indicator_of_notMem hpositive,
        allPlusNegativeLocalNormalizedIntegrand,
        indicator_of_mem hnegative,
        allPlusMiddleOpenNormalizedIntegrand,
        indicator_of_notMem hmiddle, zero_add, add_zero]
      rfl
    · have hnegativeLt : -cosineScaleMidpoint dimension <
          cosineCubeScale angles := by
        change ¬ cosineCubeScale angles ≤ -cosineScaleMidpoint dimension at hnegative
        exact lt_of_not_ge hnegative
      have hmiddle : angles ∈ middleOpenSpectralDomain dimension :=
        ⟨hnegativeLt, hpositiveLt⟩
      rw [allPlusPositiveLocalNormalizedIntegrand,
        indicator_of_notMem hpositive,
        allPlusNegativeLocalNormalizedIntegrand,
        indicator_of_notMem hnegative,
        allPlusMiddleOpenNormalizedIntegrand,
        indicator_of_mem hmiddle, zero_add]
      simp only [zero_add]
      rfl

theorem allPlusPositiveLocalIntegral_eq_angleLocal
    (dimension index : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      allPlusPositiveLocalNormalizedIntegrand dimension index angles
      ∂cosineCubeProductMeasure dimension) =
      allPlusAngleLocalNormalizedIntegral dimension index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show
    (Set.univ.pi fun _ : Fin dimension => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube dimension by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube dimension) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold allPlusAngleLocalNormalizedIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube dimension
  · by_cases hlocal : angles ∈ positiveSpectralLocalDomain dimension
    · have hangleLocal : angles ∈ anglePositiveLocalDomain dimension :=
        ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        allPlusPositiveLocalNormalizedIntegrand,
        Set.indicator_of_mem hlocal,
        allPlusAngleLocalNormalizedIntegrand,
        Set.indicator_of_mem hangleLocal]
      rfl
    · rw [Set.indicator_of_mem hcube,
        allPlusPositiveLocalNormalizedIntegrand,
        Set.indicator_of_notMem hlocal,
        allPlusAngleLocalNormalizedIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      allPlusAngleLocalNormalizedIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem allPlusFullNormalizedIntegral_partition
    {dimension : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ))
    (index : ℕ) :
    allPlusFullNormalizedIntegral dimension index =
      allPlusAngleLocalNormalizedIntegral dimension index +
        (allPlusNegativeLocalNormalizedIntegral dimension index +
          allPlusMiddleOpenNormalizedIntegral dimension index) := by
  unfold allPlusFullNormalizedIntegral
  rw [show (fun angles : Fin dimension → ℝ =>
      allPlusFullNormalizedIntegrand dimension index angles) =
      fun angles =>
        allPlusPositiveLocalNormalizedIntegrand dimension index angles +
          (allPlusNegativeLocalNormalizedIntegrand dimension index angles +
            allPlusMiddleOpenNormalizedIntegrand dimension index angles) by
    funext angles
    exact fullNormalizedIntegrand_partition hdimension index angles]
  calc
    (∫ angles : Fin dimension → ℝ,
        allPlusPositiveLocalNormalizedIntegrand dimension index angles +
          (allPlusNegativeLocalNormalizedIntegrand dimension index angles +
            allPlusMiddleOpenNormalizedIntegrand dimension index angles)
        ∂cosineCubeProductMeasure dimension) =
      (∫ angles,
        allPlusPositiveLocalNormalizedIntegrand dimension index angles
        ∂cosineCubeProductMeasure dimension) +
      ∫ angles,
        (allPlusNegativeLocalNormalizedIntegrand dimension index angles +
          allPlusMiddleOpenNormalizedIntegrand dimension index angles)
        ∂cosineCubeProductMeasure dimension :=
      integral_add
        (integrable_allPlusPositiveLocalNormalizedIntegrand dimension index)
        ((integrable_allPlusNegativeLocalNormalizedIntegrand dimension index).add
          (integrable_allPlusMiddleOpenNormalizedIntegrand dimension index))
    _ = (∫ angles,
          allPlusPositiveLocalNormalizedIntegrand dimension index angles
          ∂cosineCubeProductMeasure dimension) +
        ((∫ angles,
            allPlusNegativeLocalNormalizedIntegrand dimension index angles
            ∂cosineCubeProductMeasure dimension) +
          ∫ angles,
            allPlusMiddleOpenNormalizedIntegrand dimension index angles
            ∂cosineCubeProductMeasure dimension) := by
      rw [integral_add
        (integrable_allPlusNegativeLocalNormalizedIntegrand dimension index)
        (integrable_allPlusMiddleOpenNormalizedIntegrand dimension index)]
    _ = _ := by
      rw [allPlusPositiveLocalIntegral_eq_angleLocal]
      rfl

theorem allPlusFullNormalizedIntegral_eq_coefficient
    (dimension index : ℕ) :
    allPlusFullNormalizedIntegral dimension index =
      cosineCubeFibonacciIntegral dimension 0 index /
        (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) := by
  unfold allPlusFullNormalizedIntegral cosineCubeFibonacciIntegral
  simp only [Nat.add_zero]
  rw [show (fun angles : Fin dimension → ℝ =>
      allPlusFullNormalizedIntegrand dimension index angles) =
      fun angles : Fin dimension → ℝ =>
        ((1 / Real.pi) ^ dimension /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
          cosineCubeFibonacciIntegrand dimension 0 index angles by
    funext angles
    unfold allPlusFullNormalizedIntegrand cosineCubeFibonacciIntegrand
    ring]
  rw [integral_const_mul]
  ring

theorem tendsto_allPlusFullNormalizedIntegral
    (dimension : ℕ) (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    Tendsto
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          allPlusFullNormalizedIntegral dimension index)
      atTop (nhds (allPlusLocalLimitConstant dimension)) := by
  rw [show
    (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        allPlusFullNormalizedIntegral dimension index) =
      fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
            allPlusAngleLocalNormalizedIntegral dimension index +
          (Real.sqrt (index + 1 : ℝ) ^ dimension *
              allPlusNegativeLocalNormalizedIntegral dimension index +
            Real.sqrt (index + 1 : ℝ) ^ dimension *
              allPlusMiddleOpenNormalizedIntegral dimension index) by
    funext index
    rw [allPlusFullNormalizedIntegral_partition hdimension]
    ring]
  simpa using
    (tendsto_allPlusAngleLocalNormalizedIntegral dimension (by linarith)).add
      ((tendsto_allPlusNegativeLocalNormalizedIntegral dimension (by linarith)).add
        (tendsto_allPlusMiddleOpenNormalizedIntegral dimension hdimension))

theorem tendsto_allPlusCosineCubeFibonacciIntegral_normalized
    (dimension : ℕ) (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    Tendsto
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          (cosineCubeFibonacciIntegral dimension 0 index /
            (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
              Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))))
      atTop (nhds (allPlusLocalLimitConstant dimension)) := by
  rw [show
    (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (cosineCubeFibonacciIntegral dimension 0 index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)))) =
      fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ dimension *
        allPlusFullNormalizedIntegral dimension index by
    funext index
    rw [allPlusFullNormalizedIntegral_eq_coefficient]]
  exact tendsto_allPlusFullNormalizedIntegral dimension hdimension

end FibonacciRibbonKernel
