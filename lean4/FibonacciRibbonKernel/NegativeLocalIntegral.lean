import FibonacciRibbonKernel.AllMinusLocalScaling

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def negativeSpectralLocalDomain
    (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  {angles | cosineCubeScale angles ≤ -cosineScaleMidpoint dimension}

noncomputable def positiveSpectralLocalDomain
    (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  {angles | cosineScaleMidpoint dimension ≤ cosineCubeScale angles}

noncomputable def allPlusNegativeLocalNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (negativeSpectralLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        cosineCubeWeight dimension 0 angles)
    angles

noncomputable def allPlusNegativeLocalNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    allPlusNegativeLocalNormalizedIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

noncomputable def allMinusPositiveSpectralNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (positiveSpectralLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        allMinusAngleWeight dimension angles)
    angles

theorem measurableSet_positiveSpectralLocalDomain (dimension : ℕ) :
    MeasurableSet (positiveSpectralLocalDomain dimension) := by
  unfold positiveSpectralLocalDomain
  exact measurableSet_Ici.preimage
    (continuous_cosineCubeScale dimension).measurable

theorem negativeLocal_reflection_pointwise
    (dimension index : ℕ) (angles : Fin dimension → ℝ) :
    allPlusNegativeLocalNormalizedIntegrand dimension index
        (angleReflectionEquiv dimension angles) =
      (-1 : ℝ) ^ index *
        allMinusPositiveSpectralNormalizedIntegrand
          dimension index angles := by
  have hscale := cosineCubeScale_angleReflection dimension angles
  by_cases hdomain : angles ∈ positiveSpectralLocalDomain dimension
  · have hreflected : angleReflectionEquiv dimension angles ∈
        negativeSpectralLocalDomain dimension := by
      change cosineScaleMidpoint dimension ≤ cosineCubeScale angles at hdomain
      change cosineCubeScale (angleReflectionEquiv dimension angles) ≤
        -cosineScaleMidpoint dimension
      rw [hscale]
      linarith
    rw [allPlusNegativeLocalNormalizedIntegrand,
      indicator_of_mem hreflected,
      allMinusPositiveSpectralNormalizedIntegrand,
      indicator_of_mem hdomain,
      hscale, fibonacciScaleKernel_neg,
      cosineCubeWeight_angleReflection]
    ring
  · have hreflected : angleReflectionEquiv dimension angles ∉
        negativeSpectralLocalDomain dimension := by
      intro hreflected
      apply hdomain
      change cosineCubeScale (angleReflectionEquiv dimension angles) ≤
        -cosineScaleMidpoint dimension at hreflected
      change cosineScaleMidpoint dimension ≤ cosineCubeScale angles
      rw [hscale] at hreflected
      linarith
    rw [allPlusNegativeLocalNormalizedIntegrand,
      indicator_of_notMem hreflected,
      allMinusPositiveSpectralNormalizedIntegrand,
      indicator_of_notMem hdomain, mul_zero]

theorem allMinusPositiveSpectralIntegral_eq_angleLocal
    (dimension index : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      allMinusPositiveSpectralNormalizedIntegrand dimension index angles
      ∂cosineCubeProductMeasure dimension) =
      allMinusAngleLocalNormalizedIntegral dimension index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show
    (Set.univ.pi fun _ : Fin dimension => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube dimension by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube dimension) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold allMinusAngleLocalNormalizedIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube dimension
  · by_cases hlocal : angles ∈ positiveSpectralLocalDomain dimension
    · have hangleLocal : angles ∈ anglePositiveLocalDomain dimension := by
        exact ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        allMinusPositiveSpectralNormalizedIntegrand,
        Set.indicator_of_mem hlocal,
        allMinusAngleLocalNormalizedIntegrand,
        Set.indicator_of_mem hangleLocal]
    · rw [Set.indicator_of_mem hcube,
        allMinusPositiveSpectralNormalizedIntegrand,
        Set.indicator_of_notMem hlocal,
        allMinusAngleLocalNormalizedIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      allMinusAngleLocalNormalizedIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem allPlusNegativeLocalNormalizedIntegral_eq
    (dimension index : ℕ) :
    allPlusNegativeLocalNormalizedIntegral dimension index =
      (-1 : ℝ) ^ index *
        allMinusAngleLocalNormalizedIntegral dimension index := by
  unfold allPlusNegativeLocalNormalizedIntegral
  rw [← (measurePreserving_angleReflectionEquiv dimension).integral_comp'
    (allPlusNegativeLocalNormalizedIntegrand dimension index)]
  rw [show
    (fun angles : Fin dimension → ℝ =>
      allPlusNegativeLocalNormalizedIntegrand dimension index
        (angleReflectionEquiv dimension angles)) =
      fun angles => (-1 : ℝ) ^ index *
        allMinusPositiveSpectralNormalizedIntegrand dimension index angles by
    funext angles
    exact negativeLocal_reflection_pointwise dimension index angles]
  rw [integral_const_mul,
    allMinusPositiveSpectralIntegral_eq_angleLocal]

theorem tendsto_allPlusNegativeLocalNormalizedIntegral
    (dimension : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    Tendsto
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          allPlusNegativeLocalNormalizedIntegral dimension index)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ‖Real.sqrt (index + 1 : ℝ) ^ dimension *
        allMinusAngleLocalNormalizedIntegral dimension index‖)
  · intro index
    rw [allPlusNegativeLocalNormalizedIntegral_eq]
    simp [norm_mul]
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_allMinusAngleLocalNormalizedIntegral dimension hdimension

end FibonacciRibbonKernel
