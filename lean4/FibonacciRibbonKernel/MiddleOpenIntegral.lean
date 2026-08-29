import FibonacciRibbonKernel.NegativeLocalIntegral

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def middleOpenSpectralDomain
    (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  {angles |
    -cosineScaleMidpoint dimension < cosineCubeScale angles ∧
      cosineCubeScale angles < cosineScaleMidpoint dimension}

noncomputable def allPlusMiddleOpenNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (middleOpenSpectralDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        cosineCubeWeight dimension 0 angles)
    angles

noncomputable def allPlusMiddleOpenNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    allPlusMiddleOpenNormalizedIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

theorem middleOpen_abs_scale_le
    {dimension : ℕ} {angles : Fin dimension → ℝ}
    (hangles : angles ∈ middleOpenSpectralDomain dimension) :
    |cosineCubeScale angles| ≤ cosineScaleMidpoint dimension := by
  unfold middleOpenSpectralDomain at hangles
  rw [abs_le]
  exact ⟨hangles.1.le, hangles.2.le⟩

theorem norm_allPlusMiddleOpenNormalizedIntegrand_le
    {dimension index : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ))
    (angles : Fin dimension → ℝ) :
    ‖allPlusMiddleOpenNormalizedIntegrand dimension index angles‖ ≤
      (1 / Real.pi) ^ dimension *
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
        (2 : ℝ) ^ dimension *
        fibonacciMiddleGrowthRatio dimension ^ (index + 1) := by
  by_cases hdomain : angles ∈ middleOpenSpectralDomain dimension
  · rw [allPlusMiddleOpenNormalizedIntegrand, indicator_of_mem hdomain,
      Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    have hkernel := abs_middle_normalized_kernel_le
      (dimension := dimension) (index := index) hdimension
      (middleOpen_abs_scale_le hdomain)
    have hweight := abs_cosineCubeWeight_le_two_pow dimension 0 angles
    norm_num at hweight
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hkernel (pow_nonneg (by positivity) _))
      hweight (abs_nonneg _)
      (mul_nonneg (pow_nonneg (by positivity) _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg (fibonacciMiddleGrowthRatio_pos hdimension).le _)))
      |>.trans_eq (by ring)
  · rw [allPlusMiddleOpenNormalizedIntegrand,
      indicator_of_notMem hdomain, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _)
          (Real.sqrt_nonneg _))
        (pow_nonneg (by positivity) _))
      (pow_nonneg (fibonacciMiddleGrowthRatio_pos hdimension).le _)

theorem norm_allPlusMiddleOpenNormalizedIntegral_le
    {dimension index : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    ‖allPlusMiddleOpenNormalizedIntegral dimension index‖ ≤
      ((1 / Real.pi) ^ dimension *
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
        (2 : ℝ) ^ dimension) *
      fibonacciMiddleGrowthRatio dimension ^ (index + 1) *
      (cosineCubeProductMeasure dimension).real Set.univ := by
  unfold allPlusMiddleOpenNormalizedIntegral
  exact (norm_integral_le_of_norm_le_const
    (Eventually.of_forall
      (norm_allPlusMiddleOpenNormalizedIntegrand_le hdimension))).trans_eq (by ring)

theorem tendsto_allPlusMiddleOpenNormalizedIntegral
    (dimension : ℕ) (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    Tendsto
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          allPlusMiddleOpenNormalizedIntegral dimension index)
      atTop (nhds 0) := by
  let constant : ℝ :=
    ((1 / Real.pi) ^ dimension *
      Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
      (2 : ℝ) ^ dimension) *
      (cosineCubeProductMeasure dimension).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      (Real.sqrt (index + 1 : ℝ) ^ dimension *
        fibonacciMiddleGrowthRatio dimension ^ (index + 1)) * constant)
  · intro index
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
    have hbound := norm_allPlusMiddleOpenNormalizedIntegral_le
      (dimension := dimension) (index := index) hdimension
    exact (mul_le_mul_of_nonneg_left hbound
      (pow_nonneg (Real.sqrt_nonneg _) _)).trans_eq (by ring)
  · simpa using (tendsto_sqrt_pow_mul_fibonacciMiddleGrowthRatio
      dimension hdimension).mul_const constant

end FibonacciRibbonKernel
