import FibonacciRibbonKernel.FibonacciMiddleDecay

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable def allPlusMiddleDomain
    (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  anglePositiveCube dimension ∩
    {angles | |cosineCubeScale angles| ≤ cosineScaleMidpoint dimension}

noncomputable def allPlusMiddleNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (allPlusMiddleDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        cosineCubeWeight dimension 0 angles)
    angles

noncomputable def allPlusMiddleNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    allPlusMiddleNormalizedIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

theorem abs_cosineFactorWeight_le_two
    (plusFactor : Bool) (angle : ℝ) :
    |cosineFactorWeight plusFactor angle| ≤ 2 := by
  unfold cosineFactorWeight
  split
  · rw [abs_of_nonneg]
    · linarith [Real.cos_le_one angle]
    · linarith [Real.neg_one_le_cos angle]
  · rw [abs_of_nonneg]
    · linarith [Real.neg_one_le_cos angle]
    · linarith [Real.cos_le_one angle]

theorem abs_cosineCubeWeight_le_two_pow
    (plusPower minusPower : ℕ)
    (angles : Fin (plusPower + minusPower) → ℝ) :
    |cosineCubeWeight plusPower minusPower angles| ≤
      (2 : ℝ) ^ (plusPower + minusPower) := by
  unfold cosineCubeWeight
  rw [Finset.abs_prod]
  calc
    ∏ coordinate,
        |cosineFactorWeight
          (cosineCoordinateIsPlus plusPower minusPower coordinate)
          (angles coordinate)| ≤
      ∏ _coordinate : Fin (plusPower + minusPower), (2 : ℝ) := by
        exact Finset.prod_le_prod
          (fun coordinate _hcoordinate => abs_nonneg _)
          (fun coordinate _hcoordinate =>
            abs_cosineFactorWeight_le_two _ (angles coordinate))
    _ = (2 : ℝ) ^ (plusPower + minusPower) := by simp

theorem abs_middle_normalized_kernel_le
    {dimension index : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ))
    {scale : ℝ} (hscale : |scale| ≤ cosineScaleMidpoint dimension) :
    |fibonacciScaleKernel scale index /
        (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))| ≤
      Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
        fibonacciMiddleGrowthRatio dimension ^ (index + 1) := by
  let alpha := largeScalePreimage (2 * dimension : ℝ)
  let gamma := absoluteKernelGrowth (cosineScaleMidpoint dimension)
  let root := Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)
  have hmidOne : 1 ≤ cosineScaleMidpoint dimension := by
    unfold cosineScaleMidpoint
    linarith
  have hkernel : |fibonacciScaleKernel scale index| ≤ gamma ^ index :=
    abs_fibonacciScaleKernel_le_growth_pow hmidOne hscale index
  have halphaPos : 0 < alpha := largeScalePreimage_pos (by linarith)
  have hrootPos : 0 < root := by
    dsimp [root]
    exact Real.sqrt_pos.2 (by nlinarith)
  have hdenomPos : 0 < alpha ^ (index + 1) / root :=
    div_pos (pow_pos halphaPos _) hrootPos
  have hmidNonneg : 0 ≤ cosineScaleMidpoint dimension := by
    unfold cosineScaleMidpoint
    positivity
  have hgammaPos : 0 < gamma := absoluteKernelGrowth_pos hmidNonneg
  rw [abs_div, abs_of_pos hdenomPos]
  calc
    |fibonacciScaleKernel scale index| /
        (alpha ^ (index + 1) / root) =
      (|fibonacciScaleKernel scale index| * root) /
        alpha ^ (index + 1) := by field_simp
    _ ≤ (gamma ^ index * root) / alpha ^ (index + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkernel hrootPos.le)
        (pow_nonneg halphaPos.le _)
    _ ≤ (gamma ^ (index + 1) * root) / alpha ^ (index + 1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg halphaPos.le _)
      apply mul_le_mul_of_nonneg_right _ hrootPos.le
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hgammaPos.le _)
        (absoluteKernelGrowth_ge_bound (by
          unfold cosineScaleMidpoint
          positivity) |>.trans' hmidOne)
    _ = root * (gamma / alpha) ^ (index + 1) := by
      rw [div_pow]
      ring
    _ = _ := by rfl

theorem norm_allPlusMiddleNormalizedIntegrand_le
    {dimension index : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ))
    (angles : Fin dimension → ℝ) :
    ‖allPlusMiddleNormalizedIntegrand dimension index angles‖ ≤
      (1 / Real.pi) ^ dimension *
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
        (2 : ℝ) ^ dimension *
        fibonacciMiddleGrowthRatio dimension ^ (index + 1) := by
  by_cases hdomain : angles ∈ allPlusMiddleDomain dimension
  · rw [allPlusMiddleNormalizedIntegrand, indicator_of_mem hdomain,
      Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
    have hkernel := abs_middle_normalized_kernel_le
      (dimension := dimension) (index := index) hdimension hdomain.2
    have hweight := abs_cosineCubeWeight_le_two_pow dimension 0 angles
    norm_num at hweight
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hkernel (pow_nonneg (by positivity) _))
      hweight (abs_nonneg _)
      (mul_nonneg (pow_nonneg (by positivity) _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg (fibonacciMiddleGrowthRatio_pos hdimension).le _)))
      |>.trans_eq (by ring)
  · rw [allPlusMiddleNormalizedIntegrand, indicator_of_notMem hdomain, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _)
          (Real.sqrt_nonneg _))
        (pow_nonneg (by positivity) _))
      (pow_nonneg (fibonacciMiddleGrowthRatio_pos hdimension).le _)

theorem norm_allPlusMiddleNormalizedIntegral_le
    {dimension index : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    ‖allPlusMiddleNormalizedIntegral dimension index‖ ≤
      ((1 / Real.pi) ^ dimension *
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
        (2 : ℝ) ^ dimension) *
      fibonacciMiddleGrowthRatio dimension ^ (index + 1) *
      (cosineCubeProductMeasure dimension).real Set.univ := by
  unfold allPlusMiddleNormalizedIntegral
  exact (norm_integral_le_of_norm_le_const
    (Eventually.of_forall
      (norm_allPlusMiddleNormalizedIntegrand_le hdimension))).trans_eq (by ring)

theorem tendsto_allPlusMiddleNormalizedIntegral
    (dimension : ℕ) (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    Tendsto
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          allPlusMiddleNormalizedIntegral dimension index)
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
    have hbound := norm_allPlusMiddleNormalizedIntegral_le
      (dimension := dimension) (index := index) hdimension
    exact (mul_le_mul_of_nonneg_left hbound
      (pow_nonneg (Real.sqrt_nonneg _) _)).trans_eq (by ring)
  · simpa using (tendsto_sqrt_pow_mul_fibonacciMiddleGrowthRatio
      dimension hdimension).mul_const constant

end FibonacciRibbonKernel
