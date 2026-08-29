import FibonacciRibbonKernel.FibonacciGaussianDominance

namespace FibonacciRibbonKernel

open scoped BigOperators

noncomputable def cosineScaleMidpoint (dimension : ℕ) : ℝ :=
  ((2 * dimension : ℝ) + 2) / 2

theorem cosineScaleMidpoint_gt_two
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ)) :
    2 < cosineScaleMidpoint dimension := by
  unfold cosineScaleMidpoint
  linarith

theorem cosineScaleMidpoint_lt_base
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ)) :
    cosineScaleMidpoint dimension < (2 * dimension : ℝ) := by
  unfold cosineScaleMidpoint
  linarith

theorem cosineScale_root_ratio_le_midpoint
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    {scale : ℝ} (hscale : cosineScaleMidpoint dimension ≤ scale) :
    Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
        Real.sqrt (scale ^ 2 - 4) ≤
      Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
        Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4) := by
  have hmidPos : 0 < cosineScaleMidpoint dimension :=
    (cosineScaleMidpoint_gt_two hdimension).trans' zero_lt_two
  have hsq : cosineScaleMidpoint dimension ^ 2 - 4 ≤ scale ^ 2 - 4 := by
    nlinarith
  have hsqrt : Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4) ≤
      Real.sqrt (scale ^ 2 - 4) := Real.sqrt_le_sqrt hsq
  have hmidRootPos : 0 < Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith [cosineScaleMidpoint_gt_two hdimension]
  have hbaseRootNonneg :
      0 ≤ Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := Real.sqrt_nonneg _
  exact div_le_div_of_nonneg_left hbaseRootNonneg hmidRootPos hsqrt

theorem normalizedFibonacciCosineKernel_nonneg
    {dimension index : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hscale : 2 < cosineSumScale coordinates index) :
    0 ≤ normalizedFibonacciCosineKernel coordinates index := by
  rw [normalizedFibonacciCosineKernel_factorization
    hdimension coordinates index hscale]
  have hratioNonneg : 0 ≤
      largeScalePreimage (cosineSumScale coordinates index) /
        largeScalePreimage (2 * dimension : ℝ) :=
    div_nonneg (largeScalePreimage_pos hscale.le).le
      (largeScalePreimage_pos hdimension.le).le
  have hbaseRootPos : 0 < Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hcurrentRootPos : 0 <
      Real.sqrt (cosineSumScale coordinates index ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hrootNonneg : 0 ≤
      Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
        Real.sqrt (cosineSumScale coordinates index ^ 2 - 4) :=
    (div_pos hbaseRootPos hcurrentRootPos).le
  have hqNonneg : 0 ≤ cosineScaleRootRatio
      (cosineSumScale coordinates index) :=
    positiveScalePreimage_div_large_nonneg hscale.le
  have hqLe : cosineScaleRootRatio
      (cosineSumScale coordinates index) ≤ 1 :=
    (positiveScalePreimage_div_large_lt_one hscale).le
  exact mul_nonneg (mul_nonneg (pow_nonneg hratioNonneg _) hrootNonneg)
    (sub_nonneg.mpr (pow_le_one₀ hqNonneg hqLe))

theorem normalizedFibonacciCosineKernel_le_local_gaussian
    {dimension index : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hcoordinates : ∀ coordinate,
      |coordinates coordinate| ≤ Real.pi * Real.sqrt (index + 1 : ℝ))
    (hscaleMid : cosineScaleMidpoint dimension ≤
      cosineSumScale coordinates index) :
    normalizedFibonacciCosineKernel coordinates index ≤
      (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
        Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4)) *
      Real.exp
        (-(4 / (Real.pi ^ 2 *
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
            ∑ coordinate, coordinates coordinate ^ 2) := by
  have hscale : 2 < cosineSumScale coordinates index :=
    (cosineScaleMidpoint_gt_two hdimension).trans_le hscaleMid
  rw [normalizedFibonacciCosineKernel_factorization
    hdimension coordinates index hscale]
  have halphaBound := largeScalePreimage_cosine_ratio_pow_le_gaussian
    hdimension coordinates hcoordinates hscale
  have hrootBound := cosineScale_root_ratio_le_midpoint
    hdimension hscaleMid
  have hqNonneg : 0 ≤ cosineScaleRootRatio
      (cosineSumScale coordinates index) :=
    positiveScalePreimage_div_large_nonneg hscale.le
  have hbracket : 1 - cosineScaleRootRatio
      (cosineSumScale coordinates index) ^ (index + 1) ≤ 1 := by
    linarith [pow_nonneg hqNonneg (index + 1)]
  have halphaNonneg : 0 ≤
      (largeScalePreimage (cosineSumScale coordinates index) /
        largeScalePreimage (2 * dimension : ℝ)) ^ (index + 1) := by
    apply pow_nonneg
    exact div_nonneg (largeScalePreimage_pos hscale.le).le
      (largeScalePreimage_pos hdimension.le).le
  have hbaseRootPos : 0 < Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hcurrentRootPos : 0 <
      Real.sqrt (cosineSumScale coordinates index ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hrootNonneg : 0 ≤ Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
      Real.sqrt (cosineSumScale coordinates index ^ 2 - 4) :=
    (div_pos hbaseRootPos hcurrentRootPos).le
  calc
    (largeScalePreimage (cosineSumScale coordinates index) /
          largeScalePreimage (2 * dimension : ℝ)) ^ (index + 1) *
        (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
          Real.sqrt (cosineSumScale coordinates index ^ 2 - 4)) *
        (1 - cosineScaleRootRatio
          (cosineSumScale coordinates index) ^ (index + 1)) ≤
      (largeScalePreimage (cosineSumScale coordinates index) /
          largeScalePreimage (2 * dimension : ℝ)) ^ (index + 1) *
        (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
          Real.sqrt (cosineSumScale coordinates index ^ 2 - 4)) * 1 :=
      mul_le_mul_of_nonneg_left hbracket (mul_nonneg halphaNonneg hrootNonneg)
    _ ≤ Real.exp
          (-(4 / (Real.pi ^ 2 *
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
              ∑ coordinate, coordinates coordinate ^ 2) *
        (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
          Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4)) := by
      simpa only [mul_one] using mul_le_mul halphaBound hrootBound
        hrootNonneg (Real.exp_pos _).le
    _ = _ := by ring

end FibonacciRibbonKernel
