import FibonacciRibbonKernel.OddWeylLocalScaling

namespace FibonacciRibbonKernel

open scoped BigOperators

theorem oddCosineScaleMidpoint_gt_two
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ)) :
    2 < oddCosineScaleMidpoint dimension := by
  unfold oddCosineScaleMidpoint
  linarith

theorem oddCosineScale_root_ratio_le_midpoint
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    {scale : ℝ} (hscale : oddCosineScaleMidpoint dimension ≤ scale) :
    Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
        Real.sqrt (scale ^ 2 - 4) ≤
      Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
        Real.sqrt (oddCosineScaleMidpoint dimension ^ 2 - 4) := by
  have hmidPos : 0 < oddCosineScaleMidpoint dimension :=
    (oddCosineScaleMidpoint_gt_two hdimension).trans' zero_lt_two
  have hsq : oddCosineScaleMidpoint dimension ^ 2 - 4 ≤
      scale ^ 2 - 4 := by nlinarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  have hmidRootPos : 0 <
      Real.sqrt (oddCosineScaleMidpoint dimension ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith [oddCosineScaleMidpoint_gt_two hdimension]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
    hmidRootPos hsqrt

theorem largeScalePreimage_oddCosine_ratio_pow_le_gaussian
    {dimension index : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hcoordinates : ∀ coordinate,
      |coordinates coordinate| ≤ Real.pi * Real.sqrt (index + 1 : ℝ))
    (hscale : 2 < oddCosineSumScale coordinates index) :
    (largeScalePreimage (oddCosineSumScale coordinates index) /
        largeScalePreimage (2 * dimension + 1 : ℝ)) ^ (index + 1) ≤
      Real.exp
        (-(4 / (Real.pi ^ 2 *
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
            ∑ coordinate, coordinates coordinate ^ 2) := by
  let base : ℝ := 2 * dimension + 1
  let current : ℝ := oddCosineSumScale coordinates index
  let root : ℝ := Real.sqrt (base ^ 2 - 4)
  let normalization : ℝ := index + 1
  let squares : ℝ := ∑ coordinate, coordinates coordinate ^ 2
  have hrootPos : 0 < root := by
    dsimp only [root, base]
    apply Real.sqrt_pos.2
    nlinarith
  have hnormalizationPos : 0 < normalization := by positivity
  have hsquaresNonneg : 0 ≤ squares := by positivity
  have hdeficit := cosineSumScale_le_quadratic coordinates hcoordinates
  have hcurrentLe : current ≤ base := by
    dsimp only [current, base]
    unfold oddCosineSumScale
    have hsubNonneg :
        0 ≤ (4 / (Real.pi ^ 2 * (index + 1 : ℝ))) *
          ∑ coordinate, coordinates coordinate ^ 2 := by positivity
    linarith
  have hratio := largeScalePreimage_ratio_le_exp_tangent_of_le
    hscale hcurrentLe
  have hratioNonneg : 0 ≤
      largeScalePreimage current / largeScalePreimage base :=
    (div_pos (largeScalePreimage_pos hscale.le)
      (largeScalePreimage_pos hdimension.le)).le
  have hpow := pow_le_pow_left₀ hratioNonneg hratio (index + 1)
  have hscaledDeficit :
      normalization * (current - base) / root ≤
        -(4 / (Real.pi ^ 2 * root)) * squares := by
    have hraw : current - base ≤
        -(4 / (Real.pi ^ 2 * normalization)) * squares := by
      dsimp only [current, base, normalization, squares]
      unfold oddCosineSumScale
      linarith
    have hmul := mul_le_mul_of_nonneg_left hraw hnormalizationPos.le
    have hdivide := div_le_div_of_nonneg_right hmul hrootPos.le
    field_simp [hnormalizationPos.ne', hrootPos.ne'] at hdivide ⊢
    exact hdivide
  calc
    (largeScalePreimage current / largeScalePreimage base) ^ (index + 1) ≤
        Real.exp ((current - base) / root) ^ (index + 1) := hpow
    _ = Real.exp (normalization * (current - base) / root) := by
      rw [← Real.exp_nat_mul]
      dsimp only [normalization]
      push_cast
      congr 1
      ring
    _ ≤ Real.exp (-(4 / (Real.pi ^ 2 * root)) * squares) :=
      Real.exp_le_exp.mpr hscaledDeficit

theorem normalizedOddFibonacciKernel_nonneg
    {dimension index : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hscale : 2 < oddCosineSumScale coordinates index) :
    0 ≤ normalizedOddFibonacciKernel coordinates index := by
  rw [normalizedOddFibonacciKernel_factorization
    hdimension coordinates hscale]
  have hratioNonneg : 0 ≤
      largeScalePreimage (oddCosineSumScale coordinates index) /
        largeScalePreimage (2 * dimension + 1 : ℝ) :=
    div_nonneg (largeScalePreimage_pos hscale.le).le
      (largeScalePreimage_pos hdimension.le).le
  have hqNonneg := positiveScalePreimage_div_large_nonneg hscale.le
  have hqLe := (positiveScalePreimage_div_large_lt_one hscale).le
  change 0 ≤ cosineScaleRootRatio
    (oddCosineSumScale coordinates index) at hqNonneg
  change cosineScaleRootRatio
    (oddCosineSumScale coordinates index) ≤ 1 at hqLe
  exact mul_nonneg
    (mul_nonneg (pow_nonneg hratioNonneg _)
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (sub_nonneg.mpr (pow_le_one₀ hqNonneg hqLe))

theorem normalizedOddFibonacciKernel_le_local_gaussian
    {dimension index : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hcoordinates : ∀ coordinate,
      |coordinates coordinate| ≤ Real.pi * Real.sqrt (index + 1 : ℝ))
    (hscaleMid : oddCosineScaleMidpoint dimension ≤
      oddCosineSumScale coordinates index) :
    normalizedOddFibonacciKernel coordinates index ≤
      (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
        Real.sqrt (oddCosineScaleMidpoint dimension ^ 2 - 4)) *
      Real.exp
        (-(4 / (Real.pi ^ 2 *
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
            ∑ coordinate, coordinates coordinate ^ 2) := by
  have hscale : 2 < oddCosineSumScale coordinates index :=
    (oddCosineScaleMidpoint_gt_two hdimension).trans_le hscaleMid
  rw [normalizedOddFibonacciKernel_factorization
    hdimension coordinates hscale]
  have halphaBound := largeScalePreimage_oddCosine_ratio_pow_le_gaussian
    hdimension coordinates hcoordinates hscale
  have hrootBound := oddCosineScale_root_ratio_le_midpoint
    hdimension hscaleMid
  have hqNonneg := positiveScalePreimage_div_large_nonneg hscale.le
  change 0 ≤ cosineScaleRootRatio
    (oddCosineSumScale coordinates index) at hqNonneg
  have hbracket : 1 - cosineScaleRootRatio
      (oddCosineSumScale coordinates index) ^ (index + 1) ≤ 1 := by
    linarith [pow_nonneg hqNonneg (index + 1)]
  have halphaNonneg : 0 ≤
      (largeScalePreimage (oddCosineSumScale coordinates index) /
        largeScalePreimage (2 * dimension + 1 : ℝ)) ^ (index + 1) := by
    exact pow_nonneg (div_nonneg
      (largeScalePreimage_pos hscale.le).le
      (largeScalePreimage_pos hdimension.le).le) _
  have hbaseRootPos : 0 <
      Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hcurrentRootPos : 0 <
      Real.sqrt (oddCosineSumScale coordinates index ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hrootNonneg : 0 ≤
      Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
        Real.sqrt (oddCosineSumScale coordinates index ^ 2 - 4) := by
    exact (div_pos hbaseRootPos hcurrentRootPos).le
  calc
    _ ≤ (largeScalePreimage (oddCosineSumScale coordinates index) /
          largeScalePreimage (2 * dimension + 1 : ℝ)) ^ (index + 1) *
        (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
          Real.sqrt (oddCosineSumScale coordinates index ^ 2 - 4)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbracket
        (mul_nonneg halphaNonneg hrootNonneg)
    _ ≤ Real.exp
          (-(4 / (Real.pi ^ 2 *
            Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
              ∑ coordinate, coordinates coordinate ^ 2) *
        (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
          Real.sqrt (oddCosineScaleMidpoint dimension ^ 2 - 4)) := by
      exact mul_le_mul halphaBound hrootBound hrootNonneg
        (Real.exp_pos _).le
    _ = _ := by ring

end FibonacciRibbonKernel
