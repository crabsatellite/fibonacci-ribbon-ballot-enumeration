import FibonacciRibbonKernel.AllPlusLocalAsymptotic

namespace FibonacciRibbonKernel

noncomputable def fibonacciAbsoluteKernel (bound : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => bound
  | power + 2 =>
      bound * fibonacciAbsoluteKernel bound (power + 1) +
        fibonacciAbsoluteKernel bound power

noncomputable def absoluteKernelGrowth (bound : ℝ) : ℝ :=
  (bound + Real.sqrt (bound ^ 2 + 4)) / 2

@[simp] theorem fibonacciAbsoluteKernel_zero (bound : ℝ) :
    fibonacciAbsoluteKernel bound 0 = 1 := rfl

@[simp] theorem fibonacciAbsoluteKernel_one (bound : ℝ) :
    fibonacciAbsoluteKernel bound 1 = bound := rfl

@[simp] theorem fibonacciAbsoluteKernel_succ_succ (bound : ℝ) (power : ℕ) :
    fibonacciAbsoluteKernel bound (power + 2) =
      bound * fibonacciAbsoluteKernel bound (power + 1) +
        fibonacciAbsoluteKernel bound power := rfl

theorem fibonacciAbsoluteKernel_nonneg
    {bound : ℝ} (hbound : 0 ≤ bound) (power : ℕ) :
    0 ≤ fibonacciAbsoluteKernel bound power := by
  induction power using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hbound
  | more power hzero hone =>
      rw [fibonacciAbsoluteKernel_succ_succ]
      positivity

theorem abs_fibonacciScaleKernel_le_absolute
    {bound scale : ℝ} (hbound : 0 ≤ bound) (hscale : |scale| ≤ bound)
    (power : ℕ) :
    |fibonacciScaleKernel scale power| ≤
      fibonacciAbsoluteKernel bound power := by
  induction power using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hscale
  | more power hzero hone =>
      rw [fibonacciScaleKernel_succ_succ,
        fibonacciAbsoluteKernel_succ_succ]
      calc
        |scale * fibonacciScaleKernel scale (power + 1) -
            fibonacciScaleKernel scale power| ≤
          |scale| * |fibonacciScaleKernel scale (power + 1)| +
            |fibonacciScaleKernel scale power| := by
          calc
            |scale * fibonacciScaleKernel scale (power + 1) -
                fibonacciScaleKernel scale power| =
            |scale * fibonacciScaleKernel scale (power + 1) +
                (-fibonacciScaleKernel scale power)| := by ring_nf
            _ ≤ |scale * fibonacciScaleKernel scale (power + 1)| +
                |-fibonacciScaleKernel scale power| := abs_add_le _ _
            _ = |scale| * |fibonacciScaleKernel scale (power + 1)| +
                |fibonacciScaleKernel scale power| := by
              rw [abs_mul, abs_neg]
        _ ≤ bound * fibonacciAbsoluteKernel bound (power + 1) +
            fibonacciAbsoluteKernel bound power := by
          exact add_le_add
            (mul_le_mul hscale hone (abs_nonneg _) hbound)
            hzero

theorem absoluteKernelGrowth_pos
    {bound : ℝ} (hbound : 0 ≤ bound) :
    0 < absoluteKernelGrowth bound := by
  unfold absoluteKernelGrowth
  have hsqrt : 0 < Real.sqrt (bound ^ 2 + 4) := by positivity
  positivity

theorem absoluteKernelGrowth_ge_bound
    {bound : ℝ} (hbound : 0 ≤ bound) :
    bound ≤ absoluteKernelGrowth bound := by
  unfold absoluteKernelGrowth
  have hsqrt : bound ≤ Real.sqrt (bound ^ 2 + 4) := by
    have hsqrtNonneg : 0 ≤ Real.sqrt (bound ^ 2 + 4) :=
      Real.sqrt_nonneg _
    have hsqrtSq : Real.sqrt (bound ^ 2 + 4) ^ 2 = bound ^ 2 + 4 :=
      Real.sq_sqrt (by positivity)
    nlinarith
  linarith

theorem absoluteKernelGrowth_quadratic
    {bound : ℝ} (_hbound : 0 ≤ bound) :
    absoluteKernelGrowth bound ^ 2 =
      bound * absoluteKernelGrowth bound + 1 := by
  unfold absoluteKernelGrowth
  have hsqrtSq : Real.sqrt (bound ^ 2 + 4) ^ 2 = bound ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  nlinarith

theorem fibonacciAbsoluteKernel_le_growth_pow
    {bound : ℝ} (hbound : 1 ≤ bound) (power : ℕ) :
    fibonacciAbsoluteKernel bound power ≤ absoluteKernelGrowth bound ^ power := by
  have hboundNonneg : 0 ≤ bound := zero_le_one.trans hbound
  have hgrowthPos := absoluteKernelGrowth_pos hboundNonneg
  have hgrowthGe := absoluteKernelGrowth_ge_bound hboundNonneg
  have hquadratic := absoluteKernelGrowth_quadratic hboundNonneg
  induction power using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hgrowthGe
  | more power hzero hone =>
      rw [fibonacciAbsoluteKernel_succ_succ]
      calc
        bound * fibonacciAbsoluteKernel bound (power + 1) +
            fibonacciAbsoluteKernel bound power ≤
          bound * absoluteKernelGrowth bound ^ (power + 1) +
            absoluteKernelGrowth bound ^ power := by
          exact add_le_add (mul_le_mul_of_nonneg_left hone hboundNonneg) hzero
        _ = absoluteKernelGrowth bound ^ (power + 2) := by
          rw [show power + 2 = power + 1 + 1 by omega,
            pow_succ, pow_succ]
          calc
            bound * (absoluteKernelGrowth bound ^ power *
                absoluteKernelGrowth bound) +
                absoluteKernelGrowth bound ^ power =
              absoluteKernelGrowth bound ^ power *
                (bound * absoluteKernelGrowth bound + 1) := by ring
            _ = absoluteKernelGrowth bound ^ power *
                absoluteKernelGrowth bound ^ 2 := by rw [hquadratic]
            _ = absoluteKernelGrowth bound ^ (power + 2) := by
              rw [pow_two, pow_succ]
              ring

theorem abs_fibonacciScaleKernel_le_growth_pow
    {bound scale : ℝ} (hbound : 1 ≤ bound) (hscale : |scale| ≤ bound)
    (power : ℕ) :
    |fibonacciScaleKernel scale power| ≤ absoluteKernelGrowth bound ^ power :=
  (abs_fibonacciScaleKernel_le_absolute (zero_le_one.trans hbound)
    hscale power).trans (fibonacciAbsoluteKernel_le_growth_pow hbound power)

theorem absoluteKernelGrowth_midpoint_lt_baseGrowth
    {dimension : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    absoluteKernelGrowth (cosineScaleMidpoint dimension) <
      largeScalePreimage (2 * dimension : ℝ) := by
  let base : ℝ := 2 * dimension
  let midpoint : ℝ := cosineScaleMidpoint dimension
  let gamma : ℝ := absoluteKernelGrowth midpoint
  let alpha : ℝ := largeScalePreimage base
  have hbase : 4 ≤ base := hdimension
  have hmidpoint : midpoint = (base + 2) / 2 := rfl
  have hmidpointNonneg : 0 ≤ midpoint := by linarith
  have hgammaPos : 0 < gamma := absoluteKernelGrowth_pos hmidpointNonneg
  have halphaPos : 0 < alpha := largeScalePreimage_pos (by linarith)
  have hsqrtPos : 0 < Real.sqrt (base ^ 2 - 4) := by
    exact Real.sqrt_pos.2 (by nlinarith)
  have halphaGtTwo : 2 < alpha := by
    dsimp [alpha, largeScalePreimage]
    linarith
  have hgammaEq : gamma ^ 2 = midpoint * gamma + 1 :=
    absoluteKernelGrowth_quadratic hmidpointNonneg
  have halphaEq : alpha ^ 2 = base * alpha - 1 := by
    have hquad := positiveScalePreimage_quadratic (show 2 ≤ base by linarith)
    have hmul := positiveScalePreimage_mul_largeScalePreimage
      (show 2 ≤ base by linarith)
    have hsum := largeScalePreimage_add_positiveScalePreimage base
    nlinarith
  by_contra hnot
  have hle : alpha ≤ gamma := le_of_not_gt hnot
  have hgammaLower : 3 ≤ gamma := by
    have hmid : 3 ≤ midpoint := by rw [hmidpoint]; linarith
    exact hmid.trans (absoluteKernelGrowth_ge_bound hmidpointNonneg)
  have hleftNonneg :
      0 ≤ (gamma - alpha) * (gamma + alpha - midpoint) := by
    apply mul_nonneg
    · exact sub_nonneg.2 hle
    · nlinarith
  have hidentity :
      (gamma - alpha) * (gamma + alpha - midpoint) =
        2 - (base - midpoint) * alpha := by
    nlinarith [hgammaEq, halphaEq]
  have hrightNeg : 2 - (base - midpoint) * alpha < 0 := by
    rw [hmidpoint]
    nlinarith
  rw [hidentity] at hleftNonneg
  linarith

end FibonacciRibbonKernel
