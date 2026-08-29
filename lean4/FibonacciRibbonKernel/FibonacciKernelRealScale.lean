import FibonacciRibbonKernel.FibonacciKernelSeries

namespace FibonacciRibbonKernel

theorem largeScalePreimage_add_positiveScalePreimage
    (scale : ℝ) :
    largeScalePreimage scale + positiveScalePreimage scale = scale := by
  unfold largeScalePreimage positiveScalePreimage
  ring

theorem largeScalePreimage_sub_positiveScalePreimage
    (scale : ℝ) :
    largeScalePreimage scale - positiveScalePreimage scale =
      Real.sqrt (scale ^ 2 - 4) := by
  unfold largeScalePreimage positiveScalePreimage
  ring

theorem largeScalePreimage_ne_positiveScalePreimage
    {scale : ℝ} (hscale : 2 < scale) :
    largeScalePreimage scale ≠ positiveScalePreimage scale := by
  have hsqrt : 0 < Real.sqrt (scale ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  intro heq
  have hzero : Real.sqrt (scale ^ 2 - 4) = 0 := by
    rw [← largeScalePreimage_sub_positiveScalePreimage, heq, sub_self]
  exact hsqrt.ne' hzero

theorem fibonacciScaleKernel_closed_of_two_lt
    {scale : ℝ} (hscale : 2 < scale) (power : ℕ) :
    fibonacciScaleKernel scale power =
      (largeScalePreimage scale ^ (power + 1) -
        positiveScalePreimage scale ^ (power + 1)) /
        Real.sqrt (scale ^ 2 - 4) := by
  have hclosed := fibonacciScaleKernel_closed scale
    (largeScalePreimage scale) (positiveScalePreimage scale)
    (largeScalePreimage_add_positiveScalePreimage scale)
    (by rw [mul_comm]
        exact positiveScalePreimage_mul_largeScalePreimage hscale.le)
    (largeScalePreimage_ne_positiveScalePreimage hscale) power
  rw [largeScalePreimage_sub_positiveScalePreimage] at hclosed
  exact hclosed

theorem fibonacciScaleKernel_neg (scale : ℝ) (power : ℕ) :
    fibonacciScaleKernel (-scale) power =
      (-1 : ℝ) ^ power * fibonacciScaleKernel scale power := by
  induction power using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more power hzero hone =>
      rw [fibonacciScaleKernel_succ_succ,
        fibonacciScaleKernel_succ_succ, hzero, hone]
      rw [show power + 2 = power + 1 + 1 by omega,
        pow_succ, pow_succ]
      ring

theorem largeScalePreimage_pos
    {scale : ℝ} (hscale : 2 ≤ scale) :
    0 < largeScalePreimage scale := by
  unfold largeScalePreimage
  positivity

theorem positiveScalePreimage_lt_largeScalePreimage
    {scale : ℝ} (hscale : 2 < scale) :
    positiveScalePreimage scale < largeScalePreimage scale := by
  have hsqrt : 0 < Real.sqrt (scale ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hdiff := largeScalePreimage_sub_positiveScalePreimage scale
  linarith

theorem positiveScalePreimage_div_large_nonneg
    {scale : ℝ} (hscale : 2 ≤ scale) :
    0 ≤ positiveScalePreimage scale / largeScalePreimage scale :=
  (div_pos (positiveScalePreimage_pos hscale)
    (largeScalePreimage_pos hscale)).le

theorem positiveScalePreimage_div_large_lt_one
    {scale : ℝ} (hscale : 2 < scale) :
    positiveScalePreimage scale / largeScalePreimage scale < 1 := by
  rw [div_lt_one (largeScalePreimage_pos hscale.le)]
  exact positiveScalePreimage_lt_largeScalePreimage hscale

end FibonacciRibbonKernel
