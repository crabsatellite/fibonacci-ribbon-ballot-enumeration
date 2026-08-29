import FibonacciRibbonKernel.FibonacciKernelRealScale

namespace FibonacciRibbonKernel

theorem hasDerivAt_largeScalePreimage
    {scale : ℝ} (hscale : 2 < scale) :
    HasDerivAt largeScalePreimage
      (largeScalePreimage scale / Real.sqrt (scale ^ 2 - 4)) scale := by
  have hdisc : scale ^ 2 - 4 ≠ 0 := by nlinarith
  have hinside : HasDerivAt (fun value : ℝ => value ^ 2 - 4)
      (2 * scale) scale := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using
      (hasDerivAt_pow 2 scale).sub_const 4
  have hsqrtRaw := (Real.hasDerivAt_sqrt hdisc).comp scale hinside
  have hsqrt : HasDerivAt
      (fun value : ℝ => Real.sqrt (value ^ 2 - 4))
      ((2 * scale) / (2 * Real.sqrt (scale ^ 2 - 4))) scale := by
    have hsqrtFunction : HasDerivAt
        (fun value : ℝ => Real.sqrt (value ^ 2 - 4))
        (1 / (2 * Real.sqrt (scale ^ 2 - 4)) * (2 * scale)) scale :=
      hsqrtRaw.congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun value => rfl
    apply hsqrtFunction.congr_deriv
    ring
  have hsum := (hasDerivAt_id scale).add hsqrt
  have hdiv := hsum.div_const 2
  have hfunction : HasDerivAt largeScalePreimage
      ((1 + (2 * scale) / (2 * Real.sqrt (scale ^ 2 - 4))) / 2) scale :=
    hdiv.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun value => by
      simp [largeScalePreimage]
  have hsqrtPos : 0 < Real.sqrt (scale ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  apply hfunction.congr_deriv
  unfold largeScalePreimage
  field_simp [hsqrtPos.ne']
  ring

theorem hasDerivAt_log_largeScalePreimage
    {scale : ℝ} (hscale : 2 < scale) :
    HasDerivAt (fun value => Real.log (largeScalePreimage value))
      (1 / Real.sqrt (scale ^ 2 - 4)) scale := by
  have halphaPos := largeScalePreimage_pos hscale.le
  have hlog := (Real.hasDerivAt_log halphaPos.ne').comp scale
    (hasDerivAt_largeScalePreimage hscale)
  have hroot : Real.sqrt (scale ^ 2 - 4) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    nlinarith
  have hderivative :
      (largeScalePreimage scale / Real.sqrt (scale ^ 2 - 4)) /
          largeScalePreimage scale =
        1 / Real.sqrt (scale ^ 2 - 4) := by
    field_simp [halphaPos.ne', hroot]
  have hlogFunction : HasDerivAt
      (fun value => Real.log (largeScalePreimage value))
      ((largeScalePreimage scale)⁻¹ *
        (largeScalePreimage scale / Real.sqrt (scale ^ 2 - 4))) scale :=
    hlog.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun value => rfl
  apply hlogFunction.congr_deriv
  calc
    (largeScalePreimage scale)⁻¹ *
          (largeScalePreimage scale / Real.sqrt (scale ^ 2 - 4)) =
        (largeScalePreimage scale / Real.sqrt (scale ^ 2 - 4)) /
          largeScalePreimage scale := by
      rw [div_eq_mul_inv]
      ring
    _ = _ := hderivative

theorem continuousAt_largeScalePreimage
    {scale : ℝ} (hscale : 2 < scale) :
    ContinuousAt largeScalePreimage scale :=
  (hasDerivAt_largeScalePreimage hscale).continuousAt

theorem continuousAt_log_largeScalePreimage
    {scale : ℝ} (hscale : 2 < scale) :
    ContinuousAt (fun value => Real.log (largeScalePreimage value)) scale :=
  (hasDerivAt_log_largeScalePreimage hscale).continuousAt

theorem largeScalePreimage_natCast (alphabetSize : ℕ) :
    largeScalePreimage (alphabetSize : ℝ) = fixedRankGrowth alphabetSize := by
  unfold largeScalePreimage fixedRankGrowth
  rfl

end FibonacciRibbonKernel
