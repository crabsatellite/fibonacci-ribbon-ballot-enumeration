import FibonacciRibbonKernel.CosineQuadraticScaling
import Mathlib.Analysis.Calculus.DSlope

namespace FibonacciRibbonKernel

open Filter

theorem tendsto_variable_microscopic_derivative
    {function : ℝ → ℝ} {point derivative limit : ℝ}
    {displacement : ℕ → ℝ}
    (hderivative : HasDerivAt function derivative point)
    (hdisplacement : Tendsto displacement atTop (nhds limit)) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (function (point + displacement index / (index + 1 : ℝ)) -
            function point))
      atTop (nhds (limit * derivative)) := by
  have hinverse : Tendsto (fun index : ℕ => 1 / (index + 1 : ℝ))
      atTop (nhds 0) := by
    have hbase := (tendsto_const_div_pow 1 1 (by omega)).comp
      (tendsto_add_atTop_nat 1)
    apply hbase.congr'
    filter_upwards with index
    simp only [Function.comp_apply, pow_one]
    push_cast
    rfl
  have hsmall : Tendsto
      (fun index : ℕ => displacement index / (index + 1 : ℝ))
      atTop (nhds 0) := by
    have hproduct := hdisplacement.mul hinverse
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hproduct
  have hpoint : Tendsto
      (fun index : ℕ => point + displacement index / (index + 1 : ℝ))
      atTop (nhds point) := by
    simpa using tendsto_const_nhds.add hsmall
  have hdslopeContinuous : ContinuousAt (dslope function point) point :=
    continuousAt_dslope_same.2 hderivative.differentiableAt
  have hdslope := hdslopeContinuous.tendsto.comp hpoint
  have hproduct := hdisplacement.mul hdslope
  have hdslopeValue : dslope function point point = derivative := by
    rw [dslope_same, hderivative.deriv]
  rw [hdslopeValue] at hproduct
  apply hproduct.congr'
  filter_upwards with index
  simp only [Function.comp_apply]
  have hdenominator : (index + 1 : ℝ) ≠ 0 := by positivity
  have hslope := sub_smul_dslope function point
    (point + displacement index / (index + 1 : ℝ))
  simp only [smul_eq_mul, add_sub_cancel_left] at hslope
  calc
    displacement index *
          dslope function point
            (point + displacement index / (index + 1 : ℝ)) =
        (index + 1 : ℝ) *
          ((displacement index / (index + 1 : ℝ)) *
            dslope function point
              (point + displacement index / (index + 1 : ℝ))) := by
      field_simp [hdenominator]
    _ = (index + 1 : ℝ) *
        (function (point + displacement index / (index + 1 : ℝ)) -
          function point) := by rw [hslope]

theorem tendsto_log_largeScalePreimage_variable_microscopic
    {scale limit : ℝ} {displacement : ℕ → ℝ}
    (hscale : 2 < scale)
    (hdisplacement : Tendsto displacement atTop (nhds limit)) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (Real.log (largeScalePreimage
              (scale + displacement index / (index + 1 : ℝ))) -
            Real.log (largeScalePreimage scale)))
      atTop (nhds (limit / Real.sqrt (scale ^ 2 - 4))) := by
  have h := tendsto_variable_microscopic_derivative
    (hasDerivAt_log_largeScalePreimage hscale) hdisplacement
  simpa only [one_div, div_eq_mul_inv, one_mul] using h

end FibonacciRibbonKernel
