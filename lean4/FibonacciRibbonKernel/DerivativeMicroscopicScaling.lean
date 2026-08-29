import FibonacciRibbonKernel.FibonacciKernelLocalDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace FibonacciRibbonKernel

open Filter

theorem tendsto_microscopic_derivative
    {function : ℝ → ℝ} {point derivative displacement : ℝ}
    (hderivative : HasDerivAt function derivative point) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (function (point + displacement / (index + 1 : ℝ)) -
            function point))
      atTop (nhds (displacement * derivative)) := by
  by_cases hdisplacement : displacement = 0
  · subst displacement
    simp
  have hzero : Tendsto
      (fun index : ℕ => displacement / (index + 1 : ℝ))
      atTop (nhds 0) := by
    have hbase := (tendsto_const_div_pow displacement 1 (by omega)).comp
      (tendsto_add_atTop_nat 1)
    apply hbase.congr'
    filter_upwards with index
    simp only [Function.comp_apply, pow_one]
    push_cast
    rfl
  have hnonzero : ∀ᶠ index : ℕ in atTop,
      displacement / (index + 1 : ℝ) ≠ 0 := by
    filter_upwards with index
    exact div_ne_zero hdisplacement (by positivity)
  have hpunctured : Tendsto
      (fun index : ℕ => displacement / (index + 1 : ℝ))
      atTop (nhdsWithin 0 {0}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero, hnonzero⟩
  have hslope := hderivative.tendsto_slope_zero.comp hpunctured
  have hconstant : Tendsto (fun _ : ℕ => displacement)
      atTop (nhds displacement) := tendsto_const_nhds
  have hscaled := hconstant.mul hslope
  apply hscaled.congr'
  filter_upwards with index
  have hdenominator : (index + 1 : ℝ) ≠ 0 := by positivity
  have hfactor : displacement *
      (displacement / (index + 1 : ℝ))⁻¹ = (index + 1 : ℝ) := by
    field_simp [hdenominator, hdisplacement]
  change displacement *
      ((displacement / (index + 1 : ℝ))⁻¹ *
        (function (point + displacement / (index + 1 : ℝ)) -
          function point)) =
    (index + 1 : ℝ) *
      (function (point + displacement / (index + 1 : ℝ)) -
        function point)
  rw [← mul_assoc, hfactor]

theorem tendsto_log_largeScalePreimage_microscopic
    {scale displacement : ℝ} (hscale : 2 < scale) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (Real.log (largeScalePreimage
              (scale + displacement / (index + 1 : ℝ))) -
            Real.log (largeScalePreimage scale)))
      atTop
      (nhds (displacement / Real.sqrt (scale ^ 2 - 4))) := by
  have h := tendsto_microscopic_derivative
    (hasDerivAt_log_largeScalePreimage hscale)
    (displacement := displacement)
  simpa only [div_eq_mul_inv, one_div, one_mul] using h

end FibonacciRibbonKernel
