import FibonacciRibbonKernel.CosineSumGaussianBound
import Mathlib.Analysis.Convex.Deriv

namespace FibonacciRibbonKernel

open Set

theorem antitoneOn_deriv_log_largeScalePreimage :
    AntitoneOn (deriv (fun scale => Real.log (largeScalePreimage scale)))
      (Set.Ioi 2) := by
  intro left hleft right hright hle
  have hleftScale : 2 < left := hleft
  have hrightScale : 2 < right := hright
  rw [(hasDerivAt_log_largeScalePreimage hleftScale).deriv,
    (hasDerivAt_log_largeScalePreimage hrightScale).deriv]
  have hsq : left ^ 2 - 4 ≤ right ^ 2 - 4 := by nlinarith
  have hsqrt : Real.sqrt (left ^ 2 - 4) ≤
      Real.sqrt (right ^ 2 - 4) := Real.sqrt_le_sqrt hsq
  exact one_div_le_one_div_of_le
    (Real.sqrt_pos.2 (by nlinarith)) hsqrt

theorem concaveOn_log_largeScalePreimage :
    ConcaveOn ℝ (Set.Ioi 2)
      (fun scale => Real.log (largeScalePreimage scale)) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi 2)
  · intro scale hscale
    exact (hasDerivAt_log_largeScalePreimage hscale).continuousAt.continuousWithinAt
  · intro scale hscale
    have hscale' : scale ∈ Set.Ioi 2 := interior_subset hscale
    exact (hasDerivAt_log_largeScalePreimage hscale').differentiableAt.differentiableWithinAt
  · simpa only [interior_Ioi] using antitoneOn_deriv_log_largeScalePreimage

theorem log_largeScalePreimage_tangent_bound
    {scale base : ℝ} (hscale : 2 < scale) (hbase : scale < base) :
    Real.log (largeScalePreimage scale) -
        Real.log (largeScalePreimage base) ≤
      (scale - base) / Real.sqrt (base ^ 2 - 4) := by
  have hbaseScale : 2 < base := hscale.trans hbase
  have hslope := concaveOn_log_largeScalePreimage.le_slope_of_hasDerivAt
    hscale hbaseScale hbase
    (hasDerivAt_log_largeScalePreimage hbaseScale)
  rw [slope_def_field] at hslope
  have hgap : 0 < base - scale := sub_pos.2 hbase
  have hmul := (le_div_iff₀ hgap).1 hslope
  rw [show (scale - base) / Real.sqrt (base ^ 2 - 4) =
      -(1 / Real.sqrt (base ^ 2 - 4) * (base - scale)) by ring]
  linarith

theorem largeScalePreimage_ratio_le_exp_tangent
    {scale base : ℝ} (hscale : 2 < scale) (hbase : scale < base) :
    largeScalePreimage scale / largeScalePreimage base ≤
      Real.exp ((scale - base) / Real.sqrt (base ^ 2 - 4)) := by
  have halphaScale := largeScalePreimage_pos hscale.le
  have halphaBase := largeScalePreimage_pos (hscale.trans hbase).le
  have hlog := log_largeScalePreimage_tangent_bound hscale hbase
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_log halphaScale,
    Real.exp_log halphaBase] at hexp
  exact hexp

end FibonacciRibbonKernel
