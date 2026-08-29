import FibonacciRibbonKernel.DerivativeMicroscopicScaling

namespace FibonacciRibbonKernel

open Filter

theorem tendsto_largeScalePreimage_power_ratio_microscopic
    {scale displacement : ℝ} (hscale : 2 < scale) :
    Tendsto
      (fun index : ℕ =>
        (largeScalePreimage
            (scale + displacement / (index + 1 : ℝ)) /
          largeScalePreimage scale) ^ (index + 1))
      atTop
      (nhds (Real.exp
        (displacement / Real.sqrt (scale ^ 2 - 4)))) := by
  have hlog := tendsto_log_largeScalePreimage_microscopic
    (displacement := displacement) hscale
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  apply hexp.congr'
  have hperturb : Tendsto
      (fun index : ℕ => scale + displacement / (index + 1 : ℝ))
      atTop (nhds scale) := by
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
    simpa using tendsto_const_nhds.add hzero
  have heventuallyScale : ∀ᶠ index : ℕ in atTop,
      2 < scale + displacement / (index + 1 : ℝ) :=
    (tendsto_order.1 hperturb).1 2 hscale
  filter_upwards [heventuallyScale] with index hindex
  have halphaPerturb : 0 < largeScalePreimage
      (scale + displacement / (index + 1 : ℝ)) :=
    largeScalePreimage_pos hindex.le
  have halpha : 0 < largeScalePreimage scale :=
    largeScalePreimage_pos hscale.le
  have hratio : 0 <
      largeScalePreimage (scale + displacement / (index + 1 : ℝ)) /
        largeScalePreimage scale := div_pos halphaPerturb halpha
  simp only [Function.comp_apply]
  rw [← Real.exp_log hratio]
  rw [← Real.exp_nat_mul]
  rw [Real.log_div halphaPerturb.ne' halpha.ne']
  push_cast
  rfl

end FibonacciRibbonKernel
