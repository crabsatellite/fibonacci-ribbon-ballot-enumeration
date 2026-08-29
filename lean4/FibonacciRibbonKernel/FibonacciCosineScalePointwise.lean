import FibonacciRibbonKernel.CosineSumQuadraticScaling

namespace FibonacciRibbonKernel

open Filter
open scoped BigOperators

theorem tendsto_cosineSumScale
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) :
    Tendsto (cosineSumScale coordinates) atTop
      (nhds (2 * dimension : ℝ)) := by
  have hdisplacement := tendsto_cosineSumDisplacement coordinates
  have hinverse : Tendsto (fun index : ℕ => 1 / (index + 1 : ℝ))
      atTop (nhds 0) := by
    have hbase := (tendsto_const_div_pow 1 1 (by omega)).comp
      (tendsto_add_atTop_nat 1)
    apply hbase.congr'
    filter_upwards with index
    simp only [Function.comp_apply, pow_one]
    push_cast
    rfl
  have hsmall := hdisplacement.mul hinverse
  have hsmall' : Tendsto
      (fun index : ℕ =>
        cosineSumDisplacement coordinates index / (index + 1 : ℝ))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hsmall
  have hconstant : Tendsto (fun _ : ℕ => (2 * dimension : ℝ))
      atTop (nhds (2 * dimension : ℝ)) := tendsto_const_nhds
  have hsum := hconstant.add hsmall'
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards with index
  unfold cosineSumDisplacement
  have hdenominator : (index + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hdenominator]
  ring

theorem tendsto_largeScalePreimage_cosineSum_power_ratio
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto
      (fun index : ℕ =>
        (largeScalePreimage (cosineSumScale coordinates index) /
          largeScalePreimage (2 * dimension : ℝ)) ^ (index + 1))
      atTop
      (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) /
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)))) := by
  have hlog := tendsto_log_largeScalePreimage_cosineSum
    hdimension coordinates
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hscale := tendsto_cosineSumScale coordinates
  have heventuallyScale : ∀ᶠ index : ℕ in atTop,
      2 < cosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 2 hdimension
  apply hexp.congr'
  filter_upwards [heventuallyScale] with index hindex
  have halphaCurrent : 0 <
      largeScalePreimage (cosineSumScale coordinates index) :=
    largeScalePreimage_pos hindex.le
  have halphaBase : 0 < largeScalePreimage (2 * dimension : ℝ) :=
    largeScalePreimage_pos hdimension.le
  have hratio : 0 <
      largeScalePreimage (cosineSumScale coordinates index) /
        largeScalePreimage (2 * dimension : ℝ) :=
    div_pos halphaCurrent halphaBase
  simp only [Function.comp_apply]
  rw [← Real.exp_log hratio, ← Real.exp_nat_mul,
    Real.log_div halphaCurrent.ne' halphaBase.ne']
  push_cast
  rfl

end FibonacciRibbonKernel
