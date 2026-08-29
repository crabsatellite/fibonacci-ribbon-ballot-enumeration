import FibonacciRibbonKernel.RankFiveWeylRibbon

namespace FibonacciRibbonKernel

open Filter
open scoped BigOperators

noncomputable def oddCosineSumScale
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) (index : ℕ) : ℝ :=
  1 + cosineSumScale coordinates index

noncomputable def normalizedOddFibonacciKernel
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) (index : ℕ) : ℝ :=
  fibonacciScaleKernel (oddCosineSumScale coordinates index) index /
    (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
      Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))

theorem tendsto_oddCosineSumScale
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) :
    Tendsto (oddCosineSumScale coordinates) atTop
      (nhds (2 * dimension + 1 : ℝ)) := by
  unfold oddCosineSumScale
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
    atTop (nhds 1)).add (tendsto_cosineSumScale coordinates)
  convert h using 1
  ring

theorem oddCosineSumScale_displacement
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) (index : ℕ) :
    oddCosineSumScale coordinates index =
      (2 * dimension + 1 : ℝ) +
        cosineSumDisplacement coordinates index / (index + 1 : ℝ) := by
  unfold oddCosineSumScale cosineSumDisplacement
  have hdenominator : (index + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_log_largeScalePreimage_oddCosineSum
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (Real.log (largeScalePreimage
              (oddCosineSumScale coordinates index)) -
            Real.log (largeScalePreimage (2 * dimension + 1 : ℝ))))
      atTop
      (nhds ((-∑ coordinate, coordinates coordinate ^ 2) /
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) := by
  have h := tendsto_log_largeScalePreimage_variable_microscopic
    hdimension (tendsto_cosineSumDisplacement coordinates)
  apply h.congr'
  filter_upwards with index
  rw [oddCosineSumScale_displacement]

theorem tendsto_largeScalePreimage_oddCosineSum_power_ratio
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto
      (fun index : ℕ =>
        (largeScalePreimage (oddCosineSumScale coordinates index) /
          largeScalePreimage (2 * dimension + 1 : ℝ)) ^ (index + 1))
      atTop
      (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) /
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4)))) := by
  have hlog := tendsto_log_largeScalePreimage_oddCosineSum
    hdimension coordinates
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hscale := tendsto_oddCosineSumScale coordinates
  have heventuallyScale : ∀ᶠ index : ℕ in atTop,
      2 < oddCosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 2 hdimension
  apply hexp.congr'
  filter_upwards [heventuallyScale] with index hindex
  have halphaCurrent := largeScalePreimage_pos hindex.le
  have halphaBase := largeScalePreimage_pos hdimension.le
  have hratio : 0 <
      largeScalePreimage (oddCosineSumScale coordinates index) /
        largeScalePreimage (2 * dimension + 1 : ℝ) :=
    div_pos halphaCurrent halphaBase
  simp only [Function.comp_apply]
  rw [← Real.exp_log hratio, ← Real.exp_nat_mul,
    Real.log_div halphaCurrent.ne' halphaBase.ne']
  push_cast
  rfl

theorem normalizedOddFibonacciKernel_factorization
    {dimension index : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hscale : 2 < oddCosineSumScale coordinates index) :
    normalizedOddFibonacciKernel coordinates index =
      (largeScalePreimage (oddCosineSumScale coordinates index) /
          largeScalePreimage (2 * dimension + 1 : ℝ)) ^ (index + 1) *
        (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
          Real.sqrt (oddCosineSumScale coordinates index ^ 2 - 4)) *
        (1 - cosineScaleRootRatio
          (oddCosineSumScale coordinates index) ^ (index + 1)) := by
  unfold normalizedOddFibonacciKernel
  rw [fibonacciScaleKernel_closed_of_two_lt hscale]
  unfold cosineScaleRootRatio
  have halphaCurrent := (largeScalePreimage_pos hscale.le).ne'
  have halphaBase := (largeScalePreimage_pos hdimension.le).ne'
  have hrootCurrent :
      Real.sqrt (oddCosineSumScale coordinates index ^ 2 - 4) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    nlinarith
  have hrootBase : Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    nlinarith
  simp only [div_pow]
  field_simp [pow_ne_zero _ halphaCurrent, pow_ne_zero _ halphaBase,
    hrootCurrent, hrootBase]

theorem tendsto_normalizedOddFibonacciKernel
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index => normalizedOddFibonacciKernel coordinates index)
      atTop
      (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) /
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4)))) := by
  have hscale := tendsto_oddCosineSumScale coordinates
  have heventuallyScale : ∀ᶠ index : ℕ in atTop,
      2 < oddCosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 2 hdimension
  have halpha := tendsto_largeScalePreimage_oddCosineSum_power_ratio
    hdimension coordinates
  have hroot : Tendsto
      (fun index => Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
        Real.sqrt (oddCosineSumScale coordinates index ^ 2 - 4))
      atTop (nhds 1) := by
    have hrootNe : Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) ≠ 0 := by
      apply (Real.sqrt_pos.2 ?_).ne'
      nlinarith
    have hcontinuous : ContinuousAt
        (fun scale : ℝ => Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
          Real.sqrt (scale ^ 2 - 4)) (2 * dimension + 1 : ℝ) := by
      exact continuousAt_const.div (by fun_prop) hrootNe
    have hraw := hcontinuous.tendsto.comp hscale
    rw [div_self hrootNe] at hraw
    apply hraw.congr'
    filter_upwards with index
    rfl
  have hq : Tendsto
      (fun index => cosineScaleRootRatio
        (oddCosineSumScale coordinates index) ^ (index + 1))
      atTop (nhds 0) := by
    have hratio := (continuousAt_cosineScaleRootRatio hdimension).tendsto.comp hscale
    have hnonneg : ∀ᶠ index : ℕ in atTop,
        0 ≤ cosineScaleRootRatio (oddCosineSumScale coordinates index) := by
      filter_upwards [heventuallyScale] with index hindex
      exact positiveScalePreimage_div_large_nonneg hindex.le
    exact tendsto_variable_pow_zero hratio
      (positiveScalePreimage_div_large_nonneg hdimension.le)
      (positiveScalePreimage_div_large_lt_one hdimension) hnonneg
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have honeMinus := hone.sub hq
  rw [sub_zero] at honeMinus
  have hproduct := (halpha.mul hroot).mul honeMinus
  simp only [mul_one] at hproduct
  apply hproduct.congr'
  filter_upwards [heventuallyScale] with index hindex
  exact (normalizedOddFibonacciKernel_factorization
    hdimension coordinates hindex).symm

end FibonacciRibbonKernel
