import FibonacciRibbonKernel.VariableGeometricDecay

namespace FibonacciRibbonKernel

open Filter
open scoped BigOperators

noncomputable def cosineScaleRootRatio (scale : ℝ) : ℝ :=
  positiveScalePreimage scale / largeScalePreimage scale

theorem continuousAt_positiveScalePreimage (scale : ℝ) :
    ContinuousAt positiveScalePreimage scale := by
  unfold positiveScalePreimage
  fun_prop

theorem continuousAt_cosineScaleRootRatio
    {scale : ℝ} (hscale : 2 < scale) :
    ContinuousAt cosineScaleRootRatio scale := by
  unfold cosineScaleRootRatio
  exact (continuousAt_positiveScalePreimage scale).div
    (continuousAt_largeScalePreimage hscale)
    (largeScalePreimage_pos hscale.le).ne'

theorem tendsto_cosineScaleRootRatio
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto
      (fun index => cosineScaleRootRatio (cosineSumScale coordinates index))
      atTop (nhds (cosineScaleRootRatio (2 * dimension : ℝ))) :=
  (continuousAt_cosineScaleRootRatio hdimension).tendsto.comp
    (tendsto_cosineSumScale coordinates)

theorem tendsto_cosineScaleRootRatio_pow_zero
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto
      (fun index =>
        cosineScaleRootRatio (cosineSumScale coordinates index) ^ (index + 1))
      atTop (nhds 0) := by
  have hratio := tendsto_cosineScaleRootRatio hdimension coordinates
  have hlimitNonneg :
      0 ≤ cosineScaleRootRatio (2 * dimension : ℝ) :=
    positiveScalePreimage_div_large_nonneg hdimension.le
  have hlimitLt : cosineScaleRootRatio (2 * dimension : ℝ) < 1 :=
    positiveScalePreimage_div_large_lt_one hdimension
  have hscale := tendsto_cosineSumScale coordinates
  have heventuallyScale : ∀ᶠ index : ℕ in atTop,
      2 < cosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 2 hdimension
  have hnonneg : ∀ᶠ index : ℕ in atTop,
      0 ≤ cosineScaleRootRatio (cosineSumScale coordinates index) := by
    filter_upwards [heventuallyScale] with index hindex
    exact positiveScalePreimage_div_large_nonneg hindex.le
  exact tendsto_variable_pow_zero hratio hlimitNonneg hlimitLt hnonneg

noncomputable def normalizedFibonacciCosineKernel
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) (index : ℕ) : ℝ :=
  fibonacciScaleKernel (cosineSumScale coordinates index) index /
    (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
      Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))

theorem tendsto_cosineScale_sqrt_ratio
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto
      (fun index =>
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
          Real.sqrt (cosineSumScale coordinates index ^ 2 - 4))
      atTop (nhds 1) := by
  have hscale := tendsto_cosineSumScale coordinates
  have hroot : Tendsto
      (fun index => Real.sqrt (cosineSumScale coordinates index ^ 2 - 4))
      atTop (nhds (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) := by
    have hcontinuous : ContinuousAt
        (fun scale : ℝ => Real.sqrt (scale ^ 2 - 4))
        (2 * dimension : ℝ) := by fun_prop
    have hraw := hcontinuous.tendsto.comp hscale
    apply hraw.congr'
    filter_upwards with index
    rfl
  have hbaseRoot : Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    nlinarith
  have hconstant : Tendsto
      (fun _ : ℕ => Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))
      atTop (nhds (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) :=
    tendsto_const_nhds
  have hquotient := hconstant.div hroot hbaseRoot
  rw [div_self hbaseRoot] at hquotient
  exact hquotient

theorem normalizedFibonacciCosineKernel_factorization
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) (index : ℕ)
    (hscale : 2 < cosineSumScale coordinates index) :
    normalizedFibonacciCosineKernel coordinates index =
      (largeScalePreimage (cosineSumScale coordinates index) /
          largeScalePreimage (2 * dimension : ℝ)) ^ (index + 1) *
        (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
          Real.sqrt (cosineSumScale coordinates index ^ 2 - 4)) *
        (1 - cosineScaleRootRatio
          (cosineSumScale coordinates index) ^ (index + 1)) := by
  unfold normalizedFibonacciCosineKernel
  rw [fibonacciScaleKernel_closed_of_two_lt hscale]
  unfold cosineScaleRootRatio
  have halphaCurrent := (largeScalePreimage_pos hscale.le).ne'
  have halphaBase := (largeScalePreimage_pos hdimension.le).ne'
  have hrootCurrent :
      Real.sqrt (cosineSumScale coordinates index ^ 2 - 4) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    nlinarith
  have hrootBase : Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) ≠ 0 := by
    apply (Real.sqrt_pos.2 ?_).ne'
    nlinarith
  have halphaCurrentPow := pow_ne_zero (index + 1) halphaCurrent
  have halphaBasePow := pow_ne_zero (index + 1) halphaBase
  simp only [div_pow]
  field_simp [halphaCurrentPow, halphaBasePow, hrootCurrent, hrootBase]

theorem tendsto_normalizedFibonacciCosineKernel
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto (normalizedFibonacciCosineKernel coordinates) atTop
      (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) /
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)))) := by
  have halpha := tendsto_largeScalePreimage_cosineSum_power_ratio
    hdimension coordinates
  have hroot := tendsto_cosineScale_sqrt_ratio hdimension coordinates
  have hsecondary := tendsto_cosineScaleRootRatio_pow_zero
    hdimension coordinates
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have honeMinus := hone.sub hsecondary
  rw [sub_zero] at honeMinus
  have hproduct := (halpha.mul hroot).mul honeMinus
  simp only [mul_one] at hproduct
  have hscale := tendsto_cosineSumScale coordinates
  have heventuallyScale : ∀ᶠ index : ℕ in atTop,
      2 < cosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 2 hdimension
  apply hproduct.congr'
  filter_upwards [heventuallyScale] with index hindex
  exact (normalizedFibonacciCosineKernel_factorization
    hdimension coordinates index hindex).symm

end FibonacciRibbonKernel
