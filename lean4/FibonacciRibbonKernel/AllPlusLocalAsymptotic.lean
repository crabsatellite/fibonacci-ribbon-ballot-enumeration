import FibonacciRibbonKernel.AllPlusLocalScaling

namespace FibonacciRibbonKernel

open Filter MeasureTheory

noncomputable def allPlusLocalLimitConstant (dimension : ℕ) : ℝ :=
  ((2 / Real.pi) *
    (Real.sqrt (Real.pi *
      Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) / 2)) ^ dimension

theorem tendsto_allPlusAngleLocalNormalizedIntegral
    (dimension : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    Tendsto
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          allPlusAngleLocalNormalizedIntegral dimension index)
      atTop (nhds (allPlusLocalLimitConstant dimension)) := by
  have hscaling :
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          allPlusAngleLocalNormalizedIntegral dimension index) =
      fun index : ℕ => ∫ coordinates : Fin dimension → ℝ,
        allPlusLocalRescaledIntegrand dimension index coordinates := by
    funext index
    exact allPlusLocalScalingIntegral_identity dimension index
  rw [hscaling]
  have hlimit := tendsto_integral_allPlusLocalRescaledIntegrand
    dimension hdimension
  rw [integral_allPlusLocalLimitIntegrand] at hlimit
  exact hlimit

theorem allPlusLocalLimitConstant_pos
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ)) :
    0 < allPlusLocalLimitConstant dimension := by
  unfold allPlusLocalLimitConstant
  have hroot : 0 < Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hbase : 0 < (2 / Real.pi) *
      (Real.sqrt (Real.pi * Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) / 2) := by
    positivity
  exact pow_pos hbase _

end FibonacciRibbonKernel
