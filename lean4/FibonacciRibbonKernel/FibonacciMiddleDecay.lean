import FibonacciRibbonKernel.FibonacciKernelAbsoluteBound

namespace FibonacciRibbonKernel

open Filter

noncomputable def fibonacciMiddleGrowthRatio (dimension : ℕ) : ℝ :=
  absoluteKernelGrowth (cosineScaleMidpoint dimension) /
    largeScalePreimage (2 * dimension : ℝ)

theorem fibonacciMiddleGrowthRatio_pos
    {dimension : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    0 < fibonacciMiddleGrowthRatio dimension := by
  unfold fibonacciMiddleGrowthRatio
  exact div_pos
    (absoluteKernelGrowth_pos (by
      unfold cosineScaleMidpoint
      positivity))
    (largeScalePreimage_pos (by linarith))

theorem fibonacciMiddleGrowthRatio_lt_one
    {dimension : ℕ} (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    fibonacciMiddleGrowthRatio dimension < 1 := by
  rw [fibonacciMiddleGrowthRatio,
    div_lt_one (largeScalePreimage_pos (by linarith))]
  exact absoluteKernelGrowth_midpoint_lt_baseGrowth hdimension

theorem tendsto_sqrt_pow_mul_fibonacciMiddleGrowthRatio
    (dimension : ℕ) (hdimension : 4 ≤ (2 * dimension : ℝ)) :
    Tendsto
      (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          fibonacciMiddleGrowthRatio dimension ^ (index + 1))
      atTop (nhds 0) := by
  have hratioPos := fibonacciMiddleGrowthRatio_pos hdimension
  have hratioLt := fibonacciMiddleGrowthRatio_lt_one hdimension
  have hpolyGeom :
      Tendsto
        (fun index : ℕ =>
          (index : ℝ) ^ dimension *
            fibonacciMiddleGrowthRatio dimension ^ index)
        atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one dimension
      (by rw [abs_of_pos hratioPos]; exact hratioLt)
  have hshifted := hpolyGeom.comp (tendsto_add_atTop_nat 1)
  refine squeeze_zero
    (g := fun index : ℕ =>
      (index + 1 : ℝ) ^ dimension *
        fibonacciMiddleGrowthRatio dimension ^ (index + 1)) ?_ ?_ ?_
  · intro index
    positivity
  · intro index
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hratioPos.le _)
    have hone : (1 : ℝ) ≤ (index + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le index)
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (Real.sqrt_le_self_iff.2 (Or.inr hone)) dimension
  · rw [show
        (fun index : ℕ =>
          (index + 1 : ℝ) ^ dimension *
            fibonacciMiddleGrowthRatio dimension ^ (index + 1)) =
          (fun index : ℕ =>
            (index : ℝ) ^ dimension *
              fibonacciMiddleGrowthRatio dimension ^ index) ∘
            (fun index : ℕ => index + 1) by
        funext index
        simp [Function.comp_apply]]
    exact hshifted

end FibonacciRibbonKernel
