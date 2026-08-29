import FibonacciRibbonKernel.RankFiveLocalDCT

namespace FibonacciRibbonKernel

open Filter

theorem absoluteKernelGrowth_halfway_lt_largeScalePreimage
    {base : ℝ} (hbase : 4 ≤ base) :
    absoluteKernelGrowth ((base + 2) / 2) <
      largeScalePreimage base := by
  let midpoint : ℝ := (base + 2) / 2
  let gamma : ℝ := absoluteKernelGrowth midpoint
  let alpha : ℝ := largeScalePreimage base
  have hmidpointNonneg : 0 ≤ midpoint := by
    dsimp [midpoint]
    linarith
  have hgammaPos : 0 < gamma := absoluteKernelGrowth_pos hmidpointNonneg
  have halphaPos : 0 < alpha := largeScalePreimage_pos (by linarith)
  have hsqrtPos : 0 < Real.sqrt (base ^ 2 - 4) := by
    exact Real.sqrt_pos.2 (by nlinarith)
  have halphaGtTwo : 2 < alpha := by
    dsimp [alpha, largeScalePreimage]
    linarith
  have hgammaEq : gamma ^ 2 = midpoint * gamma + 1 :=
    absoluteKernelGrowth_quadratic hmidpointNonneg
  have halphaEq : alpha ^ 2 = base * alpha - 1 := by
    have hquad := positiveScalePreimage_quadratic
      (show 2 ≤ base by linarith)
    have hmul := positiveScalePreimage_mul_largeScalePreimage
      (show 2 ≤ base by linarith)
    have hsum := largeScalePreimage_add_positiveScalePreimage base
    nlinarith
  by_contra hnot
  have hle : alpha ≤ gamma := le_of_not_gt hnot
  have hgammaLower : 3 ≤ gamma := by
    have hmid : 3 ≤ midpoint := by dsimp [midpoint]; linarith
    exact hmid.trans (absoluteKernelGrowth_ge_bound hmidpointNonneg)
  have hleftNonneg :
      0 ≤ (gamma - alpha) * (gamma + alpha - midpoint) := by
    apply mul_nonneg
    · exact sub_nonneg.2 hle
    · nlinarith
  have hidentity :
      (gamma - alpha) * (gamma + alpha - midpoint) =
        2 - (base - midpoint) * alpha := by
    nlinarith [hgammaEq, halphaEq]
  have hrightNeg : 2 - (base - midpoint) * alpha < 0 := by
    dsimp [midpoint]
    nlinarith
  rw [hidentity] at hleftNonneg
  linarith

noncomputable def rankFiveTailGrowthRatio : ℝ :=
  absoluteKernelGrowth (7 / 2 : ℝ) / largeScalePreimage 5

theorem rankFiveTailGrowthRatio_pos : 0 < rankFiveTailGrowthRatio := by
  unfold rankFiveTailGrowthRatio
  exact div_pos (absoluteKernelGrowth_pos (by norm_num))
    (largeScalePreimage_pos (by norm_num))

theorem rankFiveTailGrowthRatio_lt_one : rankFiveTailGrowthRatio < 1 := by
  rw [rankFiveTailGrowthRatio,
    div_lt_one (largeScalePreimage_pos (by norm_num))]
  have h := absoluteKernelGrowth_halfway_lt_largeScalePreimage
    (base := 5) (by norm_num)
  norm_num at h ⊢
  exact h

theorem tendsto_rankFiveTailPolynomialGeometric :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveTailGrowthRatio ^ (index + 1))
      atTop (nhds 0) := by
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one 5
    (by rw [abs_of_pos rankFiveTailGrowthRatio_pos]
        exact rankFiveTailGrowthRatio_lt_one)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveTailGrowthRatio ^ (index + 1)) =
      (fun index : ℕ =>
        (index : ℝ) ^ 5 * rankFiveTailGrowthRatio ^ index) ∘
        (fun index : ℕ => index + 1) by
    funext index
    simp [Function.comp_apply]]
  exact hshift

end FibonacciRibbonKernel
