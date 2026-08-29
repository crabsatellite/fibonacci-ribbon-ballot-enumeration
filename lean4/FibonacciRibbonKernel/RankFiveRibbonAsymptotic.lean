import FibonacciRibbonKernel.RankFiveGaussianTransport

namespace FibonacciRibbonKernel

open Filter Asymptotics

theorem rankFiveFibonacciLocalLimitIntegral_explicit :
    (∫ coordinates : Fin 2 → ℝ,
      oddWeylLocalLimitIntegrand 2 coordinates) =
      1323 * Real.sqrt (21 : ℝ) / (64 * Real.pi) := by
  rw [rankFiveFibonacciLimitIntegral_eq_scaled_geometric,
    rankFiveGeometricLocalLimitIntegral_explicit]
  have hsqrtSq : Real.sqrt (21 : ℝ) ^ 2 = 21 :=
    Real.sq_sqrt (by positivity)
  have hsqrtFifth : Real.sqrt (21 : ℝ) ^ 5 =
      441 * Real.sqrt (21 : ℝ) := by
    calc
      Real.sqrt (21 : ℝ) ^ 5 =
          (Real.sqrt (21 : ℝ) ^ 2) ^ 2 *
            Real.sqrt (21 : ℝ) := by ring
      _ = 441 * Real.sqrt (21 : ℝ) := by rw [hsqrtSq]; norm_num
  rw [div_pow, hsqrtFifth]
  field_simp [Real.pi_ne_zero]
  ring

theorem tendsto_rankFiveRibbonNormalized_explicit :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 *
        ((ribbonCount 4 index : ℝ) /
      (largeScalePreimage 5 ^ (index + 1) / Real.sqrt 21)))
      atTop (nhds (1323 * Real.sqrt 21 / (8 * Real.pi))) := by
  have h := tendsto_rankFiveRibbonNormalizedIntegralConstant
  rw [rankFiveFibonacciLocalLimitIntegral_explicit] at h
  have hconstant :
      8 * (1323 * Real.sqrt (21 : ℝ) / (64 * Real.pi)) =
        1323 * Real.sqrt 21 / (8 * Real.pi) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hconstant] at h
  exact h

theorem tendsto_rankFiveRibbon_alphaSuccNormalized :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * (ribbonCount 4 index : ℝ) /
        fixedRankGrowth 5 ^ (index + 1))
      atTop (nhds (1323 / (8 * Real.pi))) := by
  have h := tendsto_rankFiveRibbonNormalized_explicit.div_const
    (Real.sqrt (21 : ℝ))
  have hsqrt : Real.sqrt (21 : ℝ) ≠ 0 := by positivity
  have hlimit :
      (1323 * Real.sqrt (21 : ℝ) / (8 * Real.pi)) /
          Real.sqrt (21 : ℝ) =
        1323 / (8 * Real.pi) := by
    field_simp [hsqrt, Real.pi_ne_zero]
  rw [hlimit] at h
  apply h.congr'
  filter_upwards with index
  rw [show largeScalePreimage 5 = fixedRankGrowth 5 by
    exact largeScalePreimage_natCast 5]
  field_simp [hsqrt, (fixedRankGrowth_pos 5 (by norm_num)).ne']

theorem tendsto_rankFiveRibbon_nPowerNormalized :
    Tendsto (fun index : ℕ =>
      (index : ℝ) ^ 5 * (ribbonCount 4 index : ℝ) /
        fixedRankGrowth 5 ^ index)
      atTop
      (nhds (1323 * fixedRankGrowth 5 / (8 * Real.pi))) := by
  have hratioBase := tendsto_offset_div_offset_add_real 0 1
  have hratio :
      Tendsto (fun index : ℕ =>
        ((index : ℝ) / (index + 1 : ℝ)) ^ 5)
        atTop (nhds 1) := by
    have hpow := hratioBase.pow 5
    norm_num at hpow
    exact hpow
  have hproduct := hratio.mul tendsto_rankFiveRibbon_alphaSuccNormalized
  norm_num at hproduct
  have hsucc :
      Tendsto (fun index : ℕ =>
        (index : ℝ) ^ 5 * (ribbonCount 4 index : ℝ) /
          fixedRankGrowth 5 ^ (index + 1))
        atTop (nhds (1323 / (8 * Real.pi))) := by
    apply hproduct.congr'
    filter_upwards with index
    have hsuccReal : (index + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hsuccReal,
      (fixedRankGrowth_pos 5 (by norm_num)).ne']
  have hscaled := hsucc.mul_const (fixedRankGrowth 5)
  have hlimit :
      1323 / (8 * Real.pi) * fixedRankGrowth 5 =
        1323 * fixedRankGrowth 5 / (8 * Real.pi) := by ring
  rw [hlimit] at hscaled
  apply hscaled.congr'
  filter_upwards with index
  rw [pow_succ]
  field_simp [(fixedRankGrowth_pos 5 (by norm_num)).ne']
  ring

theorem tendsto_rankFiveRibbon_nPowerNormalized_transferred :
    Tendsto (fun index : ℕ =>
      (index : ℝ) ^ 5 * (ribbonCount 4 index : ℝ) /
        fixedRankGrowth 5 ^ index)
      atTop (nhds (transferredFixedRankConstant 5)) := by
  rw [transferredFixedRankConstant_five]
  exact tendsto_rankFiveRibbon_nPowerNormalized

theorem fixedRankRibbonAsymptotic_five :
    FixedRankRibbonAsymptotic 5 := by
  unfold FixedRankRibbonAsymptotic
  have hdenominator : ∀ᶠ index : ℕ in atTop,
      fixedRankRibbonLeadingTerm 5 index ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with index hindex
    unfold fixedRankRibbonLeadingTerm
    rw [transferredFixedRankConstant_five]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact (div_pos
          (mul_pos (by norm_num) (fixedRankGrowth_pos 5 (by norm_num)))
          (mul_pos (by norm_num) Real.pi_pos)).ne'
      · exact pow_ne_zero _ (fixedRankGrowth_pos 5 (by norm_num)).ne'
    · exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [isEquivalent_iff_tendsto_one hdenominator]
  have hconstantPos : 0 < transferredFixedRankConstant 5 := by
    rw [transferredFixedRankConstant_five]
    exact div_pos
      (mul_pos (by norm_num) (fixedRankGrowth_pos 5 (by norm_num)))
      (mul_pos (by norm_num) Real.pi_pos)
  have h := tendsto_rankFiveRibbon_nPowerNormalized_transferred.div_const
    (transferredFixedRankConstant 5)
  rw [div_self hconstantPos.ne'] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hindexNonneg : (0 : ℝ) ≤ index := by positivity
  have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  simp only [Pi.div_apply]
  unfold fixedRankRibbonLeadingTerm
  rw [fixedRankExponent_five, Real.rpow_neg hindexNonneg]
  field_simp [hindexReal,
    (fixedRankGrowth_pos 5 (by norm_num)).ne', hconstantPos.ne']
  norm_num
  ring

end FibonacciRibbonKernel
