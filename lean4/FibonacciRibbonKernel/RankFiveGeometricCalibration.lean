import FibonacciRibbonKernel.RankFiveGeometricFullLimit
import FibonacciRibbonKernel.MehtaIntegralEvaluation

namespace FibonacciRibbonKernel

open Filter

theorem tendsto_heightFiveTableauNormalized_regev :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 *
        ((heightFiveTableauCount index : ℝ) / 5 ^ index))
      atTop (nhds (regevConstant 5)) := by
  have hraw := unrestrictedCount_normalized_tendsto_regevConstant_of_mehta
    4 (regevMehtaChamberEvaluation_all 4)
  have hnormalized :
      Tendsto (fun index : ℕ =>
        (index : ℝ) ^ 5 *
          ((heightFiveTableauCount index : ℝ) / 5 ^ index))
        atTop (nhds (regevConstant 5)) := by
    apply hraw.congr'
    filter_upwards [eventually_ne_atTop 0] with index hindex
    have hindexNonneg : (0 : ℝ) ≤ index := by positivity
    have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
    unfold heightFiveTableauCount generalRegevBaseScale
    rw [fixedRankExponent_five, Real.rpow_neg hindexNonneg]
    field_simp [hindexReal]
    norm_num
    ring
  have hratioBase := tendsto_offset_div_offset_add_real 1 (-1)
  have hratio :
      Tendsto (fun index : ℕ =>
        (((index : ℝ) + 1) / (index : ℝ)) ^ 5)
        atTop (nhds 1) := by
    have hpow := hratioBase.pow 5
    norm_num at hpow
    exact hpow
  have hproduct := hratio.mul hnormalized
  norm_num at hproduct
  apply hproduct.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  field_simp [hindexReal]

theorem rankFiveGeometricLocalLimitIntegral_eq_regev :
    (∫ coordinates : Fin 2 → ℝ,
      rankFiveGeometricLocalLimitIntegrand coordinates) =
      regevConstant 5 / 8 := by
  have heq := tendsto_nhds_unique
    tendsto_heightFiveTableauNormalized_regev
    tendsto_rankFiveTableauNormalizedIntegralConstant
  linarith

theorem rankFiveGeometricLocalLimitIntegral_explicit :
    (∫ coordinates : Fin 2 → ℝ,
      rankFiveGeometricLocalLimitIntegrand coordinates) =
      9375 / (64 * Real.pi) := by
  rw [rankFiveGeometricLocalLimitIntegral_eq_regev,
    regevConstant_five]
  ring

end FibonacciRibbonKernel
