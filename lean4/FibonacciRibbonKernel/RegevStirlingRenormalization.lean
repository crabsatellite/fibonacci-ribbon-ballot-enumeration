import FibonacciRibbonKernel.RegevGeneralFullLimit

namespace FibonacciRibbonKernel

open Filter Asymptotics
open scoped Classical Topology

noncomputable def generalGlobalNormalization
    (rank size : ℕ) : ℝ :=
  regevCenter rank size ^
      ((size : ℝ) + matsumotoLocalExponent (rank + 1)) /
    (((size.factorial : ℝ) * Real.exp size) *
      generalRegevScale rank size ^ rank)

noncomputable def generalRegevBaseScale
    (rank size : ℕ) : ℝ :=
  ((rank + 1 : ℕ) : ℝ) ^ size *
    (size : ℝ) ^ (-fixedRankExponent (rank + 1))

noncomputable def globalStirlingRatio (size : ℕ) : ℝ :=
  ((size.factorial : ℝ) * Real.exp size) /
    (Real.sqrt (2 * size * Real.pi) * (size : ℝ) ^ size)

theorem generalFullNormalizedAverage_eq_normalization_mul
    (rank size : ℕ) :
    generalFullNormalizedAverage rank size =
      generalGlobalNormalization rank size *
        (unrestrictedCount rank size : ℝ) := by
  unfold generalFullNormalizedAverage generalGlobalNormalization
  unfold matsumotoLocalNormalizedTableau
  simp_rw [show ∀ shape : BoundedPartition rank size,
      regevCenter rank size ^
          ((size : ℝ) + matsumotoLocalExponent (rank + 1)) *
        (standardTableauNumber shape : ℝ) /
          ((size.factorial : ℝ) * Real.exp size) =
      (regevCenter rank size ^
          ((size : ℝ) + matsumotoLocalExponent (rank + 1)) /
        ((size.factorial : ℝ) * Real.exp size)) *
          (standardTableauNumber shape : ℝ) by
    intro shape
    ring]
  rw [← Finset.mul_sum]
  rw [← Nat.cast_sum]
  rw [← unrestrictedCount_eq_sum_standardTableauNumbers]
  ring

theorem globalStirlingRatio_tendsto_one :
    Tendsto globalStirlingRatio atTop (nhds 1) := by
  have hdenomEventually : ∀ᶠ size : ℕ in atTop,
      Real.sqrt (2 * size * Real.pi) *
        ((size : ℝ) / Real.exp 1) ^ size ≠ 0 := by
    filter_upwards [eventually_ne_atTop 0] with size hsize
    positivity
  have hstirling : Tendsto
      (fun size : ℕ =>
        (size.factorial : ℝ) /
          (Real.sqrt (2 * size * Real.pi) *
            ((size : ℝ) / Real.exp 1) ^ size))
      atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hdenomEventually).1
      Stirling.factorial_isEquivalent_stirling
  apply hstirling.congr'
  filter_upwards with size
  unfold globalStirlingRatio
  have hexp : Real.exp (size : ℝ) = Real.exp 1 ^ size := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hexp, div_pow]
  have hexpNe : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  by_cases hsize : size = 0
  · subst size
    norm_num
  · have hsizeReal : (size : ℝ) ≠ 0 := by exact_mod_cast hsize
    field_simp

theorem generalRegevScale_pow
    (rank size : ℕ) :
    generalRegevScale rank size ^ rank =
      regevCenter rank size ^ ((rank : ℝ) / 2) := by
  unfold generalRegevScale regevCenter
  have hcenterNonneg : 0 ≤ (size : ℝ) / (rank + 1 : ℝ) := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hcenterNonneg]
  congr 1
  ring

noncomputable def regevIntegralScaleConstant (rank : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi) *
    ((rank + 1 : ℕ) : ℝ) ^
      (fixedRankExponent (rank + 1) + 1 / 2)

theorem regev_power_balance
    (rank size : ℕ) (hsize : 1 ≤ size) :
    (regevCenter rank size ^
          ((size : ℝ) + matsumotoLocalExponent (rank + 1)) /
        generalRegevScale rank size ^ rank) *
      generalRegevBaseScale rank size /
        (Real.sqrt (2 * size * Real.pi) * (size : ℝ) ^ size) =
      (regevIntegralScaleConstant rank)⁻¹ := by
  have hsizePos : (0 : ℝ) < size := by positivity
  have hdimensionPos : (0 : ℝ) < rank + 1 := by positivity
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hsqrt : Real.sqrt (2 * size * Real.pi) =
      Real.sqrt (2 * Real.pi) * (size : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (2 : ℝ) * size * Real.pi =
        (2 * Real.pi) * size by ring]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [show Real.sqrt (size : ℝ) =
      (size : ℝ) ^ (1 / 2 : ℝ) by rw [Real.sqrt_eq_rpow]]
  have hexponent :
      matsumotoLocalExponent (rank + 1) - (rank : ℝ) / 2 -
          fixedRankExponent (rank + 1) - 1 / 2 = 0 := by
    unfold matsumotoLocalExponent fixedRankExponent
    norm_num
    ring
  rw [generalRegevScale_pow, hsqrt]
  unfold generalRegevBaseScale regevIntegralScaleConstant
  rw [← Real.rpow_sub hcenterPos]
  unfold regevCenter
  rw [Real.div_rpow (Nat.cast_nonneg size) (by positivity)]
  simp_rw [← Real.rpow_natCast]
  have hsizePower :
      ((size : ℝ) ^ ((size : ℝ) + matsumotoLocalExponent (rank + 1) -
          (rank : ℝ) / 2) *
          (size : ℝ) ^ (-fixedRankExponent (rank + 1))) /
        ((size : ℝ) ^ (1 / 2 : ℝ) *
          (size : ℝ) ^ (size : ℝ)) = 1 := by
    rw [← Real.rpow_add hsizePos, ← Real.rpow_add hsizePos]
    rw [← Real.rpow_sub hsizePos]
    rw [show ((size : ℝ) + matsumotoLocalExponent (rank + 1) -
        (rank : ℝ) / 2) + (-fixedRankExponent (rank + 1)) -
        (1 / 2 + (size : ℝ)) = 0 by
      linarith]
    rw [Real.rpow_zero]
  have hdimensionPower :
      ((rank : ℝ) + 1) ^ (size : ℝ) /
          ((rank : ℝ) + 1) ^
            ((size : ℝ) + matsumotoLocalExponent (rank + 1) -
              (rank : ℝ) / 2) =
        ((rank : ℝ) + 1) ^
          (-(fixedRankExponent (rank + 1) + 1 / 2)) := by
    rw [← Real.rpow_sub hdimensionPos]
    congr 1
    linarith
  push_cast
  let dimensionPart : ℝ :=
    ((rank : ℝ) + 1) ^ (size : ℝ) /
      ((rank : ℝ) + 1) ^
        ((size : ℝ) + matsumotoLocalExponent (rank + 1) -
          (rank : ℝ) / 2)
  let sizePart : ℝ :=
    (((size : ℝ) ^
        ((size : ℝ) + matsumotoLocalExponent (rank + 1) -
          (rank : ℝ) / 2) *
        (size : ℝ) ^ (-fixedRankExponent (rank + 1))) /
      ((size : ℝ) ^ (1 / 2 : ℝ) * (size : ℝ) ^ (size : ℝ)))
  have hdimensionPart : dimensionPart =
      ((rank : ℝ) + 1) ^
        (-(fixedRankExponent (rank + 1) + 1 / 2)) := by
    exact hdimensionPower
  have hsizePart : sizePart = 1 := hsizePower
  calc
    ((((size : ℝ) ^ ((size : ℝ) + matsumotoLocalExponent (rank + 1) -
          (rank : ℝ) / 2)) /
        (((rank : ℝ) + 1) ^
          ((size : ℝ) + matsumotoLocalExponent (rank + 1) -
            (rank : ℝ) / 2))) *
      (((rank : ℝ) + 1) ^ (size : ℝ) *
        (size : ℝ) ^ (-fixedRankExponent (rank + 1)))) /
      (Real.sqrt (2 * Real.pi) * (size : ℝ) ^ (1 / 2 : ℝ) *
        (size : ℝ) ^ (size : ℝ)) =
      (Real.sqrt (2 * Real.pi))⁻¹ * dimensionPart * sizePart := by
        dsimp only [dimensionPart, sizePart]
        ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ((rank : ℝ) + 1) ^
          (-(fixedRankExponent (rank + 1) + 1 / 2)) := by
      rw [hsizePart, hdimensionPart]
      ring
    _ = (Real.sqrt (2 * Real.pi) *
        ((rank : ℝ) + 1) ^
          (fixedRankExponent (rank + 1) + 1 / 2))⁻¹ := by
      rw [mul_inv]
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (rank : ℝ) + 1)]

theorem normalization_mul_base_mul_stirlingRatio
    (rank size : ℕ) (hsize : 1 ≤ size) :
    generalGlobalNormalization rank size *
        generalRegevBaseScale rank size * globalStirlingRatio size =
      (regevIntegralScaleConstant rank)⁻¹ := by
  have hfactorial : (size.factorial : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp (size : ℝ) ≠ 0 := (Real.exp_pos _).ne'
  have hscale : generalRegevScale rank size ≠ 0 :=
    (generalRegevScale_pos hsize).ne'
  have hsqrt : Real.sqrt (2 * size * Real.pi) ≠ 0 := by positivity
  have hsizeReal : (size : ℝ) ≠ 0 := by positivity
  rw [show generalGlobalNormalization rank size *
      generalRegevBaseScale rank size * globalStirlingRatio size =
    (regevCenter rank size ^
          ((size : ℝ) + matsumotoLocalExponent (rank + 1)) /
        generalRegevScale rank size ^ rank) *
      generalRegevBaseScale rank size /
        (Real.sqrt (2 * size * Real.pi) * (size : ℝ) ^ size) by
    unfold generalGlobalNormalization globalStirlingRatio
    field_simp
    ]
  exact regev_power_balance rank size hsize

noncomputable def regevIntegralLeadingCoefficient (rank : ℕ) : ℝ :=
  regevIntegralScaleConstant rank * regevFullChamberIntegral rank

theorem normalization_mul_base_tendsto
    (rank : ℕ) :
    Tendsto
      (fun size => generalGlobalNormalization rank size *
        generalRegevBaseScale rank size)
      atTop (nhds ((regevIntegralScaleConstant rank)⁻¹)) := by
  have hinverse := globalStirlingRatio_tendsto_one.inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  have htarget : Tendsto
      (fun size => (regevIntegralScaleConstant rank)⁻¹ *
        (globalStirlingRatio size)⁻¹)
      atTop (nhds ((regevIntegralScaleConstant rank)⁻¹)) := by
    simpa using tendsto_const_nhds.mul hinverse
  apply htarget.congr'
  filter_upwards [eventually_ge_atTop 1] with size hsize
  have hratio : globalStirlingRatio size ≠ 0 := by
    unfold globalStirlingRatio
    positivity
  have hidentity := normalization_mul_base_mul_stirlingRatio
    rank size hsize
  rw [← div_eq_mul_inv]
  exact ((eq_div_iff hratio).2 hidentity).symm

theorem unrestrictedCount_normalized_tendsto_integralCoefficient
    (rank : ℕ) :
    Tendsto
      (fun size => (unrestrictedCount rank size : ℝ) /
        generalRegevBaseScale rank size)
      atTop (nhds (regevIntegralLeadingCoefficient rank)) := by
  have havg := general_full_normalizedAverage_tendsto rank
  have hnormalization := normalization_mul_base_tendsto rank
  have hscaleConstantPos : 0 < regevIntegralScaleConstant rank := by
    unfold regevIntegralScaleConstant
    positivity
  have hquotient := havg.div hnormalization
    (inv_ne_zero hscaleConstantPos.ne')
  have hlimit : regevFullChamberIntegral rank /
      (regevIntegralScaleConstant rank)⁻¹ =
      regevIntegralLeadingCoefficient rank := by
    unfold regevIntegralLeadingCoefficient
    field_simp
  rw [hlimit] at hquotient
  apply hquotient.congr'
  filter_upwards [eventually_ge_atTop 1] with size hsize
  have hnormalizationPos : 0 < generalGlobalNormalization rank size := by
    unfold generalGlobalNormalization
    have hcenter : 0 < regevCenter rank size := by
      unfold regevCenter
      positivity
    have hscale : 0 < generalRegevScale rank size :=
      generalRegevScale_pos hsize
    positivity
  have hbasePos : 0 < generalRegevBaseScale rank size := by
    unfold generalRegevBaseScale
    positivity
  change generalFullNormalizedAverage rank size /
      (generalGlobalNormalization rank size *
        generalRegevBaseScale rank size) =
    (unrestrictedCount rank size : ℝ) /
      generalRegevBaseScale rank size
  rw [generalFullNormalizedAverage_eq_normalization_mul]
  field_simp


end FibonacciRibbonKernel
