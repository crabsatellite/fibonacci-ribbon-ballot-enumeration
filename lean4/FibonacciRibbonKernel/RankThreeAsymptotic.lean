import FibonacciRibbonKernel.RankThreeTailLimit

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

noncomputable def rankThreeGeometricTailRatio : ℝ := 5 / 6

theorem rankThreeGeometricTailRatio_pos :
    0 < rankThreeGeometricTailRatio := by
  norm_num [rankThreeGeometricTailRatio]

theorem rankThreeGeometricTailRatio_lt_one :
    rankThreeGeometricTailRatio < 1 := by
  norm_num [rankThreeGeometricTailRatio]

theorem generalOddTailBound_one : generalOddTailBound 1 = 5 / 2 := by
  norm_num [generalOddTailBound, oddCosineScaleMidpoint]

theorem abs_rankThreeGeometricKernel_le_tail
    {index : ℕ} {angles : Fin 1 → ℝ}
    (htail : angles ∈ generalOddTailSpectralDomain 1) :
    |(oddCosineCubeScale angles / 3) ^ index| ≤
      rankThreeGeometricTailRatio ^ index := by
  have hscale := abs_oddCosineCubeScale_le_tailBound htail
  rw [generalOddTailBound_one] at hscale
  rw [abs_pow, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hratio : |oddCosineCubeScale angles| / 3 ≤
      rankThreeGeometricTailRatio := by
    unfold rankThreeGeometricTailRatio
    norm_num at hscale ⊢
    linarith
  exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (by norm_num))
    hratio index

theorem norm_rankThreeGeometricTailProductIntegrand_le
    (index : ℕ) (angles : Fin 1 → ℝ) :
    ‖generalOddGeometricTailProductIntegrand 1 index angles‖ ≤
      (1 / Real.pi) * rankThreeGeometricTailRatio ^ index := by
  by_cases htail : angles ∈ generalOddTailSpectralDomain 1
  · rw [generalOddGeometricTailProductIntegrand,
      Set.indicator_of_mem htail, generalOddGeometricFullIntegrand,
      Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (oddWeylAngleWeight_nonneg 1 angles)]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hkernel : |oddCosineCubeScale angles / 3| ^ index ≤
        rankThreeGeometricTailRatio ^ index := by
      simpa only [abs_pow] using
        (abs_rankThreeGeometricKernel_le_tail
          (index := index) htail)
    have hweight := oddWeylAngleWeight_le_constant 1 angles
    have hweightOne : oddWeylAngleWeight 1 angles ≤ 1 := by
      norm_num [weylPairCount] at hweight ⊢
      exact hweight
    have hproduct := mul_le_mul hkernel hweightOne
      (oddWeylAngleWeight_nonneg 1 angles)
      (pow_nonneg rankThreeGeometricTailRatio_pos.le _)
    have hscaled := mul_le_mul_of_nonneg_left hproduct
      (inv_nonneg.mpr Real.pi_pos.le)
    simpa only [mul_one, mul_assoc] using hscaled
  · rw [generalOddGeometricTailProductIntegrand,
      Set.indicator_of_notMem htail, norm_zero]
    exact mul_nonneg (by positivity)
      (pow_nonneg rankThreeGeometricTailRatio_pos.le _)

theorem tendsto_rankThreeGeometricTailPolynomial :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 2 * rankThreeGeometricTailRatio ^ index)
      atTop (nhds 0) := by
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
    (by rw [abs_of_pos rankThreeGeometricTailRatio_pos]
        exact rankThreeGeometricTailRatio_lt_one)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hdiv := hshift.div_const rankThreeGeometricTailRatio
  rw [zero_div] at hdiv
  apply hdiv.congr'
  filter_upwards with index
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  field_simp [rankThreeGeometricTailRatio_pos.ne']
  ring

theorem tendsto_rankThreeGeometricTailIntegral_zero :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddGeometricTailIntegral 1 index)
      atTop (nhds 0) := by
  let constant : ℝ := (1 / Real.pi) *
    (cosineCubeProductMeasure 1).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 2 *
        rankThreeGeometricTailRatio ^ index) * constant)
  · intro index
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ index + 1)]
    have hintegral : ‖generalOddGeometricTailIntegral 1 index‖ ≤
        ((1 / Real.pi) * rankThreeGeometricTailRatio ^ index) *
          (cosineCubeProductMeasure 1).real Set.univ := by
      unfold generalOddGeometricTailIntegral
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall
          (norm_rankThreeGeometricTailProductIntegrand_le index))
    have hsqrt : Real.sqrt (index + 1 : ℝ) ≤ (index + 1 : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
    have hpoly : Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) ≤
        (index + 1 : ℝ) ^ 2 := by
      nlinarith
    calc
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          ‖generalOddGeometricTailIntegral 1 index‖ ≤
        (index + 1 : ℝ) ^ 2 *
          ‖generalOddGeometricTailIntegral 1 index‖ :=
        mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hintegral (by positivity)
      _ = _ := by ring
  · simpa only [zero_mul] using
      tendsto_rankThreeGeometricTailPolynomial.mul_const constant

theorem tendsto_generalOddGeometricFullIntegral_one :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddGeometricFullIntegral 1 index)
      atTop (nhds (∫ coordinates : Fin 1 → ℝ,
        generalOddGeometricLocalLimitIntegrand 1 coordinates)) := by
  have hlocal : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddGeometricAngleLocalIntegral 1 index)
      atTop (nhds (∫ coordinates : Fin 1 → ℝ,
        generalOddGeometricLocalLimitIntegrand 1 coordinates)) := by
    rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddGeometricAngleLocalIntegral 1 index) =
      fun index : ℕ => ∫ coordinates : Fin 1 → ℝ,
        generalOddGeometricLocalRescaledIntegrand 1 index coordinates by
          funext index
          simpa using
            generalOddGeometricLocalScalingIntegral_identity 1 index]
    exact tendsto_integral_generalOddGeometricLocalRescaledIntegrand
      1 (by norm_num)
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddGeometricFullIntegral 1 index) =
    fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          generalOddGeometricAngleLocalIntegral 1 index +
        Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          generalOddGeometricTailIntegral 1 index by
      funext index
      rw [generalOddGeometricFullIntegral_partition,
        generalOddGeometricLocalProductIntegral_eq_angleLocal]
      ring]
  simpa using hlocal.add tendsto_rankThreeGeometricTailIntegral_zero

theorem tendsto_rankThreeUnrestrictedNormalized_regev :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        ((unrestrictedCount 2 index : ℝ) / 3 ^ index))
      atTop (nhds (regevConstant 3)) := by
  have h := tendsto_generalOddUnrestrictedNormalized_regev
    (dimension := 1) (by norm_num)
  norm_num at h ⊢
  exact h

theorem rankThreeGeometricLocalLimitIntegral_eq_regev :
    (∫ coordinates : Fin 1 → ℝ,
      generalOddGeometricLocalLimitIntegrand 1 coordinates) =
      regevConstant 3 * (1 / Real.pi) /
        oddWeylNormalization 1 := by
  have hcount := tendsto_rankThreeUnrestrictedNormalized_regev
  have hfull := tendsto_generalOddGeometricFullIntegral_one
  have hscaled : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddGeometricFullIntegral 1 index)
      atTop (nhds (regevConstant 3 * (1 / Real.pi) /
        oddWeylNormalization 1)) := by
    have hconstant : Tendsto (fun _ : ℕ =>
        (1 / Real.pi) / oddWeylNormalization 1)
        atTop (nhds ((1 / Real.pi) / oddWeylNormalization 1)) :=
      tendsto_const_nhds
    have hmul := hconstant.mul hcount
    rw [show regevConstant 3 * (1 / Real.pi) /
        oddWeylNormalization 1 =
      ((1 / Real.pi) / oddWeylNormalization 1) *
        regevConstant 3 by ring]
    apply hmul.congr'
    filter_upwards with index
    rw [generalOddGeometricFullIntegral_eq_unrestrictedCount
      1 (by norm_num) index]
    norm_num
    ring
  exact tendsto_nhds_unique hfull hscaled

theorem rankThreeRibbonLimitIntegral_eq_scaled_geometric :
    (∫ coordinates : Fin 1 → ℝ,
      oddWeylLocalLimitIntegrand 1 coordinates) =
      (generalOddGaussianTransportScale 1 ^ 3)⁻¹ *
      ∫ coordinates : Fin 1 → ℝ,
        generalOddGeometricLocalLimitIntegrand 1 coordinates := by
  let scalar := generalOddGaussianTransportScale 1
  let scaleMap := coordinateScalarLinearMap 1 scalar
  let geometric := generalOddGeometricLocalLimitIntegrand 1
  have hscalar := generalOddGaussianTransportScale_pos
    (dimension := 1) (by norm_num)
  have hmap :
      (∫ coordinates, geometric coordinates
        ∂Measure.map scaleMap (volume : Measure (Fin 1 → ℝ))) =
        ∫ coordinates, geometric (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 1 scalar).aemeasurable
      (stronglyMeasurable_generalOddGeometricLocalLimitIntegrand
        1).aestronglyMeasurable
  rw [map_coordinateScalarLinearMap_volume 1 hscalar.ne',
    integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (|scalar ^ 1|⁻¹)).toReal = scalar⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    · rw [pow_one, abs_of_pos hscalar]
    · positivity
  rw [htoReal, smul_eq_mul] at hmap
  dsimp only [geometric, scaleMap, scalar] at hmap
  rw [show (fun coordinates : Fin 1 → ℝ =>
      generalOddGeometricLocalLimitIntegrand 1
        (coordinateScalarLinearMap 1
          (generalOddGaussianTransportScale 1) coordinates)) =
    fun coordinates => generalOddGaussianTransportScale 1 ^ 2 *
      oddWeylLocalLimitIntegrand 1 coordinates by
      funext coordinates
      simpa using generalOddGeometricLimitIntegrand_transport
        (dimension := 1) (by norm_num) coordinates,
    integral_const_mul] at hmap
  have hscalarNe : generalOddGaussianTransportScale 1 ≠ 0 := hscalar.ne'
  have hmap' :
      (∫ coordinates : Fin 1 → ℝ,
        generalOddGeometricLocalLimitIntegrand 1 coordinates) =
      generalOddGaussianTransportScale 1 ^ 3 *
        ∫ coordinates : Fin 1 → ℝ,
          oddWeylLocalLimitIntegrand 1 coordinates := by
    calc
      _ = generalOddGaussianTransportScale 1 *
          ((generalOddGaussianTransportScale 1)⁻¹ *
            ∫ coordinates : Fin 1 → ℝ,
              generalOddGeometricLocalLimitIntegrand 1 coordinates) := by
        field_simp [hscalarNe]
      _ = generalOddGaussianTransportScale 1 *
          (generalOddGaussianTransportScale 1 ^ 2 *
            ∫ coordinates : Fin 1 → ℝ,
              oddWeylLocalLimitIntegrand 1 coordinates) := by
        rw [hmap]
      _ = _ := by ring
  rw [hmap']
  field_simp [hscalarNe]

theorem rankThreeRibbonLocalLimitIntegral_eq_regev :
    (∫ coordinates : Fin 1 → ℝ,
      oddWeylLocalLimitIntegrand 1 coordinates) =
      (generalOddGaussianTransportScale 1 ^ 3)⁻¹ *
        (regevConstant 3 * (1 / Real.pi) /
          oddWeylNormalization 1) := by
  rw [rankThreeRibbonLimitIntegral_eq_scaled_geometric,
    rankThreeGeometricLocalLimitIntegral_eq_regev]

theorem tendsto_rankThreeRibbon_alphaSuccNormalized :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        ((ribbonCount 2 index : ℝ) /
          fixedRankGrowth 3 ^ (index + 1)))
      atTop (nhds (regevConstant 3 *
        (generalOddGaussianTransportScale 1 ^ 3)⁻¹ /
          Real.sqrt 5)) := by
  have h := tendsto_rankThreeRibbonNormalizedIntegralConstant
  rw [rankThreeRibbonLocalLimitIntegral_eq_regev] at h
  have hnorm : oddWeylNormalization 1 ≠ 0 := by
    unfold oddWeylNormalization
    positivity
  have hconstant :
      (oddWeylNormalization 1 * Real.pi) *
          ((generalOddGaussianTransportScale 1 ^ 3)⁻¹ *
            (regevConstant 3 * (1 / Real.pi) /
              oddWeylNormalization 1)) =
        regevConstant 3 *
          (generalOddGaussianTransportScale 1 ^ 3)⁻¹ := by
    have hpiCancel : Real.pi * (1 / Real.pi) = 1 := by
      field_simp [Real.pi_ne_zero]
    rw [show (oddWeylNormalization 1 * Real.pi) *
          ((generalOddGaussianTransportScale 1 ^ 3)⁻¹ *
            (regevConstant 3 * (1 / Real.pi) /
              oddWeylNormalization 1)) =
      (Real.pi * (1 / Real.pi)) *
        (oddWeylNormalization 1 / oddWeylNormalization 1) *
          (regevConstant 3 *
            (generalOddGaussianTransportScale 1 ^ 3)⁻¹) by ring,
      hpiCancel, div_self hnorm, one_mul]
    ring
  rw [hconstant] at h
  have hsqrtFive : Real.sqrt 5 ≠ 0 := by positivity
  have hdiv := h.div_const (Real.sqrt 5)
  apply hdiv.congr'
  filter_upwards with index
  rw [show largeScalePreimage 3 = fixedRankGrowth 3 by
    simpa using largeScalePreimage_natCast 3]
  field_simp [hsqrtFive, (fixedRankGrowth_pos 3 (by norm_num)).ne']

theorem rankThreeTransferredConstant_eq_transport :
    regevConstant 3 * (generalOddGaussianTransportScale 1 ^ 3)⁻¹ /
        Real.sqrt 5 * fixedRankGrowth 3 =
      transferredFixedRankConstant 3 := by
  have h := generalOddTransferredConstant_eq_transport
    (dimension := 1) (by norm_num)
  norm_num at h ⊢
  exact h

theorem tendsto_rankThreeRibbon_nPowerNormalized :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index : ℝ) * (index : ℝ) *
        (ribbonCount 2 index : ℝ) / fixedRankGrowth 3 ^ index)
      atTop (nhds (transferredFixedRankConstant 3)) := by
  have hscaled := tendsto_rankThreeRibbon_alphaSuccNormalized.mul_const
    (fixedRankGrowth 3)
  rw [rankThreeTransferredConstant_eq_transport] at hscaled
  have hratioBase := tendsto_offset_div_offset_add_real 0 1
  have hratioSqrtRaw :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hratioBase
  norm_num at hratioSqrtRaw
  have hratio := hratioSqrtRaw.mul hratioBase
  norm_num at hratio
  have hproduct := hratio.mul hscaled
  norm_num at hproduct
  apply hproduct.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hi : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  have his : Real.sqrt (index + 1 : ℝ) ≠ 0 := by positivity
  have hgrowth := (fixedRankGrowth_pos 3 (by norm_num)).ne'
  rw [pow_succ]
  field_simp [hi, his, hgrowth]

theorem fixedRankRibbonAsymptotic_three :
    FixedRankRibbonAsymptotic 3 := by
  unfold FixedRankRibbonAsymptotic
  have hnormalized := tendsto_rankThreeRibbon_nPowerNormalized
  have hconstantPos : 0 < transferredFixedRankConstant 3 := by
    unfold transferredFixedRankConstant
    apply mul_pos
    · exact div_pos
        (mul_pos (regevConstant_pos 3 (by norm_num))
          (fixedRankGrowth_pos 3 (by norm_num))) (by norm_num)
    · apply Real.rpow_pos_of_pos
      exact div_pos (by positivity) (by norm_num)
  have hden : ∀ᶠ index : ℕ in atTop,
      fixedRankRibbonLeadingTerm 3 index ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with index hindex
    unfold fixedRankRibbonLeadingTerm
    exact mul_ne_zero (mul_ne_zero hconstantPos.ne'
      (pow_ne_zero _ (fixedRankGrowth_pos 3 (by norm_num)).ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [isEquivalent_iff_tendsto_one hden]
  have hdiv := hnormalized.div_const (transferredFixedRankConstant 3)
  rw [div_self hconstantPos.ne'] at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hi : (0 : ℝ) < index := by positivity
  have hiNe : (index : ℝ) ≠ 0 := hi.ne'
  have hscale : Real.sqrt (index : ℝ) * (index : ℝ) =
      (index : ℝ) ^ fixedRankExponent 3 := by
    simpa using sqrt_pow_mul_pow_eq_oddExponent 1 hi
  rw [hscale]
  simp only [Pi.div_apply]
  unfold fixedRankRibbonLeadingTerm
  rw [Real.rpow_neg hi.le]
  field_simp [hiNe, hconstantPos.ne',
    (fixedRankGrowth_pos 3 (by norm_num)).ne']

end FibonacciRibbonKernel
