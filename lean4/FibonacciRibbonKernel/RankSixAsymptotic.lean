import FibonacciRibbonKernel.RankSixGeometricFull

namespace FibonacciRibbonKernel

open Filter MeasureTheory Asymptotics Set

theorem sqrt_cube_mul_pow_six_eq_rpow_fifteen_halves
    {value : ℝ} (hvalue : 0 < value) :
    Real.sqrt value ^ 3 * value ^ 6 = value ^ (15 / 2 : ℝ) := by
  have hcube : Real.sqrt value ^ 3 = value ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hvalue.le]
    congr 1
    norm_num
  have hsix : value ^ 6 = value ^ (6 : ℝ) := by
    exact (Real.rpow_natCast value 6).symm
  rw [hcube, hsix, ← Real.rpow_add hvalue]
  congr 1
  ring

theorem tendsto_heightSixTableauNormalized_regev :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        ((heightSixTableauCount index : ℝ) / 6 ^ index))
      atTop (nhds (regevConstant 6)) := by
  have hraw := unrestrictedCount_normalized_tendsto_regevConstant_of_mehta
    5 (regevMehtaChamberEvaluation_all 5)
  have hbase : Tendsto (fun index : ℕ =>
      Real.sqrt (index : ℝ) ^ 3 * (index : ℝ) ^ 6 *
        ((heightSixTableauCount index : ℝ) / 6 ^ index))
      atTop (nhds (regevConstant 6)) := by
    apply hraw.congr'
    filter_upwards [eventually_ne_atTop 0] with index hindex
    have hi : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
    have hip : (0 : ℝ) < index := by positivity
    have hin : (0 : ℝ) ≤ index := hip.le
    unfold heightSixTableauCount generalRegevBaseScale
    rw [fixedRankExponent_six, sqrt_cube_mul_pow_six_eq_rpow_fifteen_halves hip,
      Real.rpow_neg hin]
    field_simp [hi]
    norm_num
  have hratioBase := tendsto_offset_div_offset_add_real 1 (-1)
  have hsqrtRatio := (Real.continuous_sqrt.continuousAt.tendsto.comp hratioBase).pow 3
  norm_num at hsqrtRatio
  have hpowRatio := hratioBase.pow 6
  norm_num at hpowRatio
  have hratio := hsqrtRatio.mul hpowRatio
  norm_num at hratio
  have hp := hratio.mul hbase
  norm_num at hp
  apply hp.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hi : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  have hip : (0 : ℝ) < index := by positivity
  rw [div_pow, div_pow]
  have hsqrti : Real.sqrt (index : ℝ) ≠ 0 := by positivity
  field_simp [hi, hsqrti]

theorem rankSixGeometricLimitIntegral_eq_regev :
    (∫ coordinates : Fin 3 → ℝ,
      rankSixGeometricLocalLimitIntegrand coordinates) =
      (3 / 32 : ℝ) * regevConstant 6 := by
  have heq := tendsto_nhds_unique tendsto_heightSixTableauNormalized_regev
    tendsto_rankSixTableauNormalizedIntegralConstant
  linarith

theorem evenLimitWeylWeight_three_formula (coordinates : Fin 3 → ℝ) :
    evenLimitWeylWeight 3 coordinates =
      8 * ((coordinates 0 ^ 2 - coordinates 1 ^ 2) / 2) ^ 2 *
        ((coordinates 0 ^ 2 - coordinates 2 ^ 2) / 2) ^ 2 *
        ((coordinates 1 ^ 2 - coordinates 2 ^ 2) / 2) ^ 2 := by
  unfold evenLimitWeylWeight quadraticVandermondeWeight
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))),
    Finset.prod_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
    Finset.prod_singleton]
  have h0 : Finset.Iio (0 : Fin 3) = ∅ := by decide
  have h1 : Finset.Iio (1 : Fin 3) = {0} := by decide
  have h2 : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
  rw [h0, h1, h2]
  norm_num
  ring

theorem evenLimitWeylWeight_three_scalar
    (scalar : ℝ) (coordinates : Fin 3 → ℝ) :
    evenLimitWeylWeight 3
        (coordinateScalarLinearMap 3 scalar coordinates) =
      scalar ^ 12 * evenLimitWeylWeight 3 coordinates := by
  rw [evenLimitWeylWeight_three_formula,
    evenLimitWeylWeight_three_formula]
  simp only [coordinateScalarLinearMap_apply]
  ring

theorem continuous_evenLimitWeylWeight_three :
    Continuous (evenLimitWeylWeight 3) := by
  rw [show evenLimitWeylWeight 3 = fun coordinates : Fin 3 → ℝ =>
      8 * ((coordinates 0 ^ 2 - coordinates 1 ^ 2) / 2) ^ 2 *
        ((coordinates 0 ^ 2 - coordinates 2 ^ 2) / 2) ^ 2 *
        ((coordinates 1 ^ 2 - coordinates 2 ^ 2) / 2) ^ 2 by
    funext coordinates
    exact evenLimitWeylWeight_three_formula coordinates]
  fun_prop

theorem stronglyMeasurable_rankSixGeometricLocalLimitIntegrand :
    StronglyMeasurable rankSixGeometricLocalLimitIntegrand := by
  unfold rankSixGeometricLocalLimitIntegrand
  have hs : Continuous (fun coordinates : Fin 3 → ℝ =>
      ∑ coordinate, coordinates coordinate ^ 2) := by fun_prop
  have he : Continuous (fun coordinates : Fin 3 → ℝ =>
      Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) / 6)) :=
    Real.continuous_exp.comp (hs.neg.div_const 6)
  exact (((continuous_const.mul he).mul
    continuous_evenLimitWeylWeight_three).stronglyMeasurable.indicator
      (measurableSet_positiveOrthant 3))

noncomputable def rankSixGaussianTransportScale : ℝ :=
  Real.sqrt (6 / Real.sqrt (32 : ℝ))

theorem rankSixGaussianTransportScale_pos : 0 < rankSixGaussianTransportScale := by
  unfold rankSixGaussianTransportScale
  positivity

theorem rankSixGaussianTransportScale_sq :
    rankSixGaussianTransportScale ^ 2 = 6 / Real.sqrt (32 : ℝ) := by
  unfold rankSixGaussianTransportScale
  exact Real.sq_sqrt (by positivity)

theorem sum_sq_coordinateScalar_three
    (scalar : ℝ) (coordinates : Fin 3 → ℝ) :
    (∑ coordinate,
      (coordinateScalarLinearMap 3 scalar coordinates coordinate) ^ 2) =
      scalar ^ 2 * ∑ coordinate, coordinates coordinate ^ 2 := by
  rw [show (∑ coordinate : Fin 3,
      (coordinateScalarLinearMap 3 scalar coordinates coordinate) ^ 2) =
      (scalar * coordinates 0) ^ 2 + (scalar * coordinates 1) ^ 2 +
        (scalar * coordinates 2) ^ 2 by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))),
      Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
      Finset.sum_singleton]
    simp [coordinateScalarLinearMap_apply]
    ring]
  rw [show (∑ coordinate : Fin 3, coordinates coordinate ^ 2) =
      coordinates 0 ^ 2 + coordinates 1 ^ 2 + coordinates 2 ^ 2 by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))),
      Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
      Finset.sum_singleton]
    ring]
  ring

theorem rankSixGeometricLimitIntegrand_transport
    (coordinates : Fin 3 → ℝ) :
    rankSixGeometricLocalLimitIntegrand
        (coordinateScalarLinearMap 3 rankSixGaussianTransportScale coordinates) =
      rankSixGaussianTransportScale ^ 12 *
        rankSixEvenLocalLimitIntegrand coordinates := by
  by_cases ho : coordinates ∈ positiveOrthant
  · have hso := (mem_positiveOrthant_coordinateScalar_iff
      rankSixGaussianTransportScale_pos coordinates).2 ho
    rw [rankSixGeometricLocalLimitIntegrand, Set.indicator_of_mem hso,
      rankSixEvenLocalLimitIntegrand, Set.indicator_of_mem ho,
      evenLimitWeylWeight_three_scalar, sum_sq_coordinateScalar_three]
    have hr : Real.sqrt (32 : ℝ) ≠ 0 := by positivity
    have he : (-(rankSixGaussianTransportScale ^ 2 *
        ∑ coordinate, coordinates coordinate ^ 2)) / 6 =
        (-∑ coordinate, coordinates coordinate ^ 2) / Real.sqrt 32 := by
      rw [rankSixGaussianTransportScale_sq]
      field_simp [hr]
    rw [he]
    ring
  · have hso :
        coordinateScalarLinearMap 3 rankSixGaussianTransportScale coordinates ∉
          positiveOrthant :=
      mt (mem_positiveOrthant_coordinateScalar_iff
        rankSixGaussianTransportScale_pos coordinates).1 ho
    rw [rankSixGeometricLocalLimitIntegrand, Set.indicator_of_notMem hso,
      rankSixEvenLocalLimitIntegrand, Set.indicator_of_notMem ho, mul_zero]

theorem rankSixFibonacciLimitIntegral_eq_scaled_geometric :
    (∫ coordinates : Fin 3 → ℝ,
      rankSixEvenLocalLimitIntegrand coordinates) =
      (rankSixGaussianTransportScale ^ 15)⁻¹ *
        ∫ coordinates : Fin 3 → ℝ,
          rankSixGeometricLocalLimitIntegrand coordinates := by
  let scalar := rankSixGaussianTransportScale
  let scaleMap := coordinateScalarLinearMap 3 scalar
  let geometric := rankSixGeometricLocalLimitIntegrand
  have hmap :
      (∫ coordinates, geometric coordinates
        ∂Measure.map scaleMap (volume : Measure (Fin 3 → ℝ))) =
        ∫ coordinates, geometric (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 3 scalar).aemeasurable
      stronglyMeasurable_rankSixGeometricLocalLimitIntegrand.aestronglyMeasurable
  rw [map_coordinateScalarLinearMap_volume 3
    rankSixGaussianTransportScale_pos.ne', integral_smul_measure] at hmap
  have ht : (ENNReal.ofReal (|scalar ^ 3|⁻¹)).toReal = (scalar ^ 3)⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    · rw [abs_of_pos (pow_pos rankSixGaussianTransportScale_pos 3)]
    · positivity
  rw [ht, smul_eq_mul] at hmap
  dsimp only [geometric, scaleMap, scalar] at hmap
  rw [show (fun coordinates : Fin 3 → ℝ =>
      rankSixGeometricLocalLimitIntegrand
        (coordinateScalarLinearMap 3 rankSixGaussianTransportScale coordinates)) =
      fun coordinates => rankSixGaussianTransportScale ^ 12 *
        rankSixEvenLocalLimitIntegrand coordinates by
    funext coordinates
    exact rankSixGeometricLimitIntegrand_transport coordinates,
    integral_const_mul] at hmap
  have hs : rankSixGaussianTransportScale ≠ 0 :=
    rankSixGaussianTransportScale_pos.ne'
  field_simp [hs] at hmap ⊢
  nlinarith

theorem rankSixGaussianTransportScale_inverse_power :
    (rankSixGaussianTransportScale ^ 15)⁻¹ =
      (Real.sqrt (32 : ℝ) / 6) ^ (15 / 2 : ℝ) := by
  let ratio : ℝ := 6 / Real.sqrt (32 : ℝ)
  have hr : 0 < ratio := by unfold ratio; positivity
  have hpow : rankSixGaussianTransportScale ^ 15 =
      ratio ^ (15 / 2 : ℝ) := by
    unfold rankSixGaussianTransportScale ratio
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le]
    congr 1
    norm_num
  rw [hpow, ← Real.inv_rpow hr.le]
  congr 1
  unfold ratio
  have hs : Real.sqrt (32 : ℝ) ≠ 0 := by positivity
  field_simp [hs]

theorem rankSixNormalizedLimitConstant_eq_transferred :
    (32 / 3 : ℝ) *
        (∫ coordinates : Fin 3 → ℝ,
          rankSixEvenLocalLimitIntegrand coordinates) =
      transferredFixedRankConstant 6 * Real.sqrt 32 /
        fixedRankGrowth 6 := by
  rw [rankSixFibonacciLimitIntegral_eq_scaled_geometric,
    rankSixGeometricLimitIntegral_eq_regev,
    rankSixGaussianTransportScale_inverse_power]
  have hscalePos : 0 < Real.sqrt (32 : ℝ) / 6 := by positivity
  have hpower :
      (Real.sqrt (32 : ℝ) / 6) ^ (15 / 2 : ℝ) =
        (Real.sqrt (32 : ℝ) / 6) ^ (13 / 2 : ℝ) *
          (Real.sqrt (32 : ℝ) / 6) := by
    calc
      _ = (Real.sqrt (32 : ℝ) / 6) ^
          ((13 / 2 : ℝ) + 1) := by norm_num
      _ = (Real.sqrt (32 : ℝ) / 6) ^ (13 / 2 : ℝ) *
          (Real.sqrt (32 : ℝ) / 6) ^ (1 : ℝ) := by
        rw [Real.rpow_add hscalePos]
      _ = _ := by rw [Real.rpow_one]
  rw [hpower, transferredFixedRankConstant, fixedRankExponent_six]
  have hg : fixedRankGrowth 6 ≠ 0 :=
    (fixedRankGrowth_pos 6 (by norm_num)).ne'
  have hs : Real.sqrt (32 : ℝ) ≠ 0 := by positivity
  field_simp [hg, hs]
  ring

theorem tendsto_rankSixRibbonNormalized_transferred :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        ((ribbonCount 5 index : ℝ) /
          (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)))
      atTop (nhds (transferredFixedRankConstant 6 * Real.sqrt 32 /
        fixedRankGrowth 6)) := by
  rw [← rankSixNormalizedLimitConstant_eq_transferred]
  exact tendsto_rankSixRibbonNormalizedIntegralConstant

theorem fixedRankRibbonAsymptotic_six : FixedRankRibbonAsymptotic 6 := by
  have hsqrt : Real.sqrt (32 : ℝ) ≠ 0 := by positivity
  have hgrowth : 0 < fixedRankGrowth 6 := fixedRankGrowth_pos 6 (by norm_num)
  have hdiv := tendsto_rankSixRibbonNormalized_transferred.div_const
    (Real.sqrt (32 : ℝ))
  have hlimit :
      (transferredFixedRankConstant 6 * Real.sqrt 32 /
          fixedRankGrowth 6) / Real.sqrt 32 =
        transferredFixedRankConstant 6 / fixedRankGrowth 6 := by
    field_simp [hsqrt, hgrowth.ne']
  rw [hlimit] at hdiv
  have halphaSucc : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        (ribbonCount 5 index : ℝ) /
          fixedRankGrowth 6 ^ (index + 1))
      atTop (nhds (transferredFixedRankConstant 6 / fixedRankGrowth 6)) := by
    apply hdiv.congr'
    filter_upwards with index
    rw [show largeScalePreimage 6 = fixedRankGrowth 6 by
      exact largeScalePreimage_natCast 6]
    field_simp [hsqrt, hgrowth.ne']
  have hscaled := halphaSucc.mul_const (fixedRankGrowth 6)
  have hconstantPos : 0 < transferredFixedRankConstant 6 := by
    rw [transferredFixedRankConstant_six]
    positivity
  have hlimitScaled :
      transferredFixedRankConstant 6 / fixedRankGrowth 6 *
          fixedRankGrowth 6 = transferredFixedRankConstant 6 := by
    field_simp [hgrowth.ne']
  rw [hlimitScaled] at hscaled
  have hsucc : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        (ribbonCount 5 index : ℝ) / fixedRankGrowth 6 ^ index)
      atTop (nhds (transferredFixedRankConstant 6)) := by
    apply hscaled.congr'
    filter_upwards with index
    rw [pow_succ]
    field_simp [hgrowth.ne']
    ring
  have hratioBase := tendsto_offset_div_offset_add_real 0 1
  have hsqrtRatio :=
    (Real.continuous_sqrt.continuousAt.tendsto.comp hratioBase).pow 3
  norm_num at hsqrtRatio
  have hpowRatio := hratioBase.pow 6
  norm_num at hpowRatio
  have hratio := hsqrtRatio.mul hpowRatio
  norm_num at hratio
  have hproduct := hratio.mul hsucc
  norm_num at hproduct
  have hnormalized : Tendsto (fun index : ℕ =>
      Real.sqrt (index : ℝ) ^ 3 * (index : ℝ) ^ 6 *
        (ribbonCount 5 index : ℝ) / fixedRankGrowth 6 ^ index)
      atTop (nhds (transferredFixedRankConstant 6)) := by
    apply hproduct.congr'
    filter_upwards [eventually_ne_atTop 0] with index hindex
    have hi : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
    have hsqrti : Real.sqrt (index : ℝ) ≠ 0 := by positivity
    rw [div_pow, div_pow]
    field_simp [hi, hsqrti, hgrowth.ne']
  unfold FixedRankRibbonAsymptotic
  have hden : ∀ᶠ index : ℕ in atTop,
      fixedRankRibbonLeadingTerm 6 index ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with index hindex
    unfold fixedRankRibbonLeadingTerm
    exact mul_ne_zero (mul_ne_zero hconstantPos.ne'
      (pow_ne_zero _ hgrowth.ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [isEquivalent_iff_tendsto_one hden]
  have hnormalized' : Tendsto (fun index : ℕ =>
      (index : ℝ) ^ (fixedRankExponent 6) *
        (ribbonCount 5 index : ℝ) / fixedRankGrowth 6 ^ index)
      atTop (nhds (transferredFixedRankConstant 6)) := by
    apply hnormalized.congr'
    filter_upwards [eventually_ge_atTop 1] with index hindex
    rw [fixedRankExponent_six,
      ← sqrt_cube_mul_pow_six_eq_rpow_fifteen_halves
        (show (0 : ℝ) < index by positivity)]
  have hfinal := hnormalized'.div_const (transferredFixedRankConstant 6)
  rw [div_self hconstantPos.ne'] at hfinal
  apply hfinal.congr'
  filter_upwards [eventually_ge_atTop 1] with index hindex
  have hi : (0 : ℝ) < index := by positivity
  simp only [Pi.div_apply]
  unfold fixedRankRibbonLeadingTerm
  rw [Real.rpow_neg hi.le]
  field_simp [hconstantPos.ne', hgrowth.ne', hi.ne']

end FibonacciRibbonKernel
