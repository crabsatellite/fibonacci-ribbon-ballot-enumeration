import FibonacciRibbonKernel.RankFourGeometricFull

namespace FibonacciRibbonKernel

open Filter MeasureTheory Asymptotics

theorem tendsto_heightFourTableauNormalized_regev :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 *
        ((heightFourTableauCount index : ℝ) / 4 ^ index))
      atTop (nhds (regevConstant 4)) := by
  have hraw := unrestrictedCount_normalized_tendsto_regevConstant_of_mehta
    3 (regevMehtaChamberEvaluation_all 3)
  have hnormalized : Tendsto (fun index : ℕ =>
      (index : ℝ) ^ 3 *
        ((heightFourTableauCount index : ℝ) / 4 ^ index))
      atTop (nhds (regevConstant 4)) := by
    apply hraw.congr'
    filter_upwards [eventually_ne_atTop 0] with index hindex
    have hindexNonneg : (0 : ℝ) ≤ index := by positivity
    have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
    unfold heightFourTableauCount generalRegevBaseScale
    rw [fixedRankExponent_four, Real.rpow_neg hindexNonneg]
    field_simp [hindexReal]
    norm_num
    ring
  have hratioBase := tendsto_offset_div_offset_add_real 1 (-1)
  have hratio : Tendsto (fun index : ℕ =>
      (((index : ℝ) + 1) / (index : ℝ)) ^ 3)
      atTop (nhds 1) := by
    have hpow := hratioBase.pow 3
    norm_num at hpow
    exact hpow
  have hproduct := hratio.mul hnormalized
  norm_num at hproduct
  apply hproduct.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  field_simp [hindexReal]

theorem rankFourGeometricLimitIntegral_eq_regev :
    (∫ coordinates : Fin 2 → ℝ,
      rankFourGeometricLocalLimitIntegrand coordinates) =
      regevConstant 4 / 2 := by
  have heq := tendsto_nhds_unique tendsto_heightFourTableauNormalized_regev
    tendsto_rankFourTableauNormalizedIntegralConstant
  linarith

theorem rankFourGeometricLimitIntegral_explicit :
    (∫ coordinates : Fin 2 → ℝ,
      rankFourGeometricLocalLimitIntegrand coordinates) =
      16 / Real.pi := by
  rw [rankFourGeometricLimitIntegral_eq_regev, regevConstant_four]
  ring

theorem evenLimitWeylWeight_two_formula (coordinates : Fin 2 → ℝ) :
    evenLimitWeylWeight 2 coordinates =
      (coordinates 0 ^ 2 - coordinates 1 ^ 2) ^ 2 := by
  unfold evenLimitWeylWeight quadraticVandermondeWeight
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]
  have hzero : Finset.Iio (0 : Fin 2) = ∅ := by decide
  have hone : Finset.Iio (1 : Fin 2) = {0} := by decide
  rw [hzero, hone]
  simp only [Finset.prod_empty, Finset.prod_singleton, one_mul]
  norm_num
  ring

theorem evenLimitWeylWeight_two_scalar
    (scalar : ℝ) (coordinates : Fin 2 → ℝ) :
    evenLimitWeylWeight 2
        (coordinateScalarLinearMap 2 scalar coordinates) =
      scalar ^ 4 * evenLimitWeylWeight 2 coordinates := by
  rw [evenLimitWeylWeight_two_formula, evenLimitWeylWeight_two_formula]
  simp only [coordinateScalarLinearMap_apply]
  ring

theorem continuous_evenLimitWeylWeight_two :
    Continuous (evenLimitWeylWeight 2) := by
  rw [show evenLimitWeylWeight 2 = fun coordinates : Fin 2 → ℝ =>
      (coordinates 0 ^ 2 - coordinates 1 ^ 2) ^ 2 by
    funext coordinates
    exact evenLimitWeylWeight_two_formula coordinates]
  fun_prop

theorem stronglyMeasurable_rankFourGeometricLocalLimitIntegrand :
    StronglyMeasurable rankFourGeometricLocalLimitIntegrand := by
  unfold rankFourGeometricLocalLimitIntegrand
  have hsquares : Continuous (fun coordinates : Fin 2 → ℝ =>
      ∑ coordinate, coordinates coordinate ^ 2) := by fun_prop
  have hexp : Continuous (fun coordinates : Fin 2 → ℝ =>
      Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) / 4)) :=
    Real.continuous_exp.comp (hsquares.neg.div_const 4)
  exact (((continuous_const.mul hexp).mul
    continuous_evenLimitWeylWeight_two).stronglyMeasurable.indicator
      (measurableSet_positiveOrthant 2))

noncomputable def rankFourGaussianTransportScale : ℝ :=
  Real.sqrt (4 / Real.sqrt (12 : ℝ))

theorem rankFourGaussianTransportScale_pos :
    0 < rankFourGaussianTransportScale := by
  unfold rankFourGaussianTransportScale
  positivity

theorem rankFourGaussianTransportScale_sq :
    rankFourGaussianTransportScale ^ 2 = 4 / Real.sqrt (12 : ℝ) := by
  unfold rankFourGaussianTransportScale
  exact Real.sq_sqrt (by positivity)

theorem rankFourGeometricLimitIntegrand_transport
    (coordinates : Fin 2 → ℝ) :
    rankFourGeometricLocalLimitIntegrand
        (coordinateScalarLinearMap 2 rankFourGaussianTransportScale coordinates) =
      rankFourGaussianTransportScale ^ 4 *
        rankFourEvenLocalLimitIntegrand coordinates := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hscaled := (mem_positiveOrthant_coordinateScalar_iff
      rankFourGaussianTransportScale_pos coordinates).2 horthant
    rw [rankFourGeometricLocalLimitIntegrand, Set.indicator_of_mem hscaled,
      rankFourEvenLocalLimitIntegrand, Set.indicator_of_mem horthant,
      evenLimitWeylWeight_two_scalar, sum_sq_coordinateScalar_two]
    have hsqrt : Real.sqrt (12 : ℝ) ≠ 0 := by positivity
    have hexponent :
        (-(rankFourGaussianTransportScale ^ 2 *
            ∑ coordinate, coordinates coordinate ^ 2)) / 4 =
          (-∑ coordinate, coordinates coordinate ^ 2) /
            Real.sqrt (12 : ℝ) := by
      rw [rankFourGaussianTransportScale_sq]
      field_simp [hsqrt]
    rw [hexponent]
    ring
  · have hscaled :
        coordinateScalarLinearMap 2 rankFourGaussianTransportScale coordinates ∉
          positiveOrthant :=
      mt (mem_positiveOrthant_coordinateScalar_iff
        rankFourGaussianTransportScale_pos coordinates).1 horthant
    rw [rankFourGeometricLocalLimitIntegrand, Set.indicator_of_notMem hscaled,
      rankFourEvenLocalLimitIntegrand, Set.indicator_of_notMem horthant, mul_zero]

theorem rankFourFibonacciLimitIntegral_eq_scaled_geometric :
    (∫ coordinates : Fin 2 → ℝ,
      rankFourEvenLocalLimitIntegrand coordinates) =
      (Real.sqrt (12 : ℝ) / 4) ^ 3 *
        ∫ coordinates : Fin 2 → ℝ,
          rankFourGeometricLocalLimitIntegrand coordinates := by
  let scalar := rankFourGaussianTransportScale
  let scaleMap := coordinateScalarLinearMap 2 scalar
  let geometric := rankFourGeometricLocalLimitIntegrand
  have hmap :
      (∫ coordinates, geometric coordinates
        ∂Measure.map scaleMap (volume : Measure (Fin 2 → ℝ))) =
        ∫ coordinates, geometric (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 2 scalar).aemeasurable
      stronglyMeasurable_rankFourGeometricLocalLimitIntegrand.aestronglyMeasurable
  rw [map_coordinateScalarLinearMap_volume 2
    rankFourGaussianTransportScale_pos.ne', integral_smul_measure] at hmap
  have htoReal : (ENNReal.ofReal (|scalar ^ 2|⁻¹)).toReal =
      (scalar ^ 2)⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    · rw [abs_of_pos (pow_pos rankFourGaussianTransportScale_pos 2)]
    · positivity
  rw [htoReal, smul_eq_mul] at hmap
  dsimp only [geometric, scaleMap, scalar] at hmap
  rw [show (fun coordinates : Fin 2 → ℝ =>
      rankFourGeometricLocalLimitIntegrand
        (coordinateScalarLinearMap 2 rankFourGaussianTransportScale coordinates)) =
      fun coordinates => rankFourGaussianTransportScale ^ 4 *
        rankFourEvenLocalLimitIntegrand coordinates by
    funext coordinates
    exact rankFourGeometricLimitIntegrand_transport coordinates,
    integral_const_mul] at hmap
  have hscalar : rankFourGaussianTransportScale ≠ 0 :=
    rankFourGaussianTransportScale_pos.ne'
  have hpower : (Real.sqrt (12 : ℝ) / 4) ^ 3 =
      (rankFourGaussianTransportScale ^ 6)⁻¹ := by
    rw [show rankFourGaussianTransportScale ^ 6 =
        (rankFourGaussianTransportScale ^ 2) ^ 3 by ring,
      rankFourGaussianTransportScale_sq, div_pow, ← inv_pow, inv_div,
      div_pow]
  rw [hpower]
  field_simp [hscalar] at hmap ⊢
  nlinarith

theorem rankFourFibonacciLimitIntegral_explicit :
    (∫ coordinates : Fin 2 → ℝ,
      rankFourEvenLocalLimitIntegrand coordinates) =
      6 * Real.sqrt 3 / Real.pi := by
  rw [rankFourFibonacciLimitIntegral_eq_scaled_geometric,
    rankFourGeometricLimitIntegral_explicit]
  have hsqrt12 : Real.sqrt (12 : ℝ) = 2 * Real.sqrt 3 := by
    calc
      Real.sqrt (12 : ℝ) = Real.sqrt (4 * 3) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt 3 := by norm_num
  rw [hsqrt12]
  have hsqrtSq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by positivity)
  field_simp [Real.pi_ne_zero]
  nlinarith

theorem tendsto_rankFourRibbonNormalized_explicit :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 *
        ((ribbonCount 3 index : ℝ) /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)))
      atTop (nhds (12 * Real.sqrt 3 / Real.pi)) := by
  have h := tendsto_rankFourRibbonNormalizedIntegralConstant
  rw [rankFourFibonacciLimitIntegral_explicit] at h
  convert h using 1
  ring

theorem fixedRankRibbonAsymptotic_four : FixedRankRibbonAsymptotic 4 := by
  have hsqrt12 : Real.sqrt (12 : ℝ) = 2 * Real.sqrt 3 := by
    calc
      Real.sqrt (12 : ℝ) = Real.sqrt (4 * 3) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt 3 := by norm_num
  have h := tendsto_rankFourRibbonNormalized_explicit.div_const
    (Real.sqrt (12 : ℝ))
  have hsqrtNe : Real.sqrt (12 : ℝ) ≠ 0 := by positivity
  have hlimit : (12 * Real.sqrt 3 / Real.pi) / Real.sqrt 12 =
      6 / Real.pi := by
    rw [hsqrt12]
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [hlimit] at h
  have halphaSucc : Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * (ribbonCount 3 index : ℝ) /
        fixedRankGrowth 4 ^ (index + 1))
      atTop (nhds (6 / Real.pi)) := by
    apply h.congr'
    filter_upwards with index
    rw [show largeScalePreimage 4 = fixedRankGrowth 4 by
      exact largeScalePreimage_natCast 4]
    field_simp [hsqrtNe, (fixedRankGrowth_pos 4 (by norm_num)).ne']
  have hratio := (tendsto_offset_div_offset_add_real 0 1).pow 3
  norm_num at hratio
  have hproduct := hratio.mul halphaSucc
  norm_num at hproduct
  have hsucc : Tendsto (fun index : ℕ =>
      (index : ℝ) ^ 3 * (ribbonCount 3 index : ℝ) /
        fixedRankGrowth 4 ^ (index + 1)) atTop (nhds (6 / Real.pi)) := by
    apply hproduct.congr'
    filter_upwards with index
    field_simp [(fixedRankGrowth_pos 4 (by norm_num)).ne']
  have hscaled := hsucc.mul_const (fixedRankGrowth 4)
  have hscaledLimit :
      6 / Real.pi * fixedRankGrowth 4 =
        transferredFixedRankConstant 4 := by
    rw [fixedRankGrowth_four, transferredFixedRankConstant_four]
    ring
  rw [hscaledLimit] at hscaled
  have hnormalized : Tendsto (fun index : ℕ =>
      (index : ℝ) ^ 3 * (ribbonCount 3 index : ℝ) /
        fixedRankGrowth 4 ^ index)
      atTop (nhds (transferredFixedRankConstant 4)) := by
    apply hscaled.congr'
    filter_upwards with index
    rw [pow_succ]
    field_simp [(fixedRankGrowth_pos 4 (by norm_num)).ne']
    ring
  unfold FixedRankRibbonAsymptotic
  have hconstantPos : 0 < transferredFixedRankConstant 4 := by
    rw [transferredFixedRankConstant_four]
    positivity
  have hden : ∀ᶠ index : ℕ in atTop,
      fixedRankRibbonLeadingTerm 4 index ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with index hindex
    unfold fixedRankRibbonLeadingTerm
    exact mul_ne_zero (mul_ne_zero hconstantPos.ne'
      (pow_ne_zero _ (fixedRankGrowth_pos 4 (by norm_num)).ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [isEquivalent_iff_tendsto_one hden]
  have hdiv := hnormalized.div_const (transferredFixedRankConstant 4)
  rw [div_self hconstantPos.ne'] at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hindexNonneg : (0 : ℝ) ≤ index := by positivity
  have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  simp only [Pi.div_apply]
  unfold fixedRankRibbonLeadingTerm
  rw [fixedRankExponent_four, Real.rpow_neg hindexNonneg]
  field_simp [hindexReal, hconstantPos.ne',
    (fixedRankGrowth_pos 4 (by norm_num)).ne']
  norm_num
  ring

end FibonacciRibbonKernel
