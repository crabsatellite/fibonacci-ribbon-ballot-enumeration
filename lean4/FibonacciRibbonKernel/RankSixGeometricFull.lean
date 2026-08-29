import FibonacciRibbonKernel.RankSixGeometricDCT

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankSixGeometricMinusLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 3 → ℝ) : ℝ :=
  (positiveLocalScaledDomain 3 index).indicator (fun coordinates =>
    (1 / Real.pi) ^ 3 * normalizedRankSixGeometricKernel coordinates index *
      rankSixEvenMinusScaledWeight index coordinates) coordinates

noncomputable def rankSixGeometricMinusAngleLocalIntegrand
    (index : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  (anglePositiveLocalDomain 3).indicator (fun angles =>
    (1 / Real.pi) ^ 3 * (cosineCubeScale angles / 6) ^ index *
      (cosineVandermondeWeight 3 angles * allMinusAngleWeight 3 angles)) angles

noncomputable def rankSixGeometricMinusAngleLocalIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ,
    rankSixGeometricMinusAngleLocalIntegrand index angles

theorem tendsto_rankSixGeometricMinusLocalRescaled_zero
    (coordinates : Fin 3 → ℝ) :
    Tendsto (fun index =>
      rankSixGeometricMinusLocalRescaledIntegrand index coordinates)
      atTop (nhds 0) := by
  by_cases ho : coordinates ∈ positiveOrthant
  · have hl := eventually_mem_positiveLocalScaledDomain
      (dimension := 3) (by norm_num) coordinates ho
    have hk := tendsto_normalizedRankSixGeometricKernel coordinates
    have hw := tendsto_rankSixEvenMinusScaledWeight_zero coordinates
    have hc : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 3)
        atTop (nhds ((1 / Real.pi) ^ 3)) := tendsto_const_nhds
    have hp := (hc.mul hk).mul hw
    simpa only [mul_zero] using hp.congr' (by
      filter_upwards [hl] with index hi
      rw [rankSixGeometricMinusLocalRescaledIntegrand,
        Set.indicator_of_mem hi])
  · have hn : ∃ coordinate : Fin 3, coordinates coordinate ≤ 0 := by
      by_contra h
      push Not at h
      exact ho fun coordinate _ => h coordinate
    obtain ⟨coordinate, hc⟩ := hn
    have hout : ∀ index, coordinates ∉ positiveLocalScaledDomain 3 index := by
      intro index hd
      linarith [(hd.1 coordinate (Set.mem_univ coordinate)).1]
    rw [show (fun index : ℕ =>
        rankSixGeometricMinusLocalRescaledIntegrand index coordinates) = fun _ => 0 by
      funext index
      rw [rankSixGeometricMinusLocalRescaledIntegrand,
        Set.indicator_of_notMem (hout index)]]
    exact tendsto_const_nhds

theorem aestronglyMeasurable_rankSixGeometricMinusLocalRescaled
    (index : ℕ) :
    AEStronglyMeasurable (rankSixGeometricMinusLocalRescaledIntegrand index) := by
  have hk : Continuous (normalizedRankSixGeometricKernel · index) := by
    unfold normalizedRankSixGeometricKernel
    exact ((continuous_cosineSumScale 3 index).div_const 6).pow index
  unfold rankSixGeometricMinusLocalRescaledIntegrand
  exact (((continuous_const.mul hk).mul
    ((continuous_scaledCosineVandermondeWeight 3 index).mul
      (continuous_allMinusScaledWeight 3 index))).stronglyMeasurable.indicator
    (measurableSet_positiveLocalScaledDomain 3 index)).aestronglyMeasurable

theorem norm_rankSixGeometricMinusLocalRescaled_le
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    ‖rankSixGeometricMinusLocalRescaledIntegrand index coordinates‖ ≤
      rankSixGeometricLocalDominating coordinates := by
  by_cases hd : coordinates ∈ positiveLocalScaledDomain 3 index
  · rw [rankSixGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_mem hd, Real.norm_eq_abs, abs_of_nonneg]
    · have hk := normalizedRankSixGeometricKernel_le_gaussian
        index coordinates hd.1 hd.2
      have hw := rankSixEvenMinusScaledWeight_le_polynomial index coordinates
      have hscale : 0 ≤ cosineSumScale coordinates index :=
        (by norm_num : (0 : ℝ) ≤ 2).trans
          ((cosineScaleMidpoint_gt_two
            (dimension := 3) (by norm_num)).le.trans hd.2)
      have hkn := normalizedRankSixGeometricKernel_nonneg
        (index := index) (coordinates := coordinates) hscale
      have hwn := rankSixEvenMinusScaledWeight_nonneg index coordinates
      have hp := mul_le_mul hk hw hwn (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hp
        (show 0 ≤ (1 / Real.pi) ^ 3 by positivity)
      have hpoly := rankSixWeylPolynomial_le_separable coordinates
      have hconstant : 0 ≤ Real.exp 1 * (1 / Real.pi) ^ 3 := by positivity
      have hsep :
          (Real.exp 1 * (1 / Real.pi) ^ 3) * rankSixWeylPolynomial coordinates *
              Real.exp (-rankSixGeometricGaussianCoefficient *
                ∑ coordinate, coordinates coordinate ^ 2) ≤
            (Real.exp 1 * (1 / Real.pi) ^ 3) *
              (8 * ∏ coordinate, (1 + coordinates coordinate ^ 2) ^ 4) *
              Real.exp (-rankSixGeometricGaussianCoefficient *
                ∑ coordinate, coordinates coordinate ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hconstant) (Real.exp_pos _).le
      have hg : Real.exp (-rankSixGeometricGaussianCoefficient *
            ∑ coordinate, coordinates coordinate ^ 2) =
          ∏ coordinate, Real.exp (-rankSixGeometricGaussianCoefficient *
            coordinates coordinate ^ 2) := by
        rw [← Real.exp_sum, ← Finset.mul_sum]
      calc
        _ ≤ (Real.exp 1 * (1 / Real.pi) ^ 3) *
            rankSixWeylPolynomial coordinates *
            Real.exp (-rankSixGeometricGaussianCoefficient *
              ∑ coordinate, coordinates coordinate ^ 2) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
        _ ≤ _ := hsep
        _ = rankSixGeometricLocalDominating coordinates := by
          unfold rankSixGeometricLocalDominating
            rankSixGeometricCoordinateDominating
          rw [hg]
          rw [show (∏ coordinate : Fin 3,
              ((1 + coordinates coordinate ^ 2) ^ 4 *
                Real.exp (-rankSixGeometricGaussianCoefficient *
                  coordinates coordinate ^ 2))) =
            (∏ coordinate, (1 + coordinates coordinate ^ 2) ^ 4) *
              ∏ coordinate, Real.exp (-rankSixGeometricGaussianCoefficient *
                coordinates coordinate ^ 2) by rw [Finset.prod_mul_distrib]]
          ring
    · exact mul_nonneg (mul_nonneg (by positivity)
        (normalizedRankSixGeometricKernel_nonneg
          (index := index) (coordinates := coordinates)
          ((by norm_num : (0 : ℝ) ≤ 2).trans
            ((cosineScaleMidpoint_gt_two
              (dimension := 3) (by norm_num)).le.trans hd.2))))
        (rankSixEvenMinusScaledWeight_nonneg index coordinates)
  · rw [rankSixGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hd, norm_zero]
    unfold rankSixGeometricLocalDominating rankSixGeometricCoordinateDominating
    positivity

theorem tendsto_integral_rankSixGeometricMinusLocal_zero :
    Tendsto (fun index => ∫ coordinates : Fin 3 → ℝ,
      rankSixGeometricMinusLocalRescaledIntegrand index coordinates)
      atTop (nhds 0) := by
  simpa using tendsto_integral_of_dominated_convergence
    rankSixGeometricLocalDominating
    aestronglyMeasurable_rankSixGeometricMinusLocalRescaled
    integrable_rankSixGeometricLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankSixGeometricMinusLocalRescaled_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankSixGeometricMinusLocalRescaled_zero coordinates)

theorem rankSixGeometricMinusAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    rankSixGeometricMinusAngleLocalIntegrand index
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankSixGeometricMinusLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 6 := by
  by_cases hd : coordinates ∈ positiveLocalScaledDomain 3 index
  · rw [rankSixGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff 3 index coordinates).2 hd),
      rankSixGeometricMinusLocalRescaledIntegrand, Set.indicator_of_mem hd,
      cosineCubeScale_inverseSqrt, rankSixEvenMinusAngleWeight_inverseSqrt]
    unfold normalizedRankSixGeometricKernel
    ring
  · rw [rankSixGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff 3 index coordinates).1 hd),
      rankSixGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hd, zero_div]

theorem stronglyMeasurable_rankSixGeometricMinusAngleLocalIntegrand
    (index : ℕ) :
    StronglyMeasurable (rankSixGeometricMinusAngleLocalIntegrand index) := by
  unfold rankSixGeometricMinusAngleLocalIntegrand
  have hp : Continuous (fun angles : Fin 3 → ℝ =>
      (cosineCubeScale angles / 6) ^ index) :=
    ((continuous_cosineCubeScale 3).div_const 6).pow index
  exact (((continuous_const.mul hp).mul
    ((continuous_cosineVandermondeWeight 3).mul (by
      unfold allMinusAngleWeight
      apply continuous_finsetProd
      intro coordinate _
      fun_prop))).stronglyMeasurable.indicator
    (measurableSet_anglePositiveLocalDomain 3))

theorem rankSixGeometricMinusLocalScalingIntegral_identity (index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixGeometricMinusAngleLocalIntegral index =
      ∫ coordinates : Fin 3 → ℝ,
        rankSixGeometricMinusLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 3
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankSixGeometricMinusAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 3 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 3 _).aemeasurable
      (stronglyMeasurable_rankSixGeometricMinusAngleLocalIntegrand
        index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have ht : (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 3)).toReal =
      Real.sqrt (index + 1 : ℝ) ^ 3 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [ht, smul_eq_mul] at hmap
  unfold rankSixGeometricMinusAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 3 → ℝ =>
      rankSixGeometricMinusAngleLocalIntegrand index
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates =>
        rankSixGeometricMinusLocalRescaledIntegrand index coordinates /
          (index + 1 : ℝ) ^ 6 by
    funext coordinates
    exact rankSixGeometricMinusAngleLocalIntegrand_inverseSqrt index coordinates]
    at hmap
  rw [integral_div] at hmap
  have hn : (index + 1 : ℝ) ^ 6 ≠ 0 := by positivity
  field_simp [hn] at hmap ⊢
  exact hmap

theorem tendsto_rankSixGeometricMinusAngleLocalIntegral_zero :
    Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * rankSixGeometricMinusAngleLocalIntegral index)
      atTop (nhds 0) := by
  rw [show (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * rankSixGeometricMinusAngleLocalIntegral index) =
    fun index => ∫ coordinates : Fin 3 → ℝ,
      rankSixGeometricMinusLocalRescaledIntegrand index coordinates by
    funext index
    exact rankSixGeometricMinusLocalScalingIntegral_identity index]
  exact tendsto_integral_rankSixGeometricMinusLocal_zero

noncomputable def rankSixGeometricFullIntegrand
    (index : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  (1 / Real.pi) ^ 3 * (cosineCubeScale angles / 6) ^ index *
    evenWeylAngleWeight 3 angles

noncomputable def rankSixGeometricFullIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ, rankSixGeometricFullIntegrand index angles
    ∂cosineCubeProductMeasure 3

noncomputable def rankSixGeometricNegativeIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ,
    (negativeSpectralLocalDomain 3).indicator
      (rankSixGeometricFullIntegrand index) angles
    ∂cosineCubeProductMeasure 3

noncomputable def rankSixGeometricMiddleIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ,
    (middleOpenSpectralDomain 3).indicator
      (rankSixGeometricFullIntegrand index) angles
    ∂cosineCubeProductMeasure 3

noncomputable def rankSixGeometricMinusPositiveIntegrand
    (index : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  (positiveSpectralLocalDomain 3).indicator (fun angles =>
    (1 / Real.pi) ^ 3 * (cosineCubeScale angles / 6) ^ index *
      (cosineVandermondeWeight 3 angles * allMinusAngleWeight 3 angles)) angles

theorem rankSixGeometricMinusPositiveIntegral_eq_angleLocal (index : ℕ) :
    (∫ angles : Fin 3 → ℝ,
      rankSixGeometricMinusPositiveIntegrand index angles
      ∂cosineCubeProductMeasure 3) =
      rankSixGeometricMinusAngleLocalIntegral index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin 3 => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube 3 by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube 3) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold rankSixGeometricMinusAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hc : angles ∈ anglePositiveCube 3
  · by_cases hl : angles ∈ positiveSpectralLocalDomain 3
    · have hd : angles ∈ anglePositiveLocalDomain 3 := ⟨hc, hl⟩
      rw [Set.indicator_of_mem hc, rankSixGeometricMinusPositiveIntegrand,
        Set.indicator_of_mem hl, rankSixGeometricMinusAngleLocalIntegrand,
        Set.indicator_of_mem hd]
    · rw [Set.indicator_of_mem hc, rankSixGeometricMinusPositiveIntegrand,
        Set.indicator_of_notMem hl, rankSixGeometricMinusAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hl h.2)]
  · rw [Set.indicator_of_notMem hc, rankSixGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hc h.1)]

theorem rankSixGeometricNegativeIntegral_eq (index : ℕ) :
    rankSixGeometricNegativeIntegral index =
      (-1 : ℝ) ^ index * rankSixGeometricMinusAngleLocalIntegral index := by
  unfold rankSixGeometricNegativeIntegral
  rw [← (measurePreserving_angleReflectionEquiv 3).integral_comp'
    ((negativeSpectralLocalDomain 3).indicator
      (rankSixGeometricFullIntegrand index))]
  rw [show (fun angles : Fin 3 → ℝ =>
      (negativeSpectralLocalDomain 3).indicator
        (rankSixGeometricFullIntegrand index) (angleReflectionEquiv 3 angles)) =
      fun angles => (-1 : ℝ) ^ index *
        rankSixGeometricMinusPositiveIntegrand index angles by
    funext angles
    have hs := cosineCubeScale_angleReflection 3 angles
    by_cases hd : angles ∈ positiveSpectralLocalDomain 3
    · have hr : angleReflectionEquiv 3 angles ∈ negativeSpectralLocalDomain 3 := by
        change cosineCubeScale (angleReflectionEquiv 3 angles) ≤
          -cosineScaleMidpoint 3
        rw [hs]
        exact neg_le_neg hd
      rw [Set.indicator_of_mem hr, rankSixGeometricMinusPositiveIntegrand,
        Set.indicator_of_mem hd, rankSixGeometricFullIntegrand, hs,
        evenWeylAngleWeight_reflection, neg_div, neg_pow]
      ring
    · have hr : angleReflectionEquiv 3 angles ∉ negativeSpectralLocalDomain 3 := by
        intro hr
        apply hd
        change cosineCubeScale (angleReflectionEquiv 3 angles) ≤
          -cosineScaleMidpoint 3 at hr
        rw [hs] at hr
        change cosineScaleMidpoint 3 ≤ cosineCubeScale angles
        linarith
      rw [Set.indicator_of_notMem hr, rankSixGeometricMinusPositiveIntegrand,
        Set.indicator_of_notMem hd, mul_zero],
    integral_const_mul, rankSixGeometricMinusPositiveIntegral_eq_angleLocal]

theorem tendsto_rankSixGeometricNegativeIntegral_zero :
    Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * rankSixGeometricNegativeIntegral index)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun index : ℕ => ‖Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * rankSixGeometricMinusAngleLocalIntegral index‖)
  · intro index
    rw [rankSixGeometricNegativeIntegral_eq]
    simp [norm_mul]
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_rankSixGeometricMinusAngleLocalIntegral_zero

noncomputable def rankSixGeometricMiddleRatio : ℝ := 2 / 3

theorem rankSixGeometricMiddleRatio_pos : 0 < rankSixGeometricMiddleRatio := by
  norm_num [rankSixGeometricMiddleRatio]

theorem tendsto_rankSixGeometricMiddlePolynomial :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 8 * rankSixGeometricMiddleRatio ^ index)
      atTop (nhds 0) := by
  have hbase : Tendsto (fun index : ℕ =>
      (index : ℝ) ^ 8 * rankSixGeometricMiddleRatio ^ index)
      atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one 8
      (by norm_num [rankSixGeometricMiddleRatio])
  have hs := hbase.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 8 * rankSixGeometricMiddleRatio ^ index) =
      fun index : ℕ => ((index + 1 : ℝ) ^ 8 *
        rankSixGeometricMiddleRatio ^ (index + 1)) *
          rankSixGeometricMiddleRatio⁻¹ by
    funext index
    field_simp [rankSixGeometricMiddleRatio_pos.ne']
    exact (pow_succ _ _).symm]
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, zero_mul] using
    hs.mul_const rankSixGeometricMiddleRatio⁻¹

theorem tendsto_rankSixGeometricMiddleIntegral_zero :
    Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * rankSixGeometricMiddleIntegral index)
      atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) ^ 3 * 512) *
    (cosineCubeProductMeasure 3).real Set.univ
  have hb : ∀ index, ‖rankSixGeometricMiddleIntegral index‖ ≤
      (((1 / Real.pi) ^ 3 * 512) * rankSixGeometricMiddleRatio ^ index) *
        (cosineCubeProductMeasure 3).real Set.univ := by
    intro index
    unfold rankSixGeometricMiddleIntegral
    apply norm_integral_le_of_norm_le_const
    filter_upwards with angles
    by_cases hm : angles ∈ middleOpenSpectralDomain 3
    · rw [Set.indicator_of_mem hm, rankSixGeometricFullIntegrand,
        Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
        abs_of_nonneg (evenWeylAngleWeight_nonneg 3 angles)]
      have hs : |cosineCubeScale angles| ≤ 4 := by
        change -cosineScaleMidpoint 3 < cosineCubeScale angles ∧
          cosineCubeScale angles < cosineScaleMidpoint 3 at hm
        norm_num [cosineScaleMidpoint] at hm ⊢
        exact abs_le.2 ⟨hm.1.le, hm.2.le⟩
      have hr : |cosineCubeScale angles / 6| ≤ rankSixGeometricMiddleRatio := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
        unfold rankSixGeometricMiddleRatio
        linarith
      have hp := pow_le_pow_left₀ (abs_nonneg _) hr index
      have hw := evenWeylAngleWeight_three_le_512 angles
      have ht : (1 / Real.pi) ^ 3 * |cosineCubeScale angles / 6| ^ index *
          evenWeylAngleWeight 3 angles ≤
          (1 / Real.pi) ^ 3 * rankSixGeometricMiddleRatio ^ index * 512 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hp
          (pow_nonneg (by positivity) _)) hw
          (evenWeylAngleWeight_nonneg 3 angles)
          (mul_nonneg (pow_nonneg (by positivity) _)
            (pow_nonneg rankSixGeometricMiddleRatio_pos.le _))
      calc
        (1 / Real.pi) ^ 3 * |(cosineCubeScale angles / 6) ^ index| *
            evenWeylAngleWeight 3 angles =
          (1 / Real.pi) ^ 3 * |cosineCubeScale angles / 6| ^ index *
            evenWeylAngleWeight 3 angles := by rw [abs_pow]
        _ ≤ _ := ht
        _ = ((1 / Real.pi) ^ 3 * 512) *
            rankSixGeometricMiddleRatio ^ index := by ring
    · rw [Set.indicator_of_notMem hm, norm_zero]
      exact mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _) (by norm_num))
        (pow_nonneg rankSixGeometricMiddleRatio_pos.le _)
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 8 * rankSixGeometricMiddleRatio ^ index) * constant)
  · intro index
    rw [norm_mul, norm_mul,
      Real.norm_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) 3),
      Real.norm_of_nonneg (pow_nonneg
        (show 0 ≤ (index + 1 : ℝ) by positivity) 6)]
    have h1 := mul_le_mul_of_nonneg_right (rankSixScaleFactor_le_power_eight index)
      (norm_nonneg (rankSixGeometricMiddleIntegral index))
    have h2 := mul_le_mul_of_nonneg_left (hb index)
      (pow_nonneg (show 0 ≤ (index + 1 : ℝ) by positivity) 8)
    exact h1.trans (h2.trans_eq (by ring))
  · simpa using tendsto_rankSixGeometricMiddlePolynomial.mul_const constant

theorem rankSixGeometricFullIntegral_eq_moment (index : ℕ) :
    rankSixGeometricFullIntegral index =
      (1 / Real.pi) ^ 3 * (evenWeylGeometricMoment 3 index / 6 ^ index) := by
  unfold rankSixGeometricFullIntegral rankSixGeometricFullIntegrand
    evenWeylGeometricMoment weightedCosineCubeMoment
    weightedCosineCubePowerIntegrand
  rw [show (fun angles : Fin 3 → ℝ =>
      (1 / Real.pi) ^ 3 * (cosineCubeScale angles / 6) ^ index *
        evenWeylAngleWeight 3 angles) =
      fun angles => ((1 / Real.pi) ^ 3 / 6 ^ index) *
        (cosineCubeScale angles ^ index * evenWeylAngleWeight 3 angles) by
    funext angles
    rw [div_pow]
    ring_nf
    rw [one_div_pow]
    have hi : 1 / ((6 : ℝ) ^ index) = ((6 : ℝ)⁻¹) ^ index := by
      simpa only [one_div] using (inv_pow (6 : ℝ) index).symm
    rw [hi], integral_const_mul]
  ring

theorem tendsto_rankSixTableauNormalizedIntegralConstant :
    Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * ((heightSixTableauCount index : ℝ) / 6 ^ index))
      atTop (nhds ((32 / 3 : ℝ) *
        (∫ coordinates : Fin 3 → ℝ,
          rankSixGeometricLocalLimitIntegrand coordinates))) := by
  have hfull : Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * rankSixGeometricFullIntegral index)
      atTop (nhds (∫ coordinates : Fin 3 → ℝ,
        rankSixGeometricLocalLimitIntegrand coordinates)) := by
    have hint : ∀ index, rankSixGeometricFullIntegral index =
        rankSixGeometricAngleLocalIntegral index +
          (rankSixGeometricNegativeIntegral index +
            rankSixGeometricMiddleIntegral index) := by
      intro index
      unfold rankSixGeometricFullIntegral rankSixGeometricNegativeIntegral
        rankSixGeometricMiddleIntegral
      have hc : Continuous (rankSixGeometricFullIntegrand index) := by
        unfold rankSixGeometricFullIntegrand
        have hp : Continuous (fun angles : Fin 3 → ℝ =>
            (cosineCubeScale angles / 6) ^ index) :=
          ((continuous_cosineCubeScale 3).div_const 6).pow index
        exact (continuous_const.mul hp).mul (continuous_evenWeylAngleWeight 3)
      have hi := integrable_continuous_cosineCube hc
      have hp := hi.indicator (measurableSet_positiveSpectralLocalDomain 3)
      have hn := hi.indicator (measurableSet_negativeSpectralLocalDomain 3)
      have hm := hi.indicator (measurableSet_middleOpenSpectralDomain 3)
      rw [show (fun angles : Fin 3 → ℝ => rankSixGeometricFullIntegrand index angles) =
        fun angles =>
          (positiveSpectralLocalDomain 3).indicator
              (rankSixGeometricFullIntegrand index) angles +
            ((negativeSpectralLocalDomain 3).indicator
                (rankSixGeometricFullIntegrand index) angles +
              (middleOpenSpectralDomain 3).indicator
                (rankSixGeometricFullIntegrand index) angles) by
        funext angles
        by_cases hpos : angles ∈ positiveSpectralLocalDomain 3
        · have hneg : angles ∉ negativeSpectralLocalDomain 3 := by
            intro hneg
            have hmid : 0 < cosineScaleMidpoint 3 := by
              norm_num [cosineScaleMidpoint]
            change cosineScaleMidpoint 3 ≤ cosineCubeScale angles at hpos
            change cosineCubeScale angles ≤ -cosineScaleMidpoint 3 at hneg
            linarith
          have hmid : angles ∉ middleOpenSpectralDomain 3 := fun h =>
            (not_lt_of_ge hpos) h.2
          rw [Set.indicator_of_mem hpos, Set.indicator_of_notMem hneg,
            Set.indicator_of_notMem hmid, zero_add, add_zero]
        · have hplt : cosineCubeScale angles < cosineScaleMidpoint 3 :=
            lt_of_not_ge hpos
          by_cases hneg : angles ∈ negativeSpectralLocalDomain 3
          · have hmid : angles ∉ middleOpenSpectralDomain 3 := fun h =>
              (not_lt_of_ge hneg) h.1
            rw [Set.indicator_of_notMem hpos, Set.indicator_of_mem hneg,
              Set.indicator_of_notMem hmid, zero_add, add_zero]
          · have hnlt : -cosineScaleMidpoint 3 < cosineCubeScale angles :=
              lt_of_not_ge hneg
            have hmid : angles ∈ middleOpenSpectralDomain 3 := ⟨hnlt, hplt⟩
            rw [Set.indicator_of_notMem hpos, Set.indicator_of_notMem hneg,
              Set.indicator_of_mem hmid]
            simp]
      have hpositive :
          (∫ angles : Fin 3 → ℝ,
            (positiveSpectralLocalDomain 3).indicator
              (rankSixGeometricFullIntegrand index) angles
            ∂cosineCubeProductMeasure 3) =
            rankSixGeometricAngleLocalIntegral index := by
        rw [cosineCubeProductMeasure_eq_restrict]
        rw [show (Set.univ.pi fun _ : Fin 3 => Set.Ioc (0 : ℝ) Real.pi) =
          anglePositiveCube 3 by rfl]
        rw [← integral_indicator
          (show MeasurableSet (anglePositiveCube 3) by
            unfold anglePositiveCube
            exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
        unfold rankSixGeometricAngleLocalIntegral
        apply integral_congr_ae
        filter_upwards with angles
        by_cases hcube : angles ∈ anglePositiveCube 3
        · by_cases hlocal : angles ∈ positiveSpectralLocalDomain 3
          · have hd : angles ∈ anglePositiveLocalDomain 3 := ⟨hcube, hlocal⟩
            rw [Set.indicator_of_mem hcube, Set.indicator_of_mem hlocal,
              rankSixGeometricAngleLocalIntegrand, Set.indicator_of_mem hd]
            rfl
          · rw [Set.indicator_of_mem hcube, Set.indicator_of_notMem hlocal,
              rankSixGeometricAngleLocalIntegrand,
              Set.indicator_of_notMem (fun h => hlocal h.2)]
        · rw [Set.indicator_of_notMem hcube,
            rankSixGeometricAngleLocalIntegrand,
            Set.indicator_of_notMem (fun h => hcube h.1)]
      calc
        (∫ angles : Fin 3 → ℝ,
            (positiveSpectralLocalDomain 3).indicator
                (rankSixGeometricFullIntegrand index) angles +
              ((negativeSpectralLocalDomain 3).indicator
                  (rankSixGeometricFullIntegrand index) angles +
                (middleOpenSpectralDomain 3).indicator
                  (rankSixGeometricFullIntegrand index) angles)
            ∂cosineCubeProductMeasure 3) =
          (∫ angles, (positiveSpectralLocalDomain 3).indicator
              (rankSixGeometricFullIntegrand index) angles
            ∂cosineCubeProductMeasure 3) +
          ∫ angles,
            (negativeSpectralLocalDomain 3).indicator
                (rankSixGeometricFullIntegrand index) angles +
              (middleOpenSpectralDomain 3).indicator
                (rankSixGeometricFullIntegrand index) angles
            ∂cosineCubeProductMeasure 3 := integral_add hp (hn.add hm)
        _ = (∫ angles, (positiveSpectralLocalDomain 3).indicator
              (rankSixGeometricFullIntegrand index) angles
            ∂cosineCubeProductMeasure 3) +
          ((∫ angles, (negativeSpectralLocalDomain 3).indicator
              (rankSixGeometricFullIntegrand index) angles
            ∂cosineCubeProductMeasure 3) +
           ∫ angles, (middleOpenSpectralDomain 3).indicator
              (rankSixGeometricFullIntegrand index) angles
            ∂cosineCubeProductMeasure 3) := by rw [integral_add hn hm]
        _ = _ := by rw [hpositive]
    rw [show (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
        (index + 1 : ℝ) ^ 6 * rankSixGeometricFullIntegral index) =
      fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
            rankSixGeometricAngleLocalIntegral index +
          (Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
              rankSixGeometricNegativeIntegral index +
            Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
              rankSixGeometricMiddleIntegral index) by
        funext index
        rw [hint]
        ring]
    simpa using tendsto_rankSixGeometricAngleLocalIntegral.add
      (tendsto_rankSixGeometricNegativeIntegral_zero.add
        tendsto_rankSixGeometricMiddleIntegral_zero)
  have hs := hfull.const_mul (32 / 3 : ℝ)
  apply hs.congr'
  filter_upwards with index
  rw [rankSixGeometricFullIntegral_eq_moment,
    heightSixTableauCount_eq_normalized_evenWeylMoment]
  field_simp [Real.pi_ne_zero]

end FibonacciRibbonKernel
