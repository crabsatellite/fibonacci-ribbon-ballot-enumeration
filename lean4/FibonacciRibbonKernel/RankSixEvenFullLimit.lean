import FibonacciRibbonKernel.RankSixEvenLocalDCT

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankSixEvenMinusScaledWeight
    (index : ℕ) (coordinates : Fin 3 → ℝ) : ℝ :=
  scaledCosineVandermondeWeight 3 index coordinates *
    allMinusScaledWeight 3 index coordinates

noncomputable def rankSixEvenMinusLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 3 → ℝ) : ℝ :=
  (positiveLocalScaledDomain 3 index).indicator (fun coordinates =>
    (1 / Real.pi) ^ 3 * normalizedFibonacciCosineKernel coordinates index *
      rankSixEvenMinusScaledWeight index coordinates) coordinates

noncomputable def rankSixEvenMinusAngleLocalIntegrand
    (index : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  (anglePositiveLocalDomain 3).indicator (fun angles =>
    (1 / Real.pi) ^ 3 *
      (fibonacciScaleKernel (cosineCubeScale angles) index /
        (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)) *
      (cosineVandermondeWeight 3 angles * allMinusAngleWeight 3 angles)) angles

noncomputable def rankSixEvenMinusAngleLocalIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ, rankSixEvenMinusAngleLocalIntegrand index angles

theorem tendsto_rankSixEvenMinusScaledWeight_zero
    (coordinates : Fin 3 → ℝ) :
    Tendsto (fun index => rankSixEvenMinusScaledWeight index coordinates)
      atTop (nhds 0) := by
  unfold rankSixEvenMinusScaledWeight
  simpa using (tendsto_scaledCosineVandermondeWeight 3 coordinates).mul
    (tendsto_allMinusScaledWeight (dimension := 3) (by norm_num) coordinates)

theorem tendsto_rankSixEvenMinusLocalRescaled_zero
    (coordinates : Fin 3 → ℝ) :
    Tendsto (fun index =>
      rankSixEvenMinusLocalRescaledIntegrand index coordinates)
      atTop (nhds 0) := by
  by_cases ho : coordinates ∈ positiveOrthant
  · have hl := eventually_mem_positiveLocalScaledDomain
      (dimension := 3) (by norm_num) coordinates ho
    have hk := tendsto_normalizedFibonacciCosineKernel
      (dimension := 3) (by norm_num) coordinates
    have hw := tendsto_rankSixEvenMinusScaledWeight_zero coordinates
    have hc : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 3)
        atTop (nhds ((1 / Real.pi) ^ 3)) := tendsto_const_nhds
    have hp := (hc.mul hk).mul hw
    simpa only [mul_zero] using hp.congr' (by
      filter_upwards [hl] with index hi
      rw [rankSixEvenMinusLocalRescaledIntegrand, Set.indicator_of_mem hi])
  · have hn : ∃ coordinate : Fin 3, coordinates coordinate ≤ 0 := by
      by_contra h
      push Not at h
      exact ho fun coordinate _ => h coordinate
    obtain ⟨coordinate, hc⟩ := hn
    have hout : ∀ index, coordinates ∉ positiveLocalScaledDomain 3 index := by
      intro index hd
      linarith [(hd.1 coordinate (Set.mem_univ coordinate)).1]
    rw [show (fun index : ℕ =>
        rankSixEvenMinusLocalRescaledIntegrand index coordinates) = fun _ => 0 by
      funext index
      rw [rankSixEvenMinusLocalRescaledIntegrand,
        Set.indicator_of_notMem (hout index)]]
    exact tendsto_const_nhds

theorem rankSixEvenMinusScaledWeight_nonneg
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    0 ≤ rankSixEvenMinusScaledWeight index coordinates := by
  unfold rankSixEvenMinusScaledWeight scaledCosineVandermondeWeight
  exact mul_nonneg (by positivity) (allMinusScaledWeight_nonneg 3 index coordinates)

set_option maxHeartbeats 500000 in
theorem rankSixEvenMinusScaledWeight_le_polynomial
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    rankSixEvenMinusScaledWeight index coordinates ≤ rankSixWeylPolynomial coordinates := by
  unfold rankSixEvenMinusScaledWeight rankSixWeylPolynomial
  rw [scaledCosineVandermondeWeight_three]
  have h01 := abs_scaled_cosine_difference_le index (coordinates 1) (coordinates 0)
  have h02 := abs_scaled_cosine_difference_le index (coordinates 2) (coordinates 0)
  have h12 := abs_scaled_cosine_difference_le index (coordinates 2) (coordinates 1)
  have h01s := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 h01
  have h02s := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 h02
  have h12s := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 h12
  rw [sq_abs] at h01s h02s h12s
  have hminus := allMinusScaledWeight_le_two_pow 3 index coordinates
  norm_num at hminus
  have hminusNon := allMinusScaledWeight_nonneg 3 index coordinates
  have h01n : 0 ≤ ((coordinates 1 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2 := by positivity
  have h02n : 0 ≤ ((coordinates 2 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2 := by positivity
  have h12n : 0 ≤ ((coordinates 2 ^ 2 + coordinates 1 ^ 2) / 2) ^ 2 := by positivity
  have h02lower : 0 ≤ ((index + 1 : ℝ) *
      (Real.cos (coordinates 2 / Real.sqrt (index + 1 : ℝ)) -
        Real.cos (coordinates 0 / Real.sqrt (index + 1 : ℝ)))) ^ 2 := by positivity
  have h12lower : 0 ≤ ((index + 1 : ℝ) *
      (Real.cos (coordinates 2 / Real.sqrt (index + 1 : ℝ)) -
        Real.cos (coordinates 1 / Real.sqrt (index + 1 : ℝ)))) ^ 2 := by positivity
  have hpairs := mul_le_mul
    (mul_le_mul h01s h02s h02lower h01n)
    h12s h12lower (mul_nonneg h01n h02n)
  have hpolyNon : 0 ≤
      ((coordinates 1 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2 *
        ((coordinates 2 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2 *
          ((coordinates 2 ^ 2 + coordinates 1 ^ 2) / 2) ^ 2 := by positivity
  have ht := mul_le_mul hpairs hminus hminusNon hpolyNon
  simpa [add_comm, mul_assoc, mul_comm, mul_left_comm] using ht

theorem aestronglyMeasurable_rankSixEvenMinusLocalRescaled (index : ℕ) :
    AEStronglyMeasurable (rankSixEvenMinusLocalRescaledIntegrand index) := by
  unfold rankSixEvenMinusLocalRescaledIntegrand
  exact (((continuous_const.mul
    (continuous_normalizedFibonacciCosineKernel 3 index (by norm_num))).mul
      ((continuous_scaledCosineVandermondeWeight 3 index).mul
        (continuous_allMinusScaledWeight 3 index))).stronglyMeasurable.indicator
      (measurableSet_positiveLocalScaledDomain 3 index)).aestronglyMeasurable

theorem norm_rankSixEvenMinusLocalRescaled_le
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    ‖rankSixEvenMinusLocalRescaledIntegrand index coordinates‖ ≤
      rankSixLocalDominating coordinates := by
  by_cases hd : coordinates ∈ positiveLocalScaledDomain 3 index
  · rw [rankSixEvenMinusLocalRescaledIntegrand, Set.indicator_of_mem hd,
      Real.norm_eq_abs, abs_of_nonneg]
    · have hcoord : ∀ coordinate,
          |coordinates coordinate| ≤ Real.pi * Real.sqrt (index + 1 : ℝ) := by
        intro coordinate
        have hm := hd.1 coordinate (Set.mem_univ coordinate)
        rw [abs_of_pos hm.1]
        exact hm.2
      have hk := normalizedFibonacciCosineKernel_le_local_gaussian
        (dimension := 3) (by norm_num) coordinates hcoord hd.2
      rw [show Real.sqrt ((2 * (3 : ℕ) : ℝ) ^ 2 - 4) =
        Real.sqrt (32 : ℝ) by norm_num] at hk
      have hcoef : allPlusGaussianCoefficient 3 =
          4 / (Real.pi ^ 2 * Real.sqrt (32 : ℝ)) := by
        norm_num [allPlusGaussianCoefficient]
      rw [← hcoef] at hk
      have hw := rankSixEvenMinusScaledWeight_le_polynomial index coordinates
      have hkn := normalizedFibonacciCosineKernel_nonneg
        (dimension := 3) (by norm_num) coordinates
        ((cosineScaleMidpoint_gt_two (by norm_num)).trans_le hd.2)
      have hwn := rankSixEvenMinusScaledWeight_nonneg index coordinates
      have hp := mul_le_mul hk hw hwn (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hp
        (show 0 ≤ (1 / Real.pi) ^ 3 by positivity)
      have hpoly := rankSixWeylPolynomial_le_separable coordinates
      have hconstant : 0 ≤ (1 / Real.pi) ^ 3 *
          (Real.sqrt (32 : ℝ) / Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4)) := by
        unfold cosineScaleMidpoint
        positivity
      have hsep :
          ((1 / Real.pi) ^ 3 *
            (Real.sqrt 32 / Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4))) *
              rankSixWeylPolynomial coordinates *
              Real.exp (-allPlusGaussianCoefficient 3 *
                ∑ coordinate, coordinates coordinate ^ 2) ≤
          ((1 / Real.pi) ^ 3 *
            (Real.sqrt 32 / Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4))) *
              (8 * ∏ coordinate, (1 + coordinates coordinate ^ 2) ^ 4) *
              Real.exp (-allPlusGaussianCoefficient 3 *
                ∑ coordinate, coordinates coordinate ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hconstant) (Real.exp_pos _).le
      have hgauss : Real.exp (-allPlusGaussianCoefficient 3 *
            ∑ coordinate, coordinates coordinate ^ 2) =
          ∏ coordinate, Real.exp (-allPlusGaussianCoefficient 3 *
            coordinates coordinate ^ 2) := by
        rw [← Real.exp_sum, ← Finset.mul_sum]
      calc
        (1 / Real.pi) ^ 3 * normalizedFibonacciCosineKernel coordinates index *
            rankSixEvenMinusScaledWeight index coordinates ≤
          ((1 / Real.pi) ^ 3 *
            (Real.sqrt 32 / Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4))) *
              rankSixWeylPolynomial coordinates *
              Real.exp (-allPlusGaussianCoefficient 3 *
                ∑ coordinate, coordinates coordinate ^ 2) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
        _ ≤ _ := hsep
        _ = rankSixLocalDominating coordinates := by
          unfold rankSixLocalDominating rankSixCoordinateDominating
          rw [hgauss]
          rw [show (∏ coordinate : Fin 3,
              ((1 + coordinates coordinate ^ 2) ^ 4 *
                Real.exp (-allPlusGaussianCoefficient 3 * coordinates coordinate ^ 2))) =
            (∏ coordinate, (1 + coordinates coordinate ^ 2) ^ 4) *
              ∏ coordinate, Real.exp (-allPlusGaussianCoefficient 3 *
                coordinates coordinate ^ 2) by rw [Finset.prod_mul_distrib]]
          ring
    · exact mul_nonneg (mul_nonneg (by positivity)
        (normalizedFibonacciCosineKernel_nonneg
          (dimension := 3) (by norm_num) coordinates
          ((cosineScaleMidpoint_gt_two (by norm_num)).trans_le hd.2)))
        (rankSixEvenMinusScaledWeight_nonneg index coordinates)
  · rw [rankSixEvenMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hd, norm_zero]
    unfold rankSixLocalDominating rankSixCoordinateDominating cosineScaleMidpoint
    positivity

theorem tendsto_integral_rankSixEvenMinusLocal_zero :
    Tendsto (fun index => ∫ coordinates : Fin 3 → ℝ,
      rankSixEvenMinusLocalRescaledIntegrand index coordinates)
      atTop (nhds 0) := by
  simpa using tendsto_integral_of_dominated_convergence rankSixLocalDominating
    aestronglyMeasurable_rankSixEvenMinusLocalRescaled
    integrable_rankSixLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankSixEvenMinusLocalRescaled_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankSixEvenMinusLocalRescaled_zero coordinates)

theorem rankSixEvenMinusAngleWeight_inverseSqrt
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    cosineVandermondeWeight 3
          (coordinateScalarLinearMap 3
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) *
        allMinusAngleWeight 3
          (coordinateScalarLinearMap 3
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankSixEvenMinusScaledWeight index coordinates / (index + 1 : ℝ) ^ 6 := by
  have hs := scaledCosineVandermondeWeight_eq 3 index coordinates
  rw [weylPairScalingExponent_eq] at hs
  norm_num at hs
  unfold rankSixEvenMinusScaledWeight allMinusScaledWeight allMinusAngleWeight
  rw [coordinateScalarLinearMap_apply]
  simp only [one_div]
  have hn : (index + 1 : ℝ) ^ 6 ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  rw [hs]
  ring

theorem stronglyMeasurable_rankSixEvenMinusAngleLocalIntegrand (index : ℕ) :
    StronglyMeasurable (rankSixEvenMinusAngleLocalIntegrand index) := by
  unfold rankSixEvenMinusAngleLocalIntegrand
  exact (((continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale 3)).div_const _)).mul
      ((continuous_cosineVandermondeWeight 3).mul (by
        unfold allMinusAngleWeight
        apply continuous_finsetProd
        intro coordinate _
        fun_prop))).stronglyMeasurable.indicator
      (measurableSet_anglePositiveLocalDomain 3))

theorem rankSixEvenMinusAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    rankSixEvenMinusAngleLocalIntegrand index
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankSixEvenMinusLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 6 := by
  by_cases hd : coordinates ∈ positiveLocalScaledDomain 3 index
  · rw [rankSixEvenMinusAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff 3 index coordinates).2 hd),
      rankSixEvenMinusLocalRescaledIntegrand, Set.indicator_of_mem hd,
      cosineCubeScale_inverseSqrt, rankSixEvenMinusAngleWeight_inverseSqrt]
    unfold normalizedFibonacciCosineKernel
    norm_num
    ring
  · rw [rankSixEvenMinusAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff 3 index coordinates).1 hd),
      rankSixEvenMinusLocalRescaledIntegrand, Set.indicator_of_notMem hd, zero_div]

theorem rankSixEvenMinusLocalScalingIntegral_identity (index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenMinusAngleLocalIntegral index =
      ∫ coordinates : Fin 3 → ℝ,
        rankSixEvenMinusLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 3
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankSixEvenMinusAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 3 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 3 _).aemeasurable
      (stronglyMeasurable_rankSixEvenMinusAngleLocalIntegrand index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have ht : (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 3)).toReal =
      Real.sqrt (index + 1 : ℝ) ^ 3 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [ht, smul_eq_mul] at hmap
  unfold rankSixEvenMinusAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 3 → ℝ =>
      rankSixEvenMinusAngleLocalIntegrand index
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates => rankSixEvenMinusLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 6 by
    funext coordinates
    exact rankSixEvenMinusAngleLocalIntegrand_inverseSqrt index coordinates] at hmap
  rw [integral_div] at hmap
  have hn : (index + 1 : ℝ) ^ 6 ≠ 0 := by positivity
  field_simp [hn] at hmap ⊢
  exact hmap

theorem tendsto_rankSixEvenMinusAngleLocalIntegral_zero :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenMinusAngleLocalIntegral index)
      atTop (nhds 0) := by
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenMinusAngleLocalIntegral index) =
      fun index => ∫ coordinates : Fin 3 → ℝ,
        rankSixEvenMinusLocalRescaledIntegrand index coordinates by
    funext index
    exact rankSixEvenMinusLocalScalingIntegral_identity index]
  exact tendsto_integral_rankSixEvenMinusLocal_zero

noncomputable def rankSixEvenFullNormalizedIntegrand
    (index : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  (1 / Real.pi) ^ 3 *
    (fibonacciScaleKernel (cosineCubeScale angles) index /
      (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)) *
    evenWeylAngleWeight 3 angles

noncomputable def rankSixEvenFullNormalizedIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ, rankSixEvenFullNormalizedIntegrand index angles
    ∂cosineCubeProductMeasure 3

noncomputable def rankSixEvenNegativeIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ,
    (negativeSpectralLocalDomain 3).indicator
      (rankSixEvenFullNormalizedIntegrand index) angles
    ∂cosineCubeProductMeasure 3

noncomputable def rankSixEvenMiddleIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ,
    (middleOpenSpectralDomain 3).indicator
      (rankSixEvenFullNormalizedIntegrand index) angles
    ∂cosineCubeProductMeasure 3

theorem cosineVandermondeWeight_reflection
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    cosineVandermondeWeight dimension (angleReflectionEquiv dimension angles) =
      cosineVandermondeWeight dimension angles := by
  unfold cosineVandermondeWeight
  apply Finset.prod_congr rfl
  intro upper _
  apply Finset.prod_congr rfl
  intro lower _
  simp only [angleReflectionEquiv_apply, Real.cos_pi_sub]
  ring

theorem evenWeylAngleWeight_reflection
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    evenWeylAngleWeight dimension (angleReflectionEquiv dimension angles) =
      cosineVandermondeWeight dimension angles *
        allMinusAngleWeight dimension angles := by
  unfold evenWeylAngleWeight allMinusAngleWeight
  rw [cosineVandermondeWeight_reflection]
  congr 1
  apply Finset.prod_congr rfl
  intro coordinate _
  rw [angleReflectionEquiv_apply, Real.cos_pi_sub]
  ring

noncomputable def rankSixEvenMinusPositiveIntegrand
    (index : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  (positiveSpectralLocalDomain 3).indicator (fun angles =>
    (1 / Real.pi) ^ 3 *
      (fibonacciScaleKernel (cosineCubeScale angles) index /
        (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)) *
      (cosineVandermondeWeight 3 angles * allMinusAngleWeight 3 angles)) angles

theorem rankSixEvenMinusPositiveIntegral_eq_angleLocal (index : ℕ) :
    (∫ angles : Fin 3 → ℝ, rankSixEvenMinusPositiveIntegrand index angles
      ∂cosineCubeProductMeasure 3) = rankSixEvenMinusAngleLocalIntegral index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin 3 => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube 3 by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube 3) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold rankSixEvenMinusAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hc : angles ∈ anglePositiveCube 3
  · by_cases hl : angles ∈ positiveSpectralLocalDomain 3
    · have hd : angles ∈ anglePositiveLocalDomain 3 := ⟨hc, hl⟩
      rw [Set.indicator_of_mem hc, rankSixEvenMinusPositiveIntegrand,
        Set.indicator_of_mem hl, rankSixEvenMinusAngleLocalIntegrand,
        Set.indicator_of_mem hd]
    · rw [Set.indicator_of_mem hc, rankSixEvenMinusPositiveIntegrand,
        Set.indicator_of_notMem hl, rankSixEvenMinusAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hl h.2)]
  · rw [Set.indicator_of_notMem hc, rankSixEvenMinusAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hc h.1)]

theorem rankSixEvenNegativeIntegral_eq (index : ℕ) :
    rankSixEvenNegativeIntegral index =
      (-1 : ℝ) ^ index * rankSixEvenMinusAngleLocalIntegral index := by
  unfold rankSixEvenNegativeIntegral
  rw [← (measurePreserving_angleReflectionEquiv 3).integral_comp'
    ((negativeSpectralLocalDomain 3).indicator
      (rankSixEvenFullNormalizedIntegrand index))]
  rw [show (fun angles : Fin 3 → ℝ =>
      (negativeSpectralLocalDomain 3).indicator
        (rankSixEvenFullNormalizedIntegrand index)
        (angleReflectionEquiv 3 angles)) =
      fun angles => (-1 : ℝ) ^ index *
        rankSixEvenMinusPositiveIntegrand index angles by
    funext angles
    have hs := cosineCubeScale_angleReflection 3 angles
    by_cases hd : angles ∈ positiveSpectralLocalDomain 3
    · have hr : angleReflectionEquiv 3 angles ∈ negativeSpectralLocalDomain 3 := by
        change cosineCubeScale (angleReflectionEquiv 3 angles) ≤
          -cosineScaleMidpoint 3
        rw [hs]
        exact neg_le_neg hd
      rw [Set.indicator_of_mem hr, rankSixEvenMinusPositiveIntegrand,
        Set.indicator_of_mem hd, rankSixEvenFullNormalizedIntegrand,
        hs, fibonacciScaleKernel_neg, evenWeylAngleWeight_reflection]
      ring
    · have hr : angleReflectionEquiv 3 angles ∉ negativeSpectralLocalDomain 3 := by
        intro hr
        apply hd
        change cosineCubeScale (angleReflectionEquiv 3 angles) ≤
          -cosineScaleMidpoint 3 at hr
        rw [hs] at hr
        change cosineScaleMidpoint 3 ≤ cosineCubeScale angles
        linarith
      rw [Set.indicator_of_notMem hr, rankSixEvenMinusPositiveIntegrand,
        Set.indicator_of_notMem hd, mul_zero],
    integral_const_mul, rankSixEvenMinusPositiveIntegral_eq_angleLocal]

theorem tendsto_rankSixEvenNegativeIntegral_zero :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenNegativeIntegral index)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun index : ℕ => ‖Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * rankSixEvenMinusAngleLocalIntegral index‖)
  · intro index
    rw [rankSixEvenNegativeIntegral_eq]
    simp [norm_mul]
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_rankSixEvenMinusAngleLocalIntegral_zero

noncomputable def rankSixTailGrowthRatio : ℝ :=
  absoluteKernelGrowth 4 / largeScalePreimage 6

theorem rankSixTailGrowthRatio_pos : 0 < rankSixTailGrowthRatio := by
  unfold rankSixTailGrowthRatio
  exact div_pos (absoluteKernelGrowth_pos (by norm_num))
    (largeScalePreimage_pos (by norm_num))

theorem rankSixTailGrowthRatio_lt_one : rankSixTailGrowthRatio < 1 := by
  rw [rankSixTailGrowthRatio, div_lt_one (largeScalePreimage_pos (by norm_num))]
  have h := absoluteKernelGrowth_halfway_lt_largeScalePreimage
    (base := 6) (by norm_num)
  norm_num at h ⊢
  exact h

theorem tendsto_rankSixTailPolynomialGeometric :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 8 * rankSixTailGrowthRatio ^ (index + 1))
      atTop (nhds 0) := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 8
    (by rw [abs_of_pos rankSixTailGrowthRatio_pos]
        exact rankSixTailGrowthRatio_lt_one)
  have hs := h.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 8 * rankSixTailGrowthRatio ^ (index + 1)) =
      (fun index : ℕ => (index : ℝ) ^ 8 * rankSixTailGrowthRatio ^ index) ∘
        (fun index => index + 1) by
    funext index
    simp [Function.comp_apply]]
  exact hs

theorem evenWeylAngleWeight_three_le_512 (angles : Fin 3 → ℝ) :
    evenWeylAngleWeight 3 angles ≤ 512 := by
  unfold evenWeylAngleWeight cosineVandermondeWeight
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))),
    Finset.prod_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
    Finset.prod_singleton]
  have h0 : Finset.Iio (0 : Fin 3) = ∅ := by decide
  have h1 : Finset.Iio (1 : Fin 3) = {0} := by decide
  have h2 : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
  rw [h0, h1, h2]
  norm_num
  have hdiff (i j : Fin 3) :
      (Real.cos (angles i) - Real.cos (angles j)) ^ 2 ≤ 4 := by
    have hil := Real.neg_one_le_cos (angles i)
    have hiu := Real.cos_le_one (angles i)
    have hjl := Real.neg_one_le_cos (angles j)
    have hju := Real.cos_le_one (angles j)
    nlinarith
  have hp (i : Fin 3) : 0 ≤ 1 + Real.cos (angles i) := by
    linarith [Real.neg_one_le_cos (angles i)]
  have hpu (i : Fin 3) : 1 + Real.cos (angles i) ≤ 2 := by
    linarith [Real.cos_le_one (angles i)]
  have hpair :
      (Real.cos (angles 1) - Real.cos (angles 0)) ^ 2 *
        ((Real.cos (angles 2) - Real.cos (angles 0)) ^ 2 *
          (Real.cos (angles 2) - Real.cos (angles 1)) ^ 2) ≤ 64 := by
    have hfirst :
        (Real.cos (angles 1) - Real.cos (angles 0)) ^ 2 *
            (Real.cos (angles 2) - Real.cos (angles 0)) ^ 2 ≤ 16 :=
      (mul_le_mul (hdiff 1 0) (hdiff 2 0)
        (sq_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have ht := mul_le_mul hfirst (hdiff 2 1)
      (sq_nonneg (Real.cos (angles 2) - Real.cos (angles 1)))
      (by norm_num : (0 : ℝ) ≤ 16)
    norm_num at ht
    simpa [mul_assoc] using ht
  have hplus : (1 + Real.cos (angles 0)) *
      ((1 + Real.cos (angles 1)) * (1 + Real.cos (angles 2))) ≤ 8 := by
    have hinner : (1 + Real.cos (angles 1)) *
        (1 + Real.cos (angles 2)) ≤ 4 :=
      (mul_le_mul (hpu 1) (hpu 2) (hp 2) (by norm_num)).trans_eq (by norm_num)
    exact (mul_le_mul (hpu 0) hinner
      (mul_nonneg (hp 1) (hp 2)) (by norm_num)).trans_eq (by norm_num)
  have htotal := mul_le_mul hpair hplus
    (mul_nonneg (hp 0) (mul_nonneg (hp 1) (hp 2)))
    (by norm_num : (0 : ℝ) ≤ 64)
  norm_num at htotal
  simpa [Finset.prod_insert, mul_assoc] using htotal

theorem rankSixScaleFactor_le_power_eight (index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 ≤
      (index + 1 : ℝ) ^ 8 := by
  let x : ℝ := index + 1
  have hx : 1 ≤ x := by
    dsimp [x]
    norm_num
  have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by positivity)
  have hsle : Real.sqrt x ≤ x := by
    have hsn := Real.sqrt_nonneg x
    nlinarith [sq_nonneg (Real.sqrt x - x)]
  have hcub : Real.sqrt x ^ 3 ≤ x ^ 2 := by
    rw [show Real.sqrt x ^ 3 = Real.sqrt x ^ 2 * Real.sqrt x by ring, hs]
    nlinarith
  dsimp only [x] at hcub ⊢
  have hpnon : 0 ≤ (index + 1 : ℝ) ^ 6 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hcub hpnon]

theorem abs_rankSixNormalizedKernel_le_tail
    {index : ℕ} {scale : ℝ} (hs : |scale| ≤ 4) :
    |fibonacciScaleKernel scale index /
        (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)| ≤
      Real.sqrt 32 * rankSixTailGrowthRatio ^ (index + 1) := by
  let gamma := absoluteKernelGrowth 4
  let alpha := largeScalePreimage 6
  have hk : |fibonacciScaleKernel scale index| ≤ gamma ^ index :=
    abs_fibonacciScaleKernel_le_growth_pow (by norm_num) hs index
  have hg : 1 ≤ gamma := (by norm_num : (1 : ℝ) ≤ 4).trans
    (absoluteKernelGrowth_ge_bound (by norm_num))
  have ha : 0 < alpha := largeScalePreimage_pos (by norm_num)
  have hr : 0 < Real.sqrt (32 : ℝ) := by positivity
  have hd : 0 < alpha ^ (index + 1) / Real.sqrt 32 := by positivity
  rw [abs_div, abs_of_pos hd]
  calc
    _ = (|fibonacciScaleKernel scale index| * Real.sqrt 32) /
        alpha ^ (index + 1) := by field_simp
    _ ≤ (gamma ^ index * Real.sqrt 32) / alpha ^ (index + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hk hr.le) (pow_nonneg ha.le _)
    _ ≤ (gamma ^ (index + 1) * Real.sqrt 32) / alpha ^ (index + 1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg ha.le _)
      apply mul_le_mul_of_nonneg_right _ hr.le
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg (by positivity) _) hg
    _ = Real.sqrt 32 * (gamma / alpha) ^ (index + 1) := by
      rw [div_pow]
      ring
    _ = _ := by rfl

theorem tendsto_rankSixEvenMiddleIntegral_zero :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenMiddleIntegral index) atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) ^ 3 * Real.sqrt 32 * 512) *
    (cosineCubeProductMeasure 3).real Set.univ
  have hb : ∀ index, ‖rankSixEvenMiddleIntegral index‖ ≤
      (((1 / Real.pi) ^ 3 * Real.sqrt 32 * 512) *
        rankSixTailGrowthRatio ^ (index + 1)) *
          (cosineCubeProductMeasure 3).real Set.univ := by
    intro index
    unfold rankSixEvenMiddleIntegral
    apply norm_integral_le_of_norm_le_const
    filter_upwards with angles
    by_cases hm : angles ∈ middleOpenSpectralDomain 3
    · rw [Set.indicator_of_mem hm, rankSixEvenFullNormalizedIntegrand,
        Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
        abs_of_nonneg (evenWeylAngleWeight_nonneg 3 angles)]
      have hs : |cosineCubeScale angles| ≤ 4 := by
        change -cosineScaleMidpoint 3 < cosineCubeScale angles ∧
          cosineCubeScale angles < cosineScaleMidpoint 3 at hm
        norm_num [cosineScaleMidpoint] at hm ⊢
        exact abs_le.2 ⟨hm.1.le, hm.2.le⟩
      have hk := abs_rankSixNormalizedKernel_le_tail (index := index) hs
      have hw := evenWeylAngleWeight_three_le_512 angles
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hk
        (pow_nonneg (by positivity) _)) hw
        (evenWeylAngleWeight_nonneg 3 angles)
        (mul_nonneg (pow_nonneg (by positivity) _)
          (mul_nonneg (Real.sqrt_nonneg _)
            (pow_nonneg rankSixTailGrowthRatio_pos.le _)))).trans_eq (by ring)
    · rw [Set.indicator_of_notMem hm, norm_zero]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (pow_nonneg (by positivity) _) (Real.sqrt_nonneg _))
          (by norm_num))
        (pow_nonneg rankSixTailGrowthRatio_pos.le _)
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 8 * rankSixTailGrowthRatio ^ (index + 1)) * constant)
  · intro index
    rw [norm_mul, norm_mul,
      Real.norm_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) 3),
      Real.norm_of_nonneg (pow_nonneg
        (show 0 ≤ (index + 1 : ℝ) by positivity) 6)]
    have h1 := mul_le_mul_of_nonneg_right (rankSixScaleFactor_le_power_eight index)
      (norm_nonneg (rankSixEvenMiddleIntegral index))
    have h2 := mul_le_mul_of_nonneg_left (hb index)
      (pow_nonneg (show 0 ≤ (index + 1 : ℝ) by positivity) 8)
    exact h1.trans (h2.trans_eq (by ring))
  · simpa using tendsto_rankSixTailPolynomialGeometric.mul_const constant

theorem rankSixEvenFullNormalizedIntegral_eq_weylMoment (index : ℕ) :
    rankSixEvenFullNormalizedIntegral index =
      (1 / Real.pi) ^ 3 *
        (evenWeylFibonacciMoment 3 index /
          (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)) := by
  unfold rankSixEvenFullNormalizedIntegral rankSixEvenFullNormalizedIntegrand
    evenWeylFibonacciMoment weightedCosineCubeFibonacciMoment
    weightedCosineCubeFibonacciIntegrand
  rw [show (fun angles : Fin 3 → ℝ =>
      (1 / Real.pi) ^ 3 *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)) *
        evenWeylAngleWeight 3 angles) =
      fun angles => ((1 / Real.pi) ^ 3 /
        (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)) *
          (fibonacciScaleKernel (cosineCubeScale angles) index *
            evenWeylAngleWeight 3 angles) by
    funext angles
    ring]
  rw [integral_const_mul]
  ring

theorem tendsto_rankSixRibbonNormalizedIntegralConstant :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        ((ribbonCount 5 index : ℝ) /
          (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)))
      atTop (nhds ((32 / 3 : ℝ) *
        (∫ coordinates : Fin 3 → ℝ,
          rankSixEvenLocalLimitIntegrand coordinates))) := by
  -- Split the compact spectral cube into the positive endpoint, the reflected
  -- negative endpoint, and the exponentially smaller middle region.
  have hfull : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenFullNormalizedIntegral index)
      atTop (nhds (∫ coordinates : Fin 3 → ℝ,
        rankSixEvenLocalLimitIntegrand coordinates)) := by
    have hint : ∀ index,
        rankSixEvenFullNormalizedIntegral index =
          rankSixEvenAngleLocalIntegral index +
            (rankSixEvenNegativeIntegral index + rankSixEvenMiddleIntegral index) := by
      intro index
      unfold rankSixEvenFullNormalizedIntegral rankSixEvenNegativeIntegral
        rankSixEvenMiddleIntegral
      have hcontinuous : Continuous
          (rankSixEvenFullNormalizedIntegrand index) := by
        unfold rankSixEvenFullNormalizedIntegrand
        exact (continuous_const.mul
          (((continuous_fibonacciScaleKernel index).comp
            (continuous_cosineCubeScale 3)).div_const _)).mul
          (continuous_evenWeylAngleWeight 3)
      have hraw := integrable_continuous_cosineCube hcontinuous
      have hp := hraw.indicator (measurableSet_positiveSpectralLocalDomain 3)
      have hn := hraw.indicator (measurableSet_negativeSpectralLocalDomain 3)
      have hm := hraw.indicator (measurableSet_middleOpenSpectralDomain 3)
      rw [show (fun angles : Fin 3 → ℝ => rankSixEvenFullNormalizedIntegrand index angles) =
        fun angles =>
          (positiveSpectralLocalDomain 3).indicator
              (rankSixEvenFullNormalizedIntegrand index) angles +
            ((negativeSpectralLocalDomain 3).indicator
                (rankSixEvenFullNormalizedIntegrand index) angles +
              (middleOpenSpectralDomain 3).indicator
                (rankSixEvenFullNormalizedIntegrand index) angles) by
        funext angles
        have hmidPos : 0 < cosineScaleMidpoint 3 := by
          norm_num [cosineScaleMidpoint]
        by_cases hpositive : angles ∈ positiveSpectralLocalDomain 3
        · have hnegative : angles ∉ negativeSpectralLocalDomain 3 := by
            intro hnegative
            change cosineScaleMidpoint 3 ≤ cosineCubeScale angles at hpositive
            change cosineCubeScale angles ≤ -cosineScaleMidpoint 3 at hnegative
            linarith
          have hmiddle : angles ∉ middleOpenSpectralDomain 3 := by
            intro hmiddle
            exact (not_lt_of_ge hpositive) hmiddle.2
          rw [Set.indicator_of_mem hpositive,
            Set.indicator_of_notMem hnegative,
            Set.indicator_of_notMem hmiddle, zero_add, add_zero]
        · have hpositiveLt : cosineCubeScale angles < cosineScaleMidpoint 3 :=
            lt_of_not_ge hpositive
          by_cases hnegative : angles ∈ negativeSpectralLocalDomain 3
          · have hmiddle : angles ∉ middleOpenSpectralDomain 3 := by
              intro hmiddle
              exact (not_lt_of_ge hnegative) hmiddle.1
            rw [Set.indicator_of_notMem hpositive,
              Set.indicator_of_mem hnegative,
              Set.indicator_of_notMem hmiddle, zero_add, add_zero]
          · have hnegativeLt : -cosineScaleMidpoint 3 <
                cosineCubeScale angles := lt_of_not_ge hnegative
            have hmiddle : angles ∈ middleOpenSpectralDomain 3 :=
              ⟨hnegativeLt, hpositiveLt⟩
            rw [Set.indicator_of_notMem hpositive,
              Set.indicator_of_notMem hnegative,
              Set.indicator_of_mem hmiddle]
            simp]
      have hpositive :
          (∫ angles : Fin 3 → ℝ,
            (positiveSpectralLocalDomain 3).indicator
              (rankSixEvenFullNormalizedIntegrand index) angles
            ∂cosineCubeProductMeasure 3) =
            rankSixEvenAngleLocalIntegral index := by
        rw [cosineCubeProductMeasure_eq_restrict]
        rw [show (Set.univ.pi fun _ : Fin 3 => Set.Ioc (0 : ℝ) Real.pi) =
          anglePositiveCube 3 by rfl]
        rw [← integral_indicator
          (show MeasurableSet (anglePositiveCube 3) by
            unfold anglePositiveCube
            exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
        unfold rankSixEvenAngleLocalIntegral
        apply integral_congr_ae
        filter_upwards with angles
        by_cases hc : angles ∈ anglePositiveCube 3
        · by_cases hl : angles ∈ positiveSpectralLocalDomain 3
          · have hd : angles ∈ anglePositiveLocalDomain 3 := ⟨hc, hl⟩
            rw [Set.indicator_of_mem hc, Set.indicator_of_mem hl,
              rankSixEvenAngleLocalIntegrand, Set.indicator_of_mem hd]
            rfl
          · rw [Set.indicator_of_mem hc, Set.indicator_of_notMem hl,
              rankSixEvenAngleLocalIntegrand,
              Set.indicator_of_notMem (fun h => hl h.2)]
        · rw [Set.indicator_of_notMem hc, rankSixEvenAngleLocalIntegrand,
            Set.indicator_of_notMem (fun h => hc h.1)]
      calc
        (∫ angles : Fin 3 → ℝ,
            (positiveSpectralLocalDomain 3).indicator
                (rankSixEvenFullNormalizedIntegrand index) angles +
              ((negativeSpectralLocalDomain 3).indicator
                  (rankSixEvenFullNormalizedIntegrand index) angles +
                (middleOpenSpectralDomain 3).indicator
                  (rankSixEvenFullNormalizedIntegrand index) angles)
            ∂cosineCubeProductMeasure 3) =
          (∫ angles,
            (positiveSpectralLocalDomain 3).indicator
              (rankSixEvenFullNormalizedIntegrand index) angles
            ∂cosineCubeProductMeasure 3) +
            ∫ angles,
              (negativeSpectralLocalDomain 3).indicator
                  (rankSixEvenFullNormalizedIntegrand index) angles +
                (middleOpenSpectralDomain 3).indicator
                  (rankSixEvenFullNormalizedIntegrand index) angles
              ∂cosineCubeProductMeasure 3 := integral_add hp (hn.add hm)
        _ = (∫ angles,
              (positiveSpectralLocalDomain 3).indicator
                (rankSixEvenFullNormalizedIntegrand index) angles
              ∂cosineCubeProductMeasure 3) +
            ((∫ angles,
                (negativeSpectralLocalDomain 3).indicator
                  (rankSixEvenFullNormalizedIntegrand index) angles
                ∂cosineCubeProductMeasure 3) +
              ∫ angles,
                (middleOpenSpectralDomain 3).indicator
                  (rankSixEvenFullNormalizedIntegrand index) angles
                ∂cosineCubeProductMeasure 3) := by
          rw [integral_add hn hm]
        _ = _ := by rw [hpositive]
    rw [show (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
        (index + 1 : ℝ) ^ 6 * rankSixEvenFullNormalizedIntegral index) =
      fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
            rankSixEvenAngleLocalIntegral index +
          (Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
              rankSixEvenNegativeIntegral index +
            Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
              rankSixEvenMiddleIntegral index) by
        funext index
        rw [hint]
        ring]
    simpa using tendsto_rankSixEvenAngleLocalIntegral.add
      (tendsto_rankSixEvenNegativeIntegral_zero.add
        tendsto_rankSixEvenMiddleIntegral_zero)
  have hscaled := hfull.const_mul (32 / 3 : ℝ)
  apply hscaled.congr'
  filter_upwards with index
  rw [rankSixEvenFullNormalizedIntegral_eq_weylMoment,
    heightSixRibbonCount_eq_normalized_evenWeylFibonacciMoment]
  field_simp [Real.pi_ne_zero]

end FibonacciRibbonKernel
