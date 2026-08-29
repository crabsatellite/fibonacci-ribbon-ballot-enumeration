import FibonacciRibbonKernel.RankFourEvenWeylCount

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFourEvenLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 2 → ℝ) : ℝ :=
  (positiveLocalScaledDomain 2 index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ 2 *
        normalizedFibonacciCosineKernel coordinates index *
        evenScaledWeylWeight 2 index coordinates)
    coordinates

noncomputable def rankFourEvenLocalLimitIntegrand
    (coordinates : Fin 2 → ℝ) : ℝ :=
  positiveOrthant.indicator
    (fun coordinates =>
      (1 / Real.pi) ^ 2 *
        Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) /
          Real.sqrt (12 : ℝ)) *
        evenLimitWeylWeight 2 coordinates)
    coordinates

noncomputable def rankFourEvenAngleLocalIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (anglePositiveLocalDomain 2).indicator
    (fun angles =>
      (1 / Real.pi) ^ 2 *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) *
        evenWeylAngleWeight 2 angles)
    angles

noncomputable def rankFourEvenAngleLocalIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFourEvenAngleLocalIntegrand index angles

theorem tendsto_rankFourEvenLocalRescaledIntegrand
    (coordinates : Fin 2 → ℝ) :
    Tendsto (fun index =>
      rankFourEvenLocalRescaledIntegrand index coordinates)
      atTop (nhds (rankFourEvenLocalLimitIntegrand coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain
      (dimension := 2) (by norm_num) coordinates horthant
    have hkernel := tendsto_normalizedFibonacciCosineKernel
      (dimension := 2) (by norm_num) coordinates
    have hweight := tendsto_evenScaledWeylWeight 2 coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 2)
        atTop (nhds ((1 / Real.pi) ^ 2)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    rw [show Real.sqrt ((2 * (2 : ℕ) : ℝ) ^ 2 - 4) =
      Real.sqrt (12 : ℝ) by norm_num] at hproduct
    rw [rankFourEvenLocalLimitIntegrand, Set.indicator_of_mem horthant]
    apply hproduct.congr'
    filter_upwards [hlocal] with index hindex
    rw [rankFourEvenLocalRescaledIntegrand, Set.indicator_of_mem hindex]
  · have hnot : ∃ coordinate : Fin 2, coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _hcoordinate => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveLocalScaledDomain 2 index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    have hzero : (fun index : ℕ =>
        rankFourEvenLocalRescaledIntegrand index coordinates) =
        fun _ => 0 := by
      funext index
      rw [rankFourEvenLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)]
    rw [hzero, rankFourEvenLocalLimitIntegrand,
      Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

theorem continuous_rankFourEvenAngleLocalCore (index : ℕ) :
    Continuous (fun angles : Fin 2 → ℝ =>
      (1 / Real.pi) ^ 2 *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) *
        evenWeylAngleWeight 2 angles) := by
  exact (continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale 2)).div_const _)).mul
        (continuous_evenWeylAngleWeight 2)

theorem stronglyMeasurable_rankFourEvenAngleLocalIntegrand (index : ℕ) :
    StronglyMeasurable (rankFourEvenAngleLocalIntegrand index) := by
  unfold rankFourEvenAngleLocalIntegrand
  exact (continuous_rankFourEvenAngleLocalCore index).stronglyMeasurable.indicator
    (measurableSet_anglePositiveLocalDomain 2)

theorem aestronglyMeasurable_rankFourEvenLocalRescaledIntegrand
    (index : ℕ) :
    AEStronglyMeasurable (rankFourEvenLocalRescaledIntegrand index) := by
  unfold rankFourEvenLocalRescaledIntegrand
  exact (((continuous_const.mul
    (continuous_normalizedFibonacciCosineKernel 2 index (by norm_num))).mul
      (by
        unfold evenScaledWeylWeight
        exact (continuous_scaledCosineVandermondeWeight 2 index).mul
          (by
            unfold allPlusScaledWeight
            apply continuous_finsetProd
            intro coordinate _hcoordinate
            fun_prop))).stronglyMeasurable.indicator
      (by
        unfold positiveLocalScaledDomain
        exact (measurableSet_positiveScaledCube 2 index).inter
          (measurableSet_Ici.preimage
            (continuous_cosineSumScale 2 index).measurable))).aestronglyMeasurable

theorem rankFourEvenAngleWeight_inverseSqrt
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    evenWeylAngleWeight 2
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      evenScaledWeylWeight 2 index coordinates / (index + 1 : ℝ) ^ 2 := by
  have hscale := evenScaledWeylWeight_eq 2 index coordinates
  norm_num at hscale
  have hnonzero : (index + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  rw [coordinateScalarLinearMap_apply]
  simp only [one_div]
  apply (eq_div_iff hnonzero).2
  rw [hscale]
  ring

theorem rankFourEvenAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    rankFourEvenAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankFourEvenLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 2 := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain 2 index
  · rw [rankFourEvenAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff 2 index coordinates).2 hdomain),
      rankFourEvenLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt,
      rankFourEvenAngleWeight_inverseSqrt]
    unfold normalizedFibonacciCosineKernel
    norm_num
    ring
  · rw [rankFourEvenAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff 2 index coordinates).1 hdomain),
      rankFourEvenLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem rankFourEvenLocalScalingIntegral_identity (index : ℕ) :
    (index + 1 : ℝ) ^ 3 * rankFourEvenAngleLocalIntegral index =
      ∫ coordinates : Fin 2 → ℝ,
        rankFourEvenLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 2
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankFourEvenAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 2 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 2 _).aemeasurable
      (stronglyMeasurable_rankFourEvenAngleLocalIntegrand index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 2)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ 2 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold rankFourEvenAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 2 → ℝ =>
      rankFourEvenAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates =>
        rankFourEvenLocalRescaledIntegrand index coordinates /
          (index + 1 : ℝ) ^ 2 by
    funext coordinates
    exact rankFourEvenAngleLocalIntegrand_inverseSqrt index coordinates] at hmap
  rw [integral_div] at hmap
  have hsqrt : Real.sqrt (index + 1 : ℝ) ^ 2 = index + 1 :=
    Real.sq_sqrt (by positivity)
  have hnonzero : (index + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  rw [hsqrt] at hmap
  field_simp [hnonzero] at hmap ⊢
  exact hmap

end FibonacciRibbonKernel
