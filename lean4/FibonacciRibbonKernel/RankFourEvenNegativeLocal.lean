import FibonacciRibbonKernel.RankFourEvenDominating

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFourEvenMinusScaledWeight
    (index : ℕ) (coordinates : Fin 2 → ℝ) : ℝ :=
  scaledCosineVandermondeWeight 2 index coordinates *
    allMinusScaledWeight 2 index coordinates

noncomputable def rankFourEvenMinusLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 2 → ℝ) : ℝ :=
  (positiveLocalScaledDomain 2 index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ 2 *
        normalizedFibonacciCosineKernel coordinates index *
        rankFourEvenMinusScaledWeight index coordinates)
    coordinates

noncomputable def rankFourEvenMinusAngleLocalIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (anglePositiveLocalDomain 2).indicator
    (fun angles =>
      (1 / Real.pi) ^ 2 *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) *
        (cosineVandermondeWeight 2 angles * allMinusAngleWeight 2 angles))
    angles

noncomputable def rankFourEvenMinusAngleLocalIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ,
    rankFourEvenMinusAngleLocalIntegrand index angles

theorem tendsto_rankFourEvenMinusScaledWeight_zero
    (coordinates : Fin 2 → ℝ) :
    Tendsto (fun index => rankFourEvenMinusScaledWeight index coordinates)
      atTop (nhds 0) := by
  unfold rankFourEvenMinusScaledWeight
  simpa using (tendsto_scaledCosineVandermondeWeight 2 coordinates).mul
    (tendsto_allMinusScaledWeight (dimension := 2) (by norm_num) coordinates)

theorem tendsto_rankFourEvenMinusLocalRescaledIntegrand_zero
    (coordinates : Fin 2 → ℝ) :
    Tendsto (fun index =>
      rankFourEvenMinusLocalRescaledIntegrand index coordinates)
      atTop (nhds 0) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain
      (dimension := 2) (by norm_num) coordinates horthant
    have hkernel := tendsto_normalizedFibonacciCosineKernel
      (dimension := 2) (by norm_num) coordinates
    have hweight := tendsto_rankFourEvenMinusScaledWeight_zero coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 2)
        atTop (nhds ((1 / Real.pi) ^ 2)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    simpa only [mul_zero] using hproduct.congr' (by
      filter_upwards [hlocal] with index hindex
      rw [rankFourEvenMinusLocalRescaledIntegrand,
        Set.indicator_of_mem hindex])
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
        rankFourEvenMinusLocalRescaledIntegrand index coordinates) =
        fun _ => 0 := by
      funext index
      rw [rankFourEvenMinusLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)]
    rw [hzero]
    exact tendsto_const_nhds

theorem continuous_rankFourEvenMinusScaledWeight (index : ℕ) :
    Continuous (rankFourEvenMinusScaledWeight index) := by
  unfold rankFourEvenMinusScaledWeight
  exact (continuous_scaledCosineVandermondeWeight 2 index).mul
    (continuous_allMinusScaledWeight 2 index)

theorem aestronglyMeasurable_rankFourEvenMinusLocalRescaledIntegrand
    (index : ℕ) :
    AEStronglyMeasurable
      (rankFourEvenMinusLocalRescaledIntegrand index) := by
  unfold rankFourEvenMinusLocalRescaledIntegrand
  exact (((continuous_const.mul
    (continuous_normalizedFibonacciCosineKernel 2 index (by norm_num))).mul
      (continuous_rankFourEvenMinusScaledWeight index)).stronglyMeasurable.indicator
        (measurableSet_positiveLocalScaledDomain 2 index)).aestronglyMeasurable

theorem rankFourEvenMinusScaledWeight_nonneg
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    0 ≤ rankFourEvenMinusScaledWeight index coordinates := by
  unfold rankFourEvenMinusScaledWeight
  exact mul_nonneg (by unfold scaledCosineVandermondeWeight; positivity)
    (allMinusScaledWeight_nonneg 2 index coordinates)

theorem rankFourEvenMinusScaledWeight_le_polynomial
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    rankFourEvenMinusScaledWeight index coordinates ≤
      rankFourWeylPolynomial coordinates := by
  unfold rankFourEvenMinusScaledWeight rankFourWeylPolynomial
  rw [scaledCosineVandermondeWeight_two]
  have hdiff := abs_scaled_cosine_difference_le index
    (coordinates 1) (coordinates 0)
  have hdiffSq := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 hdiff
  rw [sq_abs] at hdiffSq
  have hminus := allMinusScaledWeight_le_two_pow 2 index coordinates
  norm_num at hminus
  exact (mul_le_mul hdiffSq hminus
    (allMinusScaledWeight_nonneg 2 index coordinates)
    (by positivity : 0 ≤ ((coordinates 1 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2)).trans_eq
      (by ring)

theorem norm_rankFourEvenMinusLocalRescaledIntegrand_le
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    ‖rankFourEvenMinusLocalRescaledIntegrand index coordinates‖ ≤
      rankFourLocalDominating coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain 2 index
  · rw [rankFourEvenMinusLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, Real.norm_eq_abs, abs_of_nonneg]
    · have hcoordinate : ∀ coordinate,
          |coordinates coordinate| ≤
            Real.pi * Real.sqrt (index + 1 : ℝ) := by
        intro coordinate
        have hmem := hdomain.1 coordinate (Set.mem_univ coordinate)
        rw [abs_of_pos hmem.1]
        exact hmem.2
      have hkernel := normalizedFibonacciCosineKernel_le_local_gaussian
        (dimension := 2) (by norm_num) coordinates hcoordinate hdomain.2
      rw [show Real.sqrt ((2 * (2 : ℕ) : ℝ) ^ 2 - 4) =
        Real.sqrt (12 : ℝ) by norm_num] at hkernel
      have hkernel' : normalizedFibonacciCosineKernel coordinates index ≤
          (Real.sqrt (12 : ℝ) /
            Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4)) *
          Real.exp (-allPlusGaussianCoefficient 2 *
            ∑ coordinate, coordinates coordinate ^ 2) := by
        rw [show allPlusGaussianCoefficient 2 =
            4 / (Real.pi ^ 2 * Real.sqrt (12 : ℝ)) by
          norm_num [allPlusGaussianCoefficient]]
        exact hkernel
      have hweight :=
        rankFourEvenMinusScaledWeight_le_polynomial index coordinates
      have hkernelNonneg := normalizedFibonacciCosineKernel_nonneg
        (dimension := 2) (by norm_num) coordinates
        ((cosineScaleMidpoint_gt_two (by norm_num)).trans_le hdomain.2)
      have hweightNonneg :=
        rankFourEvenMinusScaledWeight_nonneg index coordinates
      have hproduct := mul_le_mul hkernel' hweight hweightNonneg (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ 2 by positivity)
      exact (show (1 / Real.pi) ^ 2 *
          normalizedFibonacciCosineKernel coordinates index *
            rankFourEvenMinusScaledWeight index coordinates ≤
          ((1 / Real.pi) ^ 2 *
              (Real.sqrt (12 : ℝ) /
                Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4))) *
            rankFourWeylPolynomial coordinates *
            Real.exp (-allPlusGaussianCoefficient 2 *
              ∑ coordinate, coordinates coordinate ^ 2) by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled).trans
          (rankFourPolynomial_mul_gaussian_le_dominating coordinates)
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (normalizedFibonacciCosineKernel_nonneg
            (dimension := 2) (by norm_num) coordinates
            ((cosineScaleMidpoint_gt_two (by norm_num)).trans_le hdomain.2)))
        (rankFourEvenMinusScaledWeight_nonneg index coordinates)
  · rw [rankFourEvenMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold rankFourLocalDominating rankFourCoordinateDominating
    unfold cosineScaleMidpoint
    positivity

theorem tendsto_integral_rankFourEvenMinusLocalRescaled_zero :
    Tendsto (fun index => ∫ coordinates : Fin 2 → ℝ,
      rankFourEvenMinusLocalRescaledIntegrand index coordinates)
      atTop (nhds 0) := by
  simpa using tendsto_integral_of_dominated_convergence
    rankFourLocalDominating
    aestronglyMeasurable_rankFourEvenMinusLocalRescaledIntegrand
    integrable_rankFourLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankFourEvenMinusLocalRescaledIntegrand_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankFourEvenMinusLocalRescaledIntegrand_zero coordinates)

theorem rankFourEvenMinusAngleWeight_inverseSqrt
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    cosineVandermondeWeight 2
          (coordinateScalarLinearMap 2
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) *
        allMinusAngleWeight 2
          (coordinateScalarLinearMap 2
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankFourEvenMinusScaledWeight index coordinates /
        (index + 1 : ℝ) ^ 2 := by
  have hscale := scaledCosineVandermondeWeight_eq 2 index coordinates
  norm_num [weylPairScalingExponent] at hscale
  unfold rankFourEvenMinusScaledWeight allMinusScaledWeight
    allMinusAngleWeight
  rw [coordinateScalarLinearMap_apply]
  simp only [one_div]
  have hnonzero : (index + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  apply (eq_div_iff hnonzero).2
  rw [hscale]
  ring

theorem continuous_rankFourEvenMinusAngleLocalCore (index : ℕ) :
    Continuous (fun angles : Fin 2 → ℝ =>
      (1 / Real.pi) ^ 2 *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) *
        (cosineVandermondeWeight 2 angles * allMinusAngleWeight 2 angles)) := by
  apply (continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale 2)).div_const _)).mul
  exact (continuous_cosineVandermondeWeight 2).mul (by
    unfold allMinusAngleWeight
    apply continuous_finsetProd
    intro coordinate _hcoordinate
    fun_prop)

theorem stronglyMeasurable_rankFourEvenMinusAngleLocalIntegrand
    (index : ℕ) :
    StronglyMeasurable (rankFourEvenMinusAngleLocalIntegrand index) := by
  unfold rankFourEvenMinusAngleLocalIntegrand
  exact (continuous_rankFourEvenMinusAngleLocalCore index).stronglyMeasurable.indicator
    (measurableSet_anglePositiveLocalDomain 2)

theorem rankFourEvenMinusAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    rankFourEvenMinusAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankFourEvenMinusLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 2 := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain 2 index
  · rw [rankFourEvenMinusAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff 2 index coordinates).2 hdomain),
      rankFourEvenMinusLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt,
      rankFourEvenMinusAngleWeight_inverseSqrt]
    unfold normalizedFibonacciCosineKernel
    norm_num
    ring
  · rw [rankFourEvenMinusAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff 2 index coordinates).1 hdomain),
      rankFourEvenMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem rankFourEvenMinusLocalScalingIntegral_identity (index : ℕ) :
    (index + 1 : ℝ) ^ 3 * rankFourEvenMinusAngleLocalIntegral index =
      ∫ coordinates : Fin 2 → ℝ,
        rankFourEvenMinusLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 2
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankFourEvenMinusAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 2 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 2 _).aemeasurable
      (stronglyMeasurable_rankFourEvenMinusAngleLocalIntegrand index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 2)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ 2 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold rankFourEvenMinusAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 2 → ℝ =>
      rankFourEvenMinusAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates =>
        rankFourEvenMinusLocalRescaledIntegrand index coordinates /
          (index + 1 : ℝ) ^ 2 by
    funext coordinates
    exact rankFourEvenMinusAngleLocalIntegrand_inverseSqrt index coordinates] at hmap
  rw [integral_div] at hmap
  have hsqrt : Real.sqrt (index + 1 : ℝ) ^ 2 = index + 1 :=
    Real.sq_sqrt (by positivity)
  have hnonzero : (index + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  rw [hsqrt] at hmap
  field_simp [hnonzero] at hmap ⊢
  exact hmap

theorem tendsto_rankFourEvenMinusAngleLocalIntegral_zero :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourEvenMinusAngleLocalIntegral index)
      atTop (nhds 0) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourEvenMinusAngleLocalIntegral index) =
      fun index => ∫ coordinates : Fin 2 → ℝ,
        rankFourEvenMinusLocalRescaledIntegrand index coordinates by
    funext index
    exact rankFourEvenMinusLocalScalingIntegral_identity index]
  exact tendsto_integral_rankFourEvenMinusLocalRescaled_zero

end FibonacciRibbonKernel
