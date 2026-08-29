import FibonacciRibbonKernel.RankFourGeometricDCT

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFourGeometricMinusLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 2 → ℝ) : ℝ :=
  (positiveLocalScaledDomain 2 index).indicator (fun coordinates =>
    (1 / Real.pi) ^ 2 * normalizedRankFourGeometricKernel coordinates index *
      rankFourEvenMinusScaledWeight index coordinates) coordinates

noncomputable def rankFourGeometricMinusAngleLocalIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (anglePositiveLocalDomain 2).indicator (fun angles =>
    (1 / Real.pi) ^ 2 * (cosineCubeScale angles / 4) ^ index *
      (cosineVandermondeWeight 2 angles * allMinusAngleWeight 2 angles)) angles

noncomputable def rankFourGeometricMinusAngleLocalIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ,
    rankFourGeometricMinusAngleLocalIntegrand index angles

theorem tendsto_rankFourGeometricMinusLocalRescaled_zero
    (coordinates : Fin 2 → ℝ) :
    Tendsto (fun index =>
      rankFourGeometricMinusLocalRescaledIntegrand index coordinates)
      atTop (nhds 0) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain
      (dimension := 2) (by norm_num) coordinates horthant
    have hkernel := tendsto_normalizedRankFourGeometricKernel coordinates
    have hweight := tendsto_rankFourEvenMinusScaledWeight_zero coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 2)
        atTop (nhds ((1 / Real.pi) ^ 2)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    simpa only [mul_zero] using hproduct.congr' (by
      filter_upwards [hlocal] with index hindex
      rw [rankFourGeometricMinusLocalRescaledIntegrand,
        Set.indicator_of_mem hindex])
  · have hnot : ∃ coordinate : Fin 2, coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _hcoordinate => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveLocalScaledDomain 2 index := by
      intro index hdomain
      linarith [(hdomain.1 coordinate (Set.mem_univ coordinate)).1]
    rw [show (fun index : ℕ =>
        rankFourGeometricMinusLocalRescaledIntegrand index coordinates) =
        fun _ => 0 by
      funext index
      rw [rankFourGeometricMinusLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)]]
    exact tendsto_const_nhds

theorem aestronglyMeasurable_rankFourGeometricMinusLocalRescaled
    (index : ℕ) :
    AEStronglyMeasurable (rankFourGeometricMinusLocalRescaledIntegrand index) := by
  have hkernel : Continuous (normalizedRankFourGeometricKernel · index) := by
    unfold normalizedRankFourGeometricKernel
    exact ((continuous_cosineSumScale 2 index).div_const 4).pow index
  unfold rankFourGeometricMinusLocalRescaledIntegrand
  exact (((continuous_const.mul hkernel).mul
    (continuous_rankFourEvenMinusScaledWeight index)).stronglyMeasurable.indicator
      (measurableSet_positiveLocalScaledDomain 2 index)).aestronglyMeasurable

theorem norm_rankFourGeometricMinusLocalRescaled_le
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    ‖rankFourGeometricMinusLocalRescaledIntegrand index coordinates‖ ≤
      rankFourGeometricLocalDominating coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain 2 index
  · rw [rankFourGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, Real.norm_eq_abs, abs_of_nonneg]
    · have hkernel := normalizedRankFourGeometricKernel_le_gaussian
        index coordinates hdomain.1 hdomain.2
      have hweight :=
        rankFourEvenMinusScaledWeight_le_polynomial index coordinates
      have hscaleNonneg : 0 ≤ cosineSumScale coordinates index :=
        (by norm_num : (0 : ℝ) ≤ 2).trans
          ((cosineScaleMidpoint_gt_two
            (dimension := 2) (by norm_num)).le.trans hdomain.2)
      have hkernelNonneg := normalizedRankFourGeometricKernel_nonneg
        (index := index) (coordinates := coordinates) hscaleNonneg
      have hweightNonneg :=
        rankFourEvenMinusScaledWeight_nonneg index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ 2 by positivity)
      exact (show (1 / Real.pi) ^ 2 *
          normalizedRankFourGeometricKernel coordinates index *
            rankFourEvenMinusScaledWeight index coordinates ≤
          (Real.exp 1 * (1 / Real.pi) ^ 2) *
            rankFourWeylPolynomial coordinates *
            Real.exp (-rankFourGeometricGaussianCoefficient *
              ∑ coordinate, coordinates coordinate ^ 2) by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled).trans
          (rankFourGeometricPolynomialGaussian_le_dominating coordinates)
    · exact mul_nonneg (mul_nonneg (by positivity)
        (normalizedRankFourGeometricKernel_nonneg
          (index := index) (coordinates := coordinates)
          ((by norm_num : (0 : ℝ) ≤ 2).trans
            ((cosineScaleMidpoint_gt_two
              (dimension := 2) (by norm_num)).le.trans hdomain.2))))
        (rankFourEvenMinusScaledWeight_nonneg index coordinates)
  · rw [rankFourGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold rankFourGeometricLocalDominating
      rankFourGeometricCoordinateDominating
    positivity

theorem tendsto_integral_rankFourGeometricMinusLocal_zero :
    Tendsto (fun index => ∫ coordinates : Fin 2 → ℝ,
      rankFourGeometricMinusLocalRescaledIntegrand index coordinates)
      atTop (nhds 0) := by
  simpa using tendsto_integral_of_dominated_convergence
    rankFourGeometricLocalDominating
    aestronglyMeasurable_rankFourGeometricMinusLocalRescaled
    integrable_rankFourGeometricLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankFourGeometricMinusLocalRescaled_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankFourGeometricMinusLocalRescaled_zero coordinates)

theorem rankFourGeometricMinusAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    rankFourGeometricMinusAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankFourGeometricMinusLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 2 := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain 2 index
  · rw [rankFourGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff 2 index coordinates).2 hdomain),
      rankFourGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, cosineCubeScale_inverseSqrt,
      rankFourEvenMinusAngleWeight_inverseSqrt]
    unfold normalizedRankFourGeometricKernel
    ring
  · rw [rankFourGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff 2 index coordinates).1 hdomain),
      rankFourGeometricMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem stronglyMeasurable_rankFourGeometricMinusAngleLocalIntegrand
    (index : ℕ) :
    StronglyMeasurable (rankFourGeometricMinusAngleLocalIntegrand index) := by
  unfold rankFourGeometricMinusAngleLocalIntegrand
  have hpower : Continuous (fun angles : Fin 2 → ℝ =>
      (cosineCubeScale angles / 4) ^ index) :=
    ((continuous_cosineCubeScale 2).div_const 4).pow index
  exact (((continuous_const.mul hpower).mul
    ((continuous_cosineVandermondeWeight 2).mul (by
      unfold allMinusAngleWeight
      apply continuous_finsetProd
      intro coordinate _hcoordinate
      fun_prop))).stronglyMeasurable.indicator
        (measurableSet_anglePositiveLocalDomain 2))

theorem rankFourGeometricMinusLocalScalingIntegral_identity (index : ℕ) :
    (index + 1 : ℝ) ^ 3 * rankFourGeometricMinusAngleLocalIntegral index =
      ∫ coordinates : Fin 2 → ℝ,
        rankFourGeometricMinusLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 2
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankFourGeometricMinusAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 2 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 2 _).aemeasurable
      (stronglyMeasurable_rankFourGeometricMinusAngleLocalIntegrand
        index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 2)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ 2 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold rankFourGeometricMinusAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 2 → ℝ =>
      rankFourGeometricMinusAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates =>
        rankFourGeometricMinusLocalRescaledIntegrand index coordinates /
          (index + 1 : ℝ) ^ 2 by
    funext coordinates
    exact rankFourGeometricMinusAngleLocalIntegrand_inverseSqrt
      index coordinates] at hmap
  rw [integral_div] at hmap
  have hsqrt : Real.sqrt (index + 1 : ℝ) ^ 2 = index + 1 :=
    Real.sq_sqrt (by positivity)
  have hnonzero : (index + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  rw [hsqrt] at hmap
  field_simp [hnonzero] at hmap ⊢
  exact hmap

theorem tendsto_rankFourGeometricMinusAngleLocalIntegral_zero :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricMinusAngleLocalIntegral index)
      atTop (nhds 0) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricMinusAngleLocalIntegral index) =
      fun index => ∫ coordinates : Fin 2 → ℝ,
        rankFourGeometricMinusLocalRescaledIntegrand index coordinates by
    funext index
    exact rankFourGeometricMinusLocalScalingIntegral_identity index]
  exact tendsto_integral_rankFourGeometricMinusLocal_zero

end FibonacciRibbonKernel
