import FibonacciRibbonKernel.RankFiveGeometricKernelBound

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFiveGeometricLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 2 → ℝ) : ℝ :=
  (positiveOddLocalScaledDomain 2 index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ 2 *
        normalizedRankFiveGeometricKernel coordinates index *
        oddScaledWeylWeight 2 index coordinates)
    coordinates

noncomputable def rankFiveGeometricLocalLimitIntegrand
    (coordinates : Fin 2 → ℝ) : ℝ :=
  positiveOrthant.indicator
    (fun coordinates =>
      (1 / Real.pi) ^ 2 *
        Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) / 5) *
        oddLimitWeylWeight 2 coordinates)
    coordinates

noncomputable def rankFiveGeometricAngleLocalIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (oddAngleLocalDomain 2).indicator
    (fun angles =>
      (1 / Real.pi) ^ 2 *
        (oddCosineCubeScale angles / 5) ^ index *
        oddWeylAngleWeight 2 angles)
    angles

noncomputable def rankFiveGeometricAngleLocalIntegral
    (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ,
    rankFiveGeometricAngleLocalIntegrand index angles

theorem tendsto_rankFiveGeometricLocalRescaledIntegrand
    (coordinates : Fin 2 → ℝ) :
    Tendsto
      (fun index => rankFiveGeometricLocalRescaledIntegrand index coordinates)
      atTop (nhds (rankFiveGeometricLocalLimitIntegrand coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveOddLocalScaledDomain
      (dimension := 2) (by norm_num) coordinates horthant
    have hkernel := tendsto_normalizedRankFiveGeometricKernel coordinates
    have hweight := tendsto_oddScaledWeylWeight 2 coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 2)
        atTop (nhds ((1 / Real.pi) ^ 2)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    rw [rankFiveGeometricLocalLimitIntegrand,
      Set.indicator_of_mem horthant]
    apply hproduct.congr'
    filter_upwards [hlocal] with index hindex
    rw [rankFiveGeometricLocalRescaledIntegrand,
      Set.indicator_of_mem hindex]
  · have hnot : ∃ coordinate : Fin 2, coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _hcoordinate => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveOddLocalScaledDomain 2 index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    have hzero : (fun index : ℕ =>
        rankFiveGeometricLocalRescaledIntegrand index coordinates) =
        fun _ => 0 := by
      funext index
      rw [rankFiveGeometricLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)]
    rw [hzero, rankFiveGeometricLocalLimitIntegrand,
      Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

theorem continuous_normalizedRankFiveGeometricKernel
    (index : ℕ) :
    Continuous (normalizedRankFiveGeometricKernel · index) := by
  unfold normalizedRankFiveGeometricKernel
  exact ((continuous_oddCosineSumScale 2 index).div_const 5).pow index

theorem aestronglyMeasurable_rankFiveGeometricLocalRescaledIntegrand
    (index : ℕ) :
    AEStronglyMeasurable
      (rankFiveGeometricLocalRescaledIntegrand index) := by
  unfold rankFiveGeometricLocalRescaledIntegrand
  exact (((continuous_const.mul
    (continuous_normalizedRankFiveGeometricKernel index)).mul
      (continuous_oddScaledWeylWeight 2 index)).stronglyMeasurable.indicator
        (measurableSet_positiveOddLocalScaledDomain 2 index)).aestronglyMeasurable

theorem stronglyMeasurable_rankFiveGeometricAngleLocalIntegrand
    (index : ℕ) :
    StronglyMeasurable
      (rankFiveGeometricAngleLocalIntegrand index) := by
  have hpower : Continuous (fun angles : Fin 2 → ℝ =>
      (oddCosineCubeScale angles / 5) ^ index) :=
    ((continuous_oddCosineCubeScale 2).div_const 5).pow index
  unfold rankFiveGeometricAngleLocalIntegrand
  exact (((continuous_const.mul
    hpower).mul
      (continuous_oddWeylAngleWeight 2)).stronglyMeasurable.indicator
        (measurableSet_oddAngleLocalDomain 2))

theorem rankFiveGeometricAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    rankFiveGeometricAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankFiveGeometricLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 4 := by
  by_cases hdomain : coordinates ∈ positiveOddLocalScaledDomain 2 index
  · rw [rankFiveGeometricAngleLocalIntegrand,
      Set.indicator_of_mem
        ((oddAngleLocalDomain_inverseSqrt_iff 2 index coordinates).2 hdomain),
      rankFiveGeometricLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain,
      oddCosineCubeScale_inverseSqrt,
      oddWeylAngleWeight_inverseSqrt]
    norm_num
    unfold normalizedRankFiveGeometricKernel
    ring
  · rw [rankFiveGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (oddAngleLocalDomain_inverseSqrt_iff 2 index coordinates).1 hdomain),
      rankFiveGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain,
      zero_div]

theorem rankFiveGeometricLocalScalingIntegral_identity
    (index : ℕ) :
    (index + 1 : ℝ) ^ 5 * rankFiveGeometricAngleLocalIntegral index =
      ∫ coordinates : Fin 2 → ℝ,
        rankFiveGeometricLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 2
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankFiveGeometricAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 2 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 2 _).aemeasurable
      (stronglyMeasurable_rankFiveGeometricAngleLocalIntegrand
        index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 2)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ 2 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold rankFiveGeometricAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 2 → ℝ =>
      rankFiveGeometricAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates =>
        rankFiveGeometricLocalRescaledIntegrand index coordinates /
          (index + 1 : ℝ) ^ 4 by
    funext coordinates
    exact rankFiveGeometricAngleLocalIntegrand_inverseSqrt index coordinates]
    at hmap
  rw [integral_div] at hmap
  have hsqrt : Real.sqrt (index + 1 : ℝ) ^ 2 = index + 1 :=
    Real.sq_sqrt (by positivity)
  have hnonzero : (index + 1 : ℝ) ^ 4 ≠ 0 := by positivity
  rw [hsqrt] at hmap
  field_simp [hnonzero] at hmap ⊢
  exact hmap

end FibonacciRibbonKernel
