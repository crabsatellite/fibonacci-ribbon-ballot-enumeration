import FibonacciRibbonKernel.RankFourEvenFullLimit

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable def normalizedRankFourGeometricKernel
    (coordinates : Fin 2 → ℝ) (index : ℕ) : ℝ :=
  (cosineSumScale coordinates index / 4) ^ index

theorem cosineSumScale_displacement_two
    (coordinates : Fin 2 → ℝ) (index : ℕ) :
    cosineSumScale coordinates index =
      4 + cosineSumDisplacement coordinates index / (index + 1 : ℝ) := by
  unfold cosineSumDisplacement
  have hnonzero : (index + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hnonzero]
  ring

theorem tendsto_log_cosineSum_microscopic_four
    (coordinates : Fin 2 → ℝ) :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) *
        (Real.log (cosineSumScale coordinates index) - Real.log 4))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) / 4)) := by
  have hderiv : HasDerivAt Real.log (1 / 4) 4 := by
    simpa using Real.hasDerivAt_log (by norm_num : (4 : ℝ) ≠ 0)
  have h := tendsto_variable_microscopic_derivative hderiv
    (tendsto_cosineSumDisplacement coordinates)
  have h' : Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) *
        (Real.log (4 + cosineSumDisplacement coordinates index /
          (index + 1 : ℝ)) - Real.log 4))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) / 4)) := by
    simpa only [div_eq_mul_inv, one_mul] using h
  apply h'.congr'
  filter_upwards with index
  rw [cosineSumScale_displacement_two]

theorem tendsto_normalizedRankFourGeometricKernel
    (coordinates : Fin 2 → ℝ) :
    Tendsto (fun index => normalizedRankFourGeometricKernel coordinates index)
      atTop (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) / 4))) := by
  have hlog := tendsto_log_cosineSum_microscopic_four coordinates
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hscale := tendsto_cosineSumScale coordinates
  have hpositive : ∀ᶠ index : ℕ in atTop,
      0 < cosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 0 (by norm_num)
  have hsucc : Tendsto (fun index : ℕ =>
      (cosineSumScale coordinates index / 4) ^ (index + 1))
      atTop (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) / 4))) := by
    apply hexp.congr'
    filter_upwards [hpositive] with index hindex
    have hratio : 0 < cosineSumScale coordinates index / 4 := by positivity
    simp only [Function.comp_apply]
    rw [← Real.exp_log hratio, ← Real.exp_nat_mul,
      Real.log_div hindex.ne' (by norm_num : (4 : ℝ) ≠ 0)]
    push_cast
    rfl
  have hratio : Tendsto (fun index => cosineSumScale coordinates index / 4)
      atTop (nhds 1) := by
    have h := (tendsto_cosineSumScale coordinates).div_const 4
    norm_num at h ⊢
    exact h
  have hproduct := hsucc.mul (hratio.inv₀ (by norm_num))
  rw [inv_one, mul_one] at hproduct
  unfold normalizedRankFourGeometricKernel
  apply hproduct.congr'
  filter_upwards [hpositive] with index hindex
  have hne : cosineSumScale coordinates index / 4 ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

noncomputable def rankFourGeometricGaussianCoefficient : ℝ :=
  1 / (2 * Real.pi ^ 2)

theorem rankFourGeometricGaussianCoefficient_pos :
    0 < rankFourGeometricGaussianCoefficient := by
  unfold rankFourGeometricGaussianCoefficient
  positivity

theorem normalizedRankFourGeometricKernel_nonneg
    {index : ℕ} {coordinates : Fin 2 → ℝ}
    (hscale : 0 ≤ cosineSumScale coordinates index) :
    0 ≤ normalizedRankFourGeometricKernel coordinates index := by
  unfold normalizedRankFourGeometricKernel
  exact pow_nonneg (div_nonneg hscale (by norm_num)) _

theorem normalizedRankFourGeometricKernel_le_gaussian
    (index : ℕ) (coordinates : Fin 2 → ℝ)
    (hcube : coordinates ∈ positiveScaledCube 2 index)
    (hscaleMid : cosineScaleMidpoint 2 ≤ cosineSumScale coordinates index) :
    normalizedRankFourGeometricKernel coordinates index ≤
      Real.exp 1 * Real.exp (-rankFourGeometricGaussianCoefficient *
        ∑ coordinate, coordinates coordinate ^ 2) := by
  have hscalePos : 0 < cosineSumScale coordinates index :=
    (cosineScaleMidpoint_gt_two (dimension := 2) (by norm_num)).trans_le
      hscaleMid |>.trans' zero_lt_two
  rcases index with _ | index
  · unfold normalizedRankFourGeometricKernel
    rw [pow_zero]
    have hsquares : (∑ coordinate, coordinates coordinate ^ 2) ≤
        2 * Real.pi ^ 2 := by
      simpa using sum_sq_le_two_pi_sq_of_scaledCube hcube
    have hproduct : rankFourGeometricGaussianCoefficient *
        (∑ coordinate, coordinates coordinate ^ 2) ≤ 1 := by
      calc
        _ ≤ rankFourGeometricGaussianCoefficient * (2 * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left hsquares
            rankFourGeometricGaussianCoefficient_pos.le
        _ = 1 := by
          unfold rankFourGeometricGaussianCoefficient
          field_simp [Real.pi_ne_zero]
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (1 +
          (-rankFourGeometricGaussianCoefficient *
            ∑ coordinate, coordinates coordinate ^ 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 1 * Real.exp
          (-rankFourGeometricGaussianCoefficient *
            ∑ coordinate, coordinates coordinate ^ 2) := by
        rw [Real.exp_add]
  · let current := cosineSumScale coordinates (index + 1)
    let ratio := current / 4
    let squares : ℝ := ∑ coordinate, coordinates coordinate ^ 2
    have hratioPos : 0 < ratio := by
      dsimp only [ratio, current]
      positivity
    have hlog := Real.log_le_sub_one_of_pos hratioPos
    have hcoordinate : ∀ coordinate,
        |coordinates coordinate| ≤
          Real.pi * Real.sqrt (((index + 1 : ℕ) : ℝ) + 1) := by
      intro coordinate
      have hmem := hcube coordinate (Set.mem_univ coordinate)
      rw [abs_of_pos hmem.1]
      exact hmem.2
    have hdeficit := cosineSumScale_le_quadratic coordinates hcoordinate
    have hsquaresNonneg : 0 ≤ squares := by positivity
    have hsquaresEq : squares = coordinates 0 ^ 2 + coordinates 1 ^ 2 := by
      dsimp only [squares]
      rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
      simp
    have hcurrent : current - 4 ≤
        -(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares := by
      dsimp only [current]
      rw [hsquaresEq]
      rw [show (index + 2 : ℝ) = (((index + 1 : ℕ) : ℝ) + 1) by
        push_cast
        ring]
      norm_num at hdeficit ⊢
      linarith
    have hratioSub : ratio - 1 = (current - 4) / 4 := by
      dsimp only [ratio]
      ring
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ index + 1 by positivity)
    rw [hratioSub] at hmul
    have hindexRatio : (1 / 2 : ℝ) ≤
        (index + 1 : ℝ) / (index + 2 : ℝ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hscaledCurrent :
        (index + 1 : ℝ) * ((current - 4) / 4) ≤
          -(1 / Real.pi ^ 2) *
            ((index + 1 : ℝ) / (index + 2 : ℝ)) * squares := by
      calc
        (index + 1 : ℝ) * ((current - 4) / 4) =
            ((index + 1 : ℝ) / 4) * (current - 4) := by ring
        _ ≤ ((index + 1 : ℝ) / 4) *
            (-(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares) :=
          mul_le_mul_of_nonneg_left hcurrent (by positivity)
        _ = -(1 / Real.pi ^ 2) *
            ((index + 1 : ℝ) / (index + 2 : ℝ)) * squares := by
          field_simp [Real.pi_ne_zero]
    have hcoefficient :
        -(1 / Real.pi ^ 2) *
            ((index + 1 : ℝ) / (index + 2 : ℝ)) ≤
          -(1 / (2 * Real.pi ^ 2)) := by
      have h := mul_le_mul_of_nonpos_left hindexRatio
        (neg_nonpos.mpr (show 0 ≤ 1 / Real.pi ^ 2 by positivity))
      calc
        _ ≤ -(1 / Real.pi ^ 2) * (1 / 2) := h
        _ = _ := by field_simp [Real.pi_ne_zero]
    have hweighted := mul_le_mul_of_nonneg_right hcoefficient hsquaresNonneg
    have hscaledLog :
        (index + 1 : ℝ) * Real.log ratio ≤
          -rankFourGeometricGaussianCoefficient * squares := by
      unfold rankFourGeometricGaussianCoefficient
      exact hmul.trans (hscaledCurrent.trans hweighted)
    unfold normalizedRankFourGeometricKernel
    change ratio ^ (index + 1) ≤ _
    calc
      ratio ^ (index + 1) =
          Real.exp ((index + 1 : ℝ) * Real.log ratio) := by
        have hcast : (index + 1 : ℝ) = (((index + 1 : ℕ) : ℕ) : ℝ) := by
          norm_num
        rw [hcast, Real.exp_nat_mul, Real.exp_log hratioPos]
      _ ≤ Real.exp (-rankFourGeometricGaussianCoefficient * squares) :=
        Real.exp_le_exp.mpr hscaledLog
      _ ≤ Real.exp 1 *
          Real.exp (-rankFourGeometricGaussianCoefficient * squares) := by
        exact le_mul_of_one_le_left (Real.exp_pos _).le
          (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num))

noncomputable def rankFourGeometricLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 2 → ℝ) : ℝ :=
  (positiveLocalScaledDomain 2 index).indicator
    (fun coordinates => (1 / Real.pi) ^ 2 *
      normalizedRankFourGeometricKernel coordinates index *
      evenScaledWeylWeight 2 index coordinates) coordinates

noncomputable def rankFourGeometricLocalLimitIntegrand
    (coordinates : Fin 2 → ℝ) : ℝ :=
  positiveOrthant.indicator (fun coordinates =>
    (1 / Real.pi) ^ 2 *
      Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) / 4) *
      evenLimitWeylWeight 2 coordinates) coordinates

noncomputable def rankFourGeometricAngleLocalIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (anglePositiveLocalDomain 2).indicator (fun angles =>
    (1 / Real.pi) ^ 2 * (cosineCubeScale angles / 4) ^ index *
      evenWeylAngleWeight 2 angles) angles

noncomputable def rankFourGeometricAngleLocalIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFourGeometricAngleLocalIntegrand index angles

theorem tendsto_rankFourGeometricLocalRescaledIntegrand
    (coordinates : Fin 2 → ℝ) :
    Tendsto (fun index => rankFourGeometricLocalRescaledIntegrand index coordinates)
      atTop (nhds (rankFourGeometricLocalLimitIntegrand coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain
      (dimension := 2) (by norm_num) coordinates horthant
    have hkernel := tendsto_normalizedRankFourGeometricKernel coordinates
    have hweight := tendsto_evenScaledWeylWeight 2 coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 2)
        atTop (nhds ((1 / Real.pi) ^ 2)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    rw [rankFourGeometricLocalLimitIntegrand, Set.indicator_of_mem horthant]
    apply hproduct.congr'
    filter_upwards [hlocal] with index hindex
    rw [rankFourGeometricLocalRescaledIntegrand, Set.indicator_of_mem hindex]
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
        rankFourGeometricLocalRescaledIntegrand index coordinates) =
        fun _ => 0 by
      funext index
      rw [rankFourGeometricLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)],
      rankFourGeometricLocalLimitIntegrand,
      Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

theorem rankFourGeometricAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    rankFourGeometricAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankFourGeometricLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 2 := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain 2 index
  · rw [rankFourGeometricAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff 2 index coordinates).2 hdomain),
      rankFourGeometricLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt, rankFourEvenAngleWeight_inverseSqrt]
    unfold normalizedRankFourGeometricKernel
    ring
  · rw [rankFourGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff 2 index coordinates).1 hdomain),
      rankFourGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem stronglyMeasurable_rankFourGeometricAngleLocalIntegrand (index : ℕ) :
    StronglyMeasurable (rankFourGeometricAngleLocalIntegrand index) := by
  unfold rankFourGeometricAngleLocalIntegrand
  have hpower : Continuous (fun angles : Fin 2 → ℝ =>
      (cosineCubeScale angles / 4) ^ index) :=
    ((continuous_cosineCubeScale 2).div_const 4).pow index
  exact (((continuous_const.mul hpower).mul
    (continuous_evenWeylAngleWeight 2)).stronglyMeasurable.indicator
      (measurableSet_anglePositiveLocalDomain 2))

theorem rankFourGeometricLocalScalingIntegral_identity (index : ℕ) :
    (index + 1 : ℝ) ^ 3 * rankFourGeometricAngleLocalIntegral index =
      ∫ coordinates : Fin 2 → ℝ,
        rankFourGeometricLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 2
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankFourGeometricAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 2 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 2 _).aemeasurable
      (stronglyMeasurable_rankFourGeometricAngleLocalIntegrand index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 2)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ 2 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold rankFourGeometricAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 2 → ℝ =>
      rankFourGeometricAngleLocalIntegrand index
        (coordinateScalarLinearMap 2
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates => rankFourGeometricLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 2 by
    funext coordinates
    exact rankFourGeometricAngleLocalIntegrand_inverseSqrt index coordinates] at hmap
  rw [integral_div] at hmap
  have hsqrt : Real.sqrt (index + 1 : ℝ) ^ 2 = index + 1 :=
    Real.sq_sqrt (by positivity)
  have hnonzero : (index + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  rw [hsqrt] at hmap
  field_simp [hnonzero] at hmap ⊢
  exact hmap

end FibonacciRibbonKernel
