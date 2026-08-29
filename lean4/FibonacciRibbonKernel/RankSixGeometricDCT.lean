import FibonacciRibbonKernel.RankSixEvenFullLimit

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable def normalizedRankSixGeometricKernel
    (coordinates : Fin 3 → ℝ) (index : ℕ) : ℝ :=
  (cosineSumScale coordinates index / 6) ^ index

theorem cosineSumScale_displacement_three
    (coordinates : Fin 3 → ℝ) (index : ℕ) :
    cosineSumScale coordinates index =
      6 + cosineSumDisplacement coordinates index / (index + 1 : ℝ) := by
  unfold cosineSumDisplacement
  have hn : (index + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  ring

theorem tendsto_log_cosineSum_microscopic_six
    (coordinates : Fin 3 → ℝ) :
    Tendsto (fun index : ℕ => (index + 1 : ℝ) *
      (Real.log (cosineSumScale coordinates index) - Real.log 6))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) / 6)) := by
  have hd : HasDerivAt Real.log (1 / 6) 6 := by
    simpa using Real.hasDerivAt_log (by norm_num : (6 : ℝ) ≠ 0)
  have h := tendsto_variable_microscopic_derivative hd
    (tendsto_cosineSumDisplacement coordinates)
  have h' : Tendsto (fun index : ℕ => (index + 1 : ℝ) *
      (Real.log (6 + cosineSumDisplacement coordinates index /
        (index + 1 : ℝ)) - Real.log 6))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) / 6)) := by
    simpa only [div_eq_mul_inv, one_mul] using h
  apply h'.congr'
  filter_upwards with index
  rw [cosineSumScale_displacement_three]

theorem tendsto_normalizedRankSixGeometricKernel
    (coordinates : Fin 3 → ℝ) :
    Tendsto (fun index => normalizedRankSixGeometricKernel coordinates index)
      atTop (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) / 6))) := by
  have hl := tendsto_log_cosineSum_microscopic_six coordinates
  have he := Real.continuous_exp.continuousAt.tendsto.comp hl
  have hs := tendsto_cosineSumScale coordinates
  have hp : ∀ᶠ index : ℕ in atTop, 0 < cosineSumScale coordinates index :=
    (tendsto_order.1 hs).1 0 (by norm_num)
  have hsucc : Tendsto (fun index : ℕ =>
      (cosineSumScale coordinates index / 6) ^ (index + 1))
      atTop (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) / 6))) := by
    apply he.congr'
    filter_upwards [hp] with index hi
    have hr : 0 < cosineSumScale coordinates index / 6 := by positivity
    simp only [Function.comp_apply]
    rw [← Real.exp_log hr, ← Real.exp_nat_mul,
      Real.log_div hi.ne' (by norm_num : (6 : ℝ) ≠ 0)]
    push_cast
    rfl
  have hr : Tendsto (fun index => cosineSumScale coordinates index / 6)
      atTop (nhds 1) := by
    have h := (tendsto_cosineSumScale coordinates).div_const 6
    norm_num at h ⊢
    exact h
  have hprod := hsucc.mul (hr.inv₀ (by norm_num))
  rw [inv_one, mul_one] at hprod
  unfold normalizedRankSixGeometricKernel
  apply hprod.congr'
  filter_upwards [hp] with index hi
  have hn : cosineSumScale coordinates index / 6 ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

noncomputable def rankSixGeometricGaussianCoefficient : ℝ :=
  1 / (3 * Real.pi ^ 2)

theorem rankSixGeometricGaussianCoefficient_pos :
    0 < rankSixGeometricGaussianCoefficient := by
  unfold rankSixGeometricGaussianCoefficient
  positivity

theorem sum_sq_le_three_pi_sq_of_scaledCube
    {index : ℕ} {coordinates : Fin 3 → ℝ}
    (hc : coordinates ∈ positiveScaledCube 3 index) :
    ∑ coordinate, coordinates coordinate ^ 2 ≤
      3 * Real.pi ^ 2 * (index + 1 : ℝ) := by
  rw [show (∑ coordinate : Fin 3, coordinates coordinate ^ 2) =
      coordinates 0 ^ 2 + coordinates 1 ^ 2 + coordinates 2 ^ 2 by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))),
      Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
      Finset.sum_singleton]
    ring]
  have h0 := (hc 0 (Set.mem_univ 0)).2
  have h1 := (hc 1 (Set.mem_univ 1)).2
  have h2 := (hc 2 (Set.mem_univ 2)).2
  have h0p := (hc 0 (Set.mem_univ 0)).1.le
  have h1p := (hc 1 (Set.mem_univ 1)).1.le
  have h2p := (hc 2 (Set.mem_univ 2)).1.le
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ index + 1 by positivity)
  nlinarith [sq_le_sq₀ h0p (by positivity) |>.2 h0,
    sq_le_sq₀ h1p (by positivity) |>.2 h1,
    sq_le_sq₀ h2p (by positivity) |>.2 h2]

theorem normalizedRankSixGeometricKernel_nonneg
    {index : ℕ} {coordinates : Fin 3 → ℝ}
    (hs : 0 ≤ cosineSumScale coordinates index) :
    0 ≤ normalizedRankSixGeometricKernel coordinates index := by
  unfold normalizedRankSixGeometricKernel
  exact pow_nonneg (div_nonneg hs (by norm_num)) _

theorem normalizedRankSixGeometricKernel_le_gaussian
    (index : ℕ) (coordinates : Fin 3 → ℝ)
    (hc : coordinates ∈ positiveScaledCube 3 index)
    (hm : cosineScaleMidpoint 3 ≤ cosineSumScale coordinates index) :
    normalizedRankSixGeometricKernel coordinates index ≤
      Real.exp 1 * Real.exp (-rankSixGeometricGaussianCoefficient *
        ∑ coordinate, coordinates coordinate ^ 2) := by
  have hsp : 0 < cosineSumScale coordinates index :=
    (cosineScaleMidpoint_gt_two (dimension := 3) (by norm_num)).trans_le hm
      |>.trans' zero_lt_two
  rcases index with _ | index
  · unfold normalizedRankSixGeometricKernel
    rw [pow_zero]
    have hs : (∑ coordinate, coordinates coordinate ^ 2) ≤
        3 * Real.pi ^ 2 := by
      simpa using sum_sq_le_three_pi_sq_of_scaledCube hc
    have hp : rankSixGeometricGaussianCoefficient *
        (∑ coordinate, coordinates coordinate ^ 2) ≤ 1 := by
      calc
        _ ≤ rankSixGeometricGaussianCoefficient * (3 * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left hs rankSixGeometricGaussianCoefficient_pos.le
        _ = 1 := by
          unfold rankSixGeometricGaussianCoefficient
          field_simp [Real.pi_ne_zero]
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (1 + (-rankSixGeometricGaussianCoefficient *
          ∑ coordinate, coordinates coordinate ^ 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add]
  · let current := cosineSumScale coordinates (index + 1)
    let ratio := current / 6
    let squares : ℝ := ∑ coordinate, coordinates coordinate ^ 2
    have hrp : 0 < ratio := by dsimp only [ratio, current]; positivity
    have hl := Real.log_le_sub_one_of_pos hrp
    have hcoord : ∀ coordinate,
        |coordinates coordinate| ≤
          Real.pi * Real.sqrt (((index + 1 : ℕ) : ℝ) + 1) := by
      intro coordinate
      have h := hc coordinate (Set.mem_univ coordinate)
      rw [abs_of_pos h.1]
      exact h.2
    have hd := cosineSumScale_le_quadratic coordinates hcoord
    have hsn : 0 ≤ squares := by positivity
    have hcur : current - 6 ≤
        -(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares := by
      dsimp only [current, squares]
      rw [show (index + 2 : ℝ) = (((index + 1 : ℕ) : ℝ) + 1) by
        push_cast
        ring]
      norm_num at hd ⊢
      linarith
    have hrs : ratio - 1 = (current - 6) / 6 := by
      dsimp only [ratio]
      ring
    have hmul := mul_le_mul_of_nonneg_left hl
      (show (0 : ℝ) ≤ index + 1 by positivity)
    rw [hrs] at hmul
    have hir : (1 / 2 : ℝ) ≤ (index + 1 : ℝ) / (index + 2 : ℝ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hsc : (index + 1 : ℝ) * ((current - 6) / 6) ≤
        -(2 / (3 * Real.pi ^ 2)) *
          ((index + 1 : ℝ) / (index + 2 : ℝ)) * squares := by
      calc
        _ = ((index + 1 : ℝ) / 6) * (current - 6) := by ring
        _ ≤ ((index + 1 : ℝ) / 6) *
            (-(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares) :=
          mul_le_mul_of_nonneg_left hcur (by positivity)
        _ = _ := by
          field_simp [Real.pi_ne_zero]
          ring
    have hcoef : -(2 / (3 * Real.pi ^ 2)) *
        ((index + 1 : ℝ) / (index + 2 : ℝ)) ≤
        -(1 / (3 * Real.pi ^ 2)) := by
      have h := mul_le_mul_of_nonpos_left hir
        (neg_nonpos.mpr (show 0 ≤ 2 / (3 * Real.pi ^ 2) by positivity))
      calc
        _ ≤ -(2 / (3 * Real.pi ^ 2)) * (1 / 2) := h
        _ = _ := by field_simp [Real.pi_ne_zero]
    have hw := mul_le_mul_of_nonneg_right hcoef hsn
    have hlog : (index + 1 : ℝ) * Real.log ratio ≤
        -rankSixGeometricGaussianCoefficient * squares := by
      unfold rankSixGeometricGaussianCoefficient
      exact hmul.trans (hsc.trans hw)
    unfold normalizedRankSixGeometricKernel
    change ratio ^ (index + 1) ≤ _
    calc
      ratio ^ (index + 1) = Real.exp ((index + 1 : ℝ) * Real.log ratio) := by
        have hcst : (index + 1 : ℝ) = (((index + 1 : ℕ) : ℕ) : ℝ) := by
          norm_num
        rw [hcst, Real.exp_nat_mul, Real.exp_log hrp]
      _ ≤ Real.exp (-rankSixGeometricGaussianCoefficient * squares) :=
        Real.exp_le_exp.mpr hlog
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le (by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num))

noncomputable def rankSixGeometricLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 3 → ℝ) : ℝ :=
  (positiveLocalScaledDomain 3 index).indicator (fun coordinates =>
    (1 / Real.pi) ^ 3 * normalizedRankSixGeometricKernel coordinates index *
      evenScaledWeylWeight 3 index coordinates) coordinates

noncomputable def rankSixGeometricLocalLimitIntegrand
    (coordinates : Fin 3 → ℝ) : ℝ :=
  positiveOrthant.indicator (fun coordinates =>
    (1 / Real.pi) ^ 3 *
      Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) / 6) *
      evenLimitWeylWeight 3 coordinates) coordinates

noncomputable def rankSixGeometricAngleLocalIntegrand
    (index : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  (anglePositiveLocalDomain 3).indicator (fun angles =>
    (1 / Real.pi) ^ 3 * (cosineCubeScale angles / 6) ^ index *
      evenWeylAngleWeight 3 angles) angles

noncomputable def rankSixGeometricAngleLocalIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ, rankSixGeometricAngleLocalIntegrand index angles

theorem tendsto_rankSixGeometricLocalRescaledIntegrand
    (coordinates : Fin 3 → ℝ) :
    Tendsto (fun index => rankSixGeometricLocalRescaledIntegrand index coordinates)
      atTop (nhds (rankSixGeometricLocalLimitIntegrand coordinates)) := by
  by_cases ho : coordinates ∈ positiveOrthant
  · have hl := eventually_mem_positiveLocalScaledDomain
      (dimension := 3) (by norm_num) coordinates ho
    have hk := tendsto_normalizedRankSixGeometricKernel coordinates
    have hw := tendsto_evenScaledWeylWeight 3 coordinates
    have hc : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 3)
        atTop (nhds ((1 / Real.pi) ^ 3)) := tendsto_const_nhds
    have hp := (hc.mul hk).mul hw
    rw [rankSixGeometricLocalLimitIntegrand, Set.indicator_of_mem ho]
    apply hp.congr'
    filter_upwards [hl] with index hi
    rw [rankSixGeometricLocalRescaledIntegrand, Set.indicator_of_mem hi]
  · have hn : ∃ coordinate : Fin 3, coordinates coordinate ≤ 0 := by
      by_contra h
      push Not at h
      exact ho fun coordinate _ => h coordinate
    obtain ⟨coordinate, hc⟩ := hn
    have hout : ∀ index, coordinates ∉ positiveLocalScaledDomain 3 index := by
      intro index hd
      linarith [(hd.1 coordinate (Set.mem_univ coordinate)).1]
    rw [show (fun index : ℕ =>
        rankSixGeometricLocalRescaledIntegrand index coordinates) = fun _ => 0 by
      funext index
      rw [rankSixGeometricLocalRescaledIntegrand,
        Set.indicator_of_notMem (hout index)],
      rankSixGeometricLocalLimitIntegrand, Set.indicator_of_notMem ho]
    exact tendsto_const_nhds

noncomputable def rankSixGeometricCoordinateDominating (value : ℝ) : ℝ :=
  (1 + value ^ 2) ^ 4 *
    Real.exp (-rankSixGeometricGaussianCoefficient * value ^ 2)

noncomputable def rankSixGeometricLocalDominating
    (coordinates : Fin 3 → ℝ) : ℝ :=
  (8 * Real.exp 1 * (1 / Real.pi) ^ 3) *
    ∏ coordinate, rankSixGeometricCoordinateDominating (coordinates coordinate)

theorem integrable_rankSixGeometricCoordinateDominating :
    Integrable rankSixGeometricCoordinateDominating := by
  rw [show rankSixGeometricCoordinateDominating = fun value : ℝ =>
      ∑ index ∈ Finset.range 5, (Nat.choose 4 index : ℝ) *
        (|value| ^ (2 * (4 - index)) *
          Real.exp (-rankSixGeometricGaussianCoefficient * value ^ 2)) by
    funext value
    unfold rankSixGeometricCoordinateDominating
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index hi
    rw [Finset.mem_range] at hi
    rw [show (1 : ℝ) ^ index = 1 by simp, one_mul]
    have ha : |value| ^ (2 * (4 - index)) =
        (value ^ 2) ^ (4 - index) := by
      calc
        _ = (|value| ^ 2) ^ (4 - index) := by rw [pow_mul]
        _ = _ := by rw [sq_abs]
    rw [ha]
    ring]
  apply integrable_finsetSum
  intro index hi
  exact (integrable_abs_pow_mul_exp_neg_mul_sq
    (2 * (4 - index)) rankSixGeometricGaussianCoefficient_pos).const_mul _

theorem integrable_rankSixGeometricLocalDominating :
    Integrable rankSixGeometricLocalDominating := by
  unfold rankSixGeometricLocalDominating
  rw [volume_pi]
  exact (Integrable.fintype_prod fun _ : Fin 3 =>
    integrable_rankSixGeometricCoordinateDominating).const_mul _

theorem aestronglyMeasurable_rankSixGeometricLocalRescaled (index : ℕ) :
    AEStronglyMeasurable (rankSixGeometricLocalRescaledIntegrand index) := by
  have hk : Continuous (normalizedRankSixGeometricKernel · index) := by
    unfold normalizedRankSixGeometricKernel
    exact ((continuous_cosineSumScale 3 index).div_const 6).pow index
  unfold rankSixGeometricLocalRescaledIntegrand
  exact (((continuous_const.mul hk).mul (by
    unfold evenScaledWeylWeight
    exact (continuous_scaledCosineVandermondeWeight 3 index).mul
      (continuous_allPlusScaledWeight 3 index))).stronglyMeasurable.indicator
    (measurableSet_positiveLocalScaledDomain 3 index)).aestronglyMeasurable

theorem norm_rankSixGeometricLocalRescaled_le
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    ‖rankSixGeometricLocalRescaledIntegrand index coordinates‖ ≤
      rankSixGeometricLocalDominating coordinates := by
  by_cases hd : coordinates ∈ positiveLocalScaledDomain 3 index
  · rw [rankSixGeometricLocalRescaledIntegrand, Set.indicator_of_mem hd,
      Real.norm_eq_abs, abs_of_nonneg]
    · have hk := normalizedRankSixGeometricKernel_le_gaussian
        index coordinates hd.1 hd.2
      have hw := evenScaledWeylWeight_three_le_polynomial index coordinates
      have hscale : 0 ≤ cosineSumScale coordinates index :=
        (by norm_num : (0 : ℝ) ≤ 2).trans
          ((cosineScaleMidpoint_gt_two
            (dimension := 3) (by norm_num)).le.trans hd.2)
      have hkn := normalizedRankSixGeometricKernel_nonneg
        (index := index) (coordinates := coordinates) hscale
      have hwn : 0 ≤ evenScaledWeylWeight 3 index coordinates := by
        unfold evenScaledWeylWeight scaledCosineVandermondeWeight
        exact mul_nonneg (by positivity) (allPlusScaledWeight_nonneg 3 index coordinates)
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
        (by unfold evenScaledWeylWeight scaledCosineVandermondeWeight
            exact mul_nonneg (by positivity)
              (allPlusScaledWeight_nonneg 3 index coordinates))
  · rw [rankSixGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hd, norm_zero]
    unfold rankSixGeometricLocalDominating rankSixGeometricCoordinateDominating
    positivity

theorem rankSixGeometricAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    rankSixGeometricAngleLocalIntegrand index
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankSixGeometricLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 6 := by
  by_cases hd : coordinates ∈ positiveLocalScaledDomain 3 index
  · rw [rankSixGeometricAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff 3 index coordinates).2 hd),
      rankSixGeometricLocalRescaledIntegrand, Set.indicator_of_mem hd,
      cosineCubeScale_inverseSqrt, rankSixEvenAngleWeight_inverseSqrt]
    unfold normalizedRankSixGeometricKernel
    ring
  · rw [rankSixGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff 3 index coordinates).1 hd),
      rankSixGeometricLocalRescaledIntegrand, Set.indicator_of_notMem hd, zero_div]

theorem stronglyMeasurable_rankSixGeometricAngleLocalIntegrand (index : ℕ) :
    StronglyMeasurable (rankSixGeometricAngleLocalIntegrand index) := by
  unfold rankSixGeometricAngleLocalIntegrand
  have hp : Continuous (fun angles : Fin 3 → ℝ =>
      (cosineCubeScale angles / 6) ^ index) :=
    ((continuous_cosineCubeScale 3).div_const 6).pow index
  exact (((continuous_const.mul hp).mul
    (continuous_evenWeylAngleWeight 3)).stronglyMeasurable.indicator
      (measurableSet_anglePositiveLocalDomain 3))

theorem rankSixGeometricLocalScalingIntegral_identity (index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixGeometricAngleLocalIntegral index =
      ∫ coordinates : Fin 3 → ℝ,
        rankSixGeometricLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 3
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankSixGeometricAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 3 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 3 _).aemeasurable
      (stronglyMeasurable_rankSixGeometricAngleLocalIntegrand index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have ht : (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 3)).toReal =
      Real.sqrt (index + 1 : ℝ) ^ 3 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [ht, smul_eq_mul] at hmap
  unfold rankSixGeometricAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 3 → ℝ =>
      rankSixGeometricAngleLocalIntegrand index
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates => rankSixGeometricLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 6 by
    funext coordinates
    exact rankSixGeometricAngleLocalIntegrand_inverseSqrt index coordinates] at hmap
  rw [integral_div] at hmap
  have hn : (index + 1 : ℝ) ^ 6 ≠ 0 := by positivity
  field_simp [hn] at hmap ⊢
  exact hmap

theorem tendsto_rankSixGeometricAngleLocalIntegral :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixGeometricAngleLocalIntegral index)
      atTop (nhds (∫ coordinates : Fin 3 → ℝ,
        rankSixGeometricLocalLimitIntegrand coordinates)) := by
  rw [show (fun index : ℕ => Real.sqrt (index + 1 : ℝ) ^ 3 *
      (index + 1 : ℝ) ^ 6 * rankSixGeometricAngleLocalIntegral index) =
    fun index => ∫ coordinates : Fin 3 → ℝ,
      rankSixGeometricLocalRescaledIntegrand index coordinates by
    funext index
    exact rankSixGeometricLocalScalingIntegral_identity index]
  exact tendsto_integral_of_dominated_convergence rankSixGeometricLocalDominating
    aestronglyMeasurable_rankSixGeometricLocalRescaled
    integrable_rankSixGeometricLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankSixGeometricLocalRescaled_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankSixGeometricLocalRescaledIntegrand coordinates)

end FibonacciRibbonKernel
