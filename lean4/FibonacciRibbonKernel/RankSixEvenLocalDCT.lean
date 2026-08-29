import FibonacciRibbonKernel.RankSixEvenWeylCount

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable def rankSixEvenLocalRescaledIntegrand
    (index : ℕ) (coordinates : Fin 3 → ℝ) : ℝ :=
  (positiveLocalScaledDomain 3 index).indicator (fun coordinates =>
    (1 / Real.pi) ^ 3 * normalizedFibonacciCosineKernel coordinates index *
      evenScaledWeylWeight 3 index coordinates) coordinates

noncomputable def rankSixEvenLocalLimitIntegrand
    (coordinates : Fin 3 → ℝ) : ℝ :=
  positiveOrthant.indicator (fun coordinates =>
    (1 / Real.pi) ^ 3 *
      Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) /
        Real.sqrt (32 : ℝ)) * evenLimitWeylWeight 3 coordinates) coordinates

noncomputable def rankSixEvenAngleLocalIntegrand
    (index : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  (anglePositiveLocalDomain 3).indicator (fun angles =>
    (1 / Real.pi) ^ 3 *
      (fibonacciScaleKernel (cosineCubeScale angles) index /
        (largeScalePreimage 6 ^ (index + 1) / Real.sqrt 32)) *
      evenWeylAngleWeight 3 angles) angles

noncomputable def rankSixEvenAngleLocalIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 3 → ℝ, rankSixEvenAngleLocalIntegrand index angles

theorem tendsto_rankSixEvenLocalRescaledIntegrand
    (coordinates : Fin 3 → ℝ) :
    Tendsto (fun index => rankSixEvenLocalRescaledIntegrand index coordinates)
      atTop (nhds (rankSixEvenLocalLimitIntegrand coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain
      (dimension := 3) (by norm_num) coordinates horthant
    have hk := tendsto_normalizedFibonacciCosineKernel
      (dimension := 3) (by norm_num) coordinates
    have hw := tendsto_evenScaledWeylWeight 3 coordinates
    have hc : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ 3)
        atTop (nhds ((1 / Real.pi) ^ 3)) := tendsto_const_nhds
    have hp := (hc.mul hk).mul hw
    rw [show Real.sqrt ((2 * (3 : ℕ) : ℝ) ^ 2 - 4) =
      Real.sqrt (32 : ℝ) by norm_num] at hp
    rw [rankSixEvenLocalLimitIntegrand, Set.indicator_of_mem horthant]
    apply hp.congr'
    filter_upwards [hlocal] with index hi
    rw [rankSixEvenLocalRescaledIntegrand, Set.indicator_of_mem hi]
  · have hnot : ∃ coordinate : Fin 3, coordinates coordinate ≤ 0 := by
      by_contra hn
      push Not at hn
      exact horthant fun coordinate _ => hn coordinate
    obtain ⟨coordinate, hc⟩ := hnot
    have hout : ∀ index, coordinates ∉ positiveLocalScaledDomain 3 index := by
      intro index hd
      linarith [(hd.1 coordinate (Set.mem_univ coordinate)).1]
    rw [show (fun index : ℕ =>
        rankSixEvenLocalRescaledIntegrand index coordinates) = fun _ => 0 by
      funext index
      rw [rankSixEvenLocalRescaledIntegrand, Set.indicator_of_notMem (hout index)] ,
      rankSixEvenLocalLimitIntegrand, Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

theorem rankSixEvenAngleWeight_inverseSqrt
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    evenWeylAngleWeight 3
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      evenScaledWeylWeight 3 index coordinates / (index + 1 : ℝ) ^ 6 := by
  have hs := evenScaledWeylWeight_eq 3 index coordinates
  norm_num at hs
  rw [coordinateScalarLinearMap_apply]
  simp only [one_div]
  have hn : (index + 1 : ℝ) ^ 6 ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  rw [hs]
  ring

theorem rankSixEvenAngleLocalIntegrand_inverseSqrt
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    rankSixEvenAngleLocalIntegrand index
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      rankSixEvenLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 6 := by
  by_cases hd : coordinates ∈ positiveLocalScaledDomain 3 index
  · rw [rankSixEvenAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff 3 index coordinates).2 hd),
      rankSixEvenLocalRescaledIntegrand, Set.indicator_of_mem hd,
      cosineCubeScale_inverseSqrt, rankSixEvenAngleWeight_inverseSqrt]
    unfold normalizedFibonacciCosineKernel
    norm_num
    ring
  · rw [rankSixEvenAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff 3 index coordinates).1 hd),
      rankSixEvenLocalRescaledIntegrand, Set.indicator_of_notMem hd, zero_div]

theorem stronglyMeasurable_rankSixEvenAngleLocalIntegrand (index : ℕ) :
    StronglyMeasurable (rankSixEvenAngleLocalIntegrand index) := by
  unfold rankSixEvenAngleLocalIntegrand
  exact (((continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale 3)).div_const _)).mul
        (continuous_evenWeylAngleWeight 3)).stronglyMeasurable.indicator
      (measurableSet_anglePositiveLocalDomain 3))

theorem rankSixEvenLocalScalingIntegral_identity (index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenAngleLocalIntegral index =
      ∫ coordinates : Fin 3 → ℝ,
        rankSixEvenLocalRescaledIntegrand index coordinates := by
  let scaleMap := coordinateScalarLinearMap 3
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := rankSixEvenAngleLocalIntegrand index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin 3 → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 3 _).aemeasurable
      (stronglyMeasurable_rankSixEvenAngleLocalIntegrand index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have ht :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ 3)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ 3 := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [ht, smul_eq_mul] at hmap
  unfold rankSixEvenAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin 3 → ℝ =>
      rankSixEvenAngleLocalIntegrand index
        (coordinateScalarLinearMap 3
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates => rankSixEvenLocalRescaledIntegrand index coordinates /
        (index + 1 : ℝ) ^ 6 by
    funext coordinates
    exact rankSixEvenAngleLocalIntegrand_inverseSqrt index coordinates] at hmap
  rw [integral_div] at hmap
  have hn : (index + 1 : ℝ) ^ 6 ≠ 0 := by positivity
  field_simp [hn] at hmap ⊢
  exact hmap

noncomputable def rankSixWeylPolynomial (coordinates : Fin 3 → ℝ) : ℝ :=
  8 * ((coordinates 0 ^ 2 + coordinates 1 ^ 2) / 2) ^ 2 *
    ((coordinates 0 ^ 2 + coordinates 2 ^ 2) / 2) ^ 2 *
    ((coordinates 1 ^ 2 + coordinates 2 ^ 2) / 2) ^ 2

theorem scaledCosineVandermondeWeight_three
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    scaledCosineVandermondeWeight 3 index coordinates =
      ((index + 1 : ℝ) *
        (Real.cos (coordinates 1 / Real.sqrt (index + 1 : ℝ)) -
          Real.cos (coordinates 0 / Real.sqrt (index + 1 : ℝ)))) ^ 2 *
      ((index + 1 : ℝ) *
        (Real.cos (coordinates 2 / Real.sqrt (index + 1 : ℝ)) -
          Real.cos (coordinates 0 / Real.sqrt (index + 1 : ℝ)))) ^ 2 *
      ((index + 1 : ℝ) *
        (Real.cos (coordinates 2 / Real.sqrt (index + 1 : ℝ)) -
          Real.cos (coordinates 1 / Real.sqrt (index + 1 : ℝ)))) ^ 2 := by
  unfold scaledCosineVandermondeWeight
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

set_option maxHeartbeats 500000 in
theorem evenScaledWeylWeight_three_le_polynomial
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    evenScaledWeylWeight 3 index coordinates ≤ rankSixWeylPolynomial coordinates := by
  unfold evenScaledWeylWeight rankSixWeylPolynomial
  rw [scaledCosineVandermondeWeight_three]
  have h01 := abs_scaled_cosine_difference_le index (coordinates 1) (coordinates 0)
  have h02 := abs_scaled_cosine_difference_le index (coordinates 2) (coordinates 0)
  have h12 := abs_scaled_cosine_difference_le index (coordinates 2) (coordinates 1)
  have h01s := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 h01
  have h02s := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 h02
  have h12s := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 h12
  rw [sq_abs] at h01s h02s h12s
  have hp := allPlusScaledWeight_le_two_pow 3 index coordinates
  norm_num at hp
  have hnon := allPlusScaledWeight_nonneg 3 index coordinates
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
  have hpolyPairNon : 0 ≤
      ((coordinates 1 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2 *
        ((coordinates 2 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2 *
          ((coordinates 2 ^ 2 + coordinates 1 ^ 2) / 2) ^ 2 := by positivity
  have htotal := mul_le_mul hpairs hp hnon hpolyPairNon
  simpa [add_comm, mul_assoc, mul_comm, mul_left_comm] using htotal

theorem rankSixWeylPolynomial_le_separable (coordinates : Fin 3 → ℝ) :
    rankSixWeylPolynomial coordinates ≤
      8 * ∏ coordinate, (1 + coordinates coordinate ^ 2) ^ 4 := by
  let a := coordinates 0 ^ 2
  let b := coordinates 1 ^ 2
  let c := coordinates 2 ^ 2
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  have hpair (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      ((x + y) / 2) ^ 2 ≤ ((1 + x) * (1 + y)) ^ 2 := by
    apply sq_le_sq₀ (by positivity) (by positivity) |>.2
    nlinarith [mul_nonneg hx hy]
  have h01 := hpair a b ha hb
  have h02 := hpair a c ha hc
  have h12 := hpair b c hb hc
  have hprod := mul_le_mul (mul_le_mul h01 h02 (by positivity) (by positivity))
    h12 (by positivity) (by positivity)
  unfold rankSixWeylPolynomial a b c at *
  rw [show (∏ coordinate : Fin 3, (1 + coordinates coordinate ^ 2) ^ 4) =
      (1 + coordinates 0 ^ 2) ^ 4 * (1 + coordinates 1 ^ 2) ^ 4 *
        (1 + coordinates 2 ^ 2) ^ 4 by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [Finset.prod_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))),
      Finset.prod_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
      Finset.prod_singleton]
    ring]
  nlinarith

noncomputable def rankSixCoordinateDominating (value : ℝ) : ℝ :=
  (1 + value ^ 2) ^ 4 *
    Real.exp (-allPlusGaussianCoefficient 3 * value ^ 2)

noncomputable def rankSixLocalDominating (coordinates : Fin 3 → ℝ) : ℝ :=
  (8 * (1 / Real.pi) ^ 3 *
    (Real.sqrt (32 : ℝ) / Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4))) *
    ∏ coordinate, rankSixCoordinateDominating (coordinates coordinate)

theorem integrable_rankSixCoordinateDominating :
    Integrable rankSixCoordinateDominating := by
  rw [show rankSixCoordinateDominating = fun value : ℝ =>
      ∑ index ∈ Finset.range 5, (Nat.choose 4 index : ℝ) *
        (|value| ^ (2 * (4 - index)) *
          Real.exp (-allPlusGaussianCoefficient 3 * value ^ 2)) by
    funext value
    unfold rankSixCoordinateDominating
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index hi
    rw [Finset.mem_range] at hi
    rw [show (1 : ℝ) ^ index = 1 by simp, one_mul]
    have habs : |value| ^ (2 * (4 - index)) =
        (value ^ 2) ^ (4 - index) := by
      calc
        _ = (|value| ^ 2) ^ (4 - index) := by rw [pow_mul]
        _ = _ := by rw [sq_abs]
    rw [habs]
    ring]
  apply integrable_finsetSum
  intro index hi
  exact (integrable_abs_pow_mul_exp_neg_mul_sq
    (2 * (4 - index)) (allPlusGaussianCoefficient_pos (by norm_num))).const_mul _

theorem integrable_rankSixLocalDominating : Integrable rankSixLocalDominating := by
  unfold rankSixLocalDominating
  rw [volume_pi]
  exact (Integrable.fintype_prod fun _ : Fin 3 =>
    integrable_rankSixCoordinateDominating).const_mul _

theorem norm_rankSixEvenLocalRescaledIntegrand_le
    (index : ℕ) (coordinates : Fin 3 → ℝ) :
    ‖rankSixEvenLocalRescaledIntegrand index coordinates‖ ≤
      rankSixLocalDominating coordinates := by
  by_cases hd : coordinates ∈ positiveLocalScaledDomain 3 index
  · rw [rankSixEvenLocalRescaledIntegrand, Set.indicator_of_mem hd,
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
      have hcoefficient : allPlusGaussianCoefficient 3 =
          4 / (Real.pi ^ 2 * Real.sqrt (32 : ℝ)) := by
        norm_num [allPlusGaussianCoefficient]
      rw [← hcoefficient] at hk
      have hw := evenScaledWeylWeight_three_le_polynomial index coordinates
      have hkn := normalizedFibonacciCosineKernel_nonneg
        (dimension := 3) (by norm_num) coordinates
        ((cosineScaleMidpoint_gt_two (by norm_num)).trans_le hd.2)
      have hwn : 0 ≤ evenScaledWeylWeight 3 index coordinates := by
        unfold evenScaledWeylWeight scaledCosineVandermondeWeight
        exact mul_nonneg (by positivity) (allPlusScaledWeight_nonneg 3 index coordinates)
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
              (Real.sqrt (32 : ℝ) /
                Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4))) *
              rankSixWeylPolynomial coordinates *
              Real.exp (-allPlusGaussianCoefficient 3 *
                ∑ coordinate, coordinates coordinate ^ 2) ≤
            ((1 / Real.pi) ^ 3 *
              (Real.sqrt (32 : ℝ) /
                Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4))) *
              (8 * ∏ coordinate, (1 + coordinates coordinate ^ 2) ^ 4) *
              Real.exp (-allPlusGaussianCoefficient 3 *
                ∑ coordinate, coordinates coordinate ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly hconstant) (Real.exp_pos _).le
      have hgauss :
          Real.exp (-allPlusGaussianCoefficient 3 *
              ∑ coordinate, coordinates coordinate ^ 2) =
            ∏ coordinate, Real.exp (-allPlusGaussianCoefficient 3 *
              coordinates coordinate ^ 2) := by
        rw [← Real.exp_sum, ← Finset.mul_sum]
      calc
        (1 / Real.pi) ^ 3 *
            normalizedFibonacciCosineKernel coordinates index *
              evenScaledWeylWeight 3 index coordinates ≤
          ((1 / Real.pi) ^ 3 *
            (Real.sqrt 32 / Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4))) *
            rankSixWeylPolynomial coordinates *
            Real.exp (-allPlusGaussianCoefficient 3 *
              ∑ coordinate, coordinates coordinate ^ 2) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
        _ ≤ ((1 / Real.pi) ^ 3 *
            (Real.sqrt 32 / Real.sqrt (cosineScaleMidpoint 3 ^ 2 - 4))) *
              (8 * ∏ coordinate, (1 + coordinates coordinate ^ 2) ^ 4) *
              Real.exp (-allPlusGaussianCoefficient 3 *
                ∑ coordinate, coordinates coordinate ^ 2) := hsep
        _ = rankSixLocalDominating coordinates := by
          unfold rankSixLocalDominating rankSixCoordinateDominating
          rw [hgauss]
          rw [show (∏ coordinate : Fin 3,
              ((1 + coordinates coordinate ^ 2) ^ 4 *
                Real.exp (-allPlusGaussianCoefficient 3 *
                  coordinates coordinate ^ 2))) =
            (∏ coordinate, (1 + coordinates coordinate ^ 2) ^ 4) *
              ∏ coordinate, Real.exp (-allPlusGaussianCoefficient 3 *
                coordinates coordinate ^ 2) by
              rw [Finset.prod_mul_distrib]]
          ring
    · exact mul_nonneg (mul_nonneg (by positivity)
        (normalizedFibonacciCosineKernel_nonneg
          (dimension := 3) (by norm_num) coordinates
          ((cosineScaleMidpoint_gt_two (by norm_num)).trans_le hd.2)))
        (by unfold evenScaledWeylWeight scaledCosineVandermondeWeight
            exact mul_nonneg (by positivity)
              (allPlusScaledWeight_nonneg 3 index coordinates))
  · rw [rankSixEvenLocalRescaledIntegrand, Set.indicator_of_notMem hd, norm_zero]
    unfold rankSixLocalDominating rankSixCoordinateDominating cosineScaleMidpoint
    positivity

theorem aestronglyMeasurable_rankSixEvenLocalRescaledIntegrand (index : ℕ) :
    AEStronglyMeasurable (rankSixEvenLocalRescaledIntegrand index) := by
  unfold rankSixEvenLocalRescaledIntegrand
  exact (((continuous_const.mul
    (continuous_normalizedFibonacciCosineKernel 3 index (by norm_num))).mul
      (by
        unfold evenScaledWeylWeight
        exact (continuous_scaledCosineVandermondeWeight 3 index).mul
          (continuous_allPlusScaledWeight 3 index))).stronglyMeasurable.indicator
      (measurableSet_positiveLocalScaledDomain 3 index)).aestronglyMeasurable

theorem tendsto_rankSixEvenAngleLocalIntegral :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenAngleLocalIntegral index)
      atTop (nhds (∫ coordinates : Fin 3 → ℝ,
        rankSixEvenLocalLimitIntegrand coordinates)) := by
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ 3 * (index + 1 : ℝ) ^ 6 *
        rankSixEvenAngleLocalIntegral index) =
      fun index => ∫ coordinates : Fin 3 → ℝ,
        rankSixEvenLocalRescaledIntegrand index coordinates by
    funext index
    exact rankSixEvenLocalScalingIntegral_identity index]
  exact tendsto_integral_of_dominated_convergence rankSixLocalDominating
    aestronglyMeasurable_rankSixEvenLocalRescaledIntegrand
    integrable_rankSixLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankSixEvenLocalRescaledIntegrand_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankSixEvenLocalRescaledIntegrand coordinates)

end FibonacciRibbonKernel
