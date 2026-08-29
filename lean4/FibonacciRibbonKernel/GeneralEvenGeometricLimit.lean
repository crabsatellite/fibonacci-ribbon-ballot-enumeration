import FibonacciRibbonKernel.GeneralEvenWeylFullLimit

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

noncomputable def generalEvenNormalizedGeometricKernel
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) (index : ℕ) : ℝ :=
  (cosineSumScale coordinates index / (2 * dimension : ℝ)) ^ index

theorem cosineSumScale_displacement_general
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) (index : ℕ) :
    cosineSumScale coordinates index =
      (2 * dimension : ℝ) +
        cosineSumDisplacement coordinates index / (index + 1 : ℝ) := by
  unfold cosineSumDisplacement
  have hnonzero : (index + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hnonzero]
  ring

theorem tendsto_log_cosineSum_microscopic_general
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) *
        (Real.log (cosineSumScale coordinates index) -
          Real.log (2 * dimension : ℝ)))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) /
        (2 * dimension : ℝ))) := by
  have hbase : (2 * dimension : ℝ) ≠ 0 := by positivity
  have hderiv : HasDerivAt Real.log
      (1 / (2 * dimension : ℝ)) (2 * dimension : ℝ) := by
    simpa using Real.hasDerivAt_log hbase
  have h := tendsto_variable_microscopic_derivative hderiv
    (tendsto_cosineSumDisplacement coordinates)
  have h' : Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) *
        (Real.log ((2 * dimension : ℝ) +
          cosineSumDisplacement coordinates index / (index + 1 : ℝ)) -
            Real.log (2 * dimension : ℝ)))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) /
        (2 * dimension : ℝ))) := by
    simpa only [div_eq_mul_inv, one_mul] using h
  apply h'.congr'
  filter_upwards with index
  rw [cosineSumScale_displacement_general]

theorem tendsto_generalEvenNormalizedGeometricKernel
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      generalEvenNormalizedGeometricKernel dimension coordinates index)
      atTop (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) /
          (2 * dimension : ℝ)))) := by
  have hlog := tendsto_log_cosineSum_microscopic_general
    hdimension coordinates
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hscale := tendsto_cosineSumScale coordinates
  have hbasePos : (0 : ℝ) < 2 * dimension := by positivity
  have heventuallyPositive : ∀ᶠ index : ℕ in atTop,
      0 < cosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 0 hbasePos
  have hpowSucc : Tendsto (fun index : ℕ =>
      (cosineSumScale coordinates index / (2 * dimension : ℝ)) ^ (index + 1))
      atTop (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) /
          (2 * dimension : ℝ)))) := by
    apply hexp.congr'
    filter_upwards [heventuallyPositive] with index hindex
    have hratio : 0 < cosineSumScale coordinates index /
        (2 * dimension : ℝ) := by positivity
    simp only [Function.comp_apply]
    rw [← Real.exp_log hratio, ← Real.exp_nat_mul,
      Real.log_div hindex.ne' hbasePos.ne']
    push_cast
    rfl
  have hratio : Tendsto (fun index =>
      cosineSumScale coordinates index / (2 * dimension : ℝ))
      atTop (nhds 1) := by
    have h := hscale.div_const (2 * dimension : ℝ)
    convert h using 1
    field_simp [hbasePos.ne']
  have hproduct := hpowSucc.mul (hratio.inv₀ (by norm_num))
  rw [inv_one, mul_one] at hproduct
  unfold generalEvenNormalizedGeometricKernel
  apply hproduct.congr'
  filter_upwards [heventuallyPositive] with index hindex
  have hratioNe : cosineSumScale coordinates index /
      (2 * dimension : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

noncomputable def generalEvenGeometricGaussianCoefficient (dimension : ℕ) : ℝ :=
  1 / ((dimension : ℝ) * Real.pi ^ 2)

theorem generalEvenGeometricGaussianCoefficient_pos
    {dimension : ℕ} (hdimension : 1 ≤ dimension) :
    0 < generalEvenGeometricGaussianCoefficient dimension := by
  unfold generalEvenGeometricGaussianCoefficient
  positivity

theorem generalEvenNormalizedGeometricKernel_nonneg
    {dimension index : ℕ} {coordinates : Fin dimension → ℝ}
    (hscale : 0 ≤ cosineSumScale coordinates index) :
    0 ≤ generalEvenNormalizedGeometricKernel dimension coordinates index := by
  unfold generalEvenNormalizedGeometricKernel
  exact pow_nonneg (div_nonneg hscale (by positivity)) _

theorem generalEvenNormalizedGeometricKernel_le_gaussian
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (index : ℕ) (coordinates : Fin dimension → ℝ)
    (hcube : coordinates ∈ positiveScaledCube dimension index)
    (hscaleMid : cosineScaleMidpoint dimension ≤
      cosineSumScale coordinates index) :
    generalEvenNormalizedGeometricKernel dimension coordinates index ≤
      Real.exp 1 *
        Real.exp (-generalEvenGeometricGaussianCoefficient dimension *
          ∑ coordinate, coordinates coordinate ^ 2) := by
  have hdimreal : 2 < (2 * dimension : ℝ) := by
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    linarith
  have hscalePos : 0 < cosineSumScale coordinates index :=
    (cosineScaleMidpoint_gt_two hdimreal).trans_le hscaleMid |>.trans' zero_lt_two
  rcases index with _ | index
  · unfold generalEvenNormalizedGeometricKernel
    rw [pow_zero]
    have hsquares := sum_sq_le_dimension_pi_sq_of_scaledCube hcube
    have hcoefficientPos := generalEvenGeometricGaussianCoefficient_pos
      (show 1 ≤ dimension by omega)
    have hproduct : generalEvenGeometricGaussianCoefficient dimension *
        (∑ coordinate, coordinates coordinate ^ 2) ≤ 1 := by
      calc
        _ ≤ generalEvenGeometricGaussianCoefficient dimension *
            (dimension * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left (by simpa using hsquares)
            hcoefficientPos.le
        _ = 1 := by
          unfold generalEvenGeometricGaussianCoefficient
          field_simp [Real.pi_ne_zero]
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (1 +
          (-generalEvenGeometricGaussianCoefficient dimension *
            ∑ coordinate, coordinates coordinate ^ 2)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = _ := by rw [Real.exp_add]
  · let current := cosineSumScale coordinates (index + 1)
    let ratio := current / (2 * dimension : ℝ)
    let squares : ℝ := ∑ coordinate, coordinates coordinate ^ 2
    have hratioPos : 0 < ratio := by dsimp only [ratio, current]; positivity
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
    have hcurrent : current - (2 * dimension : ℝ) ≤
        -(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares := by
      dsimp only [current]
      rw [show (index + 2 : ℝ) = (((index + 1 : ℕ) : ℝ) + 1) by
        push_cast; ring]
      dsimp only [squares]
      linarith
    have hratioSub : ratio - 1 =
        (current - (2 * dimension : ℝ)) / (2 * dimension : ℝ) := by
      dsimp only [ratio]
      have hbase : (2 * dimension : ℝ) ≠ 0 := by positivity
      field_simp [hbase]
    have hmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ index + 1 by positivity)
    rw [hratioSub] at hmul
    have hindexRatio : (1 / 2 : ℝ) ≤
        (index + 1 : ℝ) / (index + 2 : ℝ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hscaledCurrent :
        (index + 1 : ℝ) *
            ((current - (2 * dimension : ℝ)) / (2 * dimension : ℝ)) ≤
          -(2 / ((dimension : ℝ) * Real.pi ^ 2)) *
            ((index + 1 : ℝ) / (index + 2 : ℝ)) * squares := by
      calc
        _ = ((index + 1 : ℝ) / (2 * dimension : ℝ)) *
            (current - (2 * dimension : ℝ)) := by ring
        _ ≤ ((index + 1 : ℝ) / (2 * dimension : ℝ)) *
            (-(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares) :=
          mul_le_mul_of_nonneg_left hcurrent (by positivity)
        _ = _ := by field_simp [Real.pi_ne_zero]; ring
    have hcoefficient :
        -(2 / ((dimension : ℝ) * Real.pi ^ 2)) *
            ((index + 1 : ℝ) / (index + 2 : ℝ)) ≤
          -generalEvenGeometricGaussianCoefficient dimension := by
      unfold generalEvenGeometricGaussianCoefficient
      have h := mul_le_mul_of_nonpos_left hindexRatio
        (neg_nonpos.mpr (show 0 ≤
          2 / ((dimension : ℝ) * Real.pi ^ 2) by positivity))
      calc
        _ ≤ -(2 / ((dimension : ℝ) * Real.pi ^ 2)) * (1 / 2) := h
        _ = _ := by field_simp [Real.pi_ne_zero]
    have hweighted := mul_le_mul_of_nonneg_right hcoefficient hsquaresNonneg
    have hscaledLog : (index + 1 : ℝ) * Real.log ratio ≤
        -generalEvenGeometricGaussianCoefficient dimension * squares :=
      hmul.trans (hscaledCurrent.trans hweighted)
    unfold generalEvenNormalizedGeometricKernel
    change ratio ^ (index + 1) ≤ _
    calc
      ratio ^ (index + 1) =
          Real.exp ((index + 1 : ℝ) * Real.log ratio) := by
        have hcast : (index + 1 : ℝ) =
            (((index + 1 : ℕ) : ℕ) : ℝ) := by norm_num
        rw [hcast, Real.exp_nat_mul, Real.exp_log hratioPos]
      _ ≤ Real.exp (-generalEvenGeometricGaussianCoefficient dimension * squares) :=
        Real.exp_le_exp.mpr hscaledLog
      _ ≤ Real.exp 1 *
          Real.exp (-generalEvenGeometricGaussianCoefficient dimension * squares) :=
        le_mul_of_one_le_left (Real.exp_pos _).le
          (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num))

noncomputable def generalEvenGeometricLocalRescaledIntegrand
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  (positiveLocalScaledDomain dimension index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        generalEvenNormalizedGeometricKernel dimension coordinates index *
        evenScaledWeylWeight dimension index coordinates)
    coordinates

noncomputable def generalEvenGeometricLocalLimitIntegrand
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  positiveOrthant.indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) /
          (2 * dimension : ℝ)) *
        evenLimitWeylWeight dimension coordinates)
    coordinates

noncomputable def generalEvenGeometricAngleLocalIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (anglePositiveLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (cosineCubeScale angles / (2 * dimension : ℝ)) ^ index *
        evenWeylAngleWeight dimension angles)
    angles

noncomputable def generalEvenGeometricAngleLocalIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalEvenGeometricAngleLocalIntegrand dimension index angles

theorem tendsto_generalEvenGeometricLocalRescaledIntegrand
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      generalEvenGeometricLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds
        (generalEvenGeometricLocalLimitIntegrand dimension coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain (by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith) coordinates horthant
    have hkernel := tendsto_generalEvenNormalizedGeometricKernel
      (show 1 ≤ dimension by omega) coordinates
    have hweight := tendsto_evenScaledWeylWeight dimension coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    rw [generalEvenGeometricLocalLimitIntegrand,
      Set.indicator_of_mem horthant]
    apply hproduct.congr'
    filter_upwards [hlocal] with index hindex
    rw [generalEvenGeometricLocalRescaledIntegrand,
      Set.indicator_of_mem hindex]
  · have hnot : ∃ coordinate : Fin dimension,
        coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _ => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveLocalScaledDomain dimension index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    rw [show (fun index : ℕ =>
        generalEvenGeometricLocalRescaledIntegrand dimension index coordinates) =
      fun _ => 0 by
        funext index
        rw [generalEvenGeometricLocalRescaledIntegrand,
          Set.indicator_of_notMem (houtside index)],
      generalEvenGeometricLocalLimitIntegrand,
      Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

theorem continuous_generalEvenNormalizedGeometricKernel
    (dimension index : ℕ) :
    Continuous (generalEvenNormalizedGeometricKernel dimension · index) := by
  unfold generalEvenNormalizedGeometricKernel
  exact ((continuous_cosineSumScale dimension index).div_const _).pow index

noncomputable def generalEvenGeometricLocalDominating
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  weylSeparableDominating dimension 0
    ((1 / Real.pi) ^ dimension * Real.exp 1 * (2 : ℝ) ^ dimension)
    (generalEvenGeometricGaussianCoefficient dimension) coordinates

theorem integrable_generalEvenGeometricLocalDominating
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Integrable (generalEvenGeometricLocalDominating dimension) := by
  unfold generalEvenGeometricLocalDominating
  exact integrable_weylSeparableDominating dimension 0 _
    (generalEvenGeometricGaussianCoefficient_pos (show 1 ≤ dimension by omega))

theorem aestronglyMeasurable_generalEvenGeometricLocalRescaledIntegrand
    (dimension index : ℕ) :
    AEStronglyMeasurable
      (generalEvenGeometricLocalRescaledIntegrand dimension index) := by
  unfold generalEvenGeometricLocalRescaledIntegrand
  have hweight : Continuous (evenScaledWeylWeight dimension index) := by
    unfold evenScaledWeylWeight
    exact (continuous_scaledCosineVandermondeWeight dimension index).mul
      (continuous_allPlusScaledWeight dimension index)
  exact (((continuous_const.mul
    (continuous_generalEvenNormalizedGeometricKernel dimension index)).mul
      hweight).stronglyMeasurable.indicator
        (measurableSet_positiveLocalScaledDomain dimension index)).aestronglyMeasurable

theorem norm_generalEvenGeometricLocalRescaledIntegrand_le
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖generalEvenGeometricLocalRescaledIntegrand dimension index coordinates‖ ≤
      generalEvenGeometricLocalDominating dimension coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [generalEvenGeometricLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, Real.norm_eq_abs, abs_of_nonneg]
    · have hkernel := generalEvenNormalizedGeometricKernel_le_gaussian
        hdimension index coordinates hdomain.1 hdomain.2
      have hweight := evenScaledWeylWeight_le_global
        dimension index coordinates
      have hkernelNonneg := generalEvenNormalizedGeometricKernel_nonneg
        ((show (0 : ℝ) < cosineScaleMidpoint dimension by
          unfold cosineScaleMidpoint
          positivity).le.trans hdomain.2)
      have hweightNonneg := evenScaledWeylWeight_nonneg
        dimension index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg
        (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ dimension by positivity)
      calc
        (1 / Real.pi) ^ dimension *
            generalEvenNormalizedGeometricKernel dimension coordinates index *
              evenScaledWeylWeight dimension index coordinates ≤
          (1 / Real.pi) ^ dimension *
            ((Real.exp 1 *
              Real.exp (-generalEvenGeometricGaussianCoefficient dimension *
                ∑ coordinate, coordinates coordinate ^ 2)) *
              ((2 : ℝ) ^ dimension *
                weylGlobalPolynomial dimension coordinates ^
                  (weylSeparableExponent dimension 0))) := by
                    simpa only [mul_assoc] using hscaled
        _ = generalEvenGeometricLocalDominating dimension coordinates := by
          unfold generalEvenGeometricLocalDominating weylSeparableDominating
          rw [← gaussianGlobalPolynomial_eq_separable]
          ring
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (generalEvenNormalizedGeometricKernel_nonneg
            ((show (0 : ℝ) < cosineScaleMidpoint dimension by
              unfold cosineScaleMidpoint
              positivity).le.trans hdomain.2)))
        (evenScaledWeylWeight_nonneg dimension index coordinates)
  · rw [generalEvenGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold generalEvenGeometricLocalDominating weylSeparableDominating
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro coordinate hcoordinate
    unfold weylCoordinateDominating
    positivity

theorem tendsto_integral_generalEvenGeometricLocalRescaledIntegrand
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index => ∫ coordinates : Fin dimension → ℝ,
      generalEvenGeometricLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalEvenGeometricLocalLimitIntegrand dimension coordinates)) := by
  exact tendsto_integral_of_dominated_convergence
    (generalEvenGeometricLocalDominating dimension)
    (fun index =>
      aestronglyMeasurable_generalEvenGeometricLocalRescaledIntegrand
        dimension index)
    (integrable_generalEvenGeometricLocalDominating hdimension)
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_generalEvenGeometricLocalRescaledIntegrand_le
        hdimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_generalEvenGeometricLocalRescaledIntegrand
        hdimension coordinates)

theorem generalEvenGeometricAngleLocalIntegrand_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    generalEvenGeometricAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      generalEvenGeometricLocalRescaledIntegrand dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [generalEvenGeometricAngleLocalIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).2
          hdomain),
      generalEvenGeometricLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt, generalEvenAngleWeight_inverseSqrt]
    unfold generalEvenNormalizedGeometricKernel
    ring
  · rw [generalEvenGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).1
          hdomain),
      generalEvenGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem stronglyMeasurable_generalEvenGeometricAngleLocalIntegrand
    (dimension index : ℕ) :
    StronglyMeasurable
      (generalEvenGeometricAngleLocalIntegrand dimension index) := by
  unfold generalEvenGeometricAngleLocalIntegrand
  have hkernel : Continuous (fun angles : Fin dimension → ℝ =>
      (cosineCubeScale angles / (2 * dimension : ℝ)) ^ index) :=
    ((continuous_cosineCubeScale dimension).div_const _).pow index
  exact (((continuous_const.mul hkernel).mul
      (continuous_evenWeylAngleWeight dimension)).stronglyMeasurable.indicator
        (measurableSet_anglePositiveLocalDomain dimension))

theorem generalEvenGeometricLocalScalingIntegral_identity
    (dimension index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricAngleLocalIntegral dimension index =
      ∫ coordinates : Fin dimension → ℝ,
        generalEvenGeometricLocalRescaledIntegrand dimension index coordinates := by
  let scaleMap := coordinateScalarLinearMap dimension
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := generalEvenGeometricAngleLocalIntegrand dimension index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension _).aemeasurable
      (stronglyMeasurable_generalEvenGeometricAngleLocalIntegrand
        dimension index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ dimension := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold generalEvenGeometricAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      generalEvenGeometricAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
    fun coordinates =>
      generalEvenGeometricLocalRescaledIntegrand dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) by
      funext coordinates
      exact generalEvenGeometricAngleLocalIntegrand_inverseSqrt
        dimension index coordinates] at hmap
  rw [integral_div] at hmap
  have hnonzero : (index + 1 : ℝ) ^
      (dimension * (dimension - 1)) ≠ 0 := by positivity
  field_simp [hnonzero] at hmap ⊢
  exact hmap

end FibonacciRibbonKernel
