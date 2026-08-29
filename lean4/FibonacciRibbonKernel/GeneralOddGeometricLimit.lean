import FibonacciRibbonKernel.GeneralOddWeylFullLimit
import FibonacciRibbonKernel.RankFiveGeometricPointwise

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

noncomputable def generalOddNormalizedGeometricKernel
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) (index : ℕ) : ℝ :=
  (oddCosineSumScale coordinates index / (2 * dimension + 1 : ℝ)) ^ index

theorem tendsto_log_oddCosineSum_microscopic_general
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) *
        (Real.log (oddCosineSumScale coordinates index) -
          Real.log (2 * dimension + 1 : ℝ)))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) /
        (2 * dimension + 1 : ℝ))) := by
  have hbase : (2 * dimension + 1 : ℝ) ≠ 0 := by positivity
  have hderiv : HasDerivAt Real.log
      (1 / (2 * dimension + 1 : ℝ)) (2 * dimension + 1 : ℝ) := by
    simpa using Real.hasDerivAt_log hbase
  have h := tendsto_variable_microscopic_derivative hderiv
    (tendsto_cosineSumDisplacement coordinates)
  have h' : Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) *
        (Real.log ((2 * dimension + 1 : ℝ) +
          cosineSumDisplacement coordinates index / (index + 1 : ℝ)) -
            Real.log (2 * dimension + 1 : ℝ)))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) /
        (2 * dimension + 1 : ℝ))) := by
    simpa only [div_eq_mul_inv, one_mul] using h
  apply h'.congr'
  filter_upwards with index
  rw [oddCosineSumScale_displacement]

theorem tendsto_generalOddGeometricRatio_pow_succ
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index : ℕ =>
      (oddCosineSumScale coordinates index /
        (2 * dimension + 1 : ℝ)) ^ (index + 1))
      atTop (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) /
          (2 * dimension + 1 : ℝ)))) := by
  have hlog := tendsto_log_oddCosineSum_microscopic_general
    dimension coordinates
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hscale := tendsto_oddCosineSumScale coordinates
  have hbasePos : (0 : ℝ) < 2 * dimension + 1 := by positivity
  have heventuallyPositive : ∀ᶠ index : ℕ in atTop,
      0 < oddCosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 0 hbasePos
  apply hexp.congr'
  filter_upwards [heventuallyPositive] with index hindex
  have hratio : 0 < oddCosineSumScale coordinates index /
      (2 * dimension + 1 : ℝ) := by positivity
  simp only [Function.comp_apply]
  rw [← Real.exp_log hratio, ← Real.exp_nat_mul,
    Real.log_div hindex.ne' hbasePos.ne']
  push_cast
  rfl

theorem tendsto_generalOddNormalizedGeometricKernel
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      generalOddNormalizedGeometricKernel dimension coordinates index)
      atTop (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) /
          (2 * dimension + 1 : ℝ)))) := by
  have hpow := tendsto_generalOddGeometricRatio_pow_succ
    hdimension coordinates
  have hratio : Tendsto (fun index =>
      oddCosineSumScale coordinates index / (2 * dimension + 1 : ℝ))
      atTop (nhds 1) := by
    have h := (tendsto_oddCosineSumScale coordinates).div_const
      (2 * dimension + 1 : ℝ)
    have hbase : (2 * dimension + 1 : ℝ) ≠ 0 := by positivity
    convert h using 1
    field_simp [hbase]
  have hinverse := hratio.inv₀ (by norm_num)
  have hproduct := hpow.mul hinverse
  rw [inv_one, mul_one] at hproduct
  have heventuallyPositive : ∀ᶠ index : ℕ in atTop,
      0 < oddCosineSumScale coordinates index :=
    (tendsto_order.1 (tendsto_oddCosineSumScale coordinates)).1 0
      (by positivity)
  unfold generalOddNormalizedGeometricKernel
  apply hproduct.congr'
  filter_upwards [heventuallyPositive] with index hindex
  have hratioNe : oddCosineSumScale coordinates index /
      (2 * dimension + 1 : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

theorem sum_sq_le_dimension_pi_sq_of_scaledCube
    {dimension index : ℕ} {coordinates : Fin dimension → ℝ}
    (hcoordinates : coordinates ∈ positiveScaledCube dimension index) :
    ∑ coordinate, coordinates coordinate ^ 2 ≤
      dimension * Real.pi ^ 2 * (index + 1 : ℝ) := by
  calc
    ∑ coordinate, coordinates coordinate ^ 2 ≤
      ∑ _coordinate : Fin dimension,
        (Real.pi * Real.sqrt (index + 1 : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro coordinate hcoordinate
      have hmem := hcoordinates coordinate (Set.mem_univ coordinate)
      exact (sq_le_sq₀ hmem.1.le (by positivity)).2 hmem.2
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_pow, Real.sq_sqrt (by positivity)]
      ring

noncomputable def generalOddGeometricGaussianCoefficient (dimension : ℕ) : ℝ :=
  2 / ((2 * dimension + 1 : ℝ) * Real.pi ^ 2)

theorem generalOddGeometricGaussianCoefficient_pos (dimension : ℕ) :
    0 < generalOddGeometricGaussianCoefficient dimension := by
  unfold generalOddGeometricGaussianCoefficient
  positivity

theorem generalOddNormalizedGeometricKernel_nonneg
    {dimension index : ℕ} {coordinates : Fin dimension → ℝ}
    (hscale : 0 ≤ oddCosineSumScale coordinates index) :
    0 ≤ generalOddNormalizedGeometricKernel dimension coordinates index := by
  unfold generalOddNormalizedGeometricKernel
  exact pow_nonneg (div_nonneg hscale (by positivity)) _

theorem generalOddNormalizedGeometricKernel_le_gaussian
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (index : ℕ) (coordinates : Fin dimension → ℝ)
    (hcube : coordinates ∈ positiveScaledCube dimension index)
    (hscaleMid : oddCosineScaleMidpoint dimension ≤
      oddCosineSumScale coordinates index) :
    generalOddNormalizedGeometricKernel dimension coordinates index ≤
      Real.exp 1 *
        Real.exp (-generalOddGeometricGaussianCoefficient dimension *
          ∑ coordinate, coordinates coordinate ^ 2) := by
  have hscalePos : 0 < oddCosineSumScale coordinates index :=
    (oddCosineScaleMidpoint_gt_two (by
      have hdreal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith)).trans_le hscaleMid |>.trans' zero_lt_two
  rcases index with _ | index
  · unfold generalOddNormalizedGeometricKernel
    rw [pow_zero]
    have hsquares := sum_sq_le_dimension_pi_sq_of_scaledCube hcube
    have hcoefficientPos := generalOddGeometricGaussianCoefficient_pos dimension
    have hproduct : generalOddGeometricGaussianCoefficient dimension *
        (∑ coordinate, coordinates coordinate ^ 2) ≤ 1 := by
      calc
        _ ≤ generalOddGeometricGaussianCoefficient dimension *
            (dimension * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left (by simpa using hsquares)
            hcoefficientPos.le
        _ ≤ 1 := by
          unfold generalOddGeometricGaussianCoefficient
          have hd : (0 : ℝ) ≤ dimension := by positivity
          have hbase : (0 : ℝ) < 2 * dimension + 1 := by positivity
          field_simp [Real.pi_ne_zero]
          linarith
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (1 +
          (-generalOddGeometricGaussianCoefficient dimension *
            ∑ coordinate, coordinates coordinate ^ 2)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp 1 *
          Real.exp (-generalOddGeometricGaussianCoefficient dimension *
            ∑ coordinate, coordinates coordinate ^ 2) := by
        rw [Real.exp_add]
  · let current := oddCosineSumScale coordinates (index + 1)
    let ratio := current / (2 * dimension + 1 : ℝ)
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
    have hcurrent : current - (2 * dimension + 1 : ℝ) ≤
        -(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares := by
      dsimp only [current]
      unfold oddCosineSumScale
      rw [show (index + 2 : ℝ) = (((index + 1 : ℕ) : ℝ) + 1) by
        push_cast; ring]
      linarith
    have hratioSub : ratio - 1 =
        (current - (2 * dimension + 1 : ℝ)) /
          (2 * dimension + 1 : ℝ) := by
      dsimp only [ratio]
      have hbase : (2 * dimension + 1 : ℝ) ≠ 0 := by positivity
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
            ((current - (2 * dimension + 1 : ℝ)) /
              (2 * dimension + 1 : ℝ)) ≤
          -(4 / ((2 * dimension + 1 : ℝ) * Real.pi ^ 2)) *
            ((index + 1 : ℝ) / (index + 2 : ℝ)) * squares := by
      calc
        _ = ((index + 1 : ℝ) / (2 * dimension + 1 : ℝ)) *
            (current - (2 * dimension + 1 : ℝ)) := by ring
        _ ≤ ((index + 1 : ℝ) / (2 * dimension + 1 : ℝ)) *
            (-(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares) :=
          mul_le_mul_of_nonneg_left hcurrent (by positivity)
        _ = _ := by field_simp [Real.pi_ne_zero]
    have hcoefficient :
        -(4 / ((2 * dimension + 1 : ℝ) * Real.pi ^ 2)) *
            ((index + 1 : ℝ) / (index + 2 : ℝ)) ≤
          -generalOddGeometricGaussianCoefficient dimension := by
      unfold generalOddGeometricGaussianCoefficient
      have h := mul_le_mul_of_nonpos_left hindexRatio
        (neg_nonpos.mpr (show 0 ≤
          4 / ((2 * dimension + 1 : ℝ) * Real.pi ^ 2) by positivity))
      calc
        _ ≤ -(4 / ((2 * dimension + 1 : ℝ) * Real.pi ^ 2)) *
            (1 / 2) := h
        _ = _ := by field_simp [Real.pi_ne_zero]; ring
    have hweighted := mul_le_mul_of_nonneg_right hcoefficient hsquaresNonneg
    have hscaledLog :
        (index + 1 : ℝ) * Real.log ratio ≤
          -generalOddGeometricGaussianCoefficient dimension * squares :=
      hmul.trans (hscaledCurrent.trans hweighted)
    unfold generalOddNormalizedGeometricKernel
    change ratio ^ (index + 1) ≤ _
    calc
      ratio ^ (index + 1) =
          Real.exp ((index + 1 : ℝ) * Real.log ratio) := by
        have hcast : (index + 1 : ℝ) =
            (((index + 1 : ℕ) : ℕ) : ℝ) := by norm_num
        rw [hcast, Real.exp_nat_mul, Real.exp_log hratioPos]
      _ ≤ Real.exp (-generalOddGeometricGaussianCoefficient dimension * squares) :=
        Real.exp_le_exp.mpr hscaledLog
      _ ≤ Real.exp 1 *
          Real.exp (-generalOddGeometricGaussianCoefficient dimension * squares) :=
        le_mul_of_one_le_left (Real.exp_pos _).le
          (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num))

noncomputable def generalOddGeometricLocalRescaledIntegrand
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  (positiveOddLocalScaledDomain dimension index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        generalOddNormalizedGeometricKernel dimension coordinates index *
        oddScaledWeylWeight dimension index coordinates)
    coordinates

noncomputable def generalOddGeometricLocalLimitIntegrand
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  positiveOrthant.indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) /
          (2 * dimension + 1 : ℝ)) *
        oddLimitWeylWeight dimension coordinates)
    coordinates

noncomputable def generalOddGeometricAngleLocalIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (oddAngleLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (oddCosineCubeScale angles / (2 * dimension + 1 : ℝ)) ^ index *
        oddWeylAngleWeight dimension angles)
    angles

noncomputable def generalOddGeometricAngleLocalIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalOddGeometricAngleLocalIntegrand dimension index angles

theorem tendsto_generalOddGeometricLocalRescaledIntegrand
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      generalOddGeometricLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds
        (generalOddGeometricLocalLimitIntegrand dimension coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveOddLocalScaledDomain
      (dimension := dimension) (by
        have hdreal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
        linarith) coordinates horthant
    have hkernel := tendsto_generalOddNormalizedGeometricKernel
      hdimension coordinates
    have hweight := tendsto_oddScaledWeylWeight dimension coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    rw [generalOddGeometricLocalLimitIntegrand,
      Set.indicator_of_mem horthant]
    apply hproduct.congr'
    filter_upwards [hlocal] with index hindex
    rw [generalOddGeometricLocalRescaledIntegrand,
      Set.indicator_of_mem hindex]
  · have hdimensionPos : 0 < dimension := by omega
    have hnot : ∃ coordinate : Fin dimension,
        coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _ => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveOddLocalScaledDomain dimension index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    rw [show (fun index : ℕ =>
        generalOddGeometricLocalRescaledIntegrand dimension index coordinates) =
      fun _ => 0 by
        funext index
        rw [generalOddGeometricLocalRescaledIntegrand,
          Set.indicator_of_notMem (houtside index)],
      generalOddGeometricLocalLimitIntegrand,
      Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

theorem continuous_generalOddNormalizedGeometricKernel
    (dimension index : ℕ) :
    Continuous (generalOddNormalizedGeometricKernel dimension · index) := by
  unfold generalOddNormalizedGeometricKernel
  exact ((continuous_oddCosineSumScale dimension index).div_const _).pow index

theorem aestronglyMeasurable_generalOddGeometricLocalRescaledIntegrand
    (dimension index : ℕ) :
    AEStronglyMeasurable
      (generalOddGeometricLocalRescaledIntegrand dimension index) := by
  unfold generalOddGeometricLocalRescaledIntegrand
  exact (((continuous_const.mul
    (continuous_generalOddNormalizedGeometricKernel dimension index)).mul
      (continuous_oddScaledWeylWeight dimension index)).stronglyMeasurable.indicator
        (measurableSet_positiveOddLocalScaledDomain dimension index)).aestronglyMeasurable

noncomputable def generalOddGeometricLocalDominating
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  weylSeparableDominating dimension dimension
    ((1 / Real.pi) ^ dimension * Real.exp 1)
    (generalOddGeometricGaussianCoefficient dimension) coordinates

theorem integrable_generalOddGeometricLocalDominating (dimension : ℕ) :
    Integrable (generalOddGeometricLocalDominating dimension) := by
  unfold generalOddGeometricLocalDominating
  exact integrable_weylSeparableDominating dimension dimension _
    (generalOddGeometricGaussianCoefficient_pos dimension)

theorem norm_generalOddGeometricLocalRescaledIntegrand_le
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖generalOddGeometricLocalRescaledIntegrand dimension index coordinates‖ ≤
      generalOddGeometricLocalDominating dimension coordinates := by
  by_cases hdomain : coordinates ∈ positiveOddLocalScaledDomain dimension index
  · rw [generalOddGeometricLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, Real.norm_eq_abs, abs_of_nonneg]
    · have hkernel := generalOddNormalizedGeometricKernel_le_gaussian
        hdimension index coordinates hdomain.1 hdomain.2
      have hweight := oddScaledWeylWeight_le_global
        dimension index coordinates
      have hkernelNonneg := generalOddNormalizedGeometricKernel_nonneg
        ((show (0 : ℝ) < oddCosineScaleMidpoint dimension by
          unfold oddCosineScaleMidpoint
          positivity).le.trans hdomain.2)
      have hweightNonneg := oddScaledWeylWeight_nonneg
        dimension index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg
        (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ dimension by positivity)
      calc
        (1 / Real.pi) ^ dimension *
            generalOddNormalizedGeometricKernel dimension coordinates index *
              oddScaledWeylWeight dimension index coordinates ≤
          (1 / Real.pi) ^ dimension *
            ((Real.exp 1 *
              Real.exp (-generalOddGeometricGaussianCoefficient dimension *
                ∑ coordinate, coordinates coordinate ^ 2)) *
              weylGlobalPolynomial dimension coordinates ^
                (weylSeparableExponent dimension dimension)) := by
                  simpa only [mul_assoc] using hscaled
        _ = generalOddGeometricLocalDominating dimension coordinates := by
          unfold generalOddGeometricLocalDominating weylSeparableDominating
          rw [← gaussianGlobalPolynomial_eq_separable]
          ring
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (generalOddNormalizedGeometricKernel_nonneg
            ((show (0 : ℝ) < oddCosineScaleMidpoint dimension by
              unfold oddCosineScaleMidpoint
              positivity).le.trans hdomain.2)))
        (oddScaledWeylWeight_nonneg dimension index coordinates)
  · rw [generalOddGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold generalOddGeometricLocalDominating weylSeparableDominating
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro coordinate hcoordinate
    unfold weylCoordinateDominating
    positivity

theorem tendsto_integral_generalOddGeometricLocalRescaledIntegrand
    (dimension : ℕ) (hdimension : 1 ≤ dimension) :
    Tendsto (fun index => ∫ coordinates : Fin dimension → ℝ,
        generalOddGeometricLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalOddGeometricLocalLimitIntegrand dimension coordinates)) := by
  exact tendsto_integral_of_dominated_convergence
    (generalOddGeometricLocalDominating dimension)
    (fun index =>
      aestronglyMeasurable_generalOddGeometricLocalRescaledIntegrand
        dimension index)
    (integrable_generalOddGeometricLocalDominating dimension)
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_generalOddGeometricLocalRescaledIntegrand_le
        hdimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_generalOddGeometricLocalRescaledIntegrand
        hdimension coordinates)

theorem generalOddGeometricAngleLocalIntegrand_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    generalOddGeometricAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      generalOddGeometricLocalRescaledIntegrand dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension ^ 2) := by
  by_cases hdomain : coordinates ∈ positiveOddLocalScaledDomain dimension index
  · rw [generalOddGeometricAngleLocalIntegrand,
      Set.indicator_of_mem
        ((oddAngleLocalDomain_inverseSqrt_iff dimension index coordinates).2 hdomain),
      generalOddGeometricLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      oddCosineCubeScale_inverseSqrt, oddWeylAngleWeight_inverseSqrt]
    unfold generalOddNormalizedGeometricKernel
    ring
  · rw [generalOddGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem
        (mt (oddAngleLocalDomain_inverseSqrt_iff dimension index coordinates).1 hdomain),
      generalOddGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, zero_div]

theorem stronglyMeasurable_generalOddGeometricAngleLocalIntegrand
    (dimension index : ℕ) :
    StronglyMeasurable
      (generalOddGeometricAngleLocalIntegrand dimension index) := by
  unfold generalOddGeometricAngleLocalIntegrand
  have hkernel : Continuous (fun angles : Fin dimension → ℝ =>
      (oddCosineCubeScale angles / (2 * dimension + 1 : ℝ)) ^ index) :=
    ((continuous_oddCosineCubeScale dimension).div_const _).pow index
  exact (((continuous_const.mul hkernel).mul
      (continuous_oddWeylAngleWeight dimension)).stronglyMeasurable.indicator
        (measurableSet_oddAngleLocalDomain dimension))

theorem generalOddGeometricLocalScalingIntegral_identity
    (dimension index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricAngleLocalIntegral dimension index =
      ∫ coordinates : Fin dimension → ℝ,
        generalOddGeometricLocalRescaledIntegrand dimension index coordinates := by
  let scaleMap := coordinateScalarLinearMap dimension
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := generalOddGeometricAngleLocalIntegrand dimension index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension _).aemeasurable
      (stronglyMeasurable_generalOddGeometricAngleLocalIntegrand
        dimension index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ dimension := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold generalOddGeometricAngleLocalIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      generalOddGeometricAngleLocalIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates =>
        generalOddGeometricLocalRescaledIntegrand dimension index coordinates /
          (index + 1 : ℝ) ^ (dimension ^ 2) by
    funext coordinates
    exact generalOddGeometricAngleLocalIntegrand_inverseSqrt
      dimension index coordinates] at hmap
  rw [integral_div] at hmap
  have hnonzero : (index + 1 : ℝ) ^ (dimension ^ 2) ≠ 0 := by positivity
  field_simp [hnonzero] at hmap ⊢
  exact hmap

noncomputable def generalOddGeometricFullIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (1 / Real.pi) ^ dimension *
    (oddCosineCubeScale angles / (2 * dimension + 1 : ℝ)) ^ index *
    oddWeylAngleWeight dimension angles

noncomputable def generalOddGeometricLocalProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (generalOddPositiveSpectralDomain dimension).indicator
    (generalOddGeometricFullIntegrand dimension index) angles

noncomputable def generalOddGeometricTailProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (generalOddTailSpectralDomain dimension).indicator
    (generalOddGeometricFullIntegrand dimension index) angles

noncomputable def generalOddGeometricFullIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalOddGeometricFullIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

noncomputable def generalOddGeometricTailIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalOddGeometricTailProductIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

theorem generalOddGeometricFullIntegrand_partition
    (dimension index : ℕ) (angles : Fin dimension → ℝ) :
    generalOddGeometricFullIntegrand dimension index angles =
      generalOddGeometricLocalProductIntegrand dimension index angles +
        generalOddGeometricTailProductIntegrand dimension index angles := by
  by_cases hlocal : angles ∈ generalOddPositiveSpectralDomain dimension
  · have htail : angles ∉ generalOddTailSpectralDomain dimension := by
      intro htail
      change oddCosineScaleMidpoint dimension ≤ oddCosineCubeScale angles at hlocal
      change oddCosineCubeScale angles < oddCosineScaleMidpoint dimension at htail
      exact (not_lt_of_ge hlocal) htail
    rw [generalOddGeometricLocalProductIntegrand, Set.indicator_of_mem hlocal,
      generalOddGeometricTailProductIntegrand, Set.indicator_of_notMem htail,
      add_zero]
  · have htail : angles ∈ generalOddTailSpectralDomain dimension := by
      change ¬oddCosineScaleMidpoint dimension ≤ oddCosineCubeScale angles at hlocal
      change oddCosineCubeScale angles < oddCosineScaleMidpoint dimension
      exact lt_of_not_ge hlocal
    rw [generalOddGeometricLocalProductIntegrand, Set.indicator_of_notMem hlocal,
      generalOddGeometricTailProductIntegrand, Set.indicator_of_mem htail,
      zero_add]

theorem integrable_generalOddGeometricFullIntegrand
    (dimension index : ℕ) :
    Integrable (generalOddGeometricFullIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
  apply integrable_continuous_cosineCube
  unfold generalOddGeometricFullIntegrand
  have hkernel : Continuous (fun angles : Fin dimension → ℝ =>
      (oddCosineCubeScale angles / (2 * dimension + 1 : ℝ)) ^ index) :=
    ((continuous_oddCosineCubeScale dimension).div_const _).pow index
  exact (continuous_const.mul hkernel).mul
      (continuous_oddWeylAngleWeight dimension)

theorem generalOddGeometricFullIntegral_partition
    (dimension index : ℕ) :
    generalOddGeometricFullIntegral dimension index =
      (∫ angles : Fin dimension → ℝ,
        generalOddGeometricLocalProductIntegrand dimension index angles
        ∂cosineCubeProductMeasure dimension) +
      generalOddGeometricTailIntegral dimension index := by
  unfold generalOddGeometricFullIntegral generalOddGeometricTailIntegral
  rw [show (fun angles : Fin dimension → ℝ =>
      generalOddGeometricFullIntegrand dimension index angles) =
    fun angles =>
      generalOddGeometricLocalProductIntegrand dimension index angles +
        generalOddGeometricTailProductIntegrand dimension index angles by
      funext angles
      exact generalOddGeometricFullIntegrand_partition dimension index angles]
  have hlocal : Integrable
      (generalOddGeometricLocalProductIntegrand dimension index)
      (cosineCubeProductMeasure dimension) :=
    (integrable_generalOddGeometricFullIntegrand dimension index).indicator
      (measurableSet_generalOddPositiveSpectralDomain dimension)
  have htail : Integrable
      (generalOddGeometricTailProductIntegrand dimension index)
      (cosineCubeProductMeasure dimension) :=
    (integrable_generalOddGeometricFullIntegrand dimension index).indicator
      (measurableSet_generalOddTailSpectralDomain dimension)
  exact integral_add hlocal htail

theorem generalOddGeometricLocalProductIntegral_eq_angleLocal
    (dimension index : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      generalOddGeometricLocalProductIntegrand dimension index angles
      ∂cosineCubeProductMeasure dimension) =
      generalOddGeometricAngleLocalIntegral dimension index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin dimension =>
      Set.Ioc (0 : ℝ) Real.pi) = anglePositiveCube dimension by rfl]
  rw [← integral_indicator (show MeasurableSet (anglePositiveCube dimension) by
    unfold anglePositiveCube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold generalOddGeometricAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube dimension
  · by_cases hlocal : angles ∈ generalOddPositiveSpectralDomain dimension
    · have hangle : angles ∈ oddAngleLocalDomain dimension := ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        generalOddGeometricLocalProductIntegrand,
        Set.indicator_of_mem hlocal,
        generalOddGeometricAngleLocalIntegrand,
        Set.indicator_of_mem hangle]
      unfold generalOddGeometricFullIntegrand
      rfl
    · rw [Set.indicator_of_mem hcube,
        generalOddGeometricLocalProductIntegrand,
        Set.indicator_of_notMem hlocal,
        generalOddGeometricAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      generalOddGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

noncomputable def generalOddGeometricTailRatio (dimension : ℕ) : ℝ :=
  generalOddTailBound dimension / (2 * dimension + 1 : ℝ)

theorem generalOddGeometricTailRatio_pos
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    0 < generalOddGeometricTailRatio dimension := by
  unfold generalOddGeometricTailRatio
  apply div_pos
  · unfold generalOddTailBound
    exact lt_of_lt_of_le (show 0 < oddCosineScaleMidpoint dimension by
      unfold oddCosineScaleMidpoint
      positivity)
      (le_max_left _ _)
  · have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    positivity

theorem generalOddGeometricTailRatio_lt_one
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    generalOddGeometricTailRatio dimension < 1 := by
  rw [generalOddGeometricTailRatio, div_lt_one (by positivity)]
  exact generalOddTailBound_lt_base hdimension

theorem abs_generalOddGeometricKernel_le_tail
    {dimension index : ℕ} (hdimension : 2 ≤ dimension)
    {angles : Fin dimension → ℝ}
    (htail : angles ∈ generalOddTailSpectralDomain dimension) :
    |(oddCosineCubeScale angles / (2 * dimension + 1 : ℝ)) ^ index| ≤
      generalOddGeometricTailRatio dimension ^ index := by
  rw [abs_pow, abs_div, abs_of_pos (by positivity :
    (0 : ℝ) < 2 * dimension + 1)]
  exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (by positivity))
    (div_le_div_of_nonneg_right
      (abs_oddCosineCubeScale_le_tailBound htail) (by positivity)) index

theorem norm_generalOddGeometricTailProductIntegrand_le
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (index : ℕ) (angles : Fin dimension → ℝ) :
    ‖generalOddGeometricTailProductIntegrand dimension index angles‖ ≤
      ((1 / Real.pi) ^ dimension *
        (4 : ℝ) ^ weylPairCount dimension) *
          generalOddGeometricTailRatio dimension ^ index := by
  by_cases htail : angles ∈ generalOddTailSpectralDomain dimension
  · rw [generalOddGeometricTailProductIntegrand, Set.indicator_of_mem htail,
      generalOddGeometricFullIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
      abs_of_nonneg (oddWeylAngleWeight_nonneg dimension angles)]
    have hkernel := abs_generalOddGeometricKernel_le_tail
      (dimension := dimension) (index := index) hdimension htail
    have hweight := oddWeylAngleWeight_le_constant dimension angles
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left hkernel (pow_nonneg (by positivity) _))
      hweight (oddWeylAngleWeight_nonneg dimension angles)
      (mul_nonneg (pow_nonneg (by positivity) _)
        (pow_nonneg (generalOddGeometricTailRatio_pos hdimension).le _))).trans_eq
          (by ring)
  · rw [generalOddGeometricTailProductIntegrand,
      Set.indicator_of_notMem htail, norm_zero]
    exact mul_nonneg (by positivity)
      (pow_nonneg (generalOddGeometricTailRatio_pos hdimension).le _)

theorem tendsto_generalOddGeometricTailPolynomial
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ (dimension ^ 2 + dimension) *
        generalOddGeometricTailRatio dimension ^ index)
      atTop (nhds 0) := by
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one
    (dimension ^ 2 + dimension)
    (by rw [abs_of_pos (generalOddGeometricTailRatio_pos hdimension)]
        exact generalOddGeometricTailRatio_lt_one hdimension)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hdiv := hshift.div_const (generalOddGeometricTailRatio dimension)
  rw [zero_div] at hdiv
  apply hdiv.congr'
  filter_upwards with index
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  field_simp [(generalOddGeometricTailRatio_pos hdimension).ne']
  ring

theorem tendsto_generalOddGeometricTailIntegral
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricTailIntegral dimension index)
      atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) ^ dimension *
      (4 : ℝ) ^ weylPairCount dimension) *
    (cosineCubeProductMeasure dimension).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ (dimension ^ 2 + dimension) *
        generalOddGeometricTailRatio dimension ^ index) * constant)
  · intro index
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _),
      abs_of_nonneg (pow_nonneg (by positivity) _)]
    have hintegral : ‖generalOddGeometricTailIntegral dimension index‖ ≤
        (((1 / Real.pi) ^ dimension *
          (4 : ℝ) ^ weylPairCount dimension) *
          generalOddGeometricTailRatio dimension ^ index) *
          (cosineCubeProductMeasure dimension).real Set.univ := by
      unfold generalOddGeometricTailIntegral
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall
          (norm_generalOddGeometricTailProductIntegrand_le hdimension index))
    have hsqrt : Real.sqrt (index + 1 : ℝ) ≤ (index + 1 : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
    have hsqrtPow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt dimension
    have hpoly : Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension ^ 2) ≤
        (index + 1 : ℝ) ^ (dimension ^ 2 + dimension) := by
      calc
        _ ≤ (index + 1 : ℝ) ^ dimension *
            (index + 1 : ℝ) ^ (dimension ^ 2) :=
          mul_le_mul_of_nonneg_right hsqrtPow (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; omega
    calc
      Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension ^ 2) *
            ‖generalOddGeometricTailIntegral dimension index‖ ≤
        (index + 1 : ℝ) ^ (dimension ^ 2 + dimension) *
          ‖generalOddGeometricTailIntegral dimension index‖ :=
        mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hintegral (by positivity)
      _ = _ := by ring
  · simpa only [zero_mul] using
      (tendsto_generalOddGeometricTailPolynomial hdimension).mul_const constant

theorem tendsto_generalOddGeometricFullIntegral
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricFullIntegral dimension index)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalOddGeometricLocalLimitIntegrand dimension coordinates)) := by
  have hlocal : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricAngleLocalIntegral dimension index)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalOddGeometricLocalLimitIntegrand dimension coordinates)) := by
    rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricAngleLocalIntegral dimension index) =
      fun index => ∫ coordinates : Fin dimension → ℝ,
        generalOddGeometricLocalRescaledIntegrand dimension index coordinates by
      funext index
      exact generalOddGeometricLocalScalingIntegral_identity dimension index]
    exact tendsto_integral_generalOddGeometricLocalRescaledIntegrand
      dimension (by omega)
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricFullIntegral dimension index) =
    fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricAngleLocalIntegral dimension index +
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricTailIntegral dimension index by
      funext index
      rw [generalOddGeometricFullIntegral_partition,
        generalOddGeometricLocalProductIntegral_eq_angleLocal]
      ring]
  simpa using hlocal.add (tendsto_generalOddGeometricTailIntegral hdimension)

theorem generalOddGeometricFullIntegral_eq_weylMoment
    (dimension index : ℕ) :
    generalOddGeometricFullIntegral dimension index =
      (1 / Real.pi) ^ dimension *
        (oddWeylGeometricMoment dimension index /
          (2 * dimension + 1 : ℝ) ^ index) := by
  unfold generalOddGeometricFullIntegral generalOddGeometricFullIntegrand
    oddWeylGeometricMoment weightedCosineCubeMoment
    weightedCosineCubePowerIntegrand
  rw [show (fun angles : Fin dimension → ℝ =>
      (1 / Real.pi) ^ dimension *
        (oddCosineCubeScale angles / (2 * dimension + 1 : ℝ)) ^ index *
          oddWeylAngleWeight dimension angles) =
    fun angles => ((1 / Real.pi) ^ dimension /
      (2 * dimension + 1 : ℝ) ^ index) *
        (oddCosineCubeScale angles ^ index *
          oddWeylAngleWeight dimension angles) by
      funext angles
      rw [div_pow]
      ring]
  rw [integral_const_mul]
  ring

theorem generalOddGeometricFullIntegral_eq_unrestrictedCount
    (dimension : ℕ) (hdimension : 1 ≤ dimension) (index : ℕ) :
    generalOddGeometricFullIntegral dimension index =
      (1 / Real.pi) ^ dimension / oddWeylNormalization dimension *
        ((unrestrictedCount (2 * dimension) index : ℝ) /
          (2 * dimension + 1 : ℝ) ^ index) := by
  rw [generalOddGeometricFullIntegral_eq_weylMoment,
    generalOddUnrestrictedCount_eq_normalizedWeylMoment
      dimension hdimension]
  have hnorm : oddWeylNormalization dimension ≠ 0 := by
    unfold oddWeylNormalization
    positivity
  field_simp [hnorm]

theorem fixedRankExponent_odd (dimension : ℕ) :
    fixedRankExponent (2 * dimension + 1) =
      (dimension : ℝ) ^ 2 + (dimension : ℝ) / 2 := by
  unfold fixedRankExponent
  push_cast
  ring

theorem sqrt_pow_mul_pow_eq_oddExponent
    (dimension : ℕ) {value : ℝ} (hvalue : 0 < value) :
    Real.sqrt value ^ dimension * value ^ (dimension ^ 2) =
      value ^ fixedRankExponent (2 * dimension + 1) := by
  rw [fixedRankExponent_odd, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hvalue.le]
  rw [← Real.rpow_add hvalue]
  congr 1
  push_cast
  ring

theorem tendsto_generalOddUnrestrictedNormalized_regev
    {dimension : ℕ} (hdimension : 1 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          ((unrestrictedCount (2 * dimension) index : ℝ) /
            (2 * dimension + 1 : ℝ) ^ index))
      atTop (nhds (regevConstant (2 * dimension + 1))) := by
  have hraw := unrestrictedCount_normalized_tendsto_regevConstant_of_mehta
    (2 * dimension) (regevMehtaChamberEvaluation_all (2 * dimension))
  have hnormalized : Tendsto (fun index : ℕ =>
      Real.sqrt (index : ℝ) ^ dimension *
        (index : ℝ) ^ (dimension ^ 2) *
          ((unrestrictedCount (2 * dimension) index : ℝ) /
            (2 * dimension + 1 : ℝ) ^ index))
      atTop (nhds (regevConstant (2 * dimension + 1))) := by
    apply hraw.congr'
    filter_upwards [eventually_ne_atTop 0] with index hindex
    have hi : (0 : ℝ) < index := by positivity
    unfold generalRegevBaseScale
    rw [Real.rpow_neg hi.le]
    rw [sqrt_pow_mul_pow_eq_oddExponent dimension hi]
    push_cast
    field_simp [(show (2 * dimension + 1 : ℝ) ≠ 0 by positivity),
      (Real.rpow_pos_of_pos hi _).ne']
  have hratioBase := tendsto_offset_div_offset_add_real 1 (-1)
  have hratioSqrtRaw :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hratioBase
  norm_num at hratioSqrtRaw
  have hratioSqrt : Tendsto (fun index : ℕ =>
      (Real.sqrt (index + 1 : ℝ) / Real.sqrt (index : ℝ)) ^ dimension)
      atTop (nhds 1) := by
    have hpow := hratioSqrtRaw.pow dimension
    norm_num at hpow
    exact hpow
  have hratioPower := hratioBase.pow (dimension ^ 2)
  norm_num at hratioPower
  have hratio := hratioSqrt.mul hratioPower
  norm_num at hratio
  have hproduct := hratio.mul hnormalized
  norm_num at hproduct
  apply hproduct.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hi : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  have hsqrti : Real.sqrt (index : ℝ) ≠ 0 := by positivity
  rw [div_pow, div_pow]
  field_simp [hi, hsqrti]

theorem generalOddGeometricLocalLimitIntegral_eq_regev
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    (∫ coordinates : Fin dimension → ℝ,
      generalOddGeometricLocalLimitIntegrand dimension coordinates) =
      regevConstant (2 * dimension + 1) *
        (1 / Real.pi) ^ dimension /
          oddWeylNormalization dimension := by
  have hcount := tendsto_generalOddUnrestrictedNormalized_regev
    (show 1 ≤ dimension by omega)
  have hfull := tendsto_generalOddGeometricFullIntegral hdimension
  have hscaled : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddGeometricFullIntegral dimension index)
      atTop (nhds (regevConstant (2 * dimension + 1) *
        (1 / Real.pi) ^ dimension /
          oddWeylNormalization dimension)) := by
    have hconstant : Tendsto (fun _ : ℕ =>
        (1 / Real.pi) ^ dimension / oddWeylNormalization dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension /
          oddWeylNormalization dimension)) := tendsto_const_nhds
    have hmul := hconstant.mul hcount
    rw [show regevConstant (2 * dimension + 1) *
        (1 / Real.pi) ^ dimension / oddWeylNormalization dimension =
      ((1 / Real.pi) ^ dimension / oddWeylNormalization dimension) *
        regevConstant (2 * dimension + 1) by ring]
    apply hmul.congr'
    filter_upwards with index
    rw [generalOddGeometricFullIntegral_eq_unrestrictedCount
      dimension (by omega) index]
    ring
  exact tendsto_nhds_unique hfull hscaled

noncomputable def generalOddGaussianTransportScale (dimension : ℕ) : ℝ :=
  Real.sqrt ((2 * dimension + 1 : ℝ) /
    Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))

theorem generalOddGaussianTransportScale_pos
    {dimension : ℕ} (hdimension : 1 ≤ dimension) :
    0 < generalOddGaussianTransportScale dimension := by
  unfold generalOddGaussianTransportScale
  have hroot : 0 < Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    have hdreal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    nlinarith
  positivity

theorem generalOddGaussianTransportScale_sq
    {dimension : ℕ} (hdimension : 1 ≤ dimension) :
    generalOddGaussianTransportScale dimension ^ 2 =
      (2 * dimension + 1 : ℝ) /
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) := by
  unfold generalOddGaussianTransportScale
  apply Real.sq_sqrt
  have hroot : 0 < Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    have hdreal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    nlinarith
  positivity

theorem sum_sq_coordinateScalar_general
    (dimension : ℕ) (scalar : ℝ) (coordinates : Fin dimension → ℝ) :
    (∑ coordinate,
      (coordinateScalarLinearMap dimension scalar coordinates coordinate) ^ 2) =
      scalar ^ 2 * ∑ coordinate, coordinates coordinate ^ 2 := by
  simp_rw [coordinateScalarLinearMap_apply, mul_pow]
  rw [Finset.mul_sum]

theorem quadraticVandermondeWeight_scalar
    (dimension : ℕ) (scalar : ℝ) (coordinates : Fin dimension → ℝ) :
    quadraticVandermondeWeight dimension
        (coordinateScalarLinearMap dimension scalar coordinates) =
      scalar ^ (4 * weylPairCount dimension) *
        quadraticVandermondeWeight dimension coordinates := by
  unfold quadraticVandermondeWeight weylPairCount
  simp_rw [coordinateScalarLinearMap_apply, mul_pow]
  have hinner : ∀ upper : Fin dimension,
      (∏ lower ∈ Finset.Iio upper,
        ((scalar ^ 2 * coordinates lower ^ 2 -
          scalar ^ 2 * coordinates upper ^ 2) / 2) ^ 2) =
      scalar ^ (4 * (Finset.Iio upper).card) *
        ∏ lower ∈ Finset.Iio upper,
          ((coordinates lower ^ 2 - coordinates upper ^ 2) / 2) ^ 2 := by
    intro upper
    rw [show (fun lower : Fin dimension =>
        ((scalar ^ 2 * coordinates lower ^ 2 -
          scalar ^ 2 * coordinates upper ^ 2) / 2) ^ 2) =
      fun lower => scalar ^ 4 *
        ((coordinates lower ^ 2 - coordinates upper ^ 2) / 2) ^ 2 by
          funext lower
          ring]
    rw [Finset.prod_mul_distrib]
    congr 1
    calc
      ∏ _lower ∈ Finset.Iio upper, scalar ^ 4 =
          (scalar ^ 4) ^ (Finset.Iio upper).card := by simp
      _ = scalar ^ (4 * (Finset.Iio upper).card) := by rw [← pow_mul]
  simp_rw [hinner]
  rw [Finset.prod_mul_distrib]
  congr 1
  calc
    ∏ upper : Fin dimension, scalar ^ (4 * (Finset.Iio upper).card) =
        scalar ^ (∑ upper : Fin dimension,
          4 * (Finset.Iio upper).card) := by
      exact Finset.prod_pow_eq_pow_sum
        (Finset.univ : Finset (Fin dimension))
        (fun upper => 4 * (Finset.Iio upper).card) scalar
    _ = scalar ^ (4 * ∑ upper : Fin dimension,
        (Finset.Iio upper).card) := by
      congr 1
      rw [Finset.mul_sum]

theorem oddLimitWeylWeight_scalar
    (dimension : ℕ) (scalar : ℝ) (coordinates : Fin dimension → ℝ) :
    oddLimitWeylWeight dimension
        (coordinateScalarLinearMap dimension scalar coordinates) =
      scalar ^ (2 * dimension ^ 2) *
        oddLimitWeylWeight dimension coordinates := by
  unfold oddLimitWeylWeight
  rw [quadraticVandermondeWeight_scalar]
  simp_rw [coordinateScalarLinearMap_apply, mul_pow]
  rw [Finset.prod_mul_distrib]
  have hconstant : (∏ _coordinate : Fin dimension, scalar ^ 2) =
      scalar ^ (2 * dimension) := by
    calc
      _ = (scalar ^ 2) ^ dimension := by simp
      _ = _ := by rw [← pow_mul]
  rw [hconstant]
  have hexponent : 4 * weylPairCount dimension + 2 * dimension =
      2 * dimension ^ 2 := by
    calc
      4 * weylPairCount dimension + 2 * dimension =
          2 * (2 * weylPairCount dimension) + 2 * dimension := by ring
      _ = 2 * (dimension * (dimension - 1)) + 2 * dimension := by
        rw [weylPairCount_formula]
      _ = 2 * dimension ^ 2 := by
        by_cases hzero : dimension = 0
        · simp [hzero]
        · have hpositive : 1 ≤ dimension := Nat.one_le_iff_ne_zero.2 hzero
          calc
            2 * (dimension * (dimension - 1)) + 2 * dimension =
                2 * (dimension * (dimension - 1) + dimension) := by ring
            _ = 2 * (dimension * dimension) := by
              congr 1
              calc
                dimension * (dimension - 1) + dimension =
                    dimension * ((dimension - 1) + 1) := by ring
                _ = dimension * dimension := by
                  rw [Nat.sub_add_cancel hpositive]
            _ = _ := by rw [pow_two]
  rw [show scalar ^ (4 * weylPairCount dimension) *
        quadraticVandermondeWeight dimension coordinates *
          (scalar ^ (2 * dimension) *
            ∏ coordinate, coordinates coordinate ^ 2) =
      scalar ^ (4 * weylPairCount dimension + 2 * dimension) *
        (quadraticVandermondeWeight dimension coordinates *
          ∏ coordinate, coordinates coordinate ^ 2) by
    rw [pow_add]
    ring, hexponent]

theorem stronglyMeasurable_generalOddGeometricLocalLimitIntegrand
    (dimension : ℕ) :
    StronglyMeasurable
      (generalOddGeometricLocalLimitIntegrand dimension) := by
  unfold generalOddGeometricLocalLimitIntegrand
  have hweight : Continuous (oddLimitWeylWeight dimension) := by
    unfold oddLimitWeylWeight
    apply (continuous_quadraticVandermondeWeight dimension).mul
    apply continuous_finsetProd
    intro coordinate hcoordinate
    exact (continuous_apply coordinate).pow 2
  exact (((continuous_const.mul
    (Real.continuous_exp.comp (by fun_prop))).mul hweight).stronglyMeasurable.indicator
      (measurableSet_positiveOrthant dimension))

theorem generalOddGeometricLimitIntegrand_transport
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    generalOddGeometricLocalLimitIntegrand dimension
        (coordinateScalarLinearMap dimension
          (generalOddGaussianTransportScale dimension) coordinates) =
      generalOddGaussianTransportScale dimension ^ (2 * dimension ^ 2) *
        oddWeylLocalLimitIntegrand dimension coordinates := by
  let scalar := generalOddGaussianTransportScale dimension
  have hscalar := generalOddGaussianTransportScale_pos hdimension
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hscaled :=
      (mem_positiveOrthant_coordinateScalar_iff hscalar coordinates).2 horthant
    rw [generalOddGeometricLocalLimitIntegrand,
      Set.indicator_of_mem hscaled, oddWeylLocalLimitIntegrand,
      Set.indicator_of_mem horthant, oddLimitWeylWeight_scalar,
      sum_sq_coordinateScalar_general]
    have hroot : Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      have hdreal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      nlinarith
    have hexponent :
        (-(scalar ^ 2 * ∑ coordinate, coordinates coordinate ^ 2)) /
            (2 * dimension + 1 : ℝ) =
          (-∑ coordinate, coordinates coordinate ^ 2) /
            Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) := by
      dsimp only [scalar]
      rw [generalOddGaussianTransportScale_sq hdimension]
      field_simp [hroot]
    rw [hexponent]
    ring
  · have hscaled : coordinateScalarLinearMap dimension scalar coordinates ∉
        positiveOrthant :=
      mt (mem_positiveOrthant_coordinateScalar_iff hscalar coordinates).1 horthant
    rw [generalOddGeometricLocalLimitIntegrand,
      Set.indicator_of_notMem hscaled, oddWeylLocalLimitIntegrand,
      Set.indicator_of_notMem horthant, mul_zero]

theorem generalOddRibbonLimitIntegral_eq_scaled_geometric
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    (∫ coordinates : Fin dimension → ℝ,
      oddWeylLocalLimitIntegrand dimension coordinates) =
      (generalOddGaussianTransportScale dimension ^
        (2 * dimension ^ 2 + dimension))⁻¹ *
      ∫ coordinates : Fin dimension → ℝ,
        generalOddGeometricLocalLimitIntegrand dimension coordinates := by
  let scalar := generalOddGaussianTransportScale dimension
  let scaleMap := coordinateScalarLinearMap dimension scalar
  let geometric := generalOddGeometricLocalLimitIntegrand dimension
  have hscalar := generalOddGaussianTransportScale_pos (show 1 ≤ dimension by omega)
  have hmap :
      (∫ coordinates, geometric coordinates
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, geometric (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension scalar).aemeasurable
      (stronglyMeasurable_generalOddGeometricLocalLimitIntegrand
        dimension).aestronglyMeasurable
  rw [map_coordinateScalarLinearMap_volume dimension hscalar.ne',
    integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (|scalar ^ dimension|⁻¹)).toReal =
        (scalar ^ dimension)⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    · rw [abs_of_pos (pow_pos hscalar _)]
    · positivity
  rw [htoReal, smul_eq_mul] at hmap
  dsimp only [geometric, scaleMap, scalar] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      generalOddGeometricLocalLimitIntegrand dimension
        (coordinateScalarLinearMap dimension
          (generalOddGaussianTransportScale dimension) coordinates)) =
    fun coordinates => generalOddGaussianTransportScale dimension ^
      (2 * dimension ^ 2) *
        oddWeylLocalLimitIntegrand dimension coordinates by
      funext coordinates
      exact generalOddGeometricLimitIntegrand_transport
        (show 1 ≤ dimension by omega) coordinates,
    integral_const_mul] at hmap
  have hscalarNe : generalOddGaussianTransportScale dimension ≠ 0 :=
    hscalar.ne'
  have hmap' :
      (∫ coordinates : Fin dimension → ℝ,
        generalOddGeometricLocalLimitIntegrand dimension coordinates) =
      generalOddGaussianTransportScale dimension ^
          (2 * dimension ^ 2 + dimension) *
        ∫ coordinates : Fin dimension → ℝ,
          oddWeylLocalLimitIntegrand dimension coordinates := by
    calc
      _ = generalOddGaussianTransportScale dimension ^ dimension *
          ((generalOddGaussianTransportScale dimension ^ dimension)⁻¹ *
            ∫ coordinates : Fin dimension → ℝ,
              generalOddGeometricLocalLimitIntegrand dimension coordinates) := by
        field_simp [hscalarNe]
      _ = generalOddGaussianTransportScale dimension ^ dimension *
          (generalOddGaussianTransportScale dimension ^ (2 * dimension ^ 2) *
            ∫ coordinates : Fin dimension → ℝ,
              oddWeylLocalLimitIntegrand dimension coordinates) := by rw [hmap]
      _ = _ := by
        rw [show generalOddGaussianTransportScale dimension ^ dimension *
              (generalOddGaussianTransportScale dimension ^
                (2 * dimension ^ 2) *
                  ∫ coordinates : Fin dimension → ℝ,
                    oddWeylLocalLimitIntegrand dimension coordinates) =
            (generalOddGaussianTransportScale dimension ^ dimension *
              generalOddGaussianTransportScale dimension ^
                (2 * dimension ^ 2)) *
              ∫ coordinates : Fin dimension → ℝ,
                oddWeylLocalLimitIntegrand dimension coordinates by ring,
          ← pow_add]
        congr 2
        omega
  rw [hmap']
  field_simp [hscalarNe]

theorem generalOddRibbonLocalLimitIntegral_eq_regev
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    (∫ coordinates : Fin dimension → ℝ,
      oddWeylLocalLimitIntegrand dimension coordinates) =
      (generalOddGaussianTransportScale dimension ^
        (2 * dimension ^ 2 + dimension))⁻¹ *
      (regevConstant (2 * dimension + 1) *
        (1 / Real.pi) ^ dimension /
          oddWeylNormalization dimension) := by
  rw [generalOddRibbonLimitIntegral_eq_scaled_geometric hdimension,
    generalOddGeometricLocalLimitIntegral_eq_regev hdimension]

theorem generalOddTransportScale_inverse_power
    {dimension : ℕ} (hdimension : 1 ≤ dimension) :
    (generalOddGaussianTransportScale dimension ^
        (2 * dimension ^ 2 + dimension))⁻¹ =
      (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
        (2 * dimension + 1 : ℝ)) ^
          fixedRankExponent (2 * dimension + 1) := by
  let base : ℝ := 2 * dimension + 1
  let root : ℝ := Real.sqrt (base ^ 2 - 4)
  let total : ℕ := 2 * dimension ^ 2 + dimension
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hroot : 0 < root := by
    dsimp only [root]
    apply Real.sqrt_pos.2
    have hdreal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    dsimp only [base]
    nlinarith
  have hratio : 0 ≤ root / base := (div_pos hroot hbase).le
  have hexponent : fixedRankExponent (2 * dimension + 1) =
      (total : ℝ) / 2 := by
    rw [fixedRankExponent_odd]
    dsimp only [total]
    push_cast
    ring
  have hreciprocal : Real.sqrt (root / base) =
      (generalOddGaussianTransportScale dimension)⁻¹ := by
    unfold generalOddGaussianTransportScale
    dsimp only [base, root]
    rw [Real.sqrt_div hroot.le, Real.sqrt_div hbase.le]
    have hsqrtBase : Real.sqrt (2 * (dimension : ℝ) + 1) ≠ 0 := by positivity
    have hsqrtRoot : Real.sqrt
        (Real.sqrt ((2 * (dimension : ℝ) + 1) ^ 2 - 4)) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      positivity
    field_simp [hsqrtBase, hsqrtRoot]
    ring
  rw [hexponent, Real.rpow_div_two_eq_sqrt (total : ℝ) hratio,
    hreciprocal, Real.rpow_natCast, inv_pow]

theorem tendsto_generalOddRibbon_alphaSuccNormalized
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          ((ribbonCount (2 * dimension) index : ℝ) /
            fixedRankGrowth (2 * dimension + 1) ^ (index + 1)))
      atTop (nhds (regevConstant (2 * dimension + 1) *
        (generalOddGaussianTransportScale dimension ^
          (2 * dimension ^ 2 + dimension))⁻¹ /
            Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) := by
  have h := tendsto_generalOddRibbonNormalizedIntegralConstant hdimension
  rw [generalOddRibbonLocalLimitIntegral_eq_regev hdimension] at h
  have hpi : Real.pi ^ dimension ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hnorm : oddWeylNormalization dimension ≠ 0 := by
    unfold oddWeylNormalization
    positivity
  have hconstant :
      (oddWeylNormalization dimension * Real.pi ^ dimension) *
          ((generalOddGaussianTransportScale dimension ^
              (2 * dimension ^ 2 + dimension))⁻¹ *
            (regevConstant (2 * dimension + 1) *
              (1 / Real.pi) ^ dimension /
                oddWeylNormalization dimension)) =
        regevConstant (2 * dimension + 1) *
          (generalOddGaussianTransportScale dimension ^
            (2 * dimension ^ 2 + dimension))⁻¹ := by
    have hpiCancel : Real.pi ^ dimension *
        (1 / Real.pi) ^ dimension = 1 := by
      rw [← mul_pow]
      field_simp [Real.pi_ne_zero]
      norm_num
    rw [show (oddWeylNormalization dimension * Real.pi ^ dimension) *
          ((generalOddGaussianTransportScale dimension ^
              (2 * dimension ^ 2 + dimension))⁻¹ *
            (regevConstant (2 * dimension + 1) *
              (1 / Real.pi) ^ dimension /
                oddWeylNormalization dimension)) =
      (Real.pi ^ dimension * (1 / Real.pi) ^ dimension) *
        (oddWeylNormalization dimension / oddWeylNormalization dimension) *
          (regevConstant (2 * dimension + 1) *
            (generalOddGaussianTransportScale dimension ^
              (2 * dimension ^ 2 + dimension))⁻¹) by ring,
      hpiCancel, div_self hnorm, one_mul]
    ring
  rw [hconstant] at h
  have hsqrt : Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    nlinarith
  have hdiv := h.div_const
    (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))
  rw [show regevConstant (2 * dimension + 1) *
          (generalOddGaussianTransportScale dimension ^
            (2 * dimension ^ 2 + dimension))⁻¹ /
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) =
      (regevConstant (2 * dimension + 1) *
          (generalOddGaussianTransportScale dimension ^
            (2 * dimension ^ 2 + dimension))⁻¹) /
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) by rfl] at hdiv
  apply hdiv.congr'
  filter_upwards with index
  rw [show largeScalePreimage (2 * dimension + 1 : ℝ) =
      fixedRankGrowth (2 * dimension + 1) by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      largeScalePreimage_natCast (2 * dimension + 1)]
  field_simp [hsqrt,
    (fixedRankGrowth_pos (2 * dimension + 1) (by omega)).ne']

theorem generalOddTransferredConstant_eq_transport
    {dimension : ℕ} (hdimension : 1 ≤ dimension) :
    regevConstant (2 * dimension + 1) *
        (generalOddGaussianTransportScale dimension ^
          (2 * dimension ^ 2 + dimension))⁻¹ /
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) *
        fixedRankGrowth (2 * dimension + 1) =
      transferredFixedRankConstant (2 * dimension + 1) := by
  rw [generalOddTransportScale_inverse_power (show 1 ≤ dimension by omega)]
  unfold transferredFixedRankConstant
  let base : ℝ := 2 * dimension + 1
  let root : ℝ := Real.sqrt (base ^ 2 - 4)
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hroot : 0 < root := by
    dsimp only [root, base]
    apply Real.sqrt_pos.2
    have hdreal : (1 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    nlinarith
  have hratio : 0 < root / base := div_pos hroot hbase
  rw [show (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
      (2 * dimension + 1 : ℝ)) ^ fixedRankExponent (2 * dimension + 1) =
    (root / base) ^ fixedRankExponent (2 * dimension + 1) by rfl]
  rw [show (root / base) ^ fixedRankExponent (2 * dimension + 1) =
      (root / base) ^ (fixedRankExponent (2 * dimension + 1) - 1) *
        (root / base) by
    calc
      (root / base) ^ fixedRankExponent (2 * dimension + 1) =
          (root / base) ^
            ((fixedRankExponent (2 * dimension + 1) - 1) + 1) := by
        congr 1
        ring
      _ = (root / base) ^ (fixedRankExponent (2 * dimension + 1) - 1) *
          (root / base) ^ (1 : ℝ) :=
        Real.rpow_add hratio _ _
      _ = _ := by rw [Real.rpow_one]]
  have halgebra :
      regevConstant (2 * dimension + 1) *
          (root / base) ^ (fixedRankExponent (2 * dimension + 1) - 1) *
          (root / base) / root * fixedRankGrowth (2 * dimension + 1) =
        regevConstant (2 * dimension + 1) *
          fixedRankGrowth (2 * dimension + 1) / base *
          (root / base) ^ (fixedRankExponent (2 * dimension + 1) - 1) := by
    field_simp [hbase.ne', hroot.ne']
  push_cast
  dsimp only [base, root] at halgebra
  simpa only [mul_assoc] using halgebra

theorem tendsto_generalOddRibbon_nPowerNormalized
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index : ℝ) ^ dimension *
        (index : ℝ) ^ (dimension ^ 2) *
          (ribbonCount (2 * dimension) index : ℝ) /
            fixedRankGrowth (2 * dimension + 1) ^ index)
      atTop (nhds (transferredFixedRankConstant (2 * dimension + 1))) := by
  have hscaled := (tendsto_generalOddRibbon_alphaSuccNormalized hdimension).mul_const
    (fixedRankGrowth (2 * dimension + 1))
  rw [generalOddTransferredConstant_eq_transport (by omega)] at hscaled
  have hratioBase := tendsto_offset_div_offset_add_real 0 1
  have hratioSqrtRaw :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hratioBase
  norm_num at hratioSqrtRaw
  have hratioSqrt := hratioSqrtRaw.pow dimension
  norm_num at hratioSqrt
  have hratioPower := hratioBase.pow (dimension ^ 2)
  norm_num at hratioPower
  have hratio := hratioSqrt.mul hratioPower
  norm_num at hratio
  have hproduct := hratio.mul hscaled
  norm_num at hproduct
  apply hproduct.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hi : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  have his : Real.sqrt (index + 1 : ℝ) ≠ 0 := by positivity
  have hgrowth := (fixedRankGrowth_pos (2 * dimension + 1) (by omega)).ne'
  rw [div_pow, div_pow, pow_succ]
  field_simp [hi, his, hgrowth]
  ring

theorem fixedRankRibbonAsymptotic_odd_all
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    FixedRankRibbonAsymptotic (2 * dimension + 1) := by
  unfold FixedRankRibbonAsymptotic
  change (fun index : ℕ => (ribbonCount (2 * dimension) index : ℝ))
    ~[atTop] fixedRankRibbonLeadingTerm (2 * dimension + 1)
  have hnormalized := tendsto_generalOddRibbon_nPowerNormalized hdimension
  have hconstantPos : 0 < transferredFixedRankConstant (2 * dimension + 1) := by
    unfold transferredFixedRankConstant
    apply mul_pos
    · exact div_pos
        (mul_pos
          (regevConstant_pos (2 * dimension + 1) (by omega))
          (fixedRankGrowth_pos (2 * dimension + 1) (by omega)))
        (by positivity)
    · apply Real.rpow_pos_of_pos
      have halphabetPos : (0 : ℝ) < ((2 * dimension + 1 : ℕ) : ℝ) := by
        positivity
      have hrootPos : 0 < Real.sqrt
          ((((2 * dimension + 1 : ℕ) : ℝ)) ^ 2 - 4) := by
        apply Real.sqrt_pos.2
        have halphabet : (5 : ℝ) ≤ ((2 * dimension + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 5 ≤ 2 * dimension + 1 by omega)
        nlinarith
      exact div_pos hrootPos halphabetPos
  have hden : ∀ᶠ index : ℕ in atTop,
      fixedRankRibbonLeadingTerm (2 * dimension + 1) index ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with index hindex
    unfold fixedRankRibbonLeadingTerm
    exact mul_ne_zero (mul_ne_zero hconstantPos.ne'
      (pow_ne_zero _ (fixedRankGrowth_pos _ (by omega)).ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [isEquivalent_iff_tendsto_one hden]
  have hdiv := hnormalized.div_const
    (transferredFixedRankConstant (2 * dimension + 1))
  rw [div_self hconstantPos.ne'] at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hi : (0 : ℝ) < index := by positivity
  have hiNe : (index : ℝ) ≠ 0 := hi.ne'
  rw [sqrt_pow_mul_pow_eq_oddExponent dimension hi]
  simp only [Pi.div_apply]
  unfold fixedRankRibbonLeadingTerm
  rw [Real.rpow_neg hi.le]
  field_simp [hiNe, hconstantPos.ne',
    (fixedRankGrowth_pos (2 * dimension + 1) (by omega)).ne']

end FibonacciRibbonKernel
