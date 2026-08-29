import FibonacciRibbonKernel.GeneralEvenGeometricFullLimit

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

noncomputable def generalEvenGeometricMiddleRatio (dimension : ℕ) : ℝ :=
  cosineScaleMidpoint dimension / (2 * dimension : ℝ)

theorem generalEvenGeometricMiddleRatio_pos
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    0 < generalEvenGeometricMiddleRatio dimension := by
  unfold generalEvenGeometricMiddleRatio cosineScaleMidpoint
  positivity

theorem generalEvenGeometricMiddleRatio_lt_one
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    generalEvenGeometricMiddleRatio dimension < 1 := by
  rw [generalEvenGeometricMiddleRatio, div_lt_one (by positivity)]
  apply cosineScaleMidpoint_lt_base
  have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
  linarith

theorem norm_generalEvenGeometricMiddleProductIntegrand_le
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (index : ℕ) (angles : Fin dimension → ℝ) :
    ‖generalEvenGeometricMiddleProductIntegrand
        dimension index angles‖ ≤
      ((1 / Real.pi) ^ dimension *
        ((4 : ℝ) ^ weylPairCount dimension * (2 : ℝ) ^ dimension)) *
          generalEvenGeometricMiddleRatio dimension ^ index := by
  by_cases hmiddle : angles ∈ middleOpenSpectralDomain dimension
  · rw [generalEvenGeometricMiddleProductIntegrand,
      Set.indicator_of_mem hmiddle,
      generalEvenGeometricFullIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
      abs_of_nonneg (evenWeylAngleWeight_nonneg dimension angles)]
    have hscale := middleOpen_abs_scale_le hmiddle
    have hratio : |cosineCubeScale angles / (2 * dimension : ℝ)| ≤
        generalEvenGeometricMiddleRatio dimension := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * dimension)]
      unfold generalEvenGeometricMiddleRatio
      exact div_le_div_of_nonneg_right hscale (by positivity)
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hratio index
    have hweight := evenWeylAngleWeight_le_constant dimension angles
    have hproduct := mul_le_mul
      (mul_le_mul_of_nonneg_left hpow
        (pow_nonneg (le_of_lt (one_div_pos.mpr Real.pi_pos)) dimension))
      hweight (evenWeylAngleWeight_nonneg dimension angles)
      (mul_nonneg
        (pow_nonneg (le_of_lt (one_div_pos.mpr Real.pi_pos)) dimension)
        (pow_nonneg (generalEvenGeometricMiddleRatio_pos hdimension).le _))
    calc
      (1 / Real.pi) ^ dimension *
          |(cosineCubeScale angles / (2 * dimension : ℝ)) ^ index| *
            evenWeylAngleWeight dimension angles =
        (1 / Real.pi) ^ dimension *
          |cosineCubeScale angles / (2 * dimension : ℝ)| ^ index *
            evenWeylAngleWeight dimension angles := by rw [abs_pow]
      _ ≤ _ := hproduct
      _ = _ := by ring
  · rw [generalEvenGeometricMiddleProductIntegrand,
      Set.indicator_of_notMem hmiddle, norm_zero]
    exact mul_nonneg (by positivity)
      (pow_nonneg (generalEvenGeometricMiddleRatio_pos hdimension).le _)

theorem tendsto_generalEvenGeometricMiddlePolynomial
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^
          (dimension * (dimension - 1) + dimension) *
        generalEvenGeometricMiddleRatio dimension ^ index)
      atTop (nhds 0) := by
  let exponent := dimension * (dimension - 1) + dimension
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one exponent
    (by rw [abs_of_pos (generalEvenGeometricMiddleRatio_pos hdimension)]
        exact generalEvenGeometricMiddleRatio_lt_one hdimension)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hdiv := hshift.div_const
    (generalEvenGeometricMiddleRatio dimension)
  rw [zero_div] at hdiv
  apply hdiv.congr'
  filter_upwards with index
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  field_simp [(generalEvenGeometricMiddleRatio_pos hdimension).ne']
  ring

theorem tendsto_generalEvenGeometricMiddleIntegral_zero
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricMiddleIntegral dimension index)
      atTop (nhds 0) := by
  let exponent := dimension * (dimension - 1) + dimension
  let constant : ℝ :=
    ((1 / Real.pi) ^ dimension *
      ((4 : ℝ) ^ weylPairCount dimension * (2 : ℝ) ^ dimension)) *
        (cosineCubeProductMeasure dimension).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ exponent *
        generalEvenGeometricMiddleRatio dimension ^ index) * constant)
  · intro index
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _),
      abs_of_nonneg (pow_nonneg (by positivity) _)]
    have hintegral : ‖generalEvenGeometricMiddleIntegral
        dimension index‖ ≤
      (((1 / Real.pi) ^ dimension *
        ((4 : ℝ) ^ weylPairCount dimension * (2 : ℝ) ^ dimension)) *
          generalEvenGeometricMiddleRatio dimension ^ index) *
            (cosineCubeProductMeasure dimension).real Set.univ := by
      unfold generalEvenGeometricMiddleIntegral
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall
          (norm_generalEvenGeometricMiddleProductIntegrand_le
            hdimension index))
    have hsqrt : Real.sqrt (index + 1 : ℝ) ≤ (index + 1 : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
    have hsqrtPow := pow_le_pow_left₀
      (Real.sqrt_nonneg _) hsqrt dimension
    have hpoly : Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) ≤
        (index + 1 : ℝ) ^ exponent := by
      calc
        _ ≤ (index + 1 : ℝ) ^ dimension *
            (index + 1 : ℝ) ^ (dimension * (dimension - 1)) :=
          mul_le_mul_of_nonneg_right hsqrtPow (by positivity)
        _ = _ := by unfold exponent; rw [← pow_add]; congr 1; omega
    calc
      Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
            ‖generalEvenGeometricMiddleIntegral dimension index‖ ≤
        (index + 1 : ℝ) ^ exponent *
          ‖generalEvenGeometricMiddleIntegral dimension index‖ :=
        mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hintegral (by positivity)
      _ = _ := by ring
  · simpa only [zero_mul] using
      (tendsto_generalEvenGeometricMiddlePolynomial hdimension).mul_const constant

theorem generalEvenGeometricFullIntegral_partition
    (dimension index : ℕ) :
    generalEvenGeometricFullIntegral dimension index =
      generalEvenGeometricAngleLocalIntegral dimension index +
        (generalEvenGeometricNegativeIntegral dimension index +
          generalEvenGeometricMiddleIntegral dimension index) := by
  unfold generalEvenGeometricFullIntegral
    generalEvenGeometricNegativeIntegral
    generalEvenGeometricMiddleIntegral
  rw [show (fun angles : Fin dimension → ℝ =>
      generalEvenGeometricFullIntegrand dimension index angles) =
    fun angles =>
      generalEvenGeometricPositiveProductIntegrand dimension index angles +
        (generalEvenGeometricNegativeProductIntegrand dimension index angles +
          generalEvenGeometricMiddleProductIntegrand
            dimension index angles) by
      funext angles
      exact generalEvenGeometricFullIntegrand_partition
        dimension index angles]
  have hfull := integrable_generalEvenGeometricFullIntegrand dimension index
  have hpositive := hfull.indicator
    (measurableSet_positiveSpectralLocalDomain dimension)
  have hnegative := hfull.indicator
    (measurableSet_negativeSpectralLocalDomain dimension)
  have hmiddle := hfull.indicator
    (measurableSet_middleOpenSpectralDomain dimension)
  change Integrable
    (generalEvenGeometricPositiveProductIntegrand dimension index)
    (cosineCubeProductMeasure dimension) at hpositive
  change Integrable
    (generalEvenGeometricNegativeProductIntegrand dimension index)
    (cosineCubeProductMeasure dimension) at hnegative
  change Integrable
    (generalEvenGeometricMiddleProductIntegrand dimension index)
    (cosineCubeProductMeasure dimension) at hmiddle
  calc
    (∫ angles : Fin dimension → ℝ,
      generalEvenGeometricPositiveProductIntegrand dimension index angles +
        (generalEvenGeometricNegativeProductIntegrand dimension index angles +
          generalEvenGeometricMiddleProductIntegrand dimension index angles)
      ∂cosineCubeProductMeasure dimension) =
      (∫ angles : Fin dimension → ℝ,
        generalEvenGeometricPositiveProductIntegrand dimension index angles
        ∂cosineCubeProductMeasure dimension) +
      ∫ angles : Fin dimension → ℝ,
        (generalEvenGeometricNegativeProductIntegrand dimension index angles +
          generalEvenGeometricMiddleProductIntegrand dimension index angles)
        ∂cosineCubeProductMeasure dimension :=
      integral_add hpositive (hnegative.add hmiddle)
    _ = (∫ angles : Fin dimension → ℝ,
          generalEvenGeometricPositiveProductIntegrand dimension index angles
          ∂cosineCubeProductMeasure dimension) +
        ((∫ angles : Fin dimension → ℝ,
            generalEvenGeometricNegativeProductIntegrand dimension index angles
            ∂cosineCubeProductMeasure dimension) +
          ∫ angles : Fin dimension → ℝ,
            generalEvenGeometricMiddleProductIntegrand dimension index angles
            ∂cosineCubeProductMeasure dimension) := by
      rw [integral_add hnegative hmiddle]
    _ = _ := by rw [generalEvenGeometricPositiveIntegral_eq_angleLocal]

theorem tendsto_generalEvenGeometricFullIntegral
    (dimension : ℕ) (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricFullIntegral dimension index)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalEvenGeometricLocalLimitIntegrand dimension coordinates)) := by
  have hlocal : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricAngleLocalIntegral dimension index)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalEvenGeometricLocalLimitIntegrand dimension coordinates)) := by
    rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricAngleLocalIntegral dimension index) =
      fun index => ∫ coordinates : Fin dimension → ℝ,
        generalEvenGeometricLocalRescaledIntegrand
          dimension index coordinates by
        funext index
        exact generalEvenGeometricLocalScalingIntegral_identity
          dimension index]
    exact tendsto_integral_generalEvenGeometricLocalRescaledIntegrand
      dimension hdimension
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricFullIntegral dimension index) =
    fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricAngleLocalIntegral dimension index +
      (Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
            generalEvenGeometricNegativeIntegral dimension index +
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
            generalEvenGeometricMiddleIntegral dimension index) by
      funext index
      rw [generalEvenGeometricFullIntegral_partition]
      ring]
  simpa using hlocal.add
    ((tendsto_generalEvenGeometricNegativeIntegral_zero
      dimension hdimension).add
      (tendsto_generalEvenGeometricMiddleIntegral_zero
        dimension hdimension))

theorem generalEvenGeometricFullIntegral_eq_weylMoment
    (dimension index : ℕ) :
    generalEvenGeometricFullIntegral dimension index =
      (1 / Real.pi) ^ dimension *
        (evenWeylGeometricMoment dimension index /
          (2 * dimension : ℝ) ^ index) := by
  unfold generalEvenGeometricFullIntegral generalEvenGeometricFullIntegrand
    evenWeylGeometricMoment weightedCosineCubeMoment
    weightedCosineCubePowerIntegrand
  rw [show (fun angles : Fin dimension → ℝ =>
      (1 / Real.pi) ^ dimension *
        (cosineCubeScale angles / (2 * dimension : ℝ)) ^ index *
          evenWeylAngleWeight dimension angles) =
    fun angles => ((1 / Real.pi) ^ dimension /
      (2 * dimension : ℝ) ^ index) *
        (cosineCubeScale angles ^ index *
          evenWeylAngleWeight dimension angles) by
      funext angles
      let base : ℝ := (2 * dimension : ℝ)
      change (1 / Real.pi) ^ dimension *
          (cosineCubeScale angles / base) ^ index *
            evenWeylAngleWeight dimension angles =
        ((1 / Real.pi) ^ dimension / base ^ index) *
          (cosineCubeScale angles ^ index *
            evenWeylAngleWeight dimension angles)
      rw [div_pow]
      ring]
  rw [integral_const_mul]
  ring

theorem generalEvenGeometricFullIntegral_eq_unrestrictedCount
    (dimension : ℕ) (hdimension : 1 ≤ dimension) (index : ℕ) :
    generalEvenGeometricFullIntegral dimension index =
      (1 / Real.pi) ^ dimension / evenWeylNormalization dimension *
        ((unrestrictedCount (2 * dimension - 1) index : ℝ) /
          (2 * dimension : ℝ) ^ index) := by
  rw [generalEvenGeometricFullIntegral_eq_weylMoment,
    generalEvenUnrestrictedCount_eq_normalizedWeylMoment
      dimension hdimension]
  have hnorm : evenWeylNormalization dimension ≠ 0 := by
    unfold evenWeylNormalization
    positivity
  field_simp [hnorm]

end FibonacciRibbonKernel
