import FibonacciRibbonKernel.GeneralEvenGeometricTailLimit
import FibonacciRibbonKernel.GeneralOddGeometricLimit

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

theorem fixedRankExponent_even (dimension : ℕ) :
    fixedRankExponent (2 * dimension) =
      (dimension : ℝ) ^ 2 - (dimension : ℝ) / 2 := by
  by_cases hzero : dimension = 0
  · simp [hzero, fixedRankExponent]
  have hpositive : 1 ≤ dimension := Nat.one_le_iff_ne_zero.2 hzero
  unfold fixedRankExponent
  rw [Nat.cast_sub (show 1 ≤ 2 * dimension by omega)]
  push_cast
  ring

theorem sqrt_pow_mul_pow_eq_evenExponent
    (dimension : ℕ) (hdimension : 1 ≤ dimension)
    {value : ℝ} (hvalue : 0 < value) :
    Real.sqrt value ^ dimension *
        value ^ (dimension * (dimension - 1)) =
      value ^ fixedRankExponent (2 * dimension) := by
  rw [fixedRankExponent_even, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hvalue.le]
  rw [← Real.rpow_add hvalue]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sub hdimension]
  push_cast
  ring

theorem tendsto_generalEvenUnrestrictedNormalized_regev
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          ((unrestrictedCount (2 * dimension - 1) index : ℝ) /
            (2 * dimension : ℝ) ^ index))
      atTop (nhds (regevConstant (2 * dimension))) := by
  have hrankSucc : 2 * dimension - 1 + 1 = 2 * dimension := by omega
  have hraw0 := unrestrictedCount_normalized_tendsto_regevConstant_of_mehta
    (2 * dimension - 1)
      (regevMehtaChamberEvaluation_all (2 * dimension - 1))
  have hraw : Tendsto
      (fun index =>
        (unrestrictedCount (2 * dimension - 1) index : ℝ) /
          generalRegevBaseScale (2 * dimension - 1) index)
      atTop (nhds (regevConstant (2 * dimension))) := by
    simpa only [hrankSucc] using hraw0
  have hnormalized : Tendsto (fun index : ℕ =>
      Real.sqrt (index : ℝ) ^ dimension *
        (index : ℝ) ^ (dimension * (dimension - 1)) *
          ((unrestrictedCount (2 * dimension - 1) index : ℝ) /
            (2 * dimension : ℝ) ^ index))
      atTop (nhds (regevConstant (2 * dimension))) := by
    apply hraw.congr'
    filter_upwards [eventually_ne_atTop 0] with index hindex
    have hi : (0 : ℝ) < index := by positivity
    unfold generalRegevBaseScale
    rw [hrankSucc, Real.rpow_neg hi.le]
    rw [sqrt_pow_mul_pow_eq_evenExponent dimension (by omega) hi]
    push_cast
    field_simp [(show (2 * dimension : ℝ) ≠ 0 by positivity),
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
  have hratioPower := hratioBase.pow (dimension * (dimension - 1))
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

theorem generalEvenGeometricLocalLimitIntegral_eq_regev
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    (∫ coordinates : Fin dimension → ℝ,
      generalEvenGeometricLocalLimitIntegrand dimension coordinates) =
      regevConstant (2 * dimension) *
        (1 / Real.pi) ^ dimension /
          evenWeylNormalization dimension := by
  have hcount := tendsto_generalEvenUnrestrictedNormalized_regev hdimension
  have hfull := tendsto_generalEvenGeometricFullIntegral dimension hdimension
  have hscaled : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          generalEvenGeometricFullIntegral dimension index)
      atTop (nhds (regevConstant (2 * dimension) *
        (1 / Real.pi) ^ dimension /
          evenWeylNormalization dimension)) := by
    have hconstant : Tendsto (fun _ : ℕ =>
        (1 / Real.pi) ^ dimension / evenWeylNormalization dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension /
          evenWeylNormalization dimension)) := tendsto_const_nhds
    have hmul := hconstant.mul hcount
    rw [show regevConstant (2 * dimension) *
        (1 / Real.pi) ^ dimension / evenWeylNormalization dimension =
      ((1 / Real.pi) ^ dimension / evenWeylNormalization dimension) *
        regevConstant (2 * dimension) by ring]
    apply hmul.congr'
    filter_upwards with index
    rw [generalEvenGeometricFullIntegral_eq_unrestrictedCount
      dimension (by omega) index]
    ring
  exact tendsto_nhds_unique hfull hscaled

noncomputable def generalEvenGaussianTransportScale (dimension : ℕ) : ℝ :=
  Real.sqrt ((2 * dimension : ℝ) /
    Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))

theorem generalEvenGaussianTransportScale_pos
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    0 < generalEvenGaussianTransportScale dimension := by
  unfold generalEvenGaussianTransportScale
  have hroot : 0 < Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    nlinarith
  positivity

theorem generalEvenGaussianTransportScale_sq
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    generalEvenGaussianTransportScale dimension ^ 2 =
      (2 * dimension : ℝ) /
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
  unfold generalEvenGaussianTransportScale
  apply Real.sq_sqrt
  have hroot : 0 < Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    nlinarith
  positivity

theorem evenLimitWeylWeight_scalar
    (dimension : ℕ) (scalar : ℝ) (coordinates : Fin dimension → ℝ) :
    evenLimitWeylWeight dimension
        (coordinateScalarLinearMap dimension scalar coordinates) =
      scalar ^ (2 * dimension * (dimension - 1)) *
        evenLimitWeylWeight dimension coordinates := by
  unfold evenLimitWeylWeight
  rw [quadraticVandermondeWeight_scalar]
  have hexponent : 4 * weylPairCount dimension =
      2 * dimension * (dimension - 1) := by
    calc
      4 * weylPairCount dimension =
          2 * (2 * weylPairCount dimension) := by ring
      _ = 2 * (dimension * (dimension - 1)) := by
        rw [weylPairCount_formula]
      _ = _ := by ring
  rw [hexponent]
  ring

theorem stronglyMeasurable_generalEvenGeometricLocalLimitIntegrand
    (dimension : ℕ) :
    StronglyMeasurable
      (generalEvenGeometricLocalLimitIntegrand dimension) := by
  unfold generalEvenGeometricLocalLimitIntegrand
  have hweight : Continuous (evenLimitWeylWeight dimension) := by
    unfold evenLimitWeylWeight
    exact (continuous_quadraticVandermondeWeight dimension).mul
      continuous_const
  exact (((continuous_const.mul
    (Real.continuous_exp.comp (by fun_prop))).mul hweight).stronglyMeasurable.indicator
      (measurableSet_positiveOrthant dimension))

theorem generalEvenGeometricLimitIntegrand_transport
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (coordinates : Fin dimension → ℝ) :
    generalEvenGeometricLocalLimitIntegrand dimension
        (coordinateScalarLinearMap dimension
          (generalEvenGaussianTransportScale dimension) coordinates) =
      generalEvenGaussianTransportScale dimension ^
          (2 * dimension * (dimension - 1)) *
        generalEvenWeylLocalLimitIntegrand dimension coordinates := by
  let scalar := generalEvenGaussianTransportScale dimension
  have hscalar := generalEvenGaussianTransportScale_pos hdimension
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hscaled :=
      (mem_positiveOrthant_coordinateScalar_iff hscalar coordinates).2 horthant
    rw [generalEvenGeometricLocalLimitIntegrand,
      Set.indicator_of_mem hscaled, generalEvenWeylLocalLimitIntegrand,
      Set.indicator_of_mem horthant, evenLimitWeylWeight_scalar,
      sum_sq_coordinateScalar_general]
    have hroot : Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      nlinarith
    have hexponent :
        (-(scalar ^ 2 * ∑ coordinate, coordinates coordinate ^ 2)) /
            (2 * dimension : ℝ) =
          (-∑ coordinate, coordinates coordinate ^ 2) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
      dsimp only [scalar]
      rw [generalEvenGaussianTransportScale_sq hdimension]
      field_simp [hroot]
    rw [hexponent]
    ring
  · have hscaled : coordinateScalarLinearMap dimension scalar coordinates ∉
        positiveOrthant :=
      mt (mem_positiveOrthant_coordinateScalar_iff hscalar coordinates).1 horthant
    rw [generalEvenGeometricLocalLimitIntegrand,
      Set.indicator_of_notMem hscaled, generalEvenWeylLocalLimitIntegrand,
      Set.indicator_of_notMem horthant, mul_zero]

theorem generalEvenRibbonLimitIntegral_eq_scaled_geometric
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    (∫ coordinates : Fin dimension → ℝ,
      generalEvenWeylLocalLimitIntegrand dimension coordinates) =
      (generalEvenGaussianTransportScale dimension ^
        (2 * dimension * (dimension - 1) + dimension))⁻¹ *
      ∫ coordinates : Fin dimension → ℝ,
        generalEvenGeometricLocalLimitIntegrand dimension coordinates := by
  let scalar := generalEvenGaussianTransportScale dimension
  let scaleMap := coordinateScalarLinearMap dimension scalar
  let geometric := generalEvenGeometricLocalLimitIntegrand dimension
  have hscalar := generalEvenGaussianTransportScale_pos hdimension
  have hmap :
      (∫ coordinates, geometric coordinates
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, geometric (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension scalar).aemeasurable
      (stronglyMeasurable_generalEvenGeometricLocalLimitIntegrand
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
      generalEvenGeometricLocalLimitIntegrand dimension
        (coordinateScalarLinearMap dimension
          (generalEvenGaussianTransportScale dimension) coordinates)) =
    fun coordinates => generalEvenGaussianTransportScale dimension ^
      (2 * dimension * (dimension - 1)) *
        generalEvenWeylLocalLimitIntegrand dimension coordinates by
      funext coordinates
      exact generalEvenGeometricLimitIntegrand_transport
        hdimension coordinates,
    integral_const_mul] at hmap
  have hscalarNe : generalEvenGaussianTransportScale dimension ≠ 0 :=
    hscalar.ne'
  have hmap' :
      (∫ coordinates : Fin dimension → ℝ,
        generalEvenGeometricLocalLimitIntegrand dimension coordinates) =
      generalEvenGaussianTransportScale dimension ^
          (2 * dimension * (dimension - 1) + dimension) *
        ∫ coordinates : Fin dimension → ℝ,
          generalEvenWeylLocalLimitIntegrand dimension coordinates := by
    calc
      _ = generalEvenGaussianTransportScale dimension ^ dimension *
          ((generalEvenGaussianTransportScale dimension ^ dimension)⁻¹ *
            ∫ coordinates : Fin dimension → ℝ,
              generalEvenGeometricLocalLimitIntegrand
                dimension coordinates) := by
        field_simp [hscalarNe]
      _ = generalEvenGaussianTransportScale dimension ^ dimension *
          (generalEvenGaussianTransportScale dimension ^
              (2 * dimension * (dimension - 1)) *
            ∫ coordinates : Fin dimension → ℝ,
              generalEvenWeylLocalLimitIntegrand
                dimension coordinates) := by rw [hmap]
      _ = _ := by
        rw [show generalEvenGaussianTransportScale dimension ^ dimension *
              (generalEvenGaussianTransportScale dimension ^
                  (2 * dimension * (dimension - 1)) *
                ∫ coordinates : Fin dimension → ℝ,
                  generalEvenWeylLocalLimitIntegrand dimension coordinates) =
            (generalEvenGaussianTransportScale dimension ^ dimension *
              generalEvenGaussianTransportScale dimension ^
                (2 * dimension * (dimension - 1))) *
              ∫ coordinates : Fin dimension → ℝ,
                generalEvenWeylLocalLimitIntegrand dimension coordinates by ring,
          ← pow_add]
        congr 2
        omega
  rw [hmap']
  field_simp [hscalarNe]

theorem generalEvenRibbonLocalLimitIntegral_eq_regev
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    (∫ coordinates : Fin dimension → ℝ,
      generalEvenWeylLocalLimitIntegrand dimension coordinates) =
      (generalEvenGaussianTransportScale dimension ^
        (2 * dimension * (dimension - 1) + dimension))⁻¹ *
      (regevConstant (2 * dimension) *
        (1 / Real.pi) ^ dimension /
          evenWeylNormalization dimension) := by
  rw [generalEvenRibbonLimitIntegral_eq_scaled_geometric hdimension,
    generalEvenGeometricLocalLimitIntegral_eq_regev hdimension]

theorem generalEvenTransportScale_inverse_power
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    (generalEvenGaussianTransportScale dimension ^
        (2 * dimension * (dimension - 1) + dimension))⁻¹ =
      (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
        (2 * dimension : ℝ)) ^
          fixedRankExponent (2 * dimension) := by
  let base : ℝ := 2 * dimension
  let root : ℝ := Real.sqrt (base ^ 2 - 4)
  let total : ℕ := 2 * dimension * (dimension - 1) + dimension
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hroot : 0 < root := by
    dsimp only [root]
    apply Real.sqrt_pos.2
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    dsimp only [base]
    nlinarith
  have hratio : 0 ≤ root / base := (div_pos hroot hbase).le
  have hexponent : fixedRankExponent (2 * dimension) =
      (total : ℝ) / 2 := by
    rw [fixedRankExponent_even]
    dsimp only [total]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ dimension by omega)]
    push_cast
    ring
  have hreciprocal : Real.sqrt (root / base) =
      (generalEvenGaussianTransportScale dimension)⁻¹ := by
    unfold generalEvenGaussianTransportScale
    dsimp only [base, root]
    rw [Real.sqrt_div hroot.le, Real.sqrt_div hbase.le]
    have hsqrtBase : Real.sqrt (2 * (dimension : ℝ)) ≠ 0 := by positivity
    have hsqrtRoot : Real.sqrt
        (Real.sqrt ((2 * (dimension : ℝ)) ^ 2 - 4)) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.2
      positivity
    field_simp [hsqrtBase, hsqrtRoot]
    dsimp only [base, root]
    ring_nf
  rw [hexponent, Real.rpow_div_two_eq_sqrt (total : ℝ) hratio,
    hreciprocal, Real.rpow_natCast, inv_pow]

theorem tendsto_generalEvenRibbon_alphaSuccNormalized
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          ((ribbonCount (2 * dimension - 1) index : ℝ) /
            fixedRankGrowth (2 * dimension) ^ (index + 1)))
      atTop (nhds (regevConstant (2 * dimension) *
        (generalEvenGaussianTransportScale dimension ^
          (2 * dimension * (dimension - 1) + dimension))⁻¹ /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) := by
  have h := tendsto_generalEvenRibbonNormalizedIntegralConstant
    dimension hdimension
  rw [generalEvenRibbonLocalLimitIntegral_eq_regev hdimension] at h
  have hnorm : evenWeylNormalization dimension ≠ 0 := by
    unfold evenWeylNormalization
    positivity
  have hconstant :
      (evenWeylNormalization dimension * Real.pi ^ dimension) *
          ((generalEvenGaussianTransportScale dimension ^
              (2 * dimension * (dimension - 1) + dimension))⁻¹ *
            (regevConstant (2 * dimension) *
              (1 / Real.pi) ^ dimension /
                evenWeylNormalization dimension)) =
        regevConstant (2 * dimension) *
          (generalEvenGaussianTransportScale dimension ^
            (2 * dimension * (dimension - 1) + dimension))⁻¹ := by
    have hpiCancel : Real.pi ^ dimension *
        (1 / Real.pi) ^ dimension = 1 := by
      rw [← mul_pow]
      field_simp [Real.pi_ne_zero]
      norm_num
    rw [show (evenWeylNormalization dimension * Real.pi ^ dimension) *
          ((generalEvenGaussianTransportScale dimension ^
              (2 * dimension * (dimension - 1) + dimension))⁻¹ *
            (regevConstant (2 * dimension) *
              (1 / Real.pi) ^ dimension /
                evenWeylNormalization dimension)) =
      (Real.pi ^ dimension * (1 / Real.pi) ^ dimension) *
        (evenWeylNormalization dimension / evenWeylNormalization dimension) *
          (regevConstant (2 * dimension) *
            (generalEvenGaussianTransportScale dimension ^
              (2 * dimension * (dimension - 1) + dimension))⁻¹) by ring,
      hpiCancel, div_self hnorm, one_mul]
    ring
  rw [hconstant] at h
  have hsqrt : Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    nlinarith
  have hdiv := h.div_const
    (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))
  rw [show regevConstant (2 * dimension) *
          (generalEvenGaussianTransportScale dimension ^
            (2 * dimension * (dimension - 1) + dimension))⁻¹ /
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) =
      (regevConstant (2 * dimension) *
          (generalEvenGaussianTransportScale dimension ^
            (2 * dimension * (dimension - 1) + dimension))⁻¹) /
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) by rfl] at hdiv
  apply hdiv.congr'
  filter_upwards with index
  have hsqrtNormalized :
      Real.sqrt (2 ^ 2 * (dimension : ℝ) ^ 2 - 4) ≠ 0 := by
    convert hsqrt using 1
    ring_nf
  rw [show largeScalePreimage (2 * dimension : ℝ) =
      fixedRankGrowth (2 * dimension) by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      largeScalePreimage_natCast (2 * dimension)]
  field_simp [hsqrt, hsqrtNormalized,
    (fixedRankGrowth_pos (2 * dimension) (by omega)).ne']

theorem generalEvenTransferredConstant_eq_transport
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    regevConstant (2 * dimension) *
        (generalEvenGaussianTransportScale dimension ^
          (2 * dimension * (dimension - 1) + dimension))⁻¹ /
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) *
        fixedRankGrowth (2 * dimension) =
      transferredFixedRankConstant (2 * dimension) := by
  rw [generalEvenTransportScale_inverse_power hdimension]
  unfold transferredFixedRankConstant
  let base : ℝ := 2 * dimension
  let root : ℝ := Real.sqrt (base ^ 2 - 4)
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hroot : 0 < root := by
    dsimp only [root, base]
    apply Real.sqrt_pos.2
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    nlinarith
  have hratio : 0 < root / base := div_pos hroot hbase
  rw [show (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
      (2 * dimension : ℝ)) ^ fixedRankExponent (2 * dimension) =
    (root / base) ^ fixedRankExponent (2 * dimension) by rfl]
  rw [show (root / base) ^ fixedRankExponent (2 * dimension) =
      (root / base) ^ (fixedRankExponent (2 * dimension) - 1) *
        (root / base) by
    calc
      (root / base) ^ fixedRankExponent (2 * dimension) =
          (root / base) ^
            ((fixedRankExponent (2 * dimension) - 1) + 1) := by
        congr 1
        ring
      _ = (root / base) ^ (fixedRankExponent (2 * dimension) - 1) *
          (root / base) ^ (1 : ℝ) :=
        Real.rpow_add hratio _ _
      _ = _ := by rw [Real.rpow_one]]
  have halgebra :
      regevConstant (2 * dimension) *
          (root / base) ^ (fixedRankExponent (2 * dimension) - 1) *
          (root / base) / root * fixedRankGrowth (2 * dimension) =
        regevConstant (2 * dimension) *
          fixedRankGrowth (2 * dimension) / base *
          (root / base) ^ (fixedRankExponent (2 * dimension) - 1) := by
    field_simp [hbase.ne', hroot.ne']
  push_cast
  dsimp only [base, root] at halgebra
  simpa only [mul_assoc] using halgebra

theorem tendsto_generalEvenRibbon_nPowerNormalized
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index : ℝ) ^ dimension *
        (index : ℝ) ^ (dimension * (dimension - 1)) *
          (ribbonCount (2 * dimension - 1) index : ℝ) /
            fixedRankGrowth (2 * dimension) ^ index)
      atTop (nhds (transferredFixedRankConstant (2 * dimension))) := by
  have hscaled :=
    (tendsto_generalEvenRibbon_alphaSuccNormalized hdimension).mul_const
      (fixedRankGrowth (2 * dimension))
  rw [generalEvenTransferredConstant_eq_transport hdimension] at hscaled
  have hratioBase := tendsto_offset_div_offset_add_real 0 1
  have hratioSqrtRaw :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hratioBase
  norm_num at hratioSqrtRaw
  have hratioSqrt := hratioSqrtRaw.pow dimension
  norm_num at hratioSqrt
  have hratioPower := hratioBase.pow (dimension * (dimension - 1))
  norm_num at hratioPower
  have hratio := hratioSqrt.mul hratioPower
  norm_num at hratio
  have hproduct := hratio.mul hscaled
  norm_num at hproduct
  apply hproduct.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hi : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  have his : Real.sqrt (index + 1 : ℝ) ≠ 0 := by positivity
  have hgrowth := (fixedRankGrowth_pos (2 * dimension) (by omega)).ne'
  rw [div_pow, div_pow, pow_succ]
  field_simp [hi, his, hgrowth]

theorem fixedRankRibbonAsymptotic_even_all
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    FixedRankRibbonAsymptotic (2 * dimension) := by
  unfold FixedRankRibbonAsymptotic
  have hnormalized := tendsto_generalEvenRibbon_nPowerNormalized hdimension
  have hconstantPos : 0 < transferredFixedRankConstant (2 * dimension) := by
    unfold transferredFixedRankConstant
    apply mul_pos
    · exact div_pos
        (mul_pos
          (regevConstant_pos (2 * dimension) (by omega))
          (fixedRankGrowth_pos (2 * dimension) (by omega)))
        (by positivity)
    · apply Real.rpow_pos_of_pos
      have halphabetPos : (0 : ℝ) < ((2 * dimension : ℕ) : ℝ) := by
        positivity
      have hrootPos : 0 < Real.sqrt
          ((((2 * dimension : ℕ) : ℝ)) ^ 2 - 4) := by
        apply Real.sqrt_pos.2
        have halphabet : (4 : ℝ) ≤ ((2 * dimension : ℕ) : ℝ) := by
          exact_mod_cast (show 4 ≤ 2 * dimension by omega)
        nlinarith
      exact div_pos hrootPos halphabetPos
  have hden : ∀ᶠ index : ℕ in atTop,
      fixedRankRibbonLeadingTerm (2 * dimension) index ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with index hindex
    unfold fixedRankRibbonLeadingTerm
    exact mul_ne_zero (mul_ne_zero hconstantPos.ne'
      (pow_ne_zero _ (fixedRankGrowth_pos _ (by omega)).ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [isEquivalent_iff_tendsto_one hden]
  have hdiv := hnormalized.div_const
    (transferredFixedRankConstant (2 * dimension))
  rw [div_self hconstantPos.ne'] at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hi : (0 : ℝ) < index := by positivity
  have hiNe : (index : ℝ) ≠ 0 := hi.ne'
  rw [sqrt_pow_mul_pow_eq_evenExponent dimension (by omega) hi]
  simp only [Pi.div_apply]
  unfold fixedRankRibbonLeadingTerm
  rw [Real.rpow_neg hi.le]
  field_simp [hiNe, hconstantPos.ne',
    (fixedRankGrowth_pos (2 * dimension) (by omega)).ne']

end FibonacciRibbonKernel
