import FibonacciRibbonKernel.GeneralWeylDomination
import FibonacciRibbonKernel.RankFiveTailDecay

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

theorem absoluteKernelGrowth_two_below_lt_largeScalePreimage
    {base : ℝ} (hbase : 3 ≤ base) :
    absoluteKernelGrowth (base - 2) < largeScalePreimage base := by
  let bound := base - 2
  let gamma := absoluteKernelGrowth bound
  let alpha := largeScalePreimage base
  have hboundNonneg : 0 ≤ bound := by dsimp [bound]; linarith
  have hgammaPos : 0 < gamma := absoluteKernelGrowth_pos hboundNonneg
  have halphaPos : 0 < alpha := largeScalePreimage_pos (by linarith)
  have hgammaEq : gamma ^ 2 = bound * gamma + 1 :=
    absoluteKernelGrowth_quadratic hboundNonneg
  have halphaEq : alpha ^ 2 = base * alpha - 1 := by
    have hquad := positiveScalePreimage_quadratic
      (show 2 ≤ base by linarith)
    have hmul := positiveScalePreimage_mul_largeScalePreimage
      (show 2 ≤ base by linarith)
    have hsum := largeScalePreimage_add_positiveScalePreimage base
    nlinarith
  by_contra hnot
  have hle : alpha ≤ gamma := le_of_not_gt hnot
  have hfactor : 0 ≤ gamma + alpha - bound := by
    have hgammaGe := absoluteKernelGrowth_ge_bound hboundNonneg
    linarith
  have hleftNonneg : 0 ≤ (gamma - alpha) *
      (gamma + alpha - bound) :=
    mul_nonneg (sub_nonneg.2 hle) hfactor
  have hidentity :
      (gamma - alpha) * (gamma + alpha - bound) = 2 - 2 * alpha := by
    dsimp only [bound]
    nlinarith [hgammaEq, halphaEq]
  have halphaGtOne : 1 < alpha := by
    dsimp [alpha, largeScalePreimage]
    have hroot : 0 < Real.sqrt (base ^ 2 - 4) := by
      apply Real.sqrt_pos.2
      nlinarith
    linarith
  rw [hidentity] at hleftNonneg
  linarith

noncomputable def generalOddTailBound (dimension : ℕ) : ℝ :=
  max (oddCosineScaleMidpoint dimension) (2 * dimension - 1 : ℝ)

theorem generalOddTailBound_nonneg (dimension : ℕ) :
    0 ≤ generalOddTailBound dimension := by
  unfold generalOddTailBound
  apply le_max_of_le_left
  unfold oddCosineScaleMidpoint
  positivity

theorem generalOddTailBound_lt_base
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    generalOddTailBound dimension < (2 * dimension + 1 : ℝ) := by
  unfold generalOddTailBound oddCosineScaleMidpoint
  rw [max_lt_iff]
  have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
  constructor <;> linarith

theorem absoluteKernelGrowth_generalOddTailBound_lt
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    absoluteKernelGrowth (generalOddTailBound dimension) <
      largeScalePreimage (2 * dimension + 1 : ℝ) := by
  by_cases htwo : dimension = 2
  · subst dimension
    have h := absoluteKernelGrowth_halfway_lt_largeScalePreimage
      (base := 5) (by norm_num)
    norm_num [generalOddTailBound, oddCosineScaleMidpoint] at h ⊢
    exact h
  · have hthree : 3 ≤ dimension := by omega
    have hmax : generalOddTailBound dimension =
        (2 * dimension + 1 : ℝ) - 2 := by
      have hmidle : oddCosineScaleMidpoint dimension ≤
          (2 * dimension - 1 : ℝ) := by
        unfold oddCosineScaleMidpoint
        have hdreal : (3 : ℝ) ≤ dimension := by exact_mod_cast hthree
        linarith
      unfold generalOddTailBound
      rw [max_eq_right hmidle]
      have hdreal : (3 : ℝ) ≤ dimension := by exact_mod_cast hthree
      ring
    rw [hmax]
    exact absoluteKernelGrowth_two_below_lt_largeScalePreimage (by
      have hdreal : (3 : ℝ) ≤ dimension := by exact_mod_cast hthree
      linarith)

noncomputable def generalOddTailGrowthRatio (dimension : ℕ) : ℝ :=
  absoluteKernelGrowth (generalOddTailBound dimension) /
    largeScalePreimage (2 * dimension + 1 : ℝ)

theorem generalOddTailGrowthRatio_pos
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    0 < generalOddTailGrowthRatio dimension := by
  unfold generalOddTailGrowthRatio
  exact div_pos
    (absoluteKernelGrowth_pos (generalOddTailBound_nonneg dimension))
    (largeScalePreimage_pos (by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith))

theorem generalOddTailGrowthRatio_lt_one
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    generalOddTailGrowthRatio dimension < 1 := by
  rw [generalOddTailGrowthRatio,
    div_lt_one (largeScalePreimage_pos (by
      have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
      linarith))]
  exact absoluteKernelGrowth_generalOddTailBound_lt hdimension

theorem oddCosineCubeScale_lower_bound
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    -(2 * dimension - 1 : ℝ) ≤ oddCosineCubeScale angles := by
  unfold oddCosineCubeScale cosineCubeScale
  have hsum : ∑ coordinate : Fin dimension, (-1 : ℝ) ≤
      ∑ coordinate, Real.cos (angles coordinate) := by
    apply Finset.sum_le_sum
    intro coordinate hcoordinate
    exact Real.neg_one_le_cos _
  simp at hsum
  linarith

noncomputable def generalOddPositiveSpectralDomain
    (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  {angles | oddCosineScaleMidpoint dimension ≤ oddCosineCubeScale angles}

noncomputable def generalOddTailSpectralDomain
    (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  {angles | oddCosineCubeScale angles < oddCosineScaleMidpoint dimension}

theorem abs_oddCosineCubeScale_le_tailBound
    {dimension : ℕ} {angles : Fin dimension → ℝ}
    (htail : angles ∈ generalOddTailSpectralDomain dimension) :
    |oddCosineCubeScale angles| ≤ generalOddTailBound dimension := by
  rw [abs_le]
  constructor
  · calc
      -generalOddTailBound dimension ≤ -(2 * dimension - 1 : ℝ) :=
        neg_le_neg (le_max_right _ _)
      _ ≤ oddCosineCubeScale angles :=
        oddCosineCubeScale_lower_bound dimension angles
  · exact htail.le.trans (le_max_left _ _)

noncomputable def generalOddFullNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (1 / Real.pi) ^ dimension *
    (fibonacciScaleKernel (oddCosineCubeScale angles) index /
      (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
    oddWeylAngleWeight dimension angles

noncomputable def generalOddLocalProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (generalOddPositiveSpectralDomain dimension).indicator
    (generalOddFullNormalizedIntegrand dimension index) angles

noncomputable def generalOddTailProductIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (generalOddTailSpectralDomain dimension).indicator
    (generalOddFullNormalizedIntegrand dimension index) angles

noncomputable def generalOddFullNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalOddFullNormalizedIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

noncomputable def generalOddTailNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    generalOddTailProductIntegrand dimension index angles
    ∂cosineCubeProductMeasure dimension

theorem generalOddFullIntegrand_partition
    (dimension index : ℕ) (angles : Fin dimension → ℝ) :
    generalOddFullNormalizedIntegrand dimension index angles =
      generalOddLocalProductIntegrand dimension index angles +
        generalOddTailProductIntegrand dimension index angles := by
  by_cases hlocal : angles ∈ generalOddPositiveSpectralDomain dimension
  · have htail : angles ∉ generalOddTailSpectralDomain dimension := by
      intro htail
      change oddCosineScaleMidpoint dimension ≤
        oddCosineCubeScale angles at hlocal
      change oddCosineCubeScale angles <
        oddCosineScaleMidpoint dimension at htail
      exact (not_lt_of_ge hlocal) htail
    rw [generalOddLocalProductIntegrand, Set.indicator_of_mem hlocal,
      generalOddTailProductIntegrand, Set.indicator_of_notMem htail, add_zero]
  · have htail : angles ∈ generalOddTailSpectralDomain dimension :=
      by
        change ¬oddCosineScaleMidpoint dimension ≤
          oddCosineCubeScale angles at hlocal
        change oddCosineCubeScale angles < oddCosineScaleMidpoint dimension
        exact lt_of_not_ge hlocal
    rw [generalOddLocalProductIntegrand, Set.indicator_of_notMem hlocal,
      generalOddTailProductIntegrand, Set.indicator_of_mem htail, zero_add]

theorem measurableSet_generalOddPositiveSpectralDomain (dimension : ℕ) :
    MeasurableSet (generalOddPositiveSpectralDomain dimension) := by
  unfold generalOddPositiveSpectralDomain
  exact measurableSet_Ici.preimage
    (continuous_oddCosineCubeScale dimension).measurable

theorem measurableSet_generalOddTailSpectralDomain (dimension : ℕ) :
    MeasurableSet (generalOddTailSpectralDomain dimension) := by
  unfold generalOddTailSpectralDomain
  exact measurableSet_Iio.preimage
    (continuous_oddCosineCubeScale dimension).measurable

theorem integrable_generalOddFullNormalizedIntegrand
    (dimension index : ℕ) :
    Integrable (generalOddFullNormalizedIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
  apply integrable_continuous_cosineCube
  unfold generalOddFullNormalizedIntegrand
  exact (continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_oddCosineCubeScale dimension)).div_const _)).mul
        (continuous_oddWeylAngleWeight dimension)

theorem generalOddFullNormalizedIntegral_partition
    (dimension index : ℕ) :
    generalOddFullNormalizedIntegral dimension index =
      (∫ angles : Fin dimension → ℝ,
        generalOddLocalProductIntegrand dimension index angles
        ∂cosineCubeProductMeasure dimension) +
      generalOddTailNormalizedIntegral dimension index := by
  unfold generalOddFullNormalizedIntegral generalOddTailNormalizedIntegral
  rw [show (fun angles : Fin dimension → ℝ =>
      generalOddFullNormalizedIntegrand dimension index angles) =
    fun angles => generalOddLocalProductIntegrand dimension index angles +
      generalOddTailProductIntegrand dimension index angles by
        funext angles
        exact generalOddFullIntegrand_partition dimension index angles]
  have hlocalIntegrable : Integrable
      (generalOddLocalProductIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
    exact (integrable_generalOddFullNormalizedIntegrand dimension index).indicator
      (measurableSet_generalOddPositiveSpectralDomain dimension)
  have htailIntegrable : Integrable
      (generalOddTailProductIntegrand dimension index)
      (cosineCubeProductMeasure dimension) := by
    exact (integrable_generalOddFullNormalizedIntegrand dimension index).indicator
      (measurableSet_generalOddTailSpectralDomain dimension)
  exact integral_add hlocalIntegrable htailIntegrable

theorem generalOddLocalProductIntegral_eq_angleLocal
    (dimension index : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      generalOddLocalProductIntegrand dimension index angles
      ∂cosineCubeProductMeasure dimension) =
      oddWeylAngleLocalNormalizedIntegral dimension index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin dimension =>
      Set.Ioc (0 : ℝ) Real.pi) = anglePositiveCube dimension by rfl]
  rw [← integral_indicator (show MeasurableSet (anglePositiveCube dimension) by
    unfold anglePositiveCube
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold oddWeylAngleLocalNormalizedIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube dimension
  · by_cases hlocal : angles ∈ generalOddPositiveSpectralDomain dimension
    · have hangle : angles ∈ oddAngleLocalDomain dimension := ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube, generalOddLocalProductIntegrand,
        Set.indicator_of_mem hlocal,
        oddWeylAngleLocalNormalizedIntegrand,
        Set.indicator_of_mem hangle]
      rfl
    · rw [Set.indicator_of_mem hcube, generalOddLocalProductIntegrand,
        Set.indicator_of_notMem hlocal,
        oddWeylAngleLocalNormalizedIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      oddWeylAngleLocalNormalizedIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem abs_generalOddNormalizedKernel_le_tail
    {dimension index : ℕ} {scale : ℝ} (hdimension : 2 ≤ dimension)
    (hscale : |scale| ≤ generalOddTailBound dimension) :
    |fibonacciScaleKernel scale index /
        (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))| ≤
      Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) *
        generalOddTailGrowthRatio dimension ^ (index + 1) := by
  let gamma := absoluteKernelGrowth (generalOddTailBound dimension)
  let alpha := largeScalePreimage (2 * dimension + 1 : ℝ)
  have hboundOne : (1 : ℝ) ≤ generalOddTailBound dimension := by
    unfold generalOddTailBound
    apply le_max_of_le_right
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    change (1 : ℝ) ≤ 2 * (dimension : ℝ) - 1
    linarith
  have hkernel : |fibonacciScaleKernel scale index| ≤ gamma ^ index :=
    abs_fibonacciScaleKernel_le_growth_pow
      hboundOne hscale index
  have hgammaOne : 1 ≤ gamma := by
    exact hboundOne.trans
        (absoluteKernelGrowth_ge_bound (generalOddTailBound_nonneg dimension))
  have hbase : (3 : ℝ) ≤ 2 * dimension + 1 := by
    have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
    linarith
  have halphaPos : 0 < alpha :=
    largeScalePreimage_pos (show (2 : ℝ) ≤ 2 * dimension + 1 by linarith)
  have hrootPos : 0 < Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hdenomPos : 0 < alpha ^ (index + 1) /
      Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) :=
    div_pos (pow_pos halphaPos _) hrootPos
  rw [abs_div, abs_of_pos hdenomPos]
  calc
    |fibonacciScaleKernel scale index| /
        (alpha ^ (index + 1) /
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4)) =
      (|fibonacciScaleKernel scale index| *
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4)) /
          alpha ^ (index + 1) := by
      field_simp [hrootPos.ne', halphaPos.ne']
    _ ≤ (gamma ^ index *
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4)) /
          alpha ^ (index + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkernel hrootPos.le)
        (pow_nonneg halphaPos.le _)
    _ ≤ (gamma ^ (index + 1) *
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4)) /
          alpha ^ (index + 1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg halphaPos.le _)
      apply mul_le_mul_of_nonneg_right _ hrootPos.le
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg (by positivity) _) hgammaOne
    _ = _ := by
      unfold generalOddTailGrowthRatio
      dsimp only [gamma, alpha]
      rw [div_pow]
      ring

theorem norm_generalOddTailProductIntegrand_le
    {dimension : ℕ} (hdimension : 2 ≤ dimension)
    (index : ℕ) (angles : Fin dimension → ℝ) :
    ‖generalOddTailProductIntegrand dimension index angles‖ ≤
      ((1 / Real.pi) ^ dimension *
        Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) *
        (4 : ℝ) ^ weylPairCount dimension) *
          generalOddTailGrowthRatio dimension ^ (index + 1) := by
  by_cases htail : angles ∈ generalOddTailSpectralDomain dimension
  · rw [generalOddTailProductIntegrand, Set.indicator_of_mem htail,
      generalOddFullNormalizedIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
      abs_of_nonneg (oddWeylAngleWeight_nonneg dimension angles)]
    have hkernel := abs_generalOddNormalizedKernel_le_tail
      (dimension := dimension) (index := index) hdimension
      (abs_oddCosineCubeScale_le_tailBound htail)
    have hweight := oddWeylAngleWeight_le_constant dimension angles
    have hrightNonneg : 0 ≤ (1 / Real.pi) ^ dimension *
        (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) *
          generalOddTailGrowthRatio dimension ^ (index + 1)) := by
      exact mul_nonneg (pow_nonneg (by positivity) _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg (generalOddTailGrowthRatio_pos hdimension).le _))
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left hkernel (pow_nonneg (by positivity) _))
      hweight (oddWeylAngleWeight_nonneg dimension angles)
      hrightNonneg).trans_eq (by ring)
  · rw [generalOddTailProductIntegrand, Set.indicator_of_notMem htail,
      norm_zero]
    exact mul_nonneg (by positivity)
      (pow_nonneg (generalOddTailGrowthRatio_pos hdimension).le _)

theorem tendsto_generalOddTailPolynomialGeometric
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ (dimension ^ 2 + dimension) *
        generalOddTailGrowthRatio dimension ^ (index + 1))
      atTop (nhds 0) := by
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one
    (dimension ^ 2 + dimension)
    (by rw [abs_of_pos (generalOddTailGrowthRatio_pos hdimension)]
        exact generalOddTailGrowthRatio_lt_one hdimension)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ (dimension ^ 2 + dimension) *
        generalOddTailGrowthRatio dimension ^ (index + 1)) =
    (fun index : ℕ => (index : ℝ) ^ (dimension ^ 2 + dimension) *
      generalOddTailGrowthRatio dimension ^ index) ∘
        (fun index : ℕ => index + 1) by
      funext index
      simp [Function.comp_apply]]
  exact hshift

theorem tendsto_generalOddTailNormalizedIntegral
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddTailNormalizedIntegral dimension index)
      atTop (nhds 0) := by
  let constant : ℝ :=
    ((1 / Real.pi) ^ dimension *
      Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) *
      (4 : ℝ) ^ weylPairCount dimension) *
      (cosineCubeProductMeasure dimension).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ (dimension ^ 2 + dimension) *
        generalOddTailGrowthRatio dimension ^ (index + 1)) * constant)
  · intro index
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _),
      abs_of_nonneg (pow_nonneg (by positivity) _)]
    have hintegral : ‖generalOddTailNormalizedIntegral dimension index‖ ≤
        (((1 / Real.pi) ^ dimension *
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) *
          (4 : ℝ) ^ weylPairCount dimension) *
          generalOddTailGrowthRatio dimension ^ (index + 1)) *
          (cosineCubeProductMeasure dimension).real Set.univ := by
      unfold generalOddTailNormalizedIntegral
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall
          (norm_generalOddTailProductIntegrand_le hdimension index))
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
    have hnonneg : 0 ≤ ‖generalOddTailNormalizedIntegral dimension index‖ :=
      norm_nonneg _
    calc
      Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension ^ 2) *
            ‖generalOddTailNormalizedIntegral dimension index‖ ≤
        (index + 1 : ℝ) ^ (dimension ^ 2 + dimension) *
            ‖generalOddTailNormalizedIntegral dimension index‖ :=
          mul_le_mul_of_nonneg_right hpoly hnonneg
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hintegral
        positivity
      _ = _ := by ring
  · simpa only [zero_mul] using
      (tendsto_generalOddTailPolynomialGeometric hdimension).mul_const constant

theorem tendsto_generalOddFullNormalizedIntegral
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddFullNormalizedIntegral dimension index)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        oddWeylLocalLimitIntegrand dimension coordinates)) := by
  have hlocal : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          oddWeylAngleLocalNormalizedIntegral dimension index)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        oddWeylLocalLimitIntegrand dimension coordinates)) := by
    rw [show (fun index : ℕ =>
        Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension ^ 2) *
            oddWeylAngleLocalNormalizedIntegral dimension index) =
      fun index => ∫ coordinates : Fin dimension → ℝ,
        oddWeylLocalRescaledIntegrand dimension index coordinates by
          funext index
          exact oddWeylLocalScalingIntegral_identity dimension index]
    exact tendsto_integral_generalOddWeylLocalRescaledIntegrand dimension
      (by
        have hdreal : (2 : ℝ) ≤ dimension := by exact_mod_cast hdimension
        linarith)
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddFullNormalizedIntegral dimension index) =
    fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          oddWeylAngleLocalNormalizedIntegral dimension index +
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          generalOddTailNormalizedIntegral dimension index by
      funext index
      rw [generalOddFullNormalizedIntegral_partition,
        generalOddLocalProductIntegral_eq_angleLocal]
      ring]
  simpa using hlocal.add
    (tendsto_generalOddTailNormalizedIntegral hdimension)

theorem generalOddFullNormalizedIntegral_eq_weylMoment
    (dimension index : ℕ) :
    generalOddFullNormalizedIntegral dimension index =
      (1 / Real.pi) ^ dimension *
        (oddWeylFibonacciMoment dimension index /
          (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) := by
  unfold generalOddFullNormalizedIntegral generalOddFullNormalizedIntegrand
    oddWeylFibonacciMoment weightedCosineCubeFibonacciMoment
    weightedCosineCubeFibonacciIntegrand
  rw [show (fun angles : Fin dimension → ℝ =>
      (1 / Real.pi) ^ dimension *
          (fibonacciScaleKernel (oddCosineCubeScale angles) index /
            (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
              Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
        oddWeylAngleWeight dimension angles) =
      fun angles => ((1 / Real.pi) ^ dimension /
        (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
        (fibonacciScaleKernel (oddCosineCubeScale angles) index *
          oddWeylAngleWeight dimension angles) by
    funext angles
    ring]
  rw [integral_const_mul]
  ring

theorem generalOddFullNormalizedIntegral_eq_ribbonCount
    (dimension : ℕ) (hdimension : 1 ≤ dimension) (index : ℕ) :
    generalOddFullNormalizedIntegral dimension index =
      (1 / Real.pi) ^ dimension /
        oddWeylNormalization dimension *
      ((ribbonCount (2 * dimension) index : ℝ) /
        (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) := by
  rw [generalOddFullNormalizedIntegral_eq_weylMoment,
    generalOddRibbonCount_eq_normalizedWeylMoment dimension hdimension]
  have hnorm : oddWeylNormalization dimension ≠ 0 := by
    unfold oddWeylNormalization
    positivity
  field_simp [hnorm]

theorem tendsto_generalOddRibbonNormalizedIntegralConstant
    {dimension : ℕ} (hdimension : 2 ≤ dimension) :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
      ((ribbonCount (2 * dimension) index : ℝ) /
        (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
          Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))))
      atTop (nhds ((oddWeylNormalization dimension *
        Real.pi ^ dimension) *
          (∫ coordinates : Fin dimension → ℝ,
            oddWeylLocalLimitIntegrand dimension coordinates))) := by
  have h := (tendsto_generalOddFullNormalizedIntegral hdimension).const_mul
    (oddWeylNormalization dimension * Real.pi ^ dimension)
  apply h.congr'
  filter_upwards with index
  rw [generalOddFullNormalizedIntegral_eq_ribbonCount dimension
    (by omega) index]
  have hpi : Real.pi ^ dimension ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hnorm : oddWeylNormalization dimension ≠ 0 := by
    unfold oddWeylNormalization
    positivity
  have hpiCancel : Real.pi ^ dimension *
      (1 / Real.pi) ^ dimension = 1 := by
    rw [← mul_pow]
    field_simp [Real.pi_ne_zero]
    norm_num
  have hcoefficient : oddWeylNormalization dimension * Real.pi ^ dimension *
      ((1 / Real.pi) ^ dimension / oddWeylNormalization dimension) = 1 := by
    rw [show oddWeylNormalization dimension * Real.pi ^ dimension *
        ((1 / Real.pi) ^ dimension / oddWeylNormalization dimension) =
      (Real.pi ^ dimension * (1 / Real.pi) ^ dimension) *
        (oddWeylNormalization dimension / oddWeylNormalization dimension) by ring,
      hpiCancel, div_self hnorm, one_mul]
  calc
    oddWeylNormalization dimension * Real.pi ^ dimension *
        (Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension ^ 2) *
            ((1 / Real.pi) ^ dimension / oddWeylNormalization dimension *
              ((ribbonCount (2 * dimension) index : ℝ) /
                (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
                  Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))))) =
      (oddWeylNormalization dimension * Real.pi ^ dimension *
        ((1 / Real.pi) ^ dimension / oddWeylNormalization dimension)) *
        (Real.sqrt (index + 1 : ℝ) ^ dimension *
          (index + 1 : ℝ) ^ (dimension ^ 2) *
            ((ribbonCount (2 * dimension) index : ℝ) /
              (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
                Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4)))) := by ring
    _ = _ := by rw [hcoefficient, one_mul]

end FibonacciRibbonKernel
