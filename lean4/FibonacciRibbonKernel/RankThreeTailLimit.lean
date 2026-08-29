import FibonacciRibbonKernel.GeneralEvenAsymptotic

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

noncomputable def rankThreeLowTailBound : ℝ := 11 / 5

noncomputable def rankThreeLowTailGrowthRatio : ℝ :=
  absoluteKernelGrowth rankThreeLowTailBound / largeScalePreimage 3

noncomputable def rankThreeHighTailGrowthRatio : ℝ :=
  2 / largeScalePreimage 3

theorem rankThreeLowTailGrowthRatio_pos :
    0 < rankThreeLowTailGrowthRatio := by
  unfold rankThreeLowTailGrowthRatio rankThreeLowTailBound
  exact div_pos (absoluteKernelGrowth_pos (by norm_num))
    (largeScalePreimage_pos (by norm_num))

theorem rankThreeHighTailGrowthRatio_pos :
    0 < rankThreeHighTailGrowthRatio := by
  unfold rankThreeHighTailGrowthRatio
  exact div_pos (by norm_num) (largeScalePreimage_pos (by norm_num))

theorem rankThreeLowTailGrowthRatio_lt_one :
    rankThreeLowTailGrowthRatio < 1 := by
  have hsqrtFiveSq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtFiveGtTwo : (2 : ℝ) < Real.sqrt 5 := by
    have hsqrtFiveNonneg := Real.sqrt_nonneg 5
    nlinarith
  have hsqrt221Sq : Real.sqrt 221 ^ 2 = (221 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt221Nonneg := Real.sqrt_nonneg 221
  have hrhsPos : 0 < 4 + 5 * Real.sqrt 5 := by positivity
  have hsqrtComparison : Real.sqrt 221 < 4 + 5 * Real.sqrt 5 := by
    by_contra hnot
    have hle : 4 + 5 * Real.sqrt 5 ≤ Real.sqrt 221 := le_of_not_gt hnot
    have hsquares : (4 + 5 * Real.sqrt 5) ^ 2 ≤
        Real.sqrt 221 ^ 2 :=
      (sq_le_sq₀ hrhsPos.le hsqrt221Nonneg).2 hle
    nlinarith
  rw [rankThreeLowTailGrowthRatio,
    div_lt_one (largeScalePreimage_pos (by norm_num))]
  unfold rankThreeLowTailBound absoluteKernelGrowth largeScalePreimage
  have hinside : (11 / 5 : ℝ) ^ 2 + 4 = 221 / 25 := by norm_num
  rw [hinside, show Real.sqrt (221 / 25 : ℝ) = Real.sqrt 221 / 5 by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 221)]
    norm_num]
  norm_num
  nlinarith

theorem rankThreeHighTailGrowthRatio_lt_one :
    rankThreeHighTailGrowthRatio < 1 := by
  rw [rankThreeHighTailGrowthRatio,
    div_lt_one (largeScalePreimage_pos (by norm_num))]
  unfold largeScalePreimage
  have hsqrtFiveSq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtFiveNonneg := Real.sqrt_nonneg 5
  norm_num
  nlinarith

noncomputable def rankThreeLowTailDomain : Set (Fin 1 → ℝ) :=
  {angles | oddCosineCubeScale angles < rankThreeLowTailBound}

noncomputable def rankThreeHighTailDomain : Set (Fin 1 → ℝ) :=
  {angles | rankThreeLowTailBound ≤ oddCosineCubeScale angles ∧
    oddCosineCubeScale angles < oddCosineScaleMidpoint 1}

theorem measurableSet_rankThreeLowTailDomain :
    MeasurableSet rankThreeLowTailDomain := by
  unfold rankThreeLowTailDomain
  exact measurableSet_lt
    (continuous_oddCosineCubeScale 1).measurable measurable_const

theorem measurableSet_rankThreeHighTailDomain :
    MeasurableSet rankThreeHighTailDomain := by
  unfold rankThreeHighTailDomain
  exact (measurableSet_le measurable_const
    (continuous_oddCosineCubeScale 1).measurable).inter
      (measurableSet_lt
        (continuous_oddCosineCubeScale 1).measurable measurable_const)

noncomputable def rankThreeLowTailProductIntegrand
    (index : ℕ) (angles : Fin 1 → ℝ) : ℝ :=
  rankThreeLowTailDomain.indicator
    (generalOddFullNormalizedIntegrand 1 index) angles

noncomputable def rankThreeHighTailProductIntegrand
    (index : ℕ) (angles : Fin 1 → ℝ) : ℝ :=
  rankThreeHighTailDomain.indicator
    (generalOddFullNormalizedIntegrand 1 index) angles

noncomputable def rankThreeLowTailIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 1 → ℝ, rankThreeLowTailProductIntegrand index angles
    ∂cosineCubeProductMeasure 1

noncomputable def rankThreeHighTailIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 1 → ℝ, rankThreeHighTailProductIntegrand index angles
    ∂cosineCubeProductMeasure 1

theorem generalOddTailProductIntegrand_one_partition
    (index : ℕ) (angles : Fin 1 → ℝ) :
    generalOddTailProductIntegrand 1 index angles =
      rankThreeLowTailProductIntegrand index angles +
        rankThreeHighTailProductIntegrand index angles := by
  by_cases htail : angles ∈ generalOddTailSpectralDomain 1
  · have htailMem := htail
    change oddCosineCubeScale angles < oddCosineScaleMidpoint 1 at htail
    by_cases hlow : oddCosineCubeScale angles < rankThreeLowTailBound
    · have hlowMem : angles ∈ rankThreeLowTailDomain := hlow
      have hhighNot : angles ∉ rankThreeHighTailDomain := by
        intro hhigh
        exact (not_lt_of_ge hhigh.1) hlow
      rw [generalOddTailProductIntegrand, Set.indicator_of_mem htailMem,
        rankThreeLowTailProductIntegrand, Set.indicator_of_mem hlowMem,
        rankThreeHighTailProductIntegrand,
        Set.indicator_of_notMem hhighNot, add_zero]
    · have hhighMem : angles ∈ rankThreeHighTailDomain :=
        ⟨le_of_not_gt hlow, htail⟩
      have hlowNot : angles ∉ rankThreeLowTailDomain := hlow
      rw [generalOddTailProductIntegrand, Set.indicator_of_mem htailMem,
        rankThreeLowTailProductIntegrand, Set.indicator_of_notMem hlowNot,
        rankThreeHighTailProductIntegrand,
        Set.indicator_of_mem hhighMem, zero_add]
  · have hlowNot : angles ∉ rankThreeLowTailDomain := by
      intro hlow
      apply htail
      change oddCosineCubeScale angles < oddCosineScaleMidpoint 1
      change oddCosineCubeScale angles < rankThreeLowTailBound at hlow
      norm_num [rankThreeLowTailBound, oddCosineScaleMidpoint] at hlow ⊢
      linarith
    have hhighNot : angles ∉ rankThreeHighTailDomain := by
      intro hhigh
      exact htail hhigh.2
    rw [generalOddTailProductIntegrand, Set.indicator_of_notMem htail,
      rankThreeLowTailProductIntegrand, Set.indicator_of_notMem hlowNot,
      rankThreeHighTailProductIntegrand,
      Set.indicator_of_notMem hhighNot, zero_add]

theorem abs_oddCosineCubeScale_one_le_lowTailBound
    {angles : Fin 1 → ℝ} (hlow : angles ∈ rankThreeLowTailDomain) :
    |oddCosineCubeScale angles| ≤ rankThreeLowTailBound := by
  have hlower := oddCosineCubeScale_lower_bound 1 angles
  change oddCosineCubeScale angles < rankThreeLowTailBound at hlow
  rw [abs_le]
  constructor
  · norm_num [rankThreeLowTailBound] at hlower ⊢
    linarith
  · exact hlow.le

theorem abs_rankThreeLowTailNormalizedKernel_le
    {index : ℕ} {scale : ℝ}
    (hscale : |scale| ≤ rankThreeLowTailBound) :
    |fibonacciScaleKernel scale index /
        (largeScalePreimage 3 ^ (index + 1) / Real.sqrt 5)| ≤
      Real.sqrt 5 * rankThreeLowTailGrowthRatio ^ (index + 1) := by
  let gamma := absoluteKernelGrowth rankThreeLowTailBound
  let alpha := largeScalePreimage 3
  have hboundOne : (1 : ℝ) ≤ rankThreeLowTailBound := by
    norm_num [rankThreeLowTailBound]
  have hkernel : |fibonacciScaleKernel scale index| ≤ gamma ^ index :=
    abs_fibonacciScaleKernel_le_growth_pow hboundOne hscale index
  have hgammaOne : 1 ≤ gamma :=
    hboundOne.trans
      (absoluteKernelGrowth_ge_bound (by
        norm_num [rankThreeLowTailBound]))
  have halphaPos : 0 < alpha := largeScalePreimage_pos (by norm_num)
  have hrootPos : 0 < Real.sqrt 5 := by positivity
  have hdenomPos : 0 < alpha ^ (index + 1) / Real.sqrt 5 :=
    div_pos (pow_pos halphaPos _) hrootPos
  rw [abs_div, abs_of_pos hdenomPos]
  calc
    |fibonacciScaleKernel scale index| /
        (alpha ^ (index + 1) / Real.sqrt 5) =
      (|fibonacciScaleKernel scale index| * Real.sqrt 5) /
        alpha ^ (index + 1) := by field_simp
    _ ≤ (gamma ^ index * Real.sqrt 5) / alpha ^ (index + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkernel hrootPos.le)
        (pow_nonneg halphaPos.le _)
    _ ≤ (gamma ^ (index + 1) * Real.sqrt 5) /
        alpha ^ (index + 1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg halphaPos.le _)
      apply mul_le_mul_of_nonneg_right _ hrootPos.le
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg (by positivity) _) hgammaOne
    _ = _ := by
      unfold rankThreeLowTailGrowthRatio
      dsimp only [gamma, alpha]
      rw [div_pow]
      ring

theorem largeScalePreimage_le_two_of_rankThreeHighTail
    {scale : ℝ} (hlower : rankThreeLowTailBound ≤ scale)
    (hupper : scale ≤ (5 / 2 : ℝ)) :
    largeScalePreimage scale ≤ 2 := by
  have hscaleNonneg : 0 ≤ scale := by
    have : (0 : ℝ) ≤ rankThreeLowTailBound := by
      norm_num [rankThreeLowTailBound]
    linarith
  have hsquare : scale ^ 2 - 4 ≤ (3 / 2 : ℝ) ^ 2 := by
    nlinarith
  have hsqrt : Real.sqrt (scale ^ 2 - 4) ≤ (3 / 2 : ℝ) := by
    have := Real.sqrt_le_sqrt hsquare
    norm_num at this ⊢
    exact this
  unfold largeScalePreimage
  linarith

theorem four_fifths_le_rankThreeHighTail_sqrt
    {scale : ℝ} (hlower : rankThreeLowTailBound ≤ scale) :
    (4 / 5 : ℝ) ≤ Real.sqrt (scale ^ 2 - 4) := by
  have hscale : (11 / 5 : ℝ) ≤ scale := by
    simpa only [rankThreeLowTailBound] using hlower
  rw [Real.le_sqrt (by norm_num) (by nlinarith)]
  nlinarith

theorem abs_rankThreeHighTailNormalizedKernel_le
    {index : ℕ} {scale : ℝ}
    (hlower : rankThreeLowTailBound ≤ scale)
    (hupper : scale ≤ (5 / 2 : ℝ)) :
    |fibonacciScaleKernel scale index /
        (largeScalePreimage 3 ^ (index + 1) / Real.sqrt 5)| ≤
      (5 / 4 * Real.sqrt 5) *
        rankThreeHighTailGrowthRatio ^ (index + 1) := by
  have hscaleTwo : 2 < scale := by
    have : (2 : ℝ) < rankThreeLowTailBound := by
      norm_num [rankThreeLowTailBound]
    linarith
  have halphaPos := largeScalePreimage_pos hscaleTwo.le
  have hsmallPos := positiveScalePreimage_pos hscaleTwo.le
  have hsmallLe := (positiveScalePreimage_lt_largeScalePreimage hscaleTwo).le
  have hpowers : positiveScalePreimage scale ^ (index + 1) ≤
      largeScalePreimage scale ^ (index + 1) :=
    pow_le_pow_left₀ hsmallPos.le hsmallLe _
  have hrootPos : 0 < Real.sqrt (scale ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hkernelNonneg : 0 ≤ fibonacciScaleKernel scale index := by
    rw [fibonacciScaleKernel_closed_of_two_lt hscaleTwo]
    exact div_nonneg (sub_nonneg.2 hpowers) hrootPos.le
  rw [abs_div, abs_of_pos (div_pos
    (pow_pos (largeScalePreimage_pos (by norm_num : (2 : ℝ) ≤ 3)) _)
    (by positivity : 0 < Real.sqrt 5)), abs_of_nonneg hkernelNonneg]
  have hkernel : fibonacciScaleKernel scale index ≤
      (5 / 4 : ℝ) * 2 ^ (index + 1) := by
    rw [fibonacciScaleKernel_closed_of_two_lt hscaleTwo]
    have hnumerator :
        largeScalePreimage scale ^ (index + 1) -
            positiveScalePreimage scale ^ (index + 1) ≤
          largeScalePreimage scale ^ (index + 1) := by
      linarith [pow_nonneg hsmallPos.le (index + 1)]
    have halphaLe := largeScalePreimage_le_two_of_rankThreeHighTail
      hlower hupper
    have hpowerLe := pow_le_pow_left₀ halphaPos.le halphaLe (index + 1)
    have hrootLower := four_fifths_le_rankThreeHighTail_sqrt hlower
    calc
      (largeScalePreimage scale ^ (index + 1) -
          positiveScalePreimage scale ^ (index + 1)) /
          Real.sqrt (scale ^ 2 - 4) ≤
        largeScalePreimage scale ^ (index + 1) /
          Real.sqrt (scale ^ 2 - 4) :=
        div_le_div_of_nonneg_right hnumerator hrootPos.le
      _ ≤ 2 ^ (index + 1) / (4 / 5 : ℝ) := by
        exact div_le_div₀ (pow_nonneg (by norm_num) _) hpowerLe
          (by norm_num) hrootLower
      _ = (5 / 4 : ℝ) * 2 ^ (index + 1) := by ring
  have halphaThreePos := largeScalePreimage_pos (by norm_num : (2 : ℝ) ≤ 3)
  calc
    fibonacciScaleKernel scale index /
        (largeScalePreimage 3 ^ (index + 1) / Real.sqrt 5) =
      fibonacciScaleKernel scale index * Real.sqrt 5 /
        largeScalePreimage 3 ^ (index + 1) := by field_simp
    _ ≤ ((5 / 4 : ℝ) * 2 ^ (index + 1)) * Real.sqrt 5 /
        largeScalePreimage 3 ^ (index + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkernel (Real.sqrt_nonneg 5))
        (pow_nonneg halphaThreePos.le _)
    _ = _ := by
      unfold rankThreeHighTailGrowthRatio
      rw [div_pow]
      ring

theorem norm_rankThreeLowTailProductIntegrand_le
    (index : ℕ) (angles : Fin 1 → ℝ) :
    ‖rankThreeLowTailProductIntegrand index angles‖ ≤
      ((1 / Real.pi) * Real.sqrt 5) *
        rankThreeLowTailGrowthRatio ^ (index + 1) := by
  by_cases hlow : angles ∈ rankThreeLowTailDomain
  · rw [rankThreeLowTailProductIntegrand, Set.indicator_of_mem hlow,
      generalOddFullNormalizedIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul,
      abs_of_nonneg (oddWeylAngleWeight_nonneg 1 angles)]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hkernel := abs_rankThreeLowTailNormalizedKernel_le
      (index := index) (abs_oddCosineCubeScale_one_le_lowTailBound hlow)
    have hweight := oddWeylAngleWeight_le_constant 1 angles
    have hweightOne : oddWeylAngleWeight 1 angles ≤ 1 := by
      norm_num [weylPairCount] at hweight ⊢
      exact hweight
    have hratioNonneg := pow_nonneg rankThreeLowTailGrowthRatio_pos.le
      (index + 1)
    have hproduct := mul_le_mul hkernel hweightOne
      (oddWeylAngleWeight_nonneg 1 angles)
      (mul_nonneg (Real.sqrt_nonneg 5) hratioNonneg)
    have hscaled := mul_le_mul_of_nonneg_left hproduct
      (inv_nonneg.mpr Real.pi_pos.le)
    simpa only [mul_one, mul_assoc] using hscaled
  · rw [rankThreeLowTailProductIntegrand,
      Set.indicator_of_notMem hlow, norm_zero]
    exact mul_nonneg (by positivity)
      (pow_nonneg rankThreeLowTailGrowthRatio_pos.le _)

theorem norm_rankThreeHighTailProductIntegrand_le
    (index : ℕ) (angles : Fin 1 → ℝ) :
    ‖rankThreeHighTailProductIntegrand index angles‖ ≤
      ((1 / Real.pi) * (5 / 4 * Real.sqrt 5)) *
        rankThreeHighTailGrowthRatio ^ (index + 1) := by
  by_cases hhigh : angles ∈ rankThreeHighTailDomain
  · rw [rankThreeHighTailProductIntegrand, Set.indicator_of_mem hhigh,
      generalOddFullNormalizedIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul,
      abs_of_nonneg (oddWeylAngleWeight_nonneg 1 angles)]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hupper : oddCosineCubeScale angles ≤ (5 / 2 : ℝ) := by
      have := hhigh.2.le
      norm_num [oddCosineScaleMidpoint] at this ⊢
      exact this
    have hkernel := abs_rankThreeHighTailNormalizedKernel_le
      (index := index) hhigh.1 hupper
    have hweight := oddWeylAngleWeight_le_constant 1 angles
    have hweightOne : oddWeylAngleWeight 1 angles ≤ 1 := by
      norm_num [weylPairCount] at hweight ⊢
      exact hweight
    have hratioNonneg := pow_nonneg rankThreeHighTailGrowthRatio_pos.le
      (index + 1)
    have hproduct := mul_le_mul hkernel hweightOne
      (oddWeylAngleWeight_nonneg 1 angles)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 5))
        hratioNonneg)
    have hscaled := mul_le_mul_of_nonneg_left hproduct
      (inv_nonneg.mpr Real.pi_pos.le)
    simpa only [mul_one, mul_assoc] using hscaled
  · rw [rankThreeHighTailProductIntegrand,
      Set.indicator_of_notMem hhigh, norm_zero]
    exact mul_nonneg (by positivity)
      (pow_nonneg rankThreeHighTailGrowthRatio_pos.le _)

theorem tendsto_rankThreeLowTailPolynomial :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 2 *
        rankThreeLowTailGrowthRatio ^ (index + 1))
      atTop (nhds 0) := by
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
    (by rw [abs_of_pos rankThreeLowTailGrowthRatio_pos]
        exact rankThreeLowTailGrowthRatio_lt_one)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 2 *
        rankThreeLowTailGrowthRatio ^ (index + 1)) =
    (fun index : ℕ => (index : ℝ) ^ 2 *
      rankThreeLowTailGrowthRatio ^ index) ∘
        (fun index : ℕ => index + 1) by
      funext index
      simp [Function.comp_apply]]
  exact hshift

theorem tendsto_rankThreeHighTailPolynomial :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 2 *
        rankThreeHighTailGrowthRatio ^ (index + 1))
      atTop (nhds 0) := by
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
    (by rw [abs_of_pos rankThreeHighTailGrowthRatio_pos]
        exact rankThreeHighTailGrowthRatio_lt_one)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 2 *
        rankThreeHighTailGrowthRatio ^ (index + 1)) =
    (fun index : ℕ => (index : ℝ) ^ 2 *
      rankThreeHighTailGrowthRatio ^ index) ∘
        (fun index : ℕ => index + 1) by
      funext index
      simp [Function.comp_apply]]
  exact hshift

theorem tendsto_rankThreeLowTailIntegral_zero :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        rankThreeLowTailIntegral index)
      atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) * Real.sqrt 5) *
    (cosineCubeProductMeasure 1).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 2 *
        rankThreeLowTailGrowthRatio ^ (index + 1)) * constant)
  · intro index
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ index + 1)]
    have hintegral : ‖rankThreeLowTailIntegral index‖ ≤
        (((1 / Real.pi) * Real.sqrt 5) *
          rankThreeLowTailGrowthRatio ^ (index + 1)) *
            (cosineCubeProductMeasure 1).real Set.univ := by
      unfold rankThreeLowTailIntegral
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall
          (norm_rankThreeLowTailProductIntegrand_le index))
    have hsqrt : Real.sqrt (index + 1 : ℝ) ≤ (index + 1 : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
    have hpoly : Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) ≤
        (index + 1 : ℝ) ^ 2 := by
      nlinarith
    calc
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          ‖rankThreeLowTailIntegral index‖ ≤
        (index + 1 : ℝ) ^ 2 * ‖rankThreeLowTailIntegral index‖ :=
          mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hintegral (by positivity)
      _ = _ := by ring
  · simpa only [zero_mul] using
      tendsto_rankThreeLowTailPolynomial.mul_const constant

theorem tendsto_rankThreeHighTailIntegral_zero :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        rankThreeHighTailIntegral index)
      atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) * (5 / 4 * Real.sqrt 5)) *
    (cosineCubeProductMeasure 1).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 2 *
        rankThreeHighTailGrowthRatio ^ (index + 1)) * constant)
  · intro index
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ index + 1)]
    have hintegral : ‖rankThreeHighTailIntegral index‖ ≤
        (((1 / Real.pi) * (5 / 4 * Real.sqrt 5)) *
          rankThreeHighTailGrowthRatio ^ (index + 1)) *
            (cosineCubeProductMeasure 1).real Set.univ := by
      unfold rankThreeHighTailIntegral
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall
          (norm_rankThreeHighTailProductIntegrand_le index))
    have hsqrt : Real.sqrt (index + 1 : ℝ) ≤ (index + 1 : ℝ) :=
      Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
    have hpoly : Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) ≤
        (index + 1 : ℝ) ^ 2 := by
      nlinarith
    calc
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          ‖rankThreeHighTailIntegral index‖ ≤
        (index + 1 : ℝ) ^ 2 * ‖rankThreeHighTailIntegral index‖ :=
          mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hintegral (by positivity)
      _ = _ := by ring
  · simpa only [zero_mul] using
      tendsto_rankThreeHighTailPolynomial.mul_const constant

theorem generalOddTailNormalizedIntegral_one_partition (index : ℕ) :
    generalOddTailNormalizedIntegral 1 index =
      rankThreeLowTailIntegral index + rankThreeHighTailIntegral index := by
  unfold generalOddTailNormalizedIntegral rankThreeLowTailIntegral
    rankThreeHighTailIntegral
  rw [show (fun angles : Fin 1 → ℝ =>
      generalOddTailProductIntegrand 1 index angles) =
    fun angles => rankThreeLowTailProductIntegrand index angles +
      rankThreeHighTailProductIntegrand index angles by
      funext angles
      exact generalOddTailProductIntegrand_one_partition index angles]
  have hfull := integrable_generalOddFullNormalizedIntegrand 1 index
  have hlow := hfull.indicator measurableSet_rankThreeLowTailDomain
  have hhigh := hfull.indicator measurableSet_rankThreeHighTailDomain
  change Integrable (rankThreeLowTailProductIntegrand index)
    (cosineCubeProductMeasure 1) at hlow
  change Integrable (rankThreeHighTailProductIntegrand index)
    (cosineCubeProductMeasure 1) at hhigh
  exact integral_add hlow hhigh

theorem tendsto_generalOddTailNormalizedIntegral_one_zero :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddTailNormalizedIntegral 1 index)
      atTop (nhds 0) := by
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddTailNormalizedIntegral 1 index) =
    fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          rankThreeLowTailIntegral index +
        Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          rankThreeHighTailIntegral index by
      funext index
      rw [generalOddTailNormalizedIntegral_one_partition]
      ring]
  simpa using tendsto_rankThreeLowTailIntegral_zero.add
    tendsto_rankThreeHighTailIntegral_zero

theorem tendsto_generalOddFullNormalizedIntegral_one :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddFullNormalizedIntegral 1 index)
      atTop (nhds (∫ coordinates : Fin 1 → ℝ,
        oddWeylLocalLimitIntegrand 1 coordinates)) := by
  have hlocal : Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        oddWeylAngleLocalNormalizedIntegral 1 index)
      atTop (nhds (∫ coordinates : Fin 1 → ℝ,
        oddWeylLocalLimitIntegrand 1 coordinates)) := by
    rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        oddWeylAngleLocalNormalizedIntegral 1 index) =
      fun index => ∫ coordinates : Fin 1 → ℝ,
        oddWeylLocalRescaledIntegrand 1 index coordinates by
          funext index
          simpa using oddWeylLocalScalingIntegral_identity 1 index]
    exact tendsto_integral_generalOddWeylLocalRescaledIntegrand 1 (by norm_num)
  rw [show (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
        generalOddFullNormalizedIntegral 1 index) =
      fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          oddWeylAngleLocalNormalizedIntegral 1 index +
        Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          generalOddTailNormalizedIntegral 1 index by
      funext index
      rw [generalOddFullNormalizedIntegral_partition,
        generalOddLocalProductIntegral_eq_angleLocal]
      ring]
  simpa using hlocal.add tendsto_generalOddTailNormalizedIntegral_one_zero

theorem tendsto_rankThreeRibbonNormalizedIntegralConstant :
    Tendsto (fun index : ℕ =>
      Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
      ((ribbonCount 2 index : ℝ) /
        (largeScalePreimage 3 ^ (index + 1) / Real.sqrt 5)))
      atTop (nhds ((oddWeylNormalization 1 * Real.pi) *
        (∫ coordinates : Fin 1 → ℝ,
          oddWeylLocalLimitIntegrand 1 coordinates))) := by
  have h := tendsto_generalOddFullNormalizedIntegral_one.const_mul
    (oddWeylNormalization 1 * Real.pi)
  apply h.congr'
  filter_upwards with index
  rw [generalOddFullNormalizedIntegral_eq_ribbonCount 1 (by norm_num) index]
  norm_num
  have hnorm : oddWeylNormalization 1 ≠ 0 := by
    unfold oddWeylNormalization
    positivity
  have hpiCancel : Real.pi * Real.pi⁻¹ = 1 := by
    field_simp [Real.pi_ne_zero]
  have hcoefficient : oddWeylNormalization 1 * Real.pi *
      (Real.pi⁻¹ / oddWeylNormalization 1) = 1 := by
    rw [show oddWeylNormalization 1 * Real.pi *
        (Real.pi⁻¹ / oddWeylNormalization 1) =
      (Real.pi * Real.pi⁻¹) *
        (oddWeylNormalization 1 / oddWeylNormalization 1) by ring,
      hpiCancel, div_self hnorm, one_mul]
  calc
    oddWeylNormalization 1 * Real.pi *
        (Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          (Real.pi⁻¹ / oddWeylNormalization 1 *
            ((ribbonCount 2 index : ℝ) /
              (largeScalePreimage 3 ^ (index + 1) / Real.sqrt 5)))) =
      (oddWeylNormalization 1 * Real.pi *
        (Real.pi⁻¹ / oddWeylNormalization 1)) *
        (Real.sqrt (index + 1 : ℝ) * (index + 1 : ℝ) *
          ((ribbonCount 2 index : ℝ) /
            (largeScalePreimage 3 ^ (index + 1) / Real.sqrt 5))) := by ring
    _ = _ := by rw [hcoefficient, one_mul]

end FibonacciRibbonKernel
