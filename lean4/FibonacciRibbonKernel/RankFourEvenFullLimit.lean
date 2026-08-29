import FibonacciRibbonKernel.RankFourEvenNegativeLocal

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFourEvenFullNormalizedIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (1 / Real.pi) ^ 2 *
    (fibonacciScaleKernel (cosineCubeScale angles) index /
      (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) *
    evenWeylAngleWeight 2 angles

noncomputable def rankFourEvenPositiveProductIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (positiveSpectralLocalDomain 2).indicator
    (rankFourEvenFullNormalizedIntegrand index) angles

noncomputable def rankFourEvenNegativeProductIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (negativeSpectralLocalDomain 2).indicator
    (rankFourEvenFullNormalizedIntegrand index) angles

noncomputable def rankFourEvenMiddleProductIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (middleOpenSpectralDomain 2).indicator
    (rankFourEvenFullNormalizedIntegrand index) angles

noncomputable def rankFourEvenMinusPositiveProductIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (positiveSpectralLocalDomain 2).indicator
    (fun angles =>
      (1 / Real.pi) ^ 2 *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) *
        (cosineVandermondeWeight 2 angles * allMinusAngleWeight 2 angles))
    angles

noncomputable def rankFourEvenFullNormalizedIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFourEvenFullNormalizedIntegrand index angles
    ∂cosineCubeProductMeasure 2

noncomputable def rankFourEvenNegativeIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFourEvenNegativeProductIntegrand index angles
    ∂cosineCubeProductMeasure 2

noncomputable def rankFourEvenMiddleIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFourEvenMiddleProductIntegrand index angles
    ∂cosineCubeProductMeasure 2

theorem integrable_rankFourEvenFullNormalizedIntegrand (index : ℕ) :
    Integrable (rankFourEvenFullNormalizedIntegrand index)
      (cosineCubeProductMeasure 2) := by
  apply integrable_continuous_cosineCube
  unfold rankFourEvenFullNormalizedIntegrand
  exact (continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale 2)).div_const _)).mul
        (continuous_evenWeylAngleWeight 2)

theorem integrable_rankFourEvenPositiveProductIntegrand (index : ℕ) :
    Integrable (rankFourEvenPositiveProductIntegrand index)
      (cosineCubeProductMeasure 2) :=
  (integrable_rankFourEvenFullNormalizedIntegrand index).indicator
    (measurableSet_positiveSpectralLocalDomain 2)

theorem integrable_rankFourEvenNegativeProductIntegrand (index : ℕ) :
    Integrable (rankFourEvenNegativeProductIntegrand index)
      (cosineCubeProductMeasure 2) :=
  (integrable_rankFourEvenFullNormalizedIntegrand index).indicator
    (measurableSet_negativeSpectralLocalDomain 2)

theorem integrable_rankFourEvenMiddleProductIntegrand (index : ℕ) :
    Integrable (rankFourEvenMiddleProductIntegrand index)
      (cosineCubeProductMeasure 2) :=
  (integrable_rankFourEvenFullNormalizedIntegrand index).indicator
    (measurableSet_middleOpenSpectralDomain 2)

theorem rankFourEvenFullIntegrand_partition
    (index : ℕ) (angles : Fin 2 → ℝ) :
    rankFourEvenFullNormalizedIntegrand index angles =
      rankFourEvenPositiveProductIntegrand index angles +
        (rankFourEvenNegativeProductIntegrand index angles +
          rankFourEvenMiddleProductIntegrand index angles) := by
  have hmidPos : 0 < cosineScaleMidpoint 2 := by
    unfold cosineScaleMidpoint
    norm_num
  by_cases hpositive : angles ∈ positiveSpectralLocalDomain 2
  · have hnegative : angles ∉ negativeSpectralLocalDomain 2 := by
      intro hnegative
      change cosineScaleMidpoint 2 ≤ cosineCubeScale angles at hpositive
      change cosineCubeScale angles ≤ -cosineScaleMidpoint 2 at hnegative
      linarith
    have hmiddle : angles ∉ middleOpenSpectralDomain 2 := by
      intro hmiddle
      exact (not_lt_of_ge hpositive) hmiddle.2
    rw [rankFourEvenPositiveProductIntegrand, Set.indicator_of_mem hpositive,
      rankFourEvenNegativeProductIntegrand, Set.indicator_of_notMem hnegative,
      rankFourEvenMiddleProductIntegrand, Set.indicator_of_notMem hmiddle,
      zero_add, add_zero]
  · have hpositiveLt : cosineCubeScale angles < cosineScaleMidpoint 2 :=
      lt_of_not_ge hpositive
    by_cases hnegative : angles ∈ negativeSpectralLocalDomain 2
    · have hmiddle : angles ∉ middleOpenSpectralDomain 2 := by
        intro hmiddle
        exact (not_lt_of_ge hnegative) hmiddle.1
      rw [rankFourEvenPositiveProductIntegrand,
        Set.indicator_of_notMem hpositive,
        rankFourEvenNegativeProductIntegrand, Set.indicator_of_mem hnegative,
        rankFourEvenMiddleProductIntegrand, Set.indicator_of_notMem hmiddle,
        zero_add, add_zero]
    · have hnegativeLt : -cosineScaleMidpoint 2 < cosineCubeScale angles :=
        lt_of_not_ge hnegative
      have hmiddle : angles ∈ middleOpenSpectralDomain 2 :=
        ⟨hnegativeLt, hpositiveLt⟩
      rw [rankFourEvenPositiveProductIntegrand,
        Set.indicator_of_notMem hpositive,
        rankFourEvenNegativeProductIntegrand,
        Set.indicator_of_notMem hnegative,
        rankFourEvenMiddleProductIntegrand, Set.indicator_of_mem hmiddle,
        zero_add]
      simp only [zero_add]

theorem rankFourEvenPositiveIntegral_eq_angleLocal (index : ℕ) :
    (∫ angles : Fin 2 → ℝ,
      rankFourEvenPositiveProductIntegrand index angles
      ∂cosineCubeProductMeasure 2) =
      rankFourEvenAngleLocalIntegral index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin 2 => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube 2 by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube 2) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold rankFourEvenAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube 2
  · by_cases hlocal : angles ∈ positiveSpectralLocalDomain 2
    · have hangleLocal : angles ∈ anglePositiveLocalDomain 2 := ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        rankFourEvenPositiveProductIntegrand, Set.indicator_of_mem hlocal,
        rankFourEvenAngleLocalIntegrand, Set.indicator_of_mem hangleLocal]
      rfl
    · rw [Set.indicator_of_mem hcube,
        rankFourEvenPositiveProductIntegrand, Set.indicator_of_notMem hlocal,
        rankFourEvenAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      rankFourEvenAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem cosineVandermondeWeight_two_reflection (angles : Fin 2 → ℝ) :
    cosineVandermondeWeight 2 (angleReflectionEquiv 2 angles) =
      cosineVandermondeWeight 2 angles := by
  unfold cosineVandermondeWeight
  apply Finset.prod_congr rfl
  intro upper _hupper
  apply Finset.prod_congr rfl
  intro lower _hlower
  simp only [angleReflectionEquiv_apply, Real.cos_pi_sub]
  ring

theorem rankFourEvenAngleWeight_reflection (angles : Fin 2 → ℝ) :
    evenWeylAngleWeight 2 (angleReflectionEquiv 2 angles) =
      cosineVandermondeWeight 2 angles * allMinusAngleWeight 2 angles := by
  unfold evenWeylAngleWeight allMinusAngleWeight
  rw [cosineVandermondeWeight_two_reflection]
  congr 1
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  rw [angleReflectionEquiv_apply, Real.cos_pi_sub]
  ring

theorem rankFourEvenNegative_reflection_pointwise
    (index : ℕ) (angles : Fin 2 → ℝ) :
    rankFourEvenNegativeProductIntegrand index
        (angleReflectionEquiv 2 angles) =
      (-1 : ℝ) ^ index *
        rankFourEvenMinusPositiveProductIntegrand index angles := by
  have hscale := cosineCubeScale_angleReflection 2 angles
  by_cases hdomain : angles ∈ positiveSpectralLocalDomain 2
  · have hreflected : angleReflectionEquiv 2 angles ∈
        negativeSpectralLocalDomain 2 := by
      change cosineCubeScale (angleReflectionEquiv 2 angles) ≤
        -cosineScaleMidpoint 2
      rw [hscale]
      exact neg_le_neg hdomain
    rw [rankFourEvenNegativeProductIntegrand,
      Set.indicator_of_mem hreflected,
      rankFourEvenMinusPositiveProductIntegrand,
      Set.indicator_of_mem hdomain,
      rankFourEvenFullNormalizedIntegrand, hscale,
      fibonacciScaleKernel_neg, rankFourEvenAngleWeight_reflection]
    ring
  · have hreflected : angleReflectionEquiv 2 angles ∉
        negativeSpectralLocalDomain 2 := by
      intro hreflected
      apply hdomain
      change cosineCubeScale (angleReflectionEquiv 2 angles) ≤
        -cosineScaleMidpoint 2 at hreflected
      rw [hscale] at hreflected
      change cosineScaleMidpoint 2 ≤ cosineCubeScale angles
      linarith
    rw [rankFourEvenNegativeProductIntegrand,
      Set.indicator_of_notMem hreflected,
      rankFourEvenMinusPositiveProductIntegrand,
      Set.indicator_of_notMem hdomain, mul_zero]

theorem rankFourEvenMinusPositiveIntegral_eq_angleLocal (index : ℕ) :
    (∫ angles : Fin 2 → ℝ,
      rankFourEvenMinusPositiveProductIntegrand index angles
      ∂cosineCubeProductMeasure 2) =
      rankFourEvenMinusAngleLocalIntegral index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin 2 => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube 2 by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube 2) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold rankFourEvenMinusAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube 2
  · by_cases hlocal : angles ∈ positiveSpectralLocalDomain 2
    · have hangleLocal : angles ∈ anglePositiveLocalDomain 2 := ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        rankFourEvenMinusPositiveProductIntegrand,
        Set.indicator_of_mem hlocal,
        rankFourEvenMinusAngleLocalIntegrand,
        Set.indicator_of_mem hangleLocal]
    · rw [Set.indicator_of_mem hcube,
        rankFourEvenMinusPositiveProductIntegrand,
        Set.indicator_of_notMem hlocal,
        rankFourEvenMinusAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      rankFourEvenMinusAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem rankFourEvenNegativeIntegral_eq (index : ℕ) :
    rankFourEvenNegativeIntegral index =
      (-1 : ℝ) ^ index * rankFourEvenMinusAngleLocalIntegral index := by
  unfold rankFourEvenNegativeIntegral
  rw [← (measurePreserving_angleReflectionEquiv 2).integral_comp'
    (rankFourEvenNegativeProductIntegrand index)]
  rw [show (fun angles : Fin 2 → ℝ =>
      rankFourEvenNegativeProductIntegrand index
        (angleReflectionEquiv 2 angles)) =
      fun angles => (-1 : ℝ) ^ index *
        rankFourEvenMinusPositiveProductIntegrand index angles by
    funext angles
    exact rankFourEvenNegative_reflection_pointwise index angles]
  rw [integral_const_mul,
    rankFourEvenMinusPositiveIntegral_eq_angleLocal]

theorem tendsto_rankFourEvenNegativeIntegral_zero :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourEvenNegativeIntegral index)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ‖(index + 1 : ℝ) ^ 3 *
        rankFourEvenMinusAngleLocalIntegral index‖)
  · intro index
    rw [rankFourEvenNegativeIntegral_eq]
    simp [norm_mul]
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_rankFourEvenMinusAngleLocalIntegral_zero

theorem evenWeylAngleWeight_two_le_sixteen (angles : Fin 2 → ℝ) :
    evenWeylAngleWeight 2 angles ≤ 16 := by
  rw [evenWeylAngleWeight_two_formula]
  have hdiff : (Real.cos (angles 1) - Real.cos (angles 0)) ^ 2 ≤ 4 := by
    have h0l := Real.neg_one_le_cos (angles 0)
    have h0u := Real.cos_le_one (angles 0)
    have h1l := Real.neg_one_le_cos (angles 1)
    have h1u := Real.cos_le_one (angles 1)
    nlinarith
  have h0 : 0 ≤ 1 + Real.cos (angles 0) := by
    linarith [Real.neg_one_le_cos (angles 0)]
  have h1 : 0 ≤ 1 + Real.cos (angles 1) := by
    linarith [Real.neg_one_le_cos (angles 1)]
  have h0u : 1 + Real.cos (angles 0) ≤ 2 := by
    linarith [Real.cos_le_one (angles 0)]
  have h1u : 1 + Real.cos (angles 1) ≤ 2 := by
    linarith [Real.cos_le_one (angles 1)]
  nlinarith [mul_le_mul h0u h1u h1 (by norm_num : (0 : ℝ) ≤ 2)]

noncomputable def rankFourMiddleGrowthRatio : ℝ :=
  absoluteKernelGrowth 3 / largeScalePreimage 4

theorem rankFourMiddleGrowthRatio_pos : 0 < rankFourMiddleGrowthRatio := by
  unfold rankFourMiddleGrowthRatio
  exact div_pos (absoluteKernelGrowth_pos (by norm_num))
    (largeScalePreimage_pos (by norm_num))

theorem rankFourMiddleGrowthRatio_lt_one : rankFourMiddleGrowthRatio < 1 := by
  rw [rankFourMiddleGrowthRatio,
    div_lt_one (largeScalePreimage_pos (by norm_num))]
  have h := absoluteKernelGrowth_halfway_lt_largeScalePreimage
    (base := 4) (by norm_num)
  norm_num at h ⊢
  exact h

theorem tendsto_rankFourMiddlePolynomialGeometric :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourMiddleGrowthRatio ^ (index + 1))
      atTop (nhds 0) := by
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one 3
    (by rw [abs_of_pos rankFourMiddleGrowthRatio_pos]
        exact rankFourMiddleGrowthRatio_lt_one)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourMiddleGrowthRatio ^ (index + 1)) =
      (fun index : ℕ => (index : ℝ) ^ 3 *
        rankFourMiddleGrowthRatio ^ index) ∘ (fun index => index + 1) by
    funext index
    simp [Function.comp_apply]]
  exact hshift

theorem abs_cosineCubeScale_le_three_of_middle
    {angles : Fin 2 → ℝ} (hangles : angles ∈ middleOpenSpectralDomain 2) :
    |cosineCubeScale angles| ≤ 3 := by
  change -cosineScaleMidpoint 2 < cosineCubeScale angles ∧
    cosineCubeScale angles < cosineScaleMidpoint 2 at hangles
  norm_num [cosineScaleMidpoint] at hangles ⊢
  exact abs_le.2 ⟨hangles.1.le, hangles.2.le⟩

theorem abs_rankFourNormalizedKernel_le_middle
    {index : ℕ} {scale : ℝ} (hscale : |scale| ≤ 3) :
    |fibonacciScaleKernel scale index /
        (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)| ≤
      Real.sqrt 12 * rankFourMiddleGrowthRatio ^ (index + 1) := by
  let gamma := absoluteKernelGrowth 3
  let alpha := largeScalePreimage 4
  have hkernel : |fibonacciScaleKernel scale index| ≤ gamma ^ index :=
    abs_fibonacciScaleKernel_le_growth_pow (by norm_num) hscale index
  have hgammaOne : 1 ≤ gamma :=
    (by norm_num : (1 : ℝ) ≤ 3).trans
      (absoluteKernelGrowth_ge_bound (by norm_num))
  have halphaPos : 0 < alpha := largeScalePreimage_pos (by norm_num)
  have hrootPos : 0 < Real.sqrt (12 : ℝ) := by positivity
  have hdenomPos : 0 < alpha ^ (index + 1) / Real.sqrt 12 :=
    div_pos (pow_pos halphaPos _) hrootPos
  rw [abs_div, abs_of_pos hdenomPos]
  calc
    |fibonacciScaleKernel scale index| /
        (alpha ^ (index + 1) / Real.sqrt 12) =
      (|fibonacciScaleKernel scale index| * Real.sqrt 12) /
        alpha ^ (index + 1) := by field_simp
    _ ≤ (gamma ^ index * Real.sqrt 12) / alpha ^ (index + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkernel hrootPos.le)
        (pow_nonneg halphaPos.le _)
    _ ≤ (gamma ^ (index + 1) * Real.sqrt 12) /
        alpha ^ (index + 1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg halphaPos.le _)
      apply mul_le_mul_of_nonneg_right _ hrootPos.le
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg (by positivity) _) hgammaOne
    _ = Real.sqrt 12 * (gamma / alpha) ^ (index + 1) := by
      rw [div_pow]
      ring
    _ = _ := by rfl

theorem norm_rankFourEvenMiddleProductIntegrand_le
    (index : ℕ) (angles : Fin 2 → ℝ) :
    ‖rankFourEvenMiddleProductIntegrand index angles‖ ≤
      ((1 / Real.pi) ^ 2 * Real.sqrt 12 * 16) *
        rankFourMiddleGrowthRatio ^ (index + 1) := by
  by_cases hmiddle : angles ∈ middleOpenSpectralDomain 2
  · rw [rankFourEvenMiddleProductIntegrand, Set.indicator_of_mem hmiddle,
      rankFourEvenFullNormalizedIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
      abs_of_nonneg (evenWeylAngleWeight_nonneg 2 angles)]
    have hkernel := abs_rankFourNormalizedKernel_le_middle (index := index)
      (abs_cosineCubeScale_le_three_of_middle hmiddle)
    have hweight := evenWeylAngleWeight_two_le_sixteen angles
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left hkernel (pow_nonneg (by positivity) _))
      hweight (evenWeylAngleWeight_nonneg 2 angles)
      (mul_nonneg (pow_nonneg (by positivity) _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg rankFourMiddleGrowthRatio_pos.le _)))).trans_eq (by ring)
  · rw [rankFourEvenMiddleProductIntegrand,
      Set.indicator_of_notMem hmiddle, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _) (Real.sqrt_nonneg _))
        (by norm_num))
      (pow_nonneg rankFourMiddleGrowthRatio_pos.le _)

theorem tendsto_rankFourEvenMiddleIntegral_zero :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourEvenMiddleIntegral index)
      atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) ^ 2 * Real.sqrt 12 * 16) *
    (cosineCubeProductMeasure 2).real Set.univ
  have hbound : ∀ index,
      ‖rankFourEvenMiddleIntegral index‖ ≤
        (((1 / Real.pi) ^ 2 * Real.sqrt 12 * 16) *
          rankFourMiddleGrowthRatio ^ (index + 1)) *
            (cosineCubeProductMeasure 2).real Set.univ := by
    intro index
    unfold rankFourEvenMiddleIntegral
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall
        (norm_rankFourEvenMiddleProductIntegrand_le index))
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 3 *
        rankFourMiddleGrowthRatio ^ (index + 1)) * constant)
  · intro index
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by positivity) _)]
    exact (mul_le_mul_of_nonneg_left (hbound index)
      (pow_nonneg (by positivity) _)).trans_eq (by ring)
  · simpa using tendsto_rankFourMiddlePolynomialGeometric.mul_const constant

theorem rankFourEvenFullNormalizedIntegral_partition (index : ℕ) :
    rankFourEvenFullNormalizedIntegral index =
      rankFourEvenAngleLocalIntegral index +
        (rankFourEvenNegativeIntegral index + rankFourEvenMiddleIntegral index) := by
  unfold rankFourEvenFullNormalizedIntegral rankFourEvenNegativeIntegral
    rankFourEvenMiddleIntegral
  rw [show (fun angles : Fin 2 → ℝ =>
      rankFourEvenFullNormalizedIntegrand index angles) =
      fun angles => rankFourEvenPositiveProductIntegrand index angles +
        (rankFourEvenNegativeProductIntegrand index angles +
          rankFourEvenMiddleProductIntegrand index angles) by
    funext angles
    exact rankFourEvenFullIntegrand_partition index angles]
  calc
    (∫ angles : Fin 2 → ℝ,
        rankFourEvenPositiveProductIntegrand index angles +
          (rankFourEvenNegativeProductIntegrand index angles +
            rankFourEvenMiddleProductIntegrand index angles)
        ∂cosineCubeProductMeasure 2) =
      (∫ angles, rankFourEvenPositiveProductIntegrand index angles
        ∂cosineCubeProductMeasure 2) +
        ∫ angles, rankFourEvenNegativeProductIntegrand index angles +
          rankFourEvenMiddleProductIntegrand index angles
          ∂cosineCubeProductMeasure 2 :=
      integral_add (integrable_rankFourEvenPositiveProductIntegrand index)
        ((integrable_rankFourEvenNegativeProductIntegrand index).add
          (integrable_rankFourEvenMiddleProductIntegrand index))
    _ = (∫ angles, rankFourEvenPositiveProductIntegrand index angles
          ∂cosineCubeProductMeasure 2) +
        ((∫ angles, rankFourEvenNegativeProductIntegrand index angles
            ∂cosineCubeProductMeasure 2) +
          ∫ angles, rankFourEvenMiddleProductIntegrand index angles
            ∂cosineCubeProductMeasure 2) := by
      rw [integral_add (integrable_rankFourEvenNegativeProductIntegrand index)
        (integrable_rankFourEvenMiddleProductIntegrand index)]
    _ = _ := by rw [rankFourEvenPositiveIntegral_eq_angleLocal]

theorem tendsto_rankFourEvenFullNormalizedIntegral :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourEvenFullNormalizedIntegral index)
      atTop (nhds (∫ coordinates : Fin 2 → ℝ,
        rankFourEvenLocalLimitIntegrand coordinates)) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourEvenFullNormalizedIntegral index) =
      fun index : ℕ =>
        (index + 1 : ℝ) ^ 3 * rankFourEvenAngleLocalIntegral index +
          ((index + 1 : ℝ) ^ 3 * rankFourEvenNegativeIntegral index +
            (index + 1 : ℝ) ^ 3 * rankFourEvenMiddleIntegral index) by
    funext index
    rw [rankFourEvenFullNormalizedIntegral_partition]
    ring]
  simpa using tendsto_rankFourEvenAngleLocalIntegral.add
    (tendsto_rankFourEvenNegativeIntegral_zero.add
      tendsto_rankFourEvenMiddleIntegral_zero)

theorem rankFourEvenFullNormalizedIntegral_eq_weylMoment (index : ℕ) :
    rankFourEvenFullNormalizedIntegral index =
      (1 / Real.pi) ^ 2 *
        (evenWeylFibonacciMoment 2 index /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) := by
  unfold rankFourEvenFullNormalizedIntegral rankFourEvenFullNormalizedIntegrand
    evenWeylFibonacciMoment weightedCosineCubeFibonacciMoment
    weightedCosineCubeFibonacciIntegrand
  rw [show (fun angles : Fin 2 → ℝ =>
      (1 / Real.pi) ^ 2 *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) *
        evenWeylAngleWeight 2 angles) =
      fun angles => ((1 / Real.pi) ^ 2 /
        (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)) *
          (fibonacciScaleKernel (cosineCubeScale angles) index *
            evenWeylAngleWeight 2 angles) by
    funext angles
    ring]
  rw [integral_const_mul]
  ring

theorem tendsto_rankFourRibbonNormalizedIntegralConstant :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 *
        ((ribbonCount 3 index : ℝ) /
          (largeScalePreimage 4 ^ (index + 1) / Real.sqrt 12)))
      atTop (nhds (2 * (∫ coordinates : Fin 2 → ℝ,
        rankFourEvenLocalLimitIntegrand coordinates))) := by
  have h := tendsto_rankFourEvenFullNormalizedIntegral.const_mul 2
  apply h.congr'
  filter_upwards with index
  rw [rankFourEvenFullNormalizedIntegral_eq_weylMoment,
    heightFourRibbonCount_eq_normalized_evenWeylFibonacciMoment]
  field_simp [Real.pi_ne_zero]

end FibonacciRibbonKernel
