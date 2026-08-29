import FibonacciRibbonKernel.RankFourGeometricNegative

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFourGeometricFullIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (1 / Real.pi) ^ 2 * (cosineCubeScale angles / 4) ^ index *
    evenWeylAngleWeight 2 angles

noncomputable def rankFourGeometricPositiveIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (positiveSpectralLocalDomain 2).indicator
    (rankFourGeometricFullIntegrand index) angles

noncomputable def rankFourGeometricNegativeIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (negativeSpectralLocalDomain 2).indicator
    (rankFourGeometricFullIntegrand index) angles

noncomputable def rankFourGeometricMiddleIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (middleOpenSpectralDomain 2).indicator
    (rankFourGeometricFullIntegrand index) angles

noncomputable def rankFourGeometricMinusPositiveIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (positiveSpectralLocalDomain 2).indicator (fun angles =>
    (1 / Real.pi) ^ 2 * (cosineCubeScale angles / 4) ^ index *
      (cosineVandermondeWeight 2 angles * allMinusAngleWeight 2 angles)) angles

noncomputable def rankFourGeometricFullIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFourGeometricFullIntegrand index angles
    ∂cosineCubeProductMeasure 2

noncomputable def rankFourGeometricNegativeIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFourGeometricNegativeIntegrand index angles
    ∂cosineCubeProductMeasure 2

noncomputable def rankFourGeometricMiddleIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFourGeometricMiddleIntegrand index angles
    ∂cosineCubeProductMeasure 2

theorem integrable_rankFourGeometricFullIntegrand (index : ℕ) :
    Integrable (rankFourGeometricFullIntegrand index)
      (cosineCubeProductMeasure 2) := by
  apply integrable_continuous_cosineCube
  have hpower : Continuous (fun angles : Fin 2 → ℝ =>
      (cosineCubeScale angles / 4) ^ index) :=
    ((continuous_cosineCubeScale 2).div_const 4).pow index
  unfold rankFourGeometricFullIntegrand
  exact (continuous_const.mul hpower).mul (continuous_evenWeylAngleWeight 2)

theorem rankFourGeometricFull_partition
    (index : ℕ) (angles : Fin 2 → ℝ) :
    rankFourGeometricFullIntegrand index angles =
      rankFourGeometricPositiveIntegrand index angles +
        (rankFourGeometricNegativeIntegrand index angles +
          rankFourGeometricMiddleIntegrand index angles) := by
  by_cases hp : angles ∈ positiveSpectralLocalDomain 2
  · have hn : angles ∉ negativeSpectralLocalDomain 2 := by
      intro hn
      change cosineScaleMidpoint 2 ≤ cosineCubeScale angles at hp
      change cosineCubeScale angles ≤ -cosineScaleMidpoint 2 at hn
      have hm : 0 < cosineScaleMidpoint 2 := by norm_num [cosineScaleMidpoint]
      linarith
    have hm : angles ∉ middleOpenSpectralDomain 2 := fun hm =>
      (not_lt_of_ge hp) hm.2
    rw [rankFourGeometricPositiveIntegrand, Set.indicator_of_mem hp,
      rankFourGeometricNegativeIntegrand, Set.indicator_of_notMem hn,
      rankFourGeometricMiddleIntegrand, Set.indicator_of_notMem hm,
      zero_add, add_zero]
  · have hplt : cosineCubeScale angles < cosineScaleMidpoint 2 := lt_of_not_ge hp
    by_cases hn : angles ∈ negativeSpectralLocalDomain 2
    · have hm : angles ∉ middleOpenSpectralDomain 2 := fun hm =>
        (not_lt_of_ge hn) hm.1
      rw [rankFourGeometricPositiveIntegrand, Set.indicator_of_notMem hp,
        rankFourGeometricNegativeIntegrand, Set.indicator_of_mem hn,
        rankFourGeometricMiddleIntegrand, Set.indicator_of_notMem hm,
        zero_add, add_zero]
    · have hnlt : -cosineScaleMidpoint 2 < cosineCubeScale angles :=
        lt_of_not_ge hn
      have hm : angles ∈ middleOpenSpectralDomain 2 := ⟨hnlt, hplt⟩
      rw [rankFourGeometricPositiveIntegrand, Set.indicator_of_notMem hp,
        rankFourGeometricNegativeIntegrand, Set.indicator_of_notMem hn,
        rankFourGeometricMiddleIntegrand, Set.indicator_of_mem hm]
      simp

theorem rankFourGeometricPositiveIntegral_eq_angleLocal (index : ℕ) :
    (∫ angles : Fin 2 → ℝ, rankFourGeometricPositiveIntegrand index angles
      ∂cosineCubeProductMeasure 2) =
      rankFourGeometricAngleLocalIntegral index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin 2 => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube 2 by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube 2) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold rankFourGeometricAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hc : angles ∈ anglePositiveCube 2
  · by_cases hl : angles ∈ positiveSpectralLocalDomain 2
    · have hlocal : angles ∈ anglePositiveLocalDomain 2 := ⟨hc, hl⟩
      rw [Set.indicator_of_mem hc,
        rankFourGeometricPositiveIntegrand, Set.indicator_of_mem hl,
        rankFourGeometricAngleLocalIntegrand,
        Set.indicator_of_mem hlocal]
      rfl
    · rw [Set.indicator_of_mem hc,
        rankFourGeometricPositiveIntegrand, Set.indicator_of_notMem hl,
        rankFourGeometricAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hl h.2)]
  · rw [Set.indicator_of_notMem hc,
      rankFourGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hc h.1)]

theorem rankFourGeometricNegative_reflection
    (index : ℕ) (angles : Fin 2 → ℝ) :
    rankFourGeometricNegativeIntegrand index (angleReflectionEquiv 2 angles) =
      (-1 : ℝ) ^ index * rankFourGeometricMinusPositiveIntegrand index angles := by
  have hs := cosineCubeScale_angleReflection 2 angles
  by_cases hd : angles ∈ positiveSpectralLocalDomain 2
  · have hr : angleReflectionEquiv 2 angles ∈ negativeSpectralLocalDomain 2 := by
      change cosineCubeScale (angleReflectionEquiv 2 angles) ≤
        -cosineScaleMidpoint 2
      rw [hs]
      exact neg_le_neg hd
    rw [rankFourGeometricNegativeIntegrand, Set.indicator_of_mem hr,
      rankFourGeometricMinusPositiveIntegrand, Set.indicator_of_mem hd,
      rankFourGeometricFullIntegrand, hs, rankFourEvenAngleWeight_reflection]
    rw [neg_div, neg_pow]
    ring
  · have hr : angleReflectionEquiv 2 angles ∉ negativeSpectralLocalDomain 2 := by
      intro hr
      apply hd
      change cosineCubeScale (angleReflectionEquiv 2 angles) ≤
        -cosineScaleMidpoint 2 at hr
      rw [hs] at hr
      change cosineScaleMidpoint 2 ≤ cosineCubeScale angles
      linarith
    rw [rankFourGeometricNegativeIntegrand, Set.indicator_of_notMem hr,
      rankFourGeometricMinusPositiveIntegrand, Set.indicator_of_notMem hd,
      mul_zero]

theorem rankFourGeometricMinusPositiveIntegral_eq_angleLocal (index : ℕ) :
    (∫ angles : Fin 2 → ℝ,
      rankFourGeometricMinusPositiveIntegrand index angles
      ∂cosineCubeProductMeasure 2) =
      rankFourGeometricMinusAngleLocalIntegral index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin 2 => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube 2 by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube 2) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold rankFourGeometricMinusAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hc : angles ∈ anglePositiveCube 2
  · by_cases hl : angles ∈ positiveSpectralLocalDomain 2
    · have hlocal : angles ∈ anglePositiveLocalDomain 2 := ⟨hc, hl⟩
      rw [Set.indicator_of_mem hc,
        rankFourGeometricMinusPositiveIntegrand, Set.indicator_of_mem hl,
        rankFourGeometricMinusAngleLocalIntegrand,
        Set.indicator_of_mem hlocal]
    · rw [Set.indicator_of_mem hc,
        rankFourGeometricMinusPositiveIntegrand, Set.indicator_of_notMem hl,
        rankFourGeometricMinusAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hl h.2)]
  · rw [Set.indicator_of_notMem hc,
      rankFourGeometricMinusAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hc h.1)]

theorem rankFourGeometricNegativeIntegral_eq (index : ℕ) :
    rankFourGeometricNegativeIntegral index =
      (-1 : ℝ) ^ index * rankFourGeometricMinusAngleLocalIntegral index := by
  unfold rankFourGeometricNegativeIntegral
  rw [← (measurePreserving_angleReflectionEquiv 2).integral_comp'
    (rankFourGeometricNegativeIntegrand index)]
  rw [show (fun angles : Fin 2 → ℝ =>
      rankFourGeometricNegativeIntegrand index (angleReflectionEquiv 2 angles)) =
      fun angles => (-1 : ℝ) ^ index *
        rankFourGeometricMinusPositiveIntegrand index angles by
    funext angles
    exact rankFourGeometricNegative_reflection index angles,
    integral_const_mul, rankFourGeometricMinusPositiveIntegral_eq_angleLocal]

theorem tendsto_rankFourGeometricNegativeIntegral_zero :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricNegativeIntegral index)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ‖(index + 1 : ℝ) ^ 3 *
        rankFourGeometricMinusAngleLocalIntegral index‖)
  · intro index
    rw [rankFourGeometricNegativeIntegral_eq]
    simp [norm_mul]
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_rankFourGeometricMinusAngleLocalIntegral_zero

noncomputable def rankFourGeometricMiddleRatio : ℝ := 3 / 4

theorem rankFourGeometricMiddleRatio_pos : 0 < rankFourGeometricMiddleRatio := by
  norm_num [rankFourGeometricMiddleRatio]

theorem tendsto_rankFourGeometricMiddlePolynomial :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricMiddleRatio ^ index)
      atTop (nhds 0) := by
  have hbase : Tendsto (fun index : ℕ =>
      (index : ℝ) ^ 3 * rankFourGeometricMiddleRatio ^ index)
      atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one 3
      (by norm_num [rankFourGeometricMiddleRatio])
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricMiddleRatio ^ index) =
      fun index : ℕ =>
        ((index + 1 : ℝ) ^ 3 *
          rankFourGeometricMiddleRatio ^ (index + 1)) *
            rankFourGeometricMiddleRatio⁻¹ by
    funext index
    field_simp [rankFourGeometricMiddleRatio_pos.ne']
    exact (pow_succ _ _).symm]
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, zero_mul] using
    hshift.mul_const rankFourGeometricMiddleRatio⁻¹

theorem norm_rankFourGeometricMiddleIntegrand_le
    (index : ℕ) (angles : Fin 2 → ℝ) :
    ‖rankFourGeometricMiddleIntegrand index angles‖ ≤
      ((1 / Real.pi) ^ 2 * 16) * rankFourGeometricMiddleRatio ^ index := by
  by_cases hm : angles ∈ middleOpenSpectralDomain 2
  · rw [rankFourGeometricMiddleIntegrand, Set.indicator_of_mem hm,
      rankFourGeometricFullIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
      abs_of_nonneg (evenWeylAngleWeight_nonneg 2 angles)]
    have hs := abs_cosineCubeScale_le_three_of_middle hm
    have hr : |cosineCubeScale angles / 4| ≤
        rankFourGeometricMiddleRatio := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      unfold rankFourGeometricMiddleRatio
      linarith
    have hp := pow_le_pow_left₀ (abs_nonneg _) hr index
    have hw := evenWeylAngleWeight_two_le_sixteen angles
    have hscaled :
        (1 / Real.pi) ^ 2 * |cosineCubeScale angles / 4| ^ index *
            evenWeylAngleWeight 2 angles ≤
          (1 / Real.pi) ^ 2 * rankFourGeometricMiddleRatio ^ index * 16 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp
        (pow_nonneg (by positivity) _)) hw
        (evenWeylAngleWeight_nonneg 2 angles)
        (mul_nonneg (pow_nonneg (by positivity) _)
          (pow_nonneg rankFourGeometricMiddleRatio_pos.le _))
    calc
      (1 / Real.pi) ^ 2 * |(cosineCubeScale angles / 4) ^ index| *
          evenWeylAngleWeight 2 angles =
        (1 / Real.pi) ^ 2 * |cosineCubeScale angles / 4| ^ index *
          evenWeylAngleWeight 2 angles := by rw [abs_pow]
      _ ≤ (1 / Real.pi) ^ 2 * rankFourGeometricMiddleRatio ^ index * 16 :=
        hscaled
      _ = ((1 / Real.pi) ^ 2 * 16) *
          rankFourGeometricMiddleRatio ^ index := by ring
  · rw [rankFourGeometricMiddleIntegrand, Set.indicator_of_notMem hm, norm_zero]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by positivity) _) (by norm_num))
      (pow_nonneg rankFourGeometricMiddleRatio_pos.le _)

theorem tendsto_rankFourGeometricMiddleIntegral_zero :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricMiddleIntegral index)
      atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) ^ 2 * 16) *
    (cosineCubeProductMeasure 2).real Set.univ
  have hb : ∀ index, ‖rankFourGeometricMiddleIntegral index‖ ≤
      (((1 / Real.pi) ^ 2 * 16) * rankFourGeometricMiddleRatio ^ index) *
        (cosineCubeProductMeasure 2).real Set.univ := by
    intro index
    unfold rankFourGeometricMiddleIntegral
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall
        (norm_rankFourGeometricMiddleIntegrand_le index))
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 3 * rankFourGeometricMiddleRatio ^ index) * constant)
  · intro index
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by positivity) _)]
    exact (mul_le_mul_of_nonneg_left (hb index)
      (pow_nonneg (by positivity) _)).trans_eq (by ring)
  · simpa using tendsto_rankFourGeometricMiddlePolynomial.mul_const constant

theorem rankFourGeometricFullIntegral_limit :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricFullIntegral index)
      atTop (nhds (∫ coordinates : Fin 2 → ℝ,
        rankFourGeometricLocalLimitIntegrand coordinates)) := by
  have hiFull : ∀ index,
      rankFourGeometricFullIntegral index =
        rankFourGeometricAngleLocalIntegral index +
          (rankFourGeometricNegativeIntegral index +
            rankFourGeometricMiddleIntegral index) := by
    intro index
    unfold rankFourGeometricFullIntegral rankFourGeometricNegativeIntegral
      rankFourGeometricMiddleIntegral
    rw [show (fun angles : Fin 2 → ℝ => rankFourGeometricFullIntegrand index angles) =
      fun angles => rankFourGeometricPositiveIntegrand index angles +
        (rankFourGeometricNegativeIntegrand index angles +
          rankFourGeometricMiddleIntegrand index angles) by
      funext angles
      exact rankFourGeometricFull_partition index angles]
    have hpos : Integrable (rankFourGeometricPositiveIntegrand index)
        (cosineCubeProductMeasure 2) := by
      unfold rankFourGeometricPositiveIntegrand
      exact (integrable_rankFourGeometricFullIntegrand index).indicator
        (measurableSet_positiveSpectralLocalDomain 2)
    have hneg : Integrable (rankFourGeometricNegativeIntegrand index)
        (cosineCubeProductMeasure 2) := by
      unfold rankFourGeometricNegativeIntegrand
      exact (integrable_rankFourGeometricFullIntegrand index).indicator
        (measurableSet_negativeSpectralLocalDomain 2)
    have hmid : Integrable (rankFourGeometricMiddleIntegrand index)
        (cosineCubeProductMeasure 2) := by
      unfold rankFourGeometricMiddleIntegrand
      exact (integrable_rankFourGeometricFullIntegrand index).indicator
        (measurableSet_middleOpenSpectralDomain 2)
    calc
      (∫ angles : Fin 2 → ℝ,
          rankFourGeometricPositiveIntegrand index angles +
            (rankFourGeometricNegativeIntegrand index angles +
              rankFourGeometricMiddleIntegrand index angles)
          ∂cosineCubeProductMeasure 2) =
        (∫ angles, rankFourGeometricPositiveIntegrand index angles
          ∂cosineCubeProductMeasure 2) +
          ∫ angles, rankFourGeometricNegativeIntegrand index angles +
            rankFourGeometricMiddleIntegrand index angles
            ∂cosineCubeProductMeasure 2 := integral_add hpos (hneg.add hmid)
      _ = (∫ angles, rankFourGeometricPositiveIntegrand index angles
            ∂cosineCubeProductMeasure 2) +
          ((∫ angles, rankFourGeometricNegativeIntegrand index angles
              ∂cosineCubeProductMeasure 2) +
            ∫ angles, rankFourGeometricMiddleIntegrand index angles
              ∂cosineCubeProductMeasure 2) := by
        rw [integral_add hneg hmid]
      _ = _ := by rw [rankFourGeometricPositiveIntegral_eq_angleLocal]
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricFullIntegral index) =
      fun index : ℕ =>
        (index + 1 : ℝ) ^ 3 * rankFourGeometricAngleLocalIntegral index +
          ((index + 1 : ℝ) ^ 3 * rankFourGeometricNegativeIntegral index +
            (index + 1 : ℝ) ^ 3 * rankFourGeometricMiddleIntegral index) by
    funext index
    rw [hiFull]
    ring]
  simpa using tendsto_rankFourGeometricAngleLocalIntegral.add
    (tendsto_rankFourGeometricNegativeIntegral_zero.add
      tendsto_rankFourGeometricMiddleIntegral_zero)

theorem rankFourGeometricFullIntegral_eq_moment (index : ℕ) :
    rankFourGeometricFullIntegral index =
      (1 / Real.pi) ^ 2 * (evenWeylGeometricMoment 2 index / 4 ^ index) := by
  unfold rankFourGeometricFullIntegral rankFourGeometricFullIntegrand
    evenWeylGeometricMoment weightedCosineCubeMoment
    weightedCosineCubePowerIntegrand
  rw [show (fun angles : Fin 2 → ℝ =>
      (1 / Real.pi) ^ 2 * (cosineCubeScale angles / 4) ^ index *
        evenWeylAngleWeight 2 angles) =
      fun angles => ((1 / Real.pi) ^ 2 / 4 ^ index) *
        (cosineCubeScale angles ^ index * evenWeylAngleWeight 2 angles) by
    funext angles
    rw [div_pow]
    ring_nf
    rw [one_div_pow]
    have hinv : 1 / ((4 : ℝ) ^ index) = ((4 : ℝ)⁻¹) ^ index := by
      simpa only [one_div] using (inv_pow (4 : ℝ) index).symm
    rw [hinv]]
  rw [integral_const_mul]
  ring

theorem tendsto_rankFourTableauNormalizedIntegralConstant :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 *
        ((heightFourTableauCount index : ℝ) / 4 ^ index))
      atTop (nhds (2 * (∫ coordinates : Fin 2 → ℝ,
        rankFourGeometricLocalLimitIntegrand coordinates))) := by
  have h := rankFourGeometricFullIntegral_limit.const_mul 2
  apply h.congr'
  filter_upwards with index
  rw [rankFourGeometricFullIntegral_eq_moment,
    heightFourTableauCount_eq_normalized_evenWeylMoment]
  field_simp [Real.pi_ne_zero]

end FibonacciRibbonKernel
