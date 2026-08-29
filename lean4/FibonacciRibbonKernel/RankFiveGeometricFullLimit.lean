import FibonacciRibbonKernel.RankFiveGeometricLocalDCT

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFiveGeometricTailRatio : ℝ := 7 / 10

theorem rankFiveGeometricTailRatio_pos :
    0 < rankFiveGeometricTailRatio := by
  unfold rankFiveGeometricTailRatio
  norm_num

theorem rankFiveGeometricTailRatio_lt_one :
    rankFiveGeometricTailRatio < 1 := by
  unfold rankFiveGeometricTailRatio
  norm_num

theorem tendsto_rankFiveGeometricTailPolynomial :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveGeometricTailRatio ^ index)
      atTop (nhds 0) := by
  have hbase := tendsto_pow_const_mul_const_pow_of_abs_lt_one 5
    (by
      rw [abs_of_pos rankFiveGeometricTailRatio_pos]
      exact rankFiveGeometricTailRatio_lt_one)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveGeometricTailRatio ^ index) =
      fun index : ℕ =>
        ((index + 1 : ℝ) ^ 5 *
          rankFiveGeometricTailRatio ^ (index + 1)) *
            rankFiveGeometricTailRatio⁻¹ by
    funext index
    field_simp [rankFiveGeometricTailRatio_pos.ne']
    exact (pow_succ _ _).symm]
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, zero_mul] using
    hshift.mul_const (rankFiveGeometricTailRatio⁻¹)

noncomputable def rankFiveGeometricFullIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (1 / Real.pi) ^ 2 *
    (oddCosineCubeScale angles / 5) ^ index *
    oddWeylAngleWeight 2 angles

noncomputable def rankFiveGeometricLocalProductIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  rankFivePositiveSpectralDomain.indicator
    (rankFiveGeometricFullIntegrand index) angles

noncomputable def rankFiveGeometricTailProductIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  rankFiveTailSpectralDomain.indicator
    (rankFiveGeometricFullIntegrand index) angles

noncomputable def rankFiveGeometricFullIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFiveGeometricFullIntegrand index angles
    ∂cosineCubeProductMeasure 2

noncomputable def rankFiveGeometricTailIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ,
    rankFiveGeometricTailProductIntegrand index angles
    ∂cosineCubeProductMeasure 2

theorem integrable_rankFiveGeometricFullIntegrand (index : ℕ) :
    Integrable (rankFiveGeometricFullIntegrand index)
      (cosineCubeProductMeasure 2) := by
  apply integrable_continuous_cosineCube
  have hpower : Continuous (fun angles : Fin 2 → ℝ =>
      (oddCosineCubeScale angles / 5) ^ index) :=
    ((continuous_oddCosineCubeScale 2).div_const 5).pow index
  unfold rankFiveGeometricFullIntegrand
  exact (continuous_const.mul hpower).mul
      (continuous_oddWeylAngleWeight 2)

theorem integrable_rankFiveGeometricLocalProductIntegrand (index : ℕ) :
    Integrable (rankFiveGeometricLocalProductIntegrand index)
      (cosineCubeProductMeasure 2) := by
  unfold rankFiveGeometricLocalProductIntegrand
  exact (integrable_rankFiveGeometricFullIntegrand index).indicator
    measurableSet_rankFivePositiveSpectralDomain

theorem integrable_rankFiveGeometricTailProductIntegrand (index : ℕ) :
    Integrable (rankFiveGeometricTailProductIntegrand index)
      (cosineCubeProductMeasure 2) := by
  unfold rankFiveGeometricTailProductIntegrand
  exact (integrable_rankFiveGeometricFullIntegrand index).indicator
    measurableSet_rankFiveTailSpectralDomain

theorem rankFiveGeometricFullIntegrand_partition
    (index : ℕ) (angles : Fin 2 → ℝ) :
    rankFiveGeometricFullIntegrand index angles =
      rankFiveGeometricLocalProductIntegrand index angles +
        rankFiveGeometricTailProductIntegrand index angles := by
  by_cases hlocal : angles ∈ rankFivePositiveSpectralDomain
  · have htail : angles ∉ rankFiveTailSpectralDomain := by
      intro htail
      change oddCosineScaleMidpoint 2 ≤ oddCosineCubeScale angles at hlocal
      change oddCosineCubeScale angles < oddCosineScaleMidpoint 2 at htail
      exact (not_lt_of_ge hlocal) htail
    rw [rankFiveGeometricLocalProductIntegrand,
      Set.indicator_of_mem hlocal,
      rankFiveGeometricTailProductIntegrand,
      Set.indicator_of_notMem htail, add_zero]
  · have htail : angles ∈ rankFiveTailSpectralDomain := by
      change ¬ oddCosineScaleMidpoint 2 ≤ oddCosineCubeScale angles at hlocal
      change oddCosineCubeScale angles < oddCosineScaleMidpoint 2
      exact lt_of_not_ge hlocal
    rw [rankFiveGeometricLocalProductIntegrand,
      Set.indicator_of_notMem hlocal,
      rankFiveGeometricTailProductIntegrand,
      Set.indicator_of_mem htail, zero_add]

theorem rankFiveGeometricLocalProductIntegral_eq_angleLocal
    (index : ℕ) :
    (∫ angles : Fin 2 → ℝ,
      rankFiveGeometricLocalProductIntegrand index angles
      ∂cosineCubeProductMeasure 2) =
      rankFiveGeometricAngleLocalIntegral index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin 2 => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube 2 by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube 2) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold rankFiveGeometricAngleLocalIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube 2
  · by_cases hlocal : angles ∈ rankFivePositiveSpectralDomain
    · have hangleLocal : angles ∈ oddAngleLocalDomain 2 := ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        rankFiveGeometricLocalProductIntegrand,
        Set.indicator_of_mem hlocal,
        rankFiveGeometricAngleLocalIntegrand,
        Set.indicator_of_mem hangleLocal]
      rfl
    · rw [Set.indicator_of_mem hcube,
        rankFiveGeometricLocalProductIntegrand,
        Set.indicator_of_notMem hlocal,
        rankFiveGeometricAngleLocalIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      rankFiveGeometricAngleLocalIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem abs_rankFiveGeometricKernel_le_tail
    {index : ℕ} {scale : ℝ} (hscale : |scale| ≤ 7 / 2) :
    |(scale / 5) ^ index| ≤ rankFiveGeometricTailRatio ^ index := by
  rw [abs_pow]
  have hratio : |scale / 5| ≤ rankFiveGeometricTailRatio := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
    unfold rankFiveGeometricTailRatio
    linarith
  exact pow_le_pow_left₀ (abs_nonneg _) hratio index

theorem norm_rankFiveGeometricTailProductIntegrand_le
    (index : ℕ) (angles : Fin 2 → ℝ) :
    ‖rankFiveGeometricTailProductIntegrand index angles‖ ≤
      ((1 / Real.pi) ^ 2 * 4) *
        rankFiveGeometricTailRatio ^ index := by
  by_cases htail : angles ∈ rankFiveTailSpectralDomain
  · rw [rankFiveGeometricTailProductIntegrand,
      Set.indicator_of_mem htail,
      rankFiveGeometricFullIntegrand,
      Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
      abs_of_nonneg (oddWeylAngleWeight_two_nonneg angles)]
    have hkernel := abs_rankFiveGeometricKernel_le_tail (index := index)
      (abs_oddCosineCubeScale_le_midpoint_of_tail htail)
    have hweight := oddWeylAngleWeight_two_le_four angles
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left hkernel (pow_nonneg (by positivity) _))
      hweight (oddWeylAngleWeight_two_nonneg angles)
      (mul_nonneg (pow_nonneg (by positivity) _)
        (pow_nonneg rankFiveGeometricTailRatio_pos.le _))).trans_eq (by ring)
  · rw [rankFiveGeometricTailProductIntegrand,
      Set.indicator_of_notMem htail, norm_zero]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (by positivity) _) (by norm_num))
      (pow_nonneg rankFiveGeometricTailRatio_pos.le _)

theorem norm_rankFiveGeometricTailIntegral_le (index : ℕ) :
    ‖rankFiveGeometricTailIntegral index‖ ≤
      (((1 / Real.pi) ^ 2 * 4) *
        rankFiveGeometricTailRatio ^ index) *
          (cosineCubeProductMeasure 2).real Set.univ := by
  unfold rankFiveGeometricTailIntegral
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall
      (norm_rankFiveGeometricTailProductIntegrand_le index))

theorem tendsto_rankFiveGeometricTailIntegral :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveGeometricTailIntegral index)
      atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) ^ 2 * 4) *
    (cosineCubeProductMeasure 2).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 5 *
        rankFiveGeometricTailRatio ^ index) * constant)
  · intro index
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by positivity) _)]
    have hbound := norm_rankFiveGeometricTailIntegral_le index
    exact (mul_le_mul_of_nonneg_left hbound
      (pow_nonneg (by positivity) _)).trans_eq (by ring)
  · simpa using tendsto_rankFiveGeometricTailPolynomial.mul_const constant

theorem rankFiveGeometricFullIntegral_partition (index : ℕ) :
    rankFiveGeometricFullIntegral index =
      rankFiveGeometricAngleLocalIntegral index +
        rankFiveGeometricTailIntegral index := by
  unfold rankFiveGeometricFullIntegral rankFiveGeometricTailIntegral
  rw [show (fun angles : Fin 2 → ℝ =>
      rankFiveGeometricFullIntegrand index angles) =
      fun angles => rankFiveGeometricLocalProductIntegrand index angles +
        rankFiveGeometricTailProductIntegrand index angles by
    funext angles
    exact rankFiveGeometricFullIntegrand_partition index angles]
  rw [integral_add
    (integrable_rankFiveGeometricLocalProductIntegrand index)
    (integrable_rankFiveGeometricTailProductIntegrand index),
    rankFiveGeometricLocalProductIntegral_eq_angleLocal]

theorem tendsto_rankFiveGeometricFullIntegral :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveGeometricFullIntegral index)
      atTop
      (nhds (∫ coordinates : Fin 2 → ℝ,
        rankFiveGeometricLocalLimitIntegrand coordinates)) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveGeometricFullIntegral index) =
      fun index : ℕ =>
        (index + 1 : ℝ) ^ 5 *
            rankFiveGeometricAngleLocalIntegral index +
          (index + 1 : ℝ) ^ 5 *
            rankFiveGeometricTailIntegral index by
    funext index
    rw [rankFiveGeometricFullIntegral_partition]
    ring]
  simpa using tendsto_rankFiveGeometricAngleLocalIntegral.add
    tendsto_rankFiveGeometricTailIntegral

theorem rankFiveGeometricFullIntegral_eq_weylMoment (index : ℕ) :
    rankFiveGeometricFullIntegral index =
      (1 / Real.pi) ^ 2 *
        (oddWeylGeometricMoment 2 index / 5 ^ index) := by
  unfold rankFiveGeometricFullIntegral rankFiveGeometricFullIntegrand
    oddWeylGeometricMoment weightedCosineCubeMoment
    weightedCosineCubePowerIntegrand
  rw [show (fun angles : Fin 2 → ℝ =>
      (1 / Real.pi) ^ 2 *
        (oddCosineCubeScale angles / 5) ^ index *
          oddWeylAngleWeight 2 angles) =
      fun angles => ((1 / Real.pi) ^ 2 / 5 ^ index) *
        (oddCosineCubeScale angles ^ index *
          oddWeylAngleWeight 2 angles) by
    funext angles
    rw [div_pow]
    ring_nf
    rw [one_div_pow]
    have hinv : 1 / ((5 : ℝ) ^ index) = ((5 : ℝ)⁻¹) ^ index := by
      simpa only [one_div] using (inv_pow (5 : ℝ) index).symm
    rw [hinv]]
  rw [integral_const_mul]
  ring

theorem tendsto_rankFiveTableauNormalizedIntegralConstant :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 *
        ((heightFiveTableauCount index : ℝ) / 5 ^ index))
      atTop
      (nhds (8 * (∫ coordinates : Fin 2 → ℝ,
        rankFiveGeometricLocalLimitIntegrand coordinates))) := by
  have h := tendsto_rankFiveGeometricFullIntegral.const_mul 8
  apply h.congr'
  filter_upwards with index
  rw [rankFiveGeometricFullIntegral_eq_weylMoment,
    heightFiveTableauCount_eq_normalized_oddWeylMoment]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end FibonacciRibbonKernel
