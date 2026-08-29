import FibonacciRibbonKernel.RankFiveTailIntegral

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

theorem measurableSet_rankFivePositiveSpectralDomain :
    MeasurableSet rankFivePositiveSpectralDomain := by
  unfold rankFivePositiveSpectralDomain
  exact measurableSet_Ici.preimage
    (continuous_const.add (continuous_cosineCubeScale 2)).measurable

theorem measurableSet_rankFiveTailSpectralDomain :
    MeasurableSet rankFiveTailSpectralDomain := by
  unfold rankFiveTailSpectralDomain
  exact measurableSet_Iio.preimage
    (continuous_const.add (continuous_cosineCubeScale 2)).measurable

theorem integrable_rankFiveFullNormalizedIntegrand (index : ℕ) :
    Integrable (rankFiveFullNormalizedIntegrand index)
      (cosineCubeProductMeasure 2) := by
  apply integrable_continuous_cosineCube
  unfold rankFiveFullNormalizedIntegrand oddCosineCubeScale
  exact (continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_const.add (continuous_cosineCubeScale 2))).div_const _)).mul
        (continuous_oddWeylAngleWeight 2)

theorem integrable_rankFiveLocalProductIntegrand (index : ℕ) :
    Integrable (rankFiveLocalProductIntegrand index)
      (cosineCubeProductMeasure 2) := by
  unfold rankFiveLocalProductIntegrand
  exact (integrable_rankFiveFullNormalizedIntegrand index).indicator
    measurableSet_rankFivePositiveSpectralDomain

theorem integrable_rankFiveTailProductIntegrand (index : ℕ) :
    Integrable (rankFiveTailProductIntegrand index)
      (cosineCubeProductMeasure 2) := by
  unfold rankFiveTailProductIntegrand
  exact (integrable_rankFiveFullNormalizedIntegrand index).indicator
    measurableSet_rankFiveTailSpectralDomain

theorem rankFiveFullIntegrand_partition
    (index : ℕ) (angles : Fin 2 → ℝ) :
    rankFiveFullNormalizedIntegrand index angles =
      rankFiveLocalProductIntegrand index angles +
        rankFiveTailProductIntegrand index angles := by
  by_cases hlocal : angles ∈ rankFivePositiveSpectralDomain
  · have htail : angles ∉ rankFiveTailSpectralDomain := by
      intro htail
      change oddCosineScaleMidpoint 2 ≤ oddCosineCubeScale angles at hlocal
      change oddCosineCubeScale angles < oddCosineScaleMidpoint 2 at htail
      exact (not_lt_of_ge hlocal) htail
    rw [rankFiveLocalProductIntegrand, Set.indicator_of_mem hlocal,
      rankFiveTailProductIntegrand, Set.indicator_of_notMem htail, add_zero]
  · have htail : angles ∈ rankFiveTailSpectralDomain := by
      change ¬ oddCosineScaleMidpoint 2 ≤ oddCosineCubeScale angles at hlocal
      change oddCosineCubeScale angles < oddCosineScaleMidpoint 2
      exact lt_of_not_ge hlocal
    rw [rankFiveLocalProductIntegrand, Set.indicator_of_notMem hlocal,
      rankFiveTailProductIntegrand, Set.indicator_of_mem htail, zero_add]

theorem rankFiveLocalProductIntegral_eq_angleLocal (index : ℕ) :
    (∫ angles : Fin 2 → ℝ,
      rankFiveLocalProductIntegrand index angles
      ∂cosineCubeProductMeasure 2) =
      oddWeylAngleLocalNormalizedIntegral 2 index := by
  rw [cosineCubeProductMeasure_eq_restrict]
  rw [show (Set.univ.pi fun _ : Fin 2 => Set.Ioc (0 : ℝ) Real.pi) =
      anglePositiveCube 2 by rfl]
  rw [← integral_indicator
    (show MeasurableSet (anglePositiveCube 2) by
      unfold anglePositiveCube
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  unfold oddWeylAngleLocalNormalizedIntegral
  apply integral_congr_ae
  filter_upwards with angles
  by_cases hcube : angles ∈ anglePositiveCube 2
  · by_cases hlocal : angles ∈ rankFivePositiveSpectralDomain
    · have hangleLocal : angles ∈ oddAngleLocalDomain 2 := ⟨hcube, hlocal⟩
      rw [Set.indicator_of_mem hcube,
        rankFiveLocalProductIntegrand, Set.indicator_of_mem hlocal,
        oddWeylAngleLocalNormalizedIntegrand,
        Set.indicator_of_mem hangleLocal]
      unfold rankFiveFullNormalizedIntegrand
      norm_num
    · rw [Set.indicator_of_mem hcube,
        rankFiveLocalProductIntegrand, Set.indicator_of_notMem hlocal,
        oddWeylAngleLocalNormalizedIntegrand,
        Set.indicator_of_notMem (fun h => hlocal h.2)]
  · rw [Set.indicator_of_notMem hcube,
      oddWeylAngleLocalNormalizedIntegrand,
      Set.indicator_of_notMem (fun h => hcube h.1)]

theorem rankFiveFullNormalizedIntegral_partition (index : ℕ) :
    rankFiveFullNormalizedIntegral index =
      oddWeylAngleLocalNormalizedIntegral 2 index +
        rankFiveTailNormalizedIntegral index := by
  unfold rankFiveFullNormalizedIntegral rankFiveTailNormalizedIntegral
  rw [show (fun angles : Fin 2 → ℝ =>
      rankFiveFullNormalizedIntegrand index angles) =
      fun angles => rankFiveLocalProductIntegrand index angles +
        rankFiveTailProductIntegrand index angles by
    funext angles
    exact rankFiveFullIntegrand_partition index angles]
  rw [integral_add (integrable_rankFiveLocalProductIntegrand index)
    (integrable_rankFiveTailProductIntegrand index),
    rankFiveLocalProductIntegral_eq_angleLocal]

theorem rankFiveFullNormalizedIntegral_eq_weylMoment (index : ℕ) :
    rankFiveFullNormalizedIntegral index =
      (1 / Real.pi) ^ 2 *
        (oddWeylFibonacciMoment 2 index /
          (largeScalePreimage 5 ^ (index + 1) / Real.sqrt 21)) := by
  unfold rankFiveFullNormalizedIntegral rankFiveFullNormalizedIntegrand
    oddWeylFibonacciMoment weightedCosineCubeFibonacciMoment
    weightedCosineCubeFibonacciIntegrand
  rw [show (fun angles : Fin 2 → ℝ =>
      (1 / Real.pi) ^ 2 *
          (fibonacciScaleKernel (oddCosineCubeScale angles) index /
            (largeScalePreimage 5 ^ (index + 1) / Real.sqrt 21)) *
        oddWeylAngleWeight 2 angles) =
      fun angles => ((1 / Real.pi) ^ 2 /
        (largeScalePreimage 5 ^ (index + 1) / Real.sqrt 21)) *
          (fibonacciScaleKernel (oddCosineCubeScale angles) index *
            oddWeylAngleWeight 2 angles) by
    funext angles
    ring]
  rw [integral_const_mul]
  ring

theorem tendsto_rankFiveFullNormalizedIntegral :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveFullNormalizedIntegral index)
      atTop
      (nhds (∫ coordinates : Fin 2 → ℝ,
        oddWeylLocalLimitIntegrand 2 coordinates)) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveFullNormalizedIntegral index) =
      fun index : ℕ =>
        (index + 1 : ℝ) ^ 5 *
            oddWeylAngleLocalNormalizedIntegral 2 index +
          (index + 1 : ℝ) ^ 5 *
            rankFiveTailNormalizedIntegral index by
    funext index
    rw [rankFiveFullNormalizedIntegral_partition]
    ring]
  simpa using tendsto_rankFiveOddWeylAngleLocalNormalizedIntegral.add
    tendsto_rankFiveTailNormalizedIntegral

theorem rankFiveFullNormalizedIntegral_eq_ribbonCount (index : ℕ) :
    rankFiveFullNormalizedIntegral index =
      (ribbonCount 4 index : ℝ) /
        (8 * (largeScalePreimage 5 ^ (index + 1) / Real.sqrt 21)) := by
  rw [rankFiveFullNormalizedIntegral_eq_weylMoment,
    heightFiveRibbonCount_eq_normalized_oddWeylFibonacciMoment]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

theorem tendsto_rankFiveRibbonNormalizedIntegralConstant :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 *
        ((ribbonCount 4 index : ℝ) /
          (largeScalePreimage 5 ^ (index + 1) / Real.sqrt 21)))
      atTop
      (nhds (8 * (∫ coordinates : Fin 2 → ℝ,
        oddWeylLocalLimitIntegrand 2 coordinates))) := by
  have h := tendsto_rankFiveFullNormalizedIntegral.const_mul 8
  apply h.congr'
  filter_upwards with index
  rw [rankFiveFullNormalizedIntegral_eq_ribbonCount]
  ring

end FibonacciRibbonKernel
