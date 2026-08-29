import FibonacciRibbonKernel.OddWeylLocalPointwise

namespace FibonacciRibbonKernel

open MeasureTheory Set

noncomputable def oddAngleLocalDomain
    (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  anglePositiveCube dimension ∩
    {angles | oddCosineScaleMidpoint dimension ≤ oddCosineCubeScale angles}

noncomputable def oddWeylAngleLocalNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (oddAngleLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (oddCosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
        oddWeylAngleWeight dimension angles)
    angles

noncomputable def oddWeylAngleLocalNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    oddWeylAngleLocalNormalizedIntegrand dimension index angles

theorem measurableSet_oddAngleLocalDomain (dimension : ℕ) :
    MeasurableSet (oddAngleLocalDomain dimension) := by
  unfold oddAngleLocalDomain oddCosineCubeScale
  apply (MeasurableSet.univ_pi fun _ : Fin dimension => measurableSet_Ioc).inter
  exact measurableSet_Ici.preimage
    (continuous_const.add (continuous_cosineCubeScale dimension)).measurable

theorem continuous_oddWeylAngleLocalCore
    (dimension index : ℕ) :
    Continuous (fun angles : Fin dimension → ℝ =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (oddCosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension + 1 : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
        oddWeylAngleWeight dimension angles) := by
  exact (continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_const.add (continuous_cosineCubeScale dimension))).div_const _)).mul
        (continuous_oddWeylAngleWeight dimension)

theorem stronglyMeasurable_oddWeylAngleLocalNormalizedIntegrand
    (dimension index : ℕ) :
    StronglyMeasurable
      (oddWeylAngleLocalNormalizedIntegrand dimension index) := by
  unfold oddWeylAngleLocalNormalizedIntegrand
  exact (continuous_oddWeylAngleLocalCore dimension index).stronglyMeasurable.indicator
    (measurableSet_oddAngleLocalDomain dimension)

theorem oddCosineCubeScale_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    oddCosineCubeScale
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      oddCosineSumScale coordinates index := by
  unfold oddCosineCubeScale oddCosineSumScale
  rw [cosineCubeScale_inverseSqrt]

theorem oddAngleLocalDomain_inverseSqrt_iff
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates ∈
        oddAngleLocalDomain dimension ↔
      coordinates ∈ positiveOddLocalScaledDomain dimension index := by
  unfold oddAngleLocalDomain positiveOddLocalScaledDomain
  constructor
  · intro hdomain
    exact ⟨(anglePositiveCube_inverseSqrt_iff dimension index coordinates).1
        hdomain.1,
      by
        have hlocal : oddCosineScaleMidpoint dimension ≤
            oddCosineCubeScale
              (coordinateScalarLinearMap dimension
                (1 / Real.sqrt (index + 1 : ℝ)) coordinates) := hdomain.2
        rw [oddCosineCubeScale_inverseSqrt] at hlocal
        exact hlocal⟩
  · intro hdomain
    exact ⟨(anglePositiveCube_inverseSqrt_iff dimension index coordinates).2
        hdomain.1,
      by
        have hlocal : oddCosineScaleMidpoint dimension ≤
            oddCosineSumScale coordinates index := hdomain.2
        rw [← oddCosineCubeScale_inverseSqrt] at hlocal
        exact hlocal⟩

theorem oddWeylAngleWeight_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    oddWeylAngleWeight dimension
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      oddScaledWeylWeight dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension ^ 2) := by
  have hscale := oddScaledWeylWeight_eq dimension index coordinates
  have hnonzero : (index + 1 : ℝ) ^ (dimension ^ 2) ≠ 0 := by positivity
  apply (eq_div_iff hnonzero).2
  rw [hscale]
  ring

theorem oddWeylAngleLocalNormalizedIntegrand_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    oddWeylAngleLocalNormalizedIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      oddWeylLocalRescaledIntegrand dimension index coordinates /
        (index + 1 : ℝ) ^ (dimension ^ 2) := by
  by_cases hdomain : coordinates ∈ positiveOddLocalScaledDomain dimension index
  · rw [oddWeylAngleLocalNormalizedIntegrand,
      Set.indicator_of_mem
        ((oddAngleLocalDomain_inverseSqrt_iff dimension index coordinates).2 hdomain),
      oddWeylLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      oddCosineCubeScale_inverseSqrt, oddWeylAngleWeight_inverseSqrt]
    unfold normalizedOddFibonacciKernel
    ring
  · rw [oddWeylAngleLocalNormalizedIntegrand,
      Set.indicator_of_notMem
        (mt (oddAngleLocalDomain_inverseSqrt_iff dimension index coordinates).1 hdomain),
      oddWeylLocalRescaledIntegrand, Set.indicator_of_notMem hdomain,
      zero_div]

theorem oddWeylLocalScalingIntegral_identity
    (dimension index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ dimension *
        (index + 1 : ℝ) ^ (dimension ^ 2) *
          oddWeylAngleLocalNormalizedIntegral dimension index =
      ∫ coordinates : Fin dimension → ℝ,
        oddWeylLocalRescaledIntegrand dimension index coordinates := by
  let scaleMap := coordinateScalarLinearMap dimension
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := oddWeylAngleLocalNormalizedIntegrand dimension index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension _).aemeasurable
      (stronglyMeasurable_oddWeylAngleLocalNormalizedIntegrand
        dimension index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume, integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ dimension := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold oddWeylAngleLocalNormalizedIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      oddWeylAngleLocalNormalizedIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      fun coordinates =>
        oddWeylLocalRescaledIntegrand dimension index coordinates /
          (index + 1 : ℝ) ^ (dimension ^ 2) by
    funext coordinates
    exact oddWeylAngleLocalNormalizedIntegrand_inverseSqrt
      dimension index coordinates] at hmap
  rw [integral_div] at hmap
  have hnonzero : (index + 1 : ℝ) ^ (dimension ^ 2) ≠ 0 := by positivity
  field_simp [hnonzero] at hmap ⊢
  exact hmap

theorem rankFive_oddWeylLocalScalingIntegral_identity (index : ℕ) :
    (index + 1 : ℝ) ^ 5 *
        oddWeylAngleLocalNormalizedIntegral 2 index =
      ∫ coordinates : Fin 2 → ℝ,
        oddWeylLocalRescaledIntegrand 2 index coordinates := by
  have h := oddWeylLocalScalingIntegral_identity 2 index
  have hsqrt : Real.sqrt (index + 1 : ℝ) ^ 2 = index + 1 :=
    Real.sq_sqrt (by positivity)
  norm_num at h ⊢
  rw [hsqrt] at h
  convert h using 1
  ring

end FibonacciRibbonKernel
