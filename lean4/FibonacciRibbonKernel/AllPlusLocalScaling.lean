import FibonacciRibbonKernel.AllPlusLocalDCT

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped BigOperators

noncomputable def anglePositiveCube (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  Set.univ.pi fun _ : Fin dimension => Set.Ioc (0 : ℝ) Real.pi

noncomputable def anglePositiveLocalDomain
    (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  anglePositiveCube dimension ∩
    {angles | cosineScaleMidpoint dimension ≤ cosineCubeScale angles}

noncomputable def allPlusAngleLocalNormalizedIntegrand
    (dimension index : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  (anglePositiveLocalDomain dimension).indicator
    (fun angles =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        cosineCubeWeight dimension 0 angles)
    angles

noncomputable def allPlusAngleLocalNormalizedIntegral
    (dimension index : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    allPlusAngleLocalNormalizedIntegrand dimension index angles

theorem map_coordinateInverseSqrt_volume
    (dimension index : ℕ) :
    Measure.map
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)))
        (volume : Measure (Fin dimension → ℝ)) =
      ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension) • volume := by
  have hsqrtPos : 0 < Real.sqrt (index + 1 : ℝ) := by positivity
  rw [map_coordinateScalarLinearMap_volume dimension
    (one_div_ne_zero hsqrtPos.ne')]
  congr 2
  rw [one_div, inv_pow, abs_inv, abs_pow,
    abs_of_pos hsqrtPos, inv_inv]

theorem measurableSet_anglePositiveLocalDomain (dimension : ℕ) :
    MeasurableSet (anglePositiveLocalDomain dimension) := by
  unfold anglePositiveLocalDomain anglePositiveCube
  apply (MeasurableSet.univ_pi fun _ => measurableSet_Ioc).inter
  exact measurableSet_Ici.preimage (continuous_cosineCubeScale dimension).measurable

theorem continuous_allPlusAngleCore
    (dimension index : ℕ) :
    Continuous (fun angles : Fin dimension → ℝ =>
      (1 / Real.pi) ^ dimension *
        (fibonacciScaleKernel (cosineCubeScale angles) index /
          (largeScalePreimage (2 * dimension : ℝ) ^ (index + 1) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
        cosineCubeWeight dimension 0 angles) := by
  exact (continuous_const.mul
    (((continuous_fibonacciScaleKernel index).comp
      (continuous_cosineCubeScale dimension)).div_const _)).mul
        (continuous_cosineCubeWeight dimension 0)

theorem stronglyMeasurable_allPlusAngleLocalNormalizedIntegrand
    (dimension index : ℕ) :
    StronglyMeasurable
      (allPlusAngleLocalNormalizedIntegrand dimension index) := by
  unfold allPlusAngleLocalNormalizedIntegrand
  exact ((continuous_allPlusAngleCore dimension index).stronglyMeasurable.indicator
    (measurableSet_anglePositiveLocalDomain dimension))

theorem aestronglyMeasurable_allPlusAngleLocalNormalizedIntegrand
    (dimension index : ℕ) :
    AEStronglyMeasurable
      (allPlusAngleLocalNormalizedIntegrand dimension index) :=
  (stronglyMeasurable_allPlusAngleLocalNormalizedIntegrand
    dimension index).aestronglyMeasurable

theorem coordinateInverseSqrt_apply
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    coordinateScalarLinearMap dimension
        (1 / Real.sqrt (index + 1 : ℝ)) coordinates =
      fun coordinate =>
        coordinates coordinate / Real.sqrt (index + 1 : ℝ) := by
  funext coordinate
  rw [coordinateScalarLinearMap_apply]
  ring

theorem cosineCubeScale_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    cosineCubeScale
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      cosineSumScale coordinates index := by
  rw [coordinateInverseSqrt_apply]
  rfl

theorem cosineCubeWeight_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    cosineCubeWeight dimension 0
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      allPlusScaledWeight dimension index coordinates := by
  rw [coordinateInverseSqrt_apply]
  unfold cosineCubeWeight cosineCoordinateIsPlus
  unfold allPlusScaledWeight cosineFactorWeight
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  simp

theorem anglePositiveCube_inverseSqrt_iff
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates ∈
        anglePositiveCube dimension ↔
      coordinates ∈ positiveScaledCube dimension index := by
  rw [coordinateInverseSqrt_apply]
  constructor
  · intro hangles coordinate _hcoordinate
    have hmem := hangles coordinate (Set.mem_univ coordinate)
    have hsqrtPos : 0 < Real.sqrt (index + 1 : ℝ) := by positivity
    constructor
    · exact (div_pos_iff_of_pos_right hsqrtPos).mp hmem.1
    · exact (div_le_iff₀ hsqrtPos).1 hmem.2
  · intro hcoordinates coordinate _hcoordinate
    have hmem := hcoordinates coordinate (Set.mem_univ coordinate)
    have hsqrtPos : 0 < Real.sqrt (index + 1 : ℝ) := by positivity
    exact ⟨div_pos hmem.1 hsqrtPos,
      (div_le_iff₀ hsqrtPos).2 hmem.2⟩

theorem anglePositiveLocalDomain_inverseSqrt_iff
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates ∈
        anglePositiveLocalDomain dimension ↔
      coordinates ∈ positiveLocalScaledDomain dimension index := by
  unfold anglePositiveLocalDomain positiveLocalScaledDomain
  constructor
  · intro hdomain
    exact ⟨(anglePositiveCube_inverseSqrt_iff dimension index coordinates).1
        hdomain.1,
      by
        have hlocal : cosineScaleMidpoint dimension ≤
            cosineCubeScale
              (coordinateScalarLinearMap dimension
                (1 / Real.sqrt (index + 1 : ℝ)) coordinates) := hdomain.2
        rw [cosineCubeScale_inverseSqrt] at hlocal
        exact hlocal⟩
  · intro hdomain
    exact ⟨(anglePositiveCube_inverseSqrt_iff dimension index coordinates).2
        hdomain.1,
      by
        have hlocal : cosineScaleMidpoint dimension ≤
            cosineSumScale coordinates index := hdomain.2
        rw [← cosineCubeScale_inverseSqrt] at hlocal
        exact hlocal⟩

theorem allPlusAngleLocalNormalizedIntegrand_inverseSqrt
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    allPlusAngleLocalNormalizedIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates) =
      allPlusLocalRescaledIntegrand dimension index coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [allPlusAngleLocalNormalizedIntegrand,
      Set.indicator_of_mem
        ((anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).2 hdomain),
      allPlusLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      cosineCubeScale_inverseSqrt, cosineCubeWeight_inverseSqrt]
    unfold normalizedFibonacciCosineKernel
    rfl
  · rw [allPlusAngleLocalNormalizedIntegrand,
      Set.indicator_of_notMem
        (mt (anglePositiveLocalDomain_inverseSqrt_iff dimension index coordinates).1 hdomain),
      allPlusLocalRescaledIntegrand, Set.indicator_of_notMem hdomain]

theorem allPlusLocalScalingIntegral_identity
    (dimension index : ℕ) :
    Real.sqrt (index + 1 : ℝ) ^ dimension *
        allPlusAngleLocalNormalizedIntegral dimension index =
      ∫ coordinates : Fin dimension → ℝ,
        allPlusLocalRescaledIntegrand dimension index coordinates := by
  let scaleMap := coordinateScalarLinearMap dimension
    (1 / Real.sqrt (index + 1 : ℝ))
  let integrand := allPlusAngleLocalNormalizedIntegrand dimension index
  have hmap :
      (∫ angles, integrand angles
        ∂Measure.map scaleMap (volume : Measure (Fin dimension → ℝ))) =
        ∫ coordinates, integrand (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap dimension _).aemeasurable
      (stronglyMeasurable_allPlusAngleLocalNormalizedIntegrand
        dimension index).aestronglyMeasurable
  rw [map_coordinateInverseSqrt_volume] at hmap
  rw [integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (Real.sqrt (index + 1 : ℝ) ^ dimension)).toReal =
        Real.sqrt (index + 1 : ℝ) ^ dimension := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold allPlusAngleLocalNormalizedIntegral
  dsimp only [integrand, scaleMap] at hmap
  rw [show (fun coordinates : Fin dimension → ℝ =>
      allPlusAngleLocalNormalizedIntegrand dimension index
        (coordinateScalarLinearMap dimension
          (1 / Real.sqrt (index + 1 : ℝ)) coordinates)) =
      allPlusLocalRescaledIntegrand dimension index by
    funext coordinates
    exact allPlusAngleLocalNormalizedIntegrand_inverseSqrt
      dimension index coordinates] at hmap
  exact hmap

end FibonacciRibbonKernel
