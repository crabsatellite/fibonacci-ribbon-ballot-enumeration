import FibonacciRibbonKernel.RankFiveGeometricCalibration

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped BigOperators

noncomputable def rankFiveGaussianTransportScale : ℝ :=
  Real.sqrt (5 / Real.sqrt (21 : ℝ))

theorem rankFiveGaussianTransportScale_pos :
    0 < rankFiveGaussianTransportScale := by
  unfold rankFiveGaussianTransportScale
  positivity

theorem rankFiveGaussianTransportScale_sq :
    rankFiveGaussianTransportScale ^ 2 =
      5 / Real.sqrt (21 : ℝ) := by
  unfold rankFiveGaussianTransportScale
  exact Real.sq_sqrt (by positivity)

theorem measurableSet_positiveOrthant (dimension : ℕ) :
    MeasurableSet (@positiveOrthant dimension) := by
  unfold positiveOrthant
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi

theorem continuous_quadraticVandermondeWeight (dimension : ℕ) :
    Continuous (quadraticVandermondeWeight dimension) := by
  unfold quadraticVandermondeWeight
  apply continuous_finsetProd
  intro upper _hupper
  apply continuous_finsetProd
  intro lower _hlower
  fun_prop

theorem continuous_oddLimitWeylWeight (dimension : ℕ) :
    Continuous (oddLimitWeylWeight dimension) := by
  unfold oddLimitWeylWeight
  apply (continuous_quadraticVandermondeWeight dimension).mul
  apply continuous_finsetProd
  intro coordinate _hcoordinate
  fun_prop

theorem stronglyMeasurable_rankFiveGeometricLocalLimitIntegrand :
    StronglyMeasurable rankFiveGeometricLocalLimitIntegrand := by
  unfold rankFiveGeometricLocalLimitIntegrand
  have hsquares : Continuous (fun coordinates : Fin 2 → ℝ =>
      ∑ coordinate, coordinates coordinate ^ 2) := by
    fun_prop
  have hexponent : Continuous (fun coordinates : Fin 2 → ℝ =>
      (-∑ coordinate, coordinates coordinate ^ 2) / 5) :=
    hsquares.neg.div_const 5
  have hexponential : Continuous (fun coordinates : Fin 2 → ℝ =>
      Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) / 5)) :=
    Real.continuous_exp.comp hexponent
  have hcore : Continuous (fun coordinates : Fin 2 → ℝ =>
      (1 / Real.pi) ^ 2 *
        Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) / 5) *
        oddLimitWeylWeight 2 coordinates) := by
    exact (continuous_const.mul hexponential).mul
      (continuous_oddLimitWeylWeight 2)
  exact hcore.stronglyMeasurable.indicator (measurableSet_positiveOrthant 2)

theorem oddLimitWeylWeight_two_formula
    (coordinates : Fin 2 → ℝ) :
    oddLimitWeylWeight 2 coordinates =
      ((coordinates 0 ^ 2 - coordinates 1 ^ 2) / 2) ^ 2 *
        (coordinates 0 ^ 2 * coordinates 1 ^ 2) := by
  unfold oddLimitWeylWeight quadraticVandermondeWeight
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]
  have hzero : Finset.Iio (0 : Fin 2) = ∅ := by decide
  have hone : Finset.Iio (1 : Fin 2) = {0} := by decide
  rw [hzero, hone]
  simp only [Finset.prod_empty, Finset.prod_singleton, one_mul]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]

theorem oddLimitWeylWeight_two_scalar
    (scalar : ℝ) (coordinates : Fin 2 → ℝ) :
    oddLimitWeylWeight 2
        (coordinateScalarLinearMap 2 scalar coordinates) =
      scalar ^ 8 * oddLimitWeylWeight 2 coordinates := by
  rw [oddLimitWeylWeight_two_formula,
    oddLimitWeylWeight_two_formula]
  simp only [coordinateScalarLinearMap_apply]
  ring

theorem sum_sq_coordinateScalar_two
    (scalar : ℝ) (coordinates : Fin 2 → ℝ) :
    (∑ coordinate,
      (coordinateScalarLinearMap 2 scalar coordinates coordinate) ^ 2) =
      scalar ^ 2 * ∑ coordinate, coordinates coordinate ^ 2 := by
  rw [show (∑ coordinate : Fin 2,
      (coordinateScalarLinearMap 2 scalar coordinates coordinate) ^ 2) =
      (scalar * coordinates 0) ^ 2 + (scalar * coordinates 1) ^ 2 by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp [coordinateScalarLinearMap_apply]]
  rw [show (∑ coordinate : Fin 2, coordinates coordinate ^ 2) =
      coordinates 0 ^ 2 + coordinates 1 ^ 2 by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  ring

theorem mem_positiveOrthant_coordinateScalar_iff
    {dimension : ℕ} {scalar : ℝ} (hscalar : 0 < scalar)
    (coordinates : Fin dimension → ℝ) :
    coordinateScalarLinearMap dimension scalar coordinates ∈ positiveOrthant ↔
      coordinates ∈ positiveOrthant := by
  constructor
  · intro hscaled coordinate _hcoordinate
    have h := hscaled coordinate (Set.mem_univ coordinate)
    rw [coordinateScalarLinearMap_apply] at h
    change 0 < scalar * coordinates coordinate at h
    exact pos_of_mul_pos_right h hscalar.le
  · intro hcoordinates coordinate _hcoordinate
    rw [coordinateScalarLinearMap_apply]
    exact mul_pos hscalar
      (hcoordinates coordinate (Set.mem_univ coordinate))

theorem rankFiveGeometricLimitIntegrand_transport
    (coordinates : Fin 2 → ℝ) :
    rankFiveGeometricLocalLimitIntegrand
        (coordinateScalarLinearMap 2
          rankFiveGaussianTransportScale coordinates) =
      rankFiveGaussianTransportScale ^ 8 *
        oddWeylLocalLimitIntegrand 2 coordinates := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hscaled :=
      (mem_positiveOrthant_coordinateScalar_iff
        rankFiveGaussianTransportScale_pos coordinates).2 horthant
    rw [rankFiveGeometricLocalLimitIntegrand,
      Set.indicator_of_mem hscaled,
      oddWeylLocalLimitIntegrand,
      Set.indicator_of_mem horthant,
      oddLimitWeylWeight_two_scalar,
      sum_sq_coordinateScalar_two]
    rw [show Real.sqrt ((2 * (2 : ℕ) + 1 : ℝ) ^ 2 - 4) =
        Real.sqrt (21 : ℝ) by norm_num]
    have hsqrt21 : Real.sqrt (21 : ℝ) ≠ 0 := by positivity
    have hexponent :
        (-(rankFiveGaussianTransportScale ^ 2 *
            ∑ coordinate, coordinates coordinate ^ 2)) / 5 =
          (-∑ coordinate, coordinates coordinate ^ 2) /
            Real.sqrt (21 : ℝ) := by
      rw [rankFiveGaussianTransportScale_sq]
      field_simp [hsqrt21]
    rw [hexponent]
    ring
  · have hscaled :
        coordinateScalarLinearMap 2 rankFiveGaussianTransportScale coordinates ∉
          positiveOrthant :=
      mt (mem_positiveOrthant_coordinateScalar_iff
        rankFiveGaussianTransportScale_pos coordinates).1 horthant
    rw [rankFiveGeometricLocalLimitIntegrand,
      Set.indicator_of_notMem hscaled,
      oddWeylLocalLimitIntegrand,
      Set.indicator_of_notMem horthant, mul_zero]

theorem rankFiveFibonacciLimitIntegral_eq_scaled_geometric :
    (∫ coordinates : Fin 2 → ℝ,
      oddWeylLocalLimitIntegrand 2 coordinates) =
      (Real.sqrt (21 : ℝ) / 5) ^ 5 *
        ∫ coordinates : Fin 2 → ℝ,
          rankFiveGeometricLocalLimitIntegrand coordinates := by
  let scalar := rankFiveGaussianTransportScale
  let scaleMap := coordinateScalarLinearMap 2 scalar
  let geometric := rankFiveGeometricLocalLimitIntegrand
  have hmap :
      (∫ coordinates, geometric coordinates
        ∂Measure.map scaleMap (volume : Measure (Fin 2 → ℝ))) =
        ∫ coordinates, geometric (scaleMap coordinates) :=
    MeasureTheory.integral_map
      (measurable_coordinateScalarLinearMap 2 scalar).aemeasurable
      stronglyMeasurable_rankFiveGeometricLocalLimitIntegrand.aestronglyMeasurable
  rw [map_coordinateScalarLinearMap_volume 2
    rankFiveGaussianTransportScale_pos.ne', integral_smul_measure] at hmap
  have htoReal :
      (ENNReal.ofReal (|scalar ^ 2|⁻¹)).toReal = (scalar ^ 2)⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    · rw [abs_of_pos (pow_pos rankFiveGaussianTransportScale_pos 2)]
    · positivity
  rw [htoReal, smul_eq_mul] at hmap
  dsimp only [geometric, scaleMap, scalar] at hmap
  rw [show (fun coordinates : Fin 2 → ℝ =>
      rankFiveGeometricLocalLimitIntegrand
        (coordinateScalarLinearMap 2
          rankFiveGaussianTransportScale coordinates)) =
      fun coordinates => rankFiveGaussianTransportScale ^ 8 *
        oddWeylLocalLimitIntegrand 2 coordinates by
    funext coordinates
    exact rankFiveGeometricLimitIntegrand_transport coordinates,
    integral_const_mul] at hmap
  have hscalar : rankFiveGaussianTransportScale ≠ 0 :=
    rankFiveGaussianTransportScale_pos.ne'
  have hsqrt21 : Real.sqrt (21 : ℝ) ≠ 0 := by positivity
  have hpower :
      (Real.sqrt (21 : ℝ) / 5) ^ 5 =
        (rankFiveGaussianTransportScale ^ 10)⁻¹ := by
    rw [show rankFiveGaussianTransportScale ^ 10 =
        (rankFiveGaussianTransportScale ^ 2) ^ 5 by ring,
      rankFiveGaussianTransportScale_sq, div_pow, ← inv_pow, inv_div]
    rw [div_pow]
  rw [hpower]
  field_simp [hscalar] at hmap ⊢
  nlinarith

end FibonacciRibbonKernel
