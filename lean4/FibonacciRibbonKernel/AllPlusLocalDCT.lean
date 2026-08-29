import FibonacciRibbonKernel.AllPlusLocalRescaled
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

theorem tendsto_integral_allPlusLocalRescaledIntegrand
    (dimension : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    Tendsto
      (fun index => ∫ coordinates,
        allPlusLocalRescaledIntegrand dimension index coordinates)
      atTop
      (nhds (∫ coordinates, allPlusLocalLimitIntegrand dimension coordinates)) := by
  exact tendsto_integral_of_dominated_convergence
    (allPlusLocalDominating dimension)
    (fun index =>
      aestronglyMeasurable_allPlusLocalRescaledIntegrand
        dimension index hdimension)
    (integrable_allPlusLocalDominating dimension hdimension)
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_allPlusLocalRescaledIntegrand_le hdimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_allPlusLocalRescaledIntegrand hdimension coordinates)

noncomputable def allPlusLimitCoordinateFactor
    (dimension : ℕ) (value : ℝ) : ℝ :=
  Set.Ioi (0 : ℝ) |>.indicator
    (fun value =>
      Real.exp (-(1 / Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) *
        value ^ 2)) value

theorem allPlusLocalLimitIntegrand_eq_product
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    allPlusLocalLimitIntegrand dimension coordinates =
      (2 / Real.pi) ^ dimension *
        ∏ coordinate,
          allPlusLimitCoordinateFactor dimension (coordinates coordinate) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · rw [allPlusLocalLimitIntegrand, Set.indicator_of_mem horthant]
    unfold allPlusLimitCoordinateFactor
    have hpositive : ∀ coordinate : Fin dimension,
        coordinates coordinate ∈ Set.Ioi (0 : ℝ) := by
      intro coordinate
      exact horthant coordinate (Set.mem_univ coordinate)
    simp_rw [Set.indicator_of_mem (hpositive _)]
    rw [← Real.exp_sum]
    congr 2
    rw [div_eq_mul_inv, neg_mul, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro coordinate _hcoordinate
    rw [one_div]
    ring
  · rw [allPlusLocalLimitIntegrand, Set.indicator_of_notMem horthant]
    have hnot : ∃ coordinate : Fin dimension,
        coordinates coordinate ∉ Set.Ioi (0 : ℝ) := by
      by_contra hnone
      push Not at hnone
      apply horthant
      unfold positiveOrthant
      intro coordinate _hcoordinate
      exact hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have hproductZero :
        (∏ current : Fin dimension,
          allPlusLimitCoordinateFactor dimension (coordinates current)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
      unfold allPlusLimitCoordinateFactor
      rw [Set.indicator_of_notMem hcoordinate]
    rw [hproductZero, mul_zero]

theorem integral_allPlusLimitCoordinateFactor
    (dimension : ℕ) :
    (∫ value : ℝ, allPlusLimitCoordinateFactor dimension value) =
      Real.sqrt (Real.pi *
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) / 2 := by
  unfold allPlusLimitCoordinateFactor
  rw [integral_indicator measurableSet_Ioi]
  rw [integral_gaussian_Ioi]
  congr 1
  by_cases hrootZero : Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) = 0
  · rw [hrootZero]
    simp
  · field_simp [hrootZero]

theorem integral_allPlusLocalLimitIntegrand
    (dimension : ℕ) :
    (∫ coordinates : Fin dimension → ℝ,
      allPlusLocalLimitIntegrand dimension coordinates) =
      ((2 / Real.pi) *
        (Real.sqrt (Real.pi *
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) / 2)) ^ dimension := by
  rw [show (fun coordinates : Fin dimension → ℝ =>
      allPlusLocalLimitIntegrand dimension coordinates) =
      fun coordinates => (2 / Real.pi) ^ dimension *
        ∏ coordinate,
          allPlusLimitCoordinateFactor dimension (coordinates coordinate) by
    funext coordinates
    exact allPlusLocalLimitIntegrand_eq_product dimension coordinates]
  rw [integral_const_mul]
  rw [volume_pi]
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  simp_rw [integral_allPlusLimitCoordinateFactor]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow]

end FibonacciRibbonKernel
