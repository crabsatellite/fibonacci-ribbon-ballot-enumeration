import FibonacciRibbonKernel.FibonacciCosineKernelPointwise
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace FibonacciRibbonKernel

open scoped BigOperators

theorem scaledCoordinate_abs_le_pi
    {dimension index : ℕ} (coordinates : Fin dimension → ℝ)
    (hcoordinates : ∀ coordinate,
      |coordinates coordinate| ≤ Real.pi * Real.sqrt (index + 1 : ℝ))
    (coordinate : Fin dimension) :
    |coordinates coordinate / Real.sqrt (index + 1 : ℝ)| ≤ Real.pi := by
  have hsqrtPos : 0 < Real.sqrt (index + 1 : ℝ) := by positivity
  rw [abs_div, abs_of_pos hsqrtPos]
  exact (div_le_iff₀ hsqrtPos).2 (hcoordinates coordinate)

theorem cosineSumScale_le_quadratic
    {dimension index : ℕ} (coordinates : Fin dimension → ℝ)
    (hcoordinates : ∀ coordinate,
      |coordinates coordinate| ≤ Real.pi * Real.sqrt (index + 1 : ℝ)) :
    cosineSumScale coordinates index ≤
      (2 * dimension : ℝ) -
        (4 / (Real.pi ^ 2 * (index + 1 : ℝ))) *
          ∑ coordinate, coordinates coordinate ^ 2 := by
  have hsqrtPos : 0 < Real.sqrt (index + 1 : ℝ) := by positivity
  have hsqrtSq : Real.sqrt (index + 1 : ℝ) ^ 2 = (index + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcoordinate : ∀ coordinate : Fin dimension,
      Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) ≤
        1 - 2 / Real.pi ^ 2 *
          (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) ^ 2 := by
    intro coordinate
    exact Real.cos_le_one_sub_mul_cos_sq
      (scaledCoordinate_abs_le_pi coordinates hcoordinates coordinate)
  have hsum :
      (∑ coordinate : Fin dimension,
        Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ))) ≤
      ∑ coordinate : Fin dimension,
        (1 - 2 / Real.pi ^ 2 *
          (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) ^ 2) := by
    apply Finset.sum_le_sum
    intro coordinate _hcoordinate
    exact hcoordinate coordinate
  unfold cosineSumScale
  calc
    2 * ∑ coordinate,
          Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) ≤
        2 * ∑ coordinate,
          (1 - 2 / Real.pi ^ 2 *
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (2 * dimension : ℝ) -
        (4 / (Real.pi ^ 2 * (index + 1 : ℝ))) *
          ∑ coordinate, coordinates coordinate ^ 2 := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.mul_sum]
      field_simp [hpi, hsqrtPos.ne']
      rw [hsqrtSq]
      rw [mul_sub]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      ring

end FibonacciRibbonKernel
