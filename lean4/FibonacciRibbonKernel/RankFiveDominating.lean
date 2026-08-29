import FibonacciRibbonKernel.RankFiveWeylBound
import FibonacciRibbonKernel.MehtaGaussianDomination

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def rankFiveGaussianCoefficient : ℝ :=
  4 / (Real.pi ^ 2 * Real.sqrt (21 : ℝ))

noncomputable def rankFiveCoordinateDominating (value : ℝ) : ℝ :=
  (1 + value ^ 2) ^ 4 *
    Real.exp (-rankFiveGaussianCoefficient * value ^ 2)

noncomputable def rankFiveLocalDominating
    (coordinates : Fin 2 → ℝ) : ℝ :=
  ((1 / Real.pi) ^ 2 *
    (Real.sqrt (21 : ℝ) /
      Real.sqrt (oddCosineScaleMidpoint 2 ^ 2 - 4))) *
    ∏ coordinate, rankFiveCoordinateDominating (coordinates coordinate)

theorem rankFiveGaussianCoefficient_pos :
    0 < rankFiveGaussianCoefficient := by
  unfold rankFiveGaussianCoefficient
  positivity

theorem rankFiveWeylPolynomial_le_separable
    (coordinates : Fin 2 → ℝ) :
    rankFiveWeylPolynomial coordinates ≤
      (1 + coordinates 0 ^ 2) ^ 4 *
        (1 + coordinates 1 ^ 2) ^ 4 := by
  let left := coordinates 0 ^ 2
  let right := coordinates 1 ^ 2
  have hleft : 0 ≤ left := by positivity
  have hright : 0 ≤ right := by positivity
  have hsum : (left + right) / 2 ≤ (1 + left) * (1 + right) := by
    nlinarith [mul_nonneg hleft hright]
  have hsumSq := sq_le_sq₀ (by positivity) (by positivity) |>.2 hsum
  have hleftBound : left ≤ (1 + left) ^ 2 := by nlinarith
  have hrightBound : right ≤ (1 + right) ^ 2 := by nlinarith
  have hproduct := mul_le_mul hleftBound hrightBound hright
    (sq_nonneg (1 + left))
  have hcombined := mul_le_mul hsumSq hproduct
    (mul_nonneg hleft hright) (by positivity)
  unfold rankFiveWeylPolynomial left right at *
  nlinarith

theorem integrable_rankFiveCoordinateDominating :
    Integrable rankFiveCoordinateDominating := by
  rw [show rankFiveCoordinateDominating = fun value : ℝ =>
      ∑ index ∈ Finset.range 5,
        (Nat.choose 4 index : ℝ) *
          (|value| ^ (2 * (4 - index)) *
            Real.exp (-rankFiveGaussianCoefficient * value ^ 2)) by
    funext value
    unfold rankFiveCoordinateDominating
    rw [add_pow]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Finset.mem_range] at hindex
    rw [show (1 : ℝ) ^ index = 1 by simp, one_mul]
    have habs : |value| ^ (2 * (4 - index)) =
        (value ^ 2) ^ (4 - index) := by
      calc
        |value| ^ (2 * (4 - index)) =
            (|value| ^ 2) ^ (4 - index) := by rw [pow_mul]
        _ = _ := by rw [sq_abs]
    rw [habs]
    ring]
  apply integrable_finsetSum
  intro index hindex
  exact (integrable_abs_pow_mul_exp_neg_mul_sq
    (2 * (4 - index)) rankFiveGaussianCoefficient_pos).const_mul _

theorem integrable_rankFiveLocalDominating :
    Integrable rankFiveLocalDominating := by
  unfold rankFiveLocalDominating
  rw [volume_pi]
  exact (Integrable.fintype_prod fun _ : Fin 2 =>
    integrable_rankFiveCoordinateDominating).const_mul _

theorem rankFiveWeylPolynomial_mul_gaussian_le_dominating
    (coordinates : Fin 2 → ℝ) :
    ((1 / Real.pi) ^ 2 *
        (Real.sqrt (21 : ℝ) /
          Real.sqrt (oddCosineScaleMidpoint 2 ^ 2 - 4))) *
      rankFiveWeylPolynomial coordinates *
      Real.exp (-rankFiveGaussianCoefficient *
        ∑ coordinate, coordinates coordinate ^ 2) ≤
      rankFiveLocalDominating coordinates := by
  have hpoly := rankFiveWeylPolynomial_le_separable coordinates
  have hconstantNonneg : 0 ≤ (1 / Real.pi) ^ 2 *
      (Real.sqrt (21 : ℝ) /
        Real.sqrt (oddCosineScaleMidpoint 2 ^ 2 - 4)) := by positivity
  unfold rankFiveLocalDominating rankFiveCoordinateDominating
  rw [show (∑ coordinate : Fin 2, coordinates coordinate ^ 2) =
      coordinates 0 ^ 2 + coordinates 1 ^ 2 by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  rw [show (∏ coordinate : Fin 2,
      ((1 + coordinates coordinate ^ 2) ^ 4 *
        Real.exp (-rankFiveGaussianCoefficient * coordinates coordinate ^ 2))) =
      ((1 + coordinates 0 ^ 2) ^ 4 *
        Real.exp (-rankFiveGaussianCoefficient * coordinates 0 ^ 2)) *
      ((1 + coordinates 1 ^ 2) ^ 4 *
        Real.exp (-rankFiveGaussianCoefficient * coordinates 1 ^ 2)) by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  have hexp :
      Real.exp (-rankFiveGaussianCoefficient * coordinates 0 ^ 2) *
          Real.exp (-rankFiveGaussianCoefficient * coordinates 1 ^ 2) =
        Real.exp (-rankFiveGaussianCoefficient *
          (coordinates 0 ^ 2 + coordinates 1 ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpPos := Real.exp_pos
    (-rankFiveGaussianCoefficient *
      (coordinates 0 ^ 2 + coordinates 1 ^ 2))
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpoly hconstantNonneg) hexpPos.le
  calc
    _ ≤ ((1 / Real.pi) ^ 2 *
          (Real.sqrt (21 : ℝ) /
            Real.sqrt (oddCosineScaleMidpoint 2 ^ 2 - 4))) *
        ((1 + coordinates 0 ^ 2) ^ 4 *
          (1 + coordinates 1 ^ 2) ^ 4) *
        Real.exp (-rankFiveGaussianCoefficient *
          (coordinates 0 ^ 2 + coordinates 1 ^ 2)) := hscaled
    _ = _ := by rw [← hexp]; ring

theorem oddScaledWeylWeight_two_nonneg
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    0 ≤ oddScaledWeylWeight 2 index coordinates := by
  rw [oddScaledWeylWeight_eq]
  exact mul_nonneg (pow_nonneg (by positivity) _)
    (oddWeylAngleWeight_nonneg _ _)

theorem norm_rankFiveLocalRescaledIntegrand_le
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    ‖oddWeylLocalRescaledIntegrand 2 index coordinates‖ ≤
      rankFiveLocalDominating coordinates := by
  by_cases hdomain : coordinates ∈ positiveOddLocalScaledDomain 2 index
  · rw [oddWeylLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      Real.norm_eq_abs, abs_of_nonneg]
    · have hcube := hdomain.1
      have hcoordinate : ∀ coordinate,
          |coordinates coordinate| ≤
            Real.pi * Real.sqrt (index + 1 : ℝ) := by
        intro coordinate
        have hmem := hcube coordinate (Set.mem_univ coordinate)
        rw [abs_of_pos hmem.1]
        exact hmem.2
      have hkernel := normalizedOddFibonacciKernel_le_local_gaussian
        (dimension := 2) (by norm_num) coordinates hcoordinate hdomain.2
      have hsqrt21 :
          Real.sqrt ((2 * (2 : ℕ) + 1 : ℝ) ^ 2 - 4) =
            Real.sqrt (21 : ℝ) := by norm_num
      rw [hsqrt21] at hkernel
      have hkernel' : normalizedOddFibonacciKernel coordinates index ≤
        (Real.sqrt (21 : ℝ) /
          Real.sqrt (oddCosineScaleMidpoint 2 ^ 2 - 4)) *
        Real.exp (-rankFiveGaussianCoefficient *
          ∑ coordinate, coordinates coordinate ^ 2) := by
        simpa [rankFiveGaussianCoefficient] using hkernel
      have hweight := oddScaledWeylWeight_two_le_polynomial index coordinates
      have hkernelNonneg := normalizedOddFibonacciKernel_nonneg
        (dimension := 2) (by norm_num) coordinates
        ((oddCosineScaleMidpoint_gt_two (dimension := 2) (by norm_num)).trans_le
          hdomain.2)
      have hweightNonneg := oddScaledWeylWeight_two_nonneg index coordinates
      have hproduct := mul_le_mul hkernel' hweight hweightNonneg (by positivity)
      have hconstantNonneg : 0 ≤ (1 / Real.pi) ^ 2 := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hproduct hconstantNonneg
      have hscaled' :
          ((1 / Real.pi) ^ 2 *
              (Real.sqrt (21 : ℝ) /
                Real.sqrt (oddCosineScaleMidpoint 2 ^ 2 - 4))) *
            rankFiveWeylPolynomial coordinates *
            Real.exp (-rankFiveGaussianCoefficient *
              ∑ coordinate, coordinates coordinate ^ 2) ≤
            rankFiveLocalDominating coordinates := by
        exact rankFiveWeylPolynomial_mul_gaussian_le_dominating coordinates
      exact (show (1 / Real.pi) ^ 2 *
          normalizedOddFibonacciKernel coordinates index *
            oddScaledWeylWeight 2 index coordinates ≤
          ((1 / Real.pi) ^ 2 *
              (Real.sqrt (21 : ℝ) /
                Real.sqrt (oddCosineScaleMidpoint 2 ^ 2 - 4))) *
            rankFiveWeylPolynomial coordinates *
            Real.exp (-rankFiveGaussianCoefficient *
              ∑ coordinate, coordinates coordinate ^ 2) by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled).trans
        hscaled'
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (normalizedOddFibonacciKernel_nonneg
            (dimension := 2) (by norm_num) coordinates
            ((oddCosineScaleMidpoint_gt_two (dimension := 2) (by norm_num)).trans_le
              hdomain.2)))
        (oddScaledWeylWeight_two_nonneg index coordinates)
  · rw [oddWeylLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold rankFiveLocalDominating rankFiveCoordinateDominating
    positivity

end FibonacciRibbonKernel
