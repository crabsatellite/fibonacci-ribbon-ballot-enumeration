import FibonacciRibbonKernel.RankFiveGeometricLocal

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def rankFiveGeometricCoordinateDominating
    (value : ℝ) : ℝ :=
  (1 + value ^ 2) ^ 4 *
    Real.exp (-rankFiveGeometricGaussianCoefficient * value ^ 2)

noncomputable def rankFiveGeometricLocalDominating
    (coordinates : Fin 2 → ℝ) : ℝ :=
  (Real.exp (4 / 5 : ℝ) * (1 / Real.pi) ^ 2) *
    ∏ coordinate,
      rankFiveGeometricCoordinateDominating (coordinates coordinate)

theorem integrable_rankFiveGeometricCoordinateDominating :
    Integrable rankFiveGeometricCoordinateDominating := by
  rw [show rankFiveGeometricCoordinateDominating = fun value : ℝ =>
      ∑ index ∈ Finset.range 5,
        (Nat.choose 4 index : ℝ) *
          (|value| ^ (2 * (4 - index)) *
            Real.exp
              (-rankFiveGeometricGaussianCoefficient * value ^ 2)) by
    funext value
    unfold rankFiveGeometricCoordinateDominating
    rw [add_pow, Finset.sum_mul]
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
    (2 * (4 - index)) rankFiveGeometricGaussianCoefficient_pos).const_mul _

theorem integrable_rankFiveGeometricLocalDominating :
    Integrable rankFiveGeometricLocalDominating := by
  unfold rankFiveGeometricLocalDominating
  rw [volume_pi]
  exact (Integrable.fintype_prod fun _ : Fin 2 =>
    integrable_rankFiveGeometricCoordinateDominating).const_mul _

theorem rankFiveGeometricPolynomial_mul_gaussian_le_dominating
    (coordinates : Fin 2 → ℝ) :
    (Real.exp (4 / 5 : ℝ) * (1 / Real.pi) ^ 2) *
      rankFiveWeylPolynomial coordinates *
      Real.exp (-rankFiveGeometricGaussianCoefficient *
        ∑ coordinate, coordinates coordinate ^ 2) ≤
      rankFiveGeometricLocalDominating coordinates := by
  have hpoly := rankFiveWeylPolynomial_le_separable coordinates
  have hconstantNonneg :
      0 ≤ Real.exp (4 / 5 : ℝ) * (1 / Real.pi) ^ 2 := by positivity
  unfold rankFiveGeometricLocalDominating
    rankFiveGeometricCoordinateDominating
  rw [show (∑ coordinate : Fin 2, coordinates coordinate ^ 2) =
      coordinates 0 ^ 2 + coordinates 1 ^ 2 by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  rw [show (∏ coordinate : Fin 2,
      ((1 + coordinates coordinate ^ 2) ^ 4 *
        Real.exp (-rankFiveGeometricGaussianCoefficient *
          coordinates coordinate ^ 2))) =
      ((1 + coordinates 0 ^ 2) ^ 4 *
        Real.exp (-rankFiveGeometricGaussianCoefficient *
          coordinates 0 ^ 2)) *
      ((1 + coordinates 1 ^ 2) ^ 4 *
        Real.exp (-rankFiveGeometricGaussianCoefficient *
          coordinates 1 ^ 2)) by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  have hexp :
      Real.exp (-rankFiveGeometricGaussianCoefficient *
          coordinates 0 ^ 2) *
        Real.exp (-rankFiveGeometricGaussianCoefficient *
          coordinates 1 ^ 2) =
      Real.exp (-rankFiveGeometricGaussianCoefficient *
        (coordinates 0 ^ 2 + coordinates 1 ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscaled :
      (Real.exp (4 / 5 : ℝ) * (1 / Real.pi) ^ 2) *
          rankFiveWeylPolynomial coordinates *
          Real.exp (-rankFiveGeometricGaussianCoefficient *
            (coordinates 0 ^ 2 + coordinates 1 ^ 2)) ≤
        (Real.exp (4 / 5 : ℝ) * (1 / Real.pi) ^ 2) *
          ((1 + coordinates 0 ^ 2) ^ 4 *
            (1 + coordinates 1 ^ 2) ^ 4) *
          Real.exp (-rankFiveGeometricGaussianCoefficient *
            (coordinates 0 ^ 2 + coordinates 1 ^ 2)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly hconstantNonneg)
      (Real.exp_pos _).le
  calc
    _ ≤ (Real.exp (4 / 5 : ℝ) * (1 / Real.pi) ^ 2) *
        ((1 + coordinates 0 ^ 2) ^ 4 *
          (1 + coordinates 1 ^ 2) ^ 4) *
        Real.exp (-rankFiveGeometricGaussianCoefficient *
          (coordinates 0 ^ 2 + coordinates 1 ^ 2)) := hscaled
    _ = _ := by rw [← hexp]; ring

theorem norm_rankFiveGeometricLocalRescaledIntegrand_le
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    ‖rankFiveGeometricLocalRescaledIntegrand index coordinates‖ ≤
      rankFiveGeometricLocalDominating coordinates := by
  by_cases hdomain : coordinates ∈ positiveOddLocalScaledDomain 2 index
  · rw [rankFiveGeometricLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, Real.norm_eq_abs, abs_of_nonneg]
    · have hkernel := normalizedRankFiveGeometricKernel_le_gaussian
        index coordinates hdomain.1 hdomain.2
      have hweight := oddScaledWeylWeight_two_le_polynomial index coordinates
      have hscaleNonneg : 0 ≤ oddCosineSumScale coordinates index :=
        (by norm_num : (0 : ℝ) ≤ 2).trans
          ((oddCosineScaleMidpoint_gt_two
            (dimension := 2) (by norm_num)).le.trans hdomain.2)
      have hkernelNonneg := normalizedRankFiveGeometricKernel_nonneg
        (index := index) (coordinates := coordinates) hscaleNonneg
      have hweightNonneg := oddScaledWeylWeight_two_nonneg index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg
        (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ 2 by positivity)
      exact (show (1 / Real.pi) ^ 2 *
          normalizedRankFiveGeometricKernel coordinates index *
            oddScaledWeylWeight 2 index coordinates ≤
          (Real.exp (4 / 5 : ℝ) * (1 / Real.pi) ^ 2) *
            rankFiveWeylPolynomial coordinates *
            Real.exp (-rankFiveGeometricGaussianCoefficient *
              ∑ coordinate, coordinates coordinate ^ 2) by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled).trans
          (rankFiveGeometricPolynomial_mul_gaussian_le_dominating coordinates)
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (normalizedRankFiveGeometricKernel_nonneg
            (index := index) (coordinates := coordinates)
            ((by norm_num : (0 : ℝ) ≤ 2).trans
              ((oddCosineScaleMidpoint_gt_two
                (dimension := 2) (by norm_num)).le.trans hdomain.2))))
        (oddScaledWeylWeight_two_nonneg index coordinates)
  · rw [rankFiveGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold rankFiveGeometricLocalDominating
      rankFiveGeometricCoordinateDominating
    positivity

end FibonacciRibbonKernel
