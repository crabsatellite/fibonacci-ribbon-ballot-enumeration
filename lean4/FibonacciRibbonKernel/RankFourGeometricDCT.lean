import FibonacciRibbonKernel.RankFourGeometricLocal

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFourGeometricCoordinateDominating (value : ℝ) : ℝ :=
  (1 + value ^ 2) ^ 2 *
    Real.exp (-rankFourGeometricGaussianCoefficient * value ^ 2)

noncomputable def rankFourGeometricLocalDominating
    (coordinates : Fin 2 → ℝ) : ℝ :=
  (4 * Real.exp 1 * (1 / Real.pi) ^ 2) *
    ∏ coordinate,
      rankFourGeometricCoordinateDominating (coordinates coordinate)

theorem integrable_rankFourGeometricCoordinateDominating :
    Integrable rankFourGeometricCoordinateDominating := by
  rw [show rankFourGeometricCoordinateDominating = fun value : ℝ =>
      ∑ index ∈ Finset.range 3,
        (Nat.choose 2 index : ℝ) *
          (|value| ^ (2 * (2 - index)) *
            Real.exp (-rankFourGeometricGaussianCoefficient * value ^ 2)) by
    funext value
    unfold rankFourGeometricCoordinateDominating
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Finset.mem_range] at hindex
    rw [show (1 : ℝ) ^ index = 1 by simp, one_mul]
    have habs : |value| ^ (2 * (2 - index)) =
        (value ^ 2) ^ (2 - index) := by
      calc
        |value| ^ (2 * (2 - index)) =
            (|value| ^ 2) ^ (2 - index) := by rw [pow_mul]
        _ = _ := by rw [sq_abs]
    rw [habs]
    ring]
  apply integrable_finsetSum
  intro index hindex
  exact (integrable_abs_pow_mul_exp_neg_mul_sq
    (2 * (2 - index)) rankFourGeometricGaussianCoefficient_pos).const_mul _

theorem integrable_rankFourGeometricLocalDominating :
    Integrable rankFourGeometricLocalDominating := by
  unfold rankFourGeometricLocalDominating
  rw [volume_pi]
  exact (Integrable.fintype_prod fun _ : Fin 2 =>
    integrable_rankFourGeometricCoordinateDominating).const_mul _

theorem rankFourGeometricPolynomialGaussian_le_dominating
    (coordinates : Fin 2 → ℝ) :
    (Real.exp 1 * (1 / Real.pi) ^ 2) *
        rankFourWeylPolynomial coordinates *
        Real.exp (-rankFourGeometricGaussianCoefficient *
          ∑ coordinate, coordinates coordinate ^ 2) ≤
      rankFourGeometricLocalDominating coordinates := by
  have hpoly := rankFourWeylPolynomial_le_separable coordinates
  have hconstant : 0 ≤ Real.exp 1 * (1 / Real.pi) ^ 2 := by positivity
  unfold rankFourGeometricLocalDominating
    rankFourGeometricCoordinateDominating
  rw [show (∑ coordinate : Fin 2, coordinates coordinate ^ 2) =
      coordinates 0 ^ 2 + coordinates 1 ^ 2 by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  rw [show (∏ coordinate : Fin 2,
      ((1 + coordinates coordinate ^ 2) ^ 2 *
        Real.exp (-rankFourGeometricGaussianCoefficient *
          coordinates coordinate ^ 2))) =
      ((1 + coordinates 0 ^ 2) ^ 2 *
        Real.exp (-rankFourGeometricGaussianCoefficient * coordinates 0 ^ 2)) *
      ((1 + coordinates 1 ^ 2) ^ 2 *
        Real.exp (-rankFourGeometricGaussianCoefficient * coordinates 1 ^ 2)) by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  have hexp :
      Real.exp (-rankFourGeometricGaussianCoefficient * coordinates 0 ^ 2) *
        Real.exp (-rankFourGeometricGaussianCoefficient * coordinates 1 ^ 2) =
      Real.exp (-rankFourGeometricGaussianCoefficient *
        (coordinates 0 ^ 2 + coordinates 1 ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscaled :
      (Real.exp 1 * (1 / Real.pi) ^ 2) *
          rankFourWeylPolynomial coordinates *
          Real.exp (-rankFourGeometricGaussianCoefficient *
            (coordinates 0 ^ 2 + coordinates 1 ^ 2)) ≤
        (Real.exp 1 * (1 / Real.pi) ^ 2) *
          (4 * (1 + coordinates 0 ^ 2) ^ 2 *
            (1 + coordinates 1 ^ 2) ^ 2) *
          Real.exp (-rankFourGeometricGaussianCoefficient *
            (coordinates 0 ^ 2 + coordinates 1 ^ 2)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly hconstant) (Real.exp_pos _).le
  calc
    _ ≤ _ := hscaled
    _ = _ := by rw [← hexp]; ring

theorem aestronglyMeasurable_rankFourGeometricLocalRescaledIntegrand
    (index : ℕ) :
    AEStronglyMeasurable (rankFourGeometricLocalRescaledIntegrand index) := by
  have hkernel : Continuous (normalizedRankFourGeometricKernel · index) := by
    unfold normalizedRankFourGeometricKernel
    exact ((continuous_cosineSumScale 2 index).div_const 4).pow index
  unfold rankFourGeometricLocalRescaledIntegrand
  exact (((continuous_const.mul
    hkernel).mul
      (by
        unfold evenScaledWeylWeight
        exact (continuous_scaledCosineVandermondeWeight 2 index).mul
          (continuous_allPlusScaledWeight 2 index))).stronglyMeasurable.indicator
        (measurableSet_positiveLocalScaledDomain 2 index)).aestronglyMeasurable

theorem norm_rankFourGeometricLocalRescaledIntegrand_le
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    ‖rankFourGeometricLocalRescaledIntegrand index coordinates‖ ≤
      rankFourGeometricLocalDominating coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain 2 index
  · rw [rankFourGeometricLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      Real.norm_eq_abs, abs_of_nonneg]
    · have hkernel := normalizedRankFourGeometricKernel_le_gaussian
        index coordinates hdomain.1 hdomain.2
      have hweight := evenScaledWeylWeight_two_le_polynomial index coordinates
      have hscaleNonneg : 0 ≤ cosineSumScale coordinates index :=
        (by norm_num : (0 : ℝ) ≤ 2).trans
          ((cosineScaleMidpoint_gt_two
            (dimension := 2) (by norm_num)).le.trans hdomain.2)
      have hkernelNonneg := normalizedRankFourGeometricKernel_nonneg
        (index := index) (coordinates := coordinates) hscaleNonneg
      have hweightNonneg := evenScaledWeylWeight_two_nonneg index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ 2 by positivity)
      exact (show (1 / Real.pi) ^ 2 *
          normalizedRankFourGeometricKernel coordinates index *
            evenScaledWeylWeight 2 index coordinates ≤
          (Real.exp 1 * (1 / Real.pi) ^ 2) *
            rankFourWeylPolynomial coordinates *
            Real.exp (-rankFourGeometricGaussianCoefficient *
              ∑ coordinate, coordinates coordinate ^ 2) by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled).trans
          (rankFourGeometricPolynomialGaussian_le_dominating coordinates)
    · exact mul_nonneg (mul_nonneg (by positivity)
        (normalizedRankFourGeometricKernel_nonneg
          (index := index) (coordinates := coordinates)
          ((by norm_num : (0 : ℝ) ≤ 2).trans
            ((cosineScaleMidpoint_gt_two
              (dimension := 2) (by norm_num)).le.trans hdomain.2))))
        (evenScaledWeylWeight_two_nonneg index coordinates)
  · rw [rankFourGeometricLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold rankFourGeometricLocalDominating
      rankFourGeometricCoordinateDominating
    positivity

theorem tendsto_rankFourGeometricAngleLocalIntegral :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricAngleLocalIntegral index)
      atTop (nhds (∫ coordinates : Fin 2 → ℝ,
        rankFourGeometricLocalLimitIntegrand coordinates)) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourGeometricAngleLocalIntegral index) =
      fun index => ∫ coordinates : Fin 2 → ℝ,
        rankFourGeometricLocalRescaledIntegrand index coordinates by
    funext index
    exact rankFourGeometricLocalScalingIntegral_identity index]
  exact tendsto_integral_of_dominated_convergence
    rankFourGeometricLocalDominating
    aestronglyMeasurable_rankFourGeometricLocalRescaledIntegrand
    integrable_rankFourGeometricLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankFourGeometricLocalRescaledIntegrand_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankFourGeometricLocalRescaledIntegrand coordinates)

end FibonacciRibbonKernel
