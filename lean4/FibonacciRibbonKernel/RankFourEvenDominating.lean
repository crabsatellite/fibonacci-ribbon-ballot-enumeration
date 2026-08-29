import FibonacciRibbonKernel.RankFourEvenLocal

namespace FibonacciRibbonKernel

open Filter MeasureTheory
open scoped BigOperators

noncomputable def rankFourWeylPolynomial
    (coordinates : Fin 2 → ℝ) : ℝ :=
  4 * ((coordinates 0 ^ 2 + coordinates 1 ^ 2) / 2) ^ 2

theorem evenScaledWeylWeight_two_nonneg
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    0 ≤ evenScaledWeylWeight 2 index coordinates := by
  unfold evenScaledWeylWeight
  exact mul_nonneg (by
    unfold scaledCosineVandermondeWeight
    positivity) (allPlusScaledWeight_nonneg 2 index coordinates)

theorem evenScaledWeylWeight_two_le_polynomial
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    evenScaledWeylWeight 2 index coordinates ≤
      rankFourWeylPolynomial coordinates := by
  unfold evenScaledWeylWeight rankFourWeylPolynomial
  rw [scaledCosineVandermondeWeight_two]
  have hdiff := abs_scaled_cosine_difference_le index
    (coordinates 1) (coordinates 0)
  have hdiffSq := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 hdiff
  rw [sq_abs] at hdiffSq
  have hplus := allPlusScaledWeight_le_two_pow 2 index coordinates
  norm_num at hplus
  have hplusNonneg := allPlusScaledWeight_nonneg 2 index coordinates
  exact (mul_le_mul hdiffSq hplus hplusNonneg
    (by positivity : 0 ≤ ((coordinates 1 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2)).trans_eq
      (by ring)

theorem rankFourWeylPolynomial_le_separable
    (coordinates : Fin 2 → ℝ) :
    rankFourWeylPolynomial coordinates ≤
      4 * (1 + coordinates 0 ^ 2) ^ 2 *
        (1 + coordinates 1 ^ 2) ^ 2 := by
  let left := coordinates 0 ^ 2
  let right := coordinates 1 ^ 2
  have hleft : 0 ≤ left := by positivity
  have hright : 0 ≤ right := by positivity
  have hsum : (left + right) / 2 ≤ (1 + left) * (1 + right) := by
    nlinarith [mul_nonneg hleft hright]
  have hsq := sq_le_sq₀ (by positivity) (by positivity) |>.2 hsum
  unfold rankFourWeylPolynomial left right at *
  nlinarith

noncomputable def rankFourCoordinateDominating (value : ℝ) : ℝ :=
  (1 + value ^ 2) ^ 2 *
    Real.exp (-allPlusGaussianCoefficient 2 * value ^ 2)

noncomputable def rankFourLocalDominating
    (coordinates : Fin 2 → ℝ) : ℝ :=
  (4 * (1 / Real.pi) ^ 2 *
    (Real.sqrt (12 : ℝ) /
      Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4))) *
    ∏ coordinate, rankFourCoordinateDominating (coordinates coordinate)

theorem integrable_rankFourCoordinateDominating :
    Integrable rankFourCoordinateDominating := by
  rw [show rankFourCoordinateDominating = fun value : ℝ =>
      ∑ index ∈ Finset.range 3,
        (Nat.choose 2 index : ℝ) *
          (|value| ^ (2 * (2 - index)) *
            Real.exp (-allPlusGaussianCoefficient 2 * value ^ 2)) by
    funext value
    unfold rankFourCoordinateDominating
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
    (2 * (2 - index)) (allPlusGaussianCoefficient_pos (by norm_num))).const_mul _

theorem integrable_rankFourLocalDominating :
    Integrable rankFourLocalDominating := by
  unfold rankFourLocalDominating
  rw [volume_pi]
  exact (Integrable.fintype_prod fun _ : Fin 2 =>
    integrable_rankFourCoordinateDominating).const_mul _

theorem rankFourPolynomial_mul_gaussian_le_dominating
    (coordinates : Fin 2 → ℝ) :
    ((1 / Real.pi) ^ 2 *
        (Real.sqrt (12 : ℝ) /
          Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4))) *
      rankFourWeylPolynomial coordinates *
      Real.exp (-allPlusGaussianCoefficient 2 *
        ∑ coordinate, coordinates coordinate ^ 2) ≤
      rankFourLocalDominating coordinates := by
  have hpoly := rankFourWeylPolynomial_le_separable coordinates
  have hconstantNonneg : 0 ≤ (1 / Real.pi) ^ 2 *
      (Real.sqrt (12 : ℝ) /
        Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4)) := by
    unfold cosineScaleMidpoint
    positivity
  unfold rankFourLocalDominating rankFourCoordinateDominating
  rw [show (∑ coordinate : Fin 2, coordinates coordinate ^ 2) =
      coordinates 0 ^ 2 + coordinates 1 ^ 2 by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  rw [show (∏ coordinate : Fin 2,
      ((1 + coordinates coordinate ^ 2) ^ 2 *
        Real.exp (-allPlusGaussianCoefficient 2 *
          coordinates coordinate ^ 2))) =
      ((1 + coordinates 0 ^ 2) ^ 2 *
        Real.exp (-allPlusGaussianCoefficient 2 * coordinates 0 ^ 2)) *
      ((1 + coordinates 1 ^ 2) ^ 2 *
        Real.exp (-allPlusGaussianCoefficient 2 * coordinates 1 ^ 2)) by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  have hexp :
      Real.exp (-allPlusGaussianCoefficient 2 * coordinates 0 ^ 2) *
        Real.exp (-allPlusGaussianCoefficient 2 * coordinates 1 ^ 2) =
      Real.exp (-allPlusGaussianCoefficient 2 *
        (coordinates 0 ^ 2 + coordinates 1 ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscaled :
      ((1 / Real.pi) ^ 2 *
          (Real.sqrt (12 : ℝ) /
            Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4))) *
        rankFourWeylPolynomial coordinates *
        Real.exp (-allPlusGaussianCoefficient 2 *
          (coordinates 0 ^ 2 + coordinates 1 ^ 2)) ≤
      ((1 / Real.pi) ^ 2 *
          (Real.sqrt (12 : ℝ) /
            Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4))) *
        (4 * (1 + coordinates 0 ^ 2) ^ 2 *
          (1 + coordinates 1 ^ 2) ^ 2) *
        Real.exp (-allPlusGaussianCoefficient 2 *
          (coordinates 0 ^ 2 + coordinates 1 ^ 2)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpoly hconstantNonneg)
      (Real.exp_pos _).le
  calc
    _ ≤ ((1 / Real.pi) ^ 2 *
          (Real.sqrt (12 : ℝ) /
            Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4))) *
        (4 * (1 + coordinates 0 ^ 2) ^ 2 *
          (1 + coordinates 1 ^ 2) ^ 2) *
        Real.exp (-allPlusGaussianCoefficient 2 *
          (coordinates 0 ^ 2 + coordinates 1 ^ 2)) := hscaled
    _ = _ := by rw [← hexp]; ring

theorem norm_rankFourEvenLocalRescaledIntegrand_le
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    ‖rankFourEvenLocalRescaledIntegrand index coordinates‖ ≤
      rankFourLocalDominating coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain 2 index
  · rw [rankFourEvenLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      Real.norm_eq_abs, abs_of_nonneg]
    · have hcube := hdomain.1
      have hcoordinate : ∀ coordinate,
          |coordinates coordinate| ≤
            Real.pi * Real.sqrt (index + 1 : ℝ) := by
        intro coordinate
        have hmem := hcube coordinate (Set.mem_univ coordinate)
        rw [abs_of_pos hmem.1]
        exact hmem.2
      have hkernel := normalizedFibonacciCosineKernel_le_local_gaussian
        (dimension := 2) (by norm_num) coordinates hcoordinate hdomain.2
      have hkernel' : normalizedFibonacciCosineKernel coordinates index ≤
          (Real.sqrt (12 : ℝ) /
            Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4)) *
          Real.exp (-allPlusGaussianCoefficient 2 *
            ∑ coordinate, coordinates coordinate ^ 2) := by
        rw [show Real.sqrt ((2 * (2 : ℕ) : ℝ) ^ 2 - 4) =
          Real.sqrt (12 : ℝ) by norm_num] at hkernel
        rw [show allPlusGaussianCoefficient 2 =
            4 / (Real.pi ^ 2 * Real.sqrt (12 : ℝ)) by
          norm_num [allPlusGaussianCoefficient]]
        exact hkernel
      have hweight := evenScaledWeylWeight_two_le_polynomial index coordinates
      have hkernelNonneg := normalizedFibonacciCosineKernel_nonneg
        (dimension := 2) (by norm_num) coordinates
        ((cosineScaleMidpoint_gt_two (by norm_num)).trans_le hdomain.2)
      have hweightNonneg := evenScaledWeylWeight_two_nonneg index coordinates
      have hproduct := mul_le_mul hkernel' hweight hweightNonneg (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ 2 by positivity)
      exact (show (1 / Real.pi) ^ 2 *
          normalizedFibonacciCosineKernel coordinates index *
            evenScaledWeylWeight 2 index coordinates ≤
          ((1 / Real.pi) ^ 2 *
              (Real.sqrt (12 : ℝ) /
                Real.sqrt (cosineScaleMidpoint 2 ^ 2 - 4))) *
            rankFourWeylPolynomial coordinates *
            Real.exp (-allPlusGaussianCoefficient 2 *
              ∑ coordinate, coordinates coordinate ^ 2) by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled).trans
          (rankFourPolynomial_mul_gaussian_le_dominating coordinates)
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (normalizedFibonacciCosineKernel_nonneg
            (dimension := 2) (by norm_num) coordinates
            ((cosineScaleMidpoint_gt_two (by norm_num)).trans_le hdomain.2)))
        (evenScaledWeylWeight_two_nonneg index coordinates)
  · rw [rankFourEvenLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold rankFourLocalDominating rankFourCoordinateDominating
    unfold cosineScaleMidpoint
    positivity

theorem tendsto_rankFourEvenAngleLocalIntegral :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourEvenAngleLocalIntegral index)
      Filter.atTop
      (nhds (∫ coordinates : Fin 2 → ℝ,
        rankFourEvenLocalLimitIntegrand coordinates)) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 3 * rankFourEvenAngleLocalIntegral index) =
      fun index => ∫ coordinates : Fin 2 → ℝ,
        rankFourEvenLocalRescaledIntegrand index coordinates by
    funext index
    exact rankFourEvenLocalScalingIntegral_identity index]
  exact tendsto_integral_of_dominated_convergence
    rankFourLocalDominating
    aestronglyMeasurable_rankFourEvenLocalRescaledIntegrand
    integrable_rankFourLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankFourEvenLocalRescaledIntegrand_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankFourEvenLocalRescaledIntegrand coordinates)

end FibonacciRibbonKernel
