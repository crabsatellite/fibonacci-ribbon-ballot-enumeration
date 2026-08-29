import FibonacciRibbonKernel.GeneralActualWeylCarrier
import FibonacciRibbonKernel.OddKernelDomination
import FibonacciRibbonKernel.MehtaGaussianDomination
import FibonacciRibbonKernel.RankFiveLocalDCT

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

def weylPairCount (dimension : ℕ) : ℕ :=
  ∑ upper : Fin dimension, (Finset.Iio upper).card

theorem weylPairCount_formula (dimension : ℕ) :
    2 * weylPairCount dimension = dimension * (dimension - 1) := by
  unfold weylPairCount
  simp only [Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun value : ℕ => value)]
  rw [mul_comm]
  exact Finset.sum_range_id_mul_two dimension

def weylSeparableExponent (dimension extra : ℕ) : ℕ :=
  2 * weylPairCount dimension + extra

noncomputable def weylCoordinateDominating
    (exponent : ℕ) (decay value : ℝ) : ℝ :=
  (1 + value ^ 2) ^ exponent * Real.exp (-decay * value ^ 2)

noncomputable def weylSeparableDominating
    (dimension extra : ℕ) (constant decay : ℝ)
    (coordinates : Fin dimension → ℝ) : ℝ :=
  constant * ∏ coordinate,
    weylCoordinateDominating (weylSeparableExponent dimension extra)
      decay (coordinates coordinate)

theorem integrable_weylCoordinateDominating
    (exponent : ℕ) {decay : ℝ} (hdecay : 0 < decay) :
    Integrable (weylCoordinateDominating exponent decay) := by
  rw [show weylCoordinateDominating exponent decay = fun value : ℝ =>
      ∑ index ∈ Finset.range (exponent + 1), (Nat.choose exponent index : ℝ) *
        (|value| ^ (2 * (exponent - index)) *
          Real.exp (-decay * value ^ 2)) by
    funext value
    unfold weylCoordinateDominating
    rw [add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Finset.mem_range] at hindex
    rw [show (1 : ℝ) ^ index = 1 by simp, one_mul]
    have habs : |value| ^ (2 * (exponent - index)) =
        (value ^ 2) ^ (exponent - index) := by
      calc
        _ = (|value| ^ 2) ^ (exponent - index) := by rw [pow_mul]
        _ = _ := by rw [sq_abs]
    rw [habs]
    ring]
  apply integrable_finsetSum
  intro index hindex
  exact (integrable_abs_pow_mul_exp_neg_mul_sq
    (2 * (exponent - index)) hdecay).const_mul _

theorem integrable_weylSeparableDominating
    (dimension extra : ℕ) (constant : ℝ)
    {decay : ℝ} (hdecay : 0 < decay) :
    Integrable (weylSeparableDominating dimension extra constant decay) := by
  unfold weylSeparableDominating
  rw [volume_pi]
  exact (Integrable.fintype_prod fun _ : Fin dimension =>
    integrable_weylCoordinateDominating
      (weylSeparableExponent dimension extra) hdecay).const_mul _

noncomputable def weylGlobalPolynomial
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  ∏ coordinate, (1 + coordinates coordinate ^ 2)

theorem one_le_weylGlobalPolynomial
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    1 ≤ weylGlobalPolynomial dimension coordinates := by
  unfold weylGlobalPolynomial
  calc
    (1 : ℝ) = ∏ _coordinate : Fin dimension, (1 : ℝ) := by simp
    _ ≤ ∏ coordinate : Fin dimension,
        (1 + coordinates coordinate ^ 2) := by
      apply Finset.prod_le_prod
      · intro coordinate hcoordinate
        norm_num
      · intro coordinate hcoordinate
        nlinarith [sq_nonneg (coordinates coordinate)]

theorem coordinate_sq_le_weylGlobalPolynomial
    (dimension : ℕ) (coordinates : Fin dimension → ℝ)
    (coordinate : Fin dimension) :
    coordinates coordinate ^ 2 ≤
      weylGlobalPolynomial dimension coordinates := by
  have hfactor : 1 + coordinates coordinate ^ 2 ≤
      weylGlobalPolynomial dimension coordinates := by
    unfold weylGlobalPolynomial
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ coordinate)]
    have hrest : (1 : ℝ) ≤
        ∏ other ∈ (Finset.univ : Finset (Fin dimension)).erase coordinate,
          (1 + coordinates other ^ 2) := by
      calc
        (1 : ℝ) = ∏ _other ∈
            (Finset.univ : Finset (Fin dimension)).erase coordinate,
            (1 : ℝ) := by simp
        _ ≤ _ := by
          apply Finset.prod_le_prod
          · intro other hother
            norm_num
          · intro other hother
            nlinarith [sq_nonneg (coordinates other)]
    have hmul := mul_le_mul_of_nonneg_right hrest
      (show 0 ≤ 1 + coordinates coordinate ^ 2 by positivity)
    simpa [mul_comm] using hmul
  linarith

theorem scaledCosinePair_sq_le_global_sq
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ)
    (upper lower : Fin dimension) :
    (((index + 1 : ℝ) *
      (Real.cos (coordinates upper / Real.sqrt (index + 1 : ℝ)) -
        Real.cos (coordinates lower / Real.sqrt (index + 1 : ℝ)))) ^ 2) ≤
      weylGlobalPolynomial dimension coordinates ^ 2 := by
  have hdiff := abs_scaled_cosine_difference_le index
    (coordinates upper) (coordinates lower)
  have hglobalNonneg : 0 ≤ weylGlobalPolynomial dimension coordinates :=
    le_trans (by norm_num) (one_le_weylGlobalPolynomial dimension coordinates)
  have haverage :
      (coordinates upper ^ 2 + coordinates lower ^ 2) / 2 ≤
        weylGlobalPolynomial dimension coordinates := by
    have hu := coordinate_sq_le_weylGlobalPolynomial
      dimension coordinates upper
    have hl := coordinate_sq_le_weylGlobalPolynomial
      dimension coordinates lower
    linarith
  have habsNonneg : 0 ≤ |(index + 1 : ℝ) *
      (Real.cos (coordinates upper / Real.sqrt (index + 1 : ℝ)) -
        Real.cos (coordinates lower / Real.sqrt (index + 1 : ℝ)))| :=
    abs_nonneg _
  have hsquare := (sq_le_sq₀ habsNonneg hglobalNonneg).2
    (hdiff.trans haverage)
  rw [sq_abs] at hsquare
  simpa [pow_two] using hsquare

theorem scaledCosineVandermondeWeight_le_global
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    scaledCosineVandermondeWeight dimension index coordinates ≤
      weylGlobalPolynomial dimension coordinates ^
        (2 * weylPairCount dimension) := by
  unfold scaledCosineVandermondeWeight weylPairCount
  have hinner : ∀ upper : Fin dimension,
      (∏ lower ∈ Finset.Iio upper,
        (((index + 1 : ℝ) *
          (Real.cos (coordinates upper / Real.sqrt (index + 1 : ℝ)) -
            Real.cos (coordinates lower / Real.sqrt (index + 1 : ℝ)))) ^ 2)) ≤
      (weylGlobalPolynomial dimension coordinates ^ 2) ^
        (Finset.Iio upper).card := by
    intro upper
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro lower hlower
      positivity
    · intro lower hlower
      exact scaledCosinePair_sq_le_global_sq
        dimension index coordinates upper lower
  calc
    (∏ upper : Fin dimension,
      ∏ lower ∈ Finset.Iio upper,
        (((index + 1 : ℝ) *
          (Real.cos (coordinates upper / Real.sqrt (index + 1 : ℝ)) -
            Real.cos (coordinates lower / Real.sqrt (index + 1 : ℝ)))) ^ 2)) ≤
      ∏ upper : Fin dimension,
        (weylGlobalPolynomial dimension coordinates ^ 2) ^
          (Finset.Iio upper).card := by
        apply Finset.prod_le_prod
        · intro upper hupper
          positivity
        · intro upper hupper
          exact hinner upper
    _ = _ := by
      calc
        (∏ upper : Fin dimension,
          (weylGlobalPolynomial dimension coordinates ^ 2) ^
            (Finset.Iio upper).card) =
          (weylGlobalPolynomial dimension coordinates ^ 2) ^
            (∑ upper : Fin dimension, (Finset.Iio upper).card) := by
              exact Finset.prod_pow_eq_pow_sum
                (Finset.univ : Finset (Fin dimension))
                (fun upper => (Finset.Iio upper).card)
                (weylGlobalPolynomial dimension coordinates ^ 2)
        _ = _ := by rw [← pow_mul]

theorem evenScaledWeylWeight_le_global
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    evenScaledWeylWeight dimension index coordinates ≤
      (2 : ℝ) ^ dimension *
        weylGlobalPolynomial dimension coordinates ^
          (weylSeparableExponent dimension 0) := by
  unfold evenScaledWeylWeight weylSeparableExponent
  have hv := scaledCosineVandermondeWeight_le_global
    dimension index coordinates
  have hp := allPlusScaledWeight_le_two_pow dimension index coordinates
  have hvNonneg : 0 ≤ scaledCosineVandermondeWeight dimension index coordinates :=
    by
      unfold scaledCosineVandermondeWeight
      positivity
  have hpNonneg : 0 ≤ allPlusScaledWeight dimension index coordinates :=
    allPlusScaledWeight_nonneg dimension index coordinates
  have h := mul_le_mul hv hp hpNonneg
    (pow_nonneg (le_trans (by norm_num)
      (one_le_weylGlobalPolynomial dimension coordinates)) _)
  simpa [Nat.add_zero, mul_comm] using h

theorem oddCoordinateProduct_le_global
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    (∏ coordinate,
      ((index + 1 : ℝ) *
          (1 - Real.cos
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) *
        (1 + Real.cos
          (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) ≤
      weylGlobalPolynomial dimension coordinates ^ dimension := by
  have hcoordinate : ∀ coordinate : Fin dimension,
      ((index + 1 : ℝ) *
          (1 - Real.cos
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) *
        (1 + Real.cos
          (coordinates coordinate / Real.sqrt (index + 1 : ℝ))) ≤
        weylGlobalPolynomial dimension coordinates := by
    intro coordinate
    exact (scaled_oddCoordinateWeight_le_sq index
      (coordinates coordinate)).trans
        (coordinate_sq_le_weylGlobalPolynomial dimension coordinates coordinate)
  calc
    (∏ coordinate,
      ((index + 1 : ℝ) *
          (1 - Real.cos
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) *
        (1 + Real.cos
          (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) ≤
      ∏ _coordinate : Fin dimension,
        weylGlobalPolynomial dimension coordinates := by
          apply Finset.prod_le_prod
          · intro coordinate hcoordinateMem
            have hcos := Real.neg_one_le_cos
              (coordinates coordinate / Real.sqrt (index + 1 : ℝ))
            exact mul_nonneg
              (mul_nonneg (by positivity)
                (sub_nonneg.2 (Real.cos_le_one _)))
              (by linarith)
          · intro coordinate hcoordinateMem
            exact hcoordinate coordinate
    _ = _ := by simp

theorem oddScaledWeylWeight_le_global
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    oddScaledWeylWeight dimension index coordinates ≤
      weylGlobalPolynomial dimension coordinates ^
        (weylSeparableExponent dimension dimension) := by
  unfold oddScaledWeylWeight weylSeparableExponent
  have hv := scaledCosineVandermondeWeight_le_global
    dimension index coordinates
  have hc := oddCoordinateProduct_le_global dimension index coordinates
  have hcNonneg : 0 ≤ ∏ coordinate,
      ((index + 1 : ℝ) *
          (1 - Real.cos
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) *
        (1 + Real.cos
          (coordinates coordinate / Real.sqrt (index + 1 : ℝ))) := by
    apply Finset.prod_nonneg
    intro coordinate hcoordinate
    have hcos := Real.neg_one_le_cos
      (coordinates coordinate / Real.sqrt (index + 1 : ℝ))
    exact mul_nonneg
      (mul_nonneg (by positivity) (sub_nonneg.2 (Real.cos_le_one _)))
      (by linarith)
  have h := mul_le_mul hv hc hcNonneg
    (pow_nonneg (le_trans (by norm_num)
      (one_le_weylGlobalPolynomial dimension coordinates)) _)
  calc
    scaledCosineVandermondeWeight dimension index coordinates *
        ∏ coordinate,
          ((index + 1 : ℝ) *
              (1 - Real.cos
                (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) *
            (1 + Real.cos
              (coordinates coordinate / Real.sqrt (index + 1 : ℝ))) ≤
      weylGlobalPolynomial dimension coordinates ^
          (2 * weylPairCount dimension) *
        weylGlobalPolynomial dimension coordinates ^ dimension := h
    _ = _ := by rw [← pow_add]

theorem weylGlobalPolynomial_pow_eq_separable
    (dimension exponent : ℕ) (coordinates : Fin dimension → ℝ) :
    weylGlobalPolynomial dimension coordinates ^ exponent =
      ∏ coordinate, (1 + coordinates coordinate ^ 2) ^ exponent := by
  unfold weylGlobalPolynomial
  exact (Finset.prod_pow _ _ _).symm

theorem evenScaledWeylWeight_nonneg
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    0 ≤ evenScaledWeylWeight dimension index coordinates := by
  unfold evenScaledWeylWeight scaledCosineVandermondeWeight
  exact mul_nonneg (by positivity)
    (allPlusScaledWeight_nonneg dimension index coordinates)

theorem oddScaledWeylWeight_nonneg
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    0 ≤ oddScaledWeylWeight dimension index coordinates := by
  unfold oddScaledWeylWeight scaledCosineVandermondeWeight
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro coordinate hcoordinate
  have hcos := Real.neg_one_le_cos
    (coordinates coordinate / Real.sqrt (index + 1 : ℝ))
  exact mul_nonneg
    (mul_nonneg (by positivity) (sub_nonneg.2 (Real.cos_le_one _)))
    (by linarith)

theorem gaussianGlobalPolynomial_eq_separable
    (dimension exponent : ℕ) (decay : ℝ)
    (coordinates : Fin dimension → ℝ) :
    weylGlobalPolynomial dimension coordinates ^ exponent *
        Real.exp (-decay * ∑ coordinate, coordinates coordinate ^ 2) =
      ∏ coordinate,
        weylCoordinateDominating exponent decay (coordinates coordinate) := by
  rw [weylGlobalPolynomial_pow_eq_separable]
  unfold weylCoordinateDominating
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

noncomputable def generalEvenWeylLocalRescaledIntegrand
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  (positiveLocalScaledDomain dimension index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        normalizedFibonacciCosineKernel coordinates index *
        evenScaledWeylWeight dimension index coordinates)
    coordinates

noncomputable def generalEvenWeylLocalLimitIntegrand
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  positiveOrthant.indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        Real.exp ((-∑ coordinate, coordinates coordinate ^ 2) /
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) *
        evenLimitWeylWeight dimension coordinates)
    coordinates

noncomputable def generalEvenWeylDominatingConstant (dimension : ℕ) : ℝ :=
  (1 / Real.pi) ^ dimension *
    (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
      Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4)) *
    2 ^ dimension

noncomputable def generalEvenWeylLocalDominating
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  weylSeparableDominating dimension 0
    (generalEvenWeylDominatingConstant dimension)
    (allPlusGaussianCoefficient dimension) coordinates

noncomputable def generalOddWeylGaussianCoefficient (dimension : ℕ) : ℝ :=
  4 / (Real.pi ^ 2 *
    Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))

noncomputable def generalOddWeylDominatingConstant (dimension : ℕ) : ℝ :=
  (1 / Real.pi) ^ dimension *
    (Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
      Real.sqrt (oddCosineScaleMidpoint dimension ^ 2 - 4))

noncomputable def generalOddWeylLocalDominating
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  weylSeparableDominating dimension dimension
    (generalOddWeylDominatingConstant dimension)
    (generalOddWeylGaussianCoefficient dimension) coordinates

theorem generalOddWeylGaussianCoefficient_pos
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ)) :
    0 < generalOddWeylGaussianCoefficient dimension := by
  unfold generalOddWeylGaussianCoefficient
  have hroot : 0 < Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  positivity

theorem integrable_generalEvenWeylLocalDominating
    (dimension : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    Integrable (generalEvenWeylLocalDominating dimension) := by
  unfold generalEvenWeylLocalDominating
  exact integrable_weylSeparableDominating dimension 0 _
    (allPlusGaussianCoefficient_pos hdimension)

theorem integrable_generalOddWeylLocalDominating
    (dimension : ℕ) (hdimension : 2 < (2 * dimension + 1 : ℝ)) :
    Integrable (generalOddWeylLocalDominating dimension) := by
  unfold generalOddWeylLocalDominating
  exact integrable_weylSeparableDominating dimension dimension _
    (generalOddWeylGaussianCoefficient_pos hdimension)

theorem tendsto_generalEvenWeylLocalRescaledIntegrand
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      generalEvenWeylLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds (generalEvenWeylLocalLimitIntegrand dimension coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain
      hdimension coordinates horthant
    have hkernel := tendsto_normalizedFibonacciCosineKernel
      hdimension coordinates
    have hweight := tendsto_evenScaledWeylWeight dimension coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    rw [generalEvenWeylLocalLimitIntegrand,
      Set.indicator_of_mem horthant]
    apply hproduct.congr'
    filter_upwards [hlocal] with index hindex
    rw [generalEvenWeylLocalRescaledIntegrand,
      Set.indicator_of_mem hindex]
  · have hdimensionPos : 0 < dimension := by
      by_contra hzero
      have : dimension = 0 := Nat.eq_zero_of_not_pos hzero
      subst dimension
      norm_num at hdimension
    have hnot : ∃ coordinate : Fin dimension,
        coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _ => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveLocalScaledDomain dimension index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    have hzero : (fun index : ℕ =>
        generalEvenWeylLocalRescaledIntegrand dimension index coordinates) =
        fun _ => 0 := by
      funext index
      rw [generalEvenWeylLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)]
    rw [hzero, generalEvenWeylLocalLimitIntegrand,
      Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

theorem aestronglyMeasurable_generalEvenWeylLocalRescaledIntegrand
    (dimension index : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    AEStronglyMeasurable
      (generalEvenWeylLocalRescaledIntegrand dimension index) := by
  unfold generalEvenWeylLocalRescaledIntegrand
  have hweight : Continuous (evenScaledWeylWeight dimension index) := by
    unfold evenScaledWeylWeight
    exact (continuous_scaledCosineVandermondeWeight dimension index).mul
      (continuous_allPlusScaledWeight dimension index)
  exact (((continuous_const.mul
    (continuous_normalizedFibonacciCosineKernel dimension index hdimension)).mul
      hweight).stronglyMeasurable.indicator
        (measurableSet_positiveLocalScaledDomain dimension index)).aestronglyMeasurable

theorem norm_generalEvenWeylLocalRescaledIntegrand_le
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖generalEvenWeylLocalRescaledIntegrand dimension index coordinates‖ ≤
      generalEvenWeylLocalDominating dimension coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [generalEvenWeylLocalRescaledIntegrand,
      Set.indicator_of_mem hdomain, Real.norm_eq_abs, abs_of_nonneg]
    · have hcoordinate : ∀ coordinate,
          |coordinates coordinate| ≤
            Real.pi * Real.sqrt (index + 1 : ℝ) := by
        intro coordinate
        have hmem := hdomain.1 coordinate (Set.mem_univ coordinate)
        rw [abs_of_pos hmem.1]
        exact hmem.2
      have hkernel := normalizedFibonacciCosineKernel_le_local_gaussian
        hdimension coordinates hcoordinate hdomain.2
      have hweight := evenScaledWeylWeight_le_global
        dimension index coordinates
      have hkernelNonneg := normalizedFibonacciCosineKernel_nonneg
        hdimension coordinates
        ((cosineScaleMidpoint_gt_two hdimension).trans_le hdomain.2)
      have hweightNonneg := evenScaledWeylWeight_nonneg
        dimension index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg
        (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ dimension by positivity)
      calc
        (1 / Real.pi) ^ dimension *
            normalizedFibonacciCosineKernel coordinates index *
              evenScaledWeylWeight dimension index coordinates ≤
          (1 / Real.pi) ^ dimension *
            ((Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
                Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4) *
              Real.exp
                (-(4 / (Real.pi ^ 2 *
                  Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
                    ∑ coordinate, coordinates coordinate ^ 2)) *
              ((2 : ℝ) ^ dimension *
                weylGlobalPolynomial dimension coordinates ^
                  (weylSeparableExponent dimension 0))) := by
                    simpa only [mul_assoc] using hscaled
        _ = generalEvenWeylLocalDominating dimension coordinates := by
          unfold generalEvenWeylLocalDominating
            generalEvenWeylDominatingConstant weylSeparableDominating
            allPlusGaussianCoefficient
          rw [← gaussianGlobalPolynomial_eq_separable]
          ring
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (normalizedFibonacciCosineKernel_nonneg
            hdimension coordinates
            ((cosineScaleMidpoint_gt_two hdimension).trans_le hdomain.2)))
        (evenScaledWeylWeight_nonneg dimension index coordinates)
  · rw [generalEvenWeylLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold generalEvenWeylLocalDominating weylSeparableDominating
      generalEvenWeylDominatingConstant
    have hroot : 0 < Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
      apply Real.sqrt_pos.2
      nlinarith
    have hmid := cosineScaleMidpoint_gt_two hdimension
    have hmidRoot : 0 < Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4) := by
      apply Real.sqrt_pos.2
      nlinarith
    apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _)
          (div_nonneg hroot.le hmidRoot.le))
        (pow_nonneg (by norm_num) _)
    · apply Finset.prod_nonneg
      intro coordinate hcoordinate
      unfold weylCoordinateDominating
      positivity

theorem norm_generalOddWeylLocalRescaledIntegrand_le
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖oddWeylLocalRescaledIntegrand dimension index coordinates‖ ≤
      generalOddWeylLocalDominating dimension coordinates := by
  by_cases hdomain : coordinates ∈ positiveOddLocalScaledDomain dimension index
  · rw [oddWeylLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      Real.norm_eq_abs, abs_of_nonneg]
    · have hcoordinate : ∀ coordinate,
          |coordinates coordinate| ≤
            Real.pi * Real.sqrt (index + 1 : ℝ) := by
        intro coordinate
        have hmem := hdomain.1 coordinate (Set.mem_univ coordinate)
        rw [abs_of_pos hmem.1]
        exact hmem.2
      have hkernel := normalizedOddFibonacciKernel_le_local_gaussian
        hdimension coordinates hcoordinate hdomain.2
      have hweight := oddScaledWeylWeight_le_global
        dimension index coordinates
      have hkernelNonneg := normalizedOddFibonacciKernel_nonneg
        hdimension coordinates
        ((oddCosineScaleMidpoint_gt_two hdimension).trans_le hdomain.2)
      have hweightNonneg := oddScaledWeylWeight_nonneg
        dimension index coordinates
      have hproduct := mul_le_mul hkernel hweight hweightNonneg
        (by positivity)
      have hscaled := mul_le_mul_of_nonneg_left hproduct
        (show 0 ≤ (1 / Real.pi) ^ dimension by positivity)
      calc
        (1 / Real.pi) ^ dimension *
            normalizedOddFibonacciKernel coordinates index *
              oddScaledWeylWeight dimension index coordinates ≤
          (1 / Real.pi) ^ dimension *
            ((Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) /
                Real.sqrt (oddCosineScaleMidpoint dimension ^ 2 - 4) *
              Real.exp
                (-(4 / (Real.pi ^ 2 *
                  Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4))) *
                    ∑ coordinate, coordinates coordinate ^ 2)) *
              weylGlobalPolynomial dimension coordinates ^
                (weylSeparableExponent dimension dimension)) := by
                  simpa only [mul_assoc] using hscaled
        _ = generalOddWeylLocalDominating dimension coordinates := by
          unfold generalOddWeylLocalDominating
            generalOddWeylDominatingConstant weylSeparableDominating
            generalOddWeylGaussianCoefficient
          rw [← gaussianGlobalPolynomial_eq_separable]
          ring
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (normalizedOddFibonacciKernel_nonneg
            hdimension coordinates
            ((oddCosineScaleMidpoint_gt_two hdimension).trans_le hdomain.2)))
        (oddScaledWeylWeight_nonneg dimension index coordinates)
  · rw [oddWeylLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold generalOddWeylLocalDominating weylSeparableDominating
      generalOddWeylDominatingConstant
    have hroot : 0 < Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4) := by
      apply Real.sqrt_pos.2
      nlinarith
    have hmid := oddCosineScaleMidpoint_gt_two hdimension
    have hmidRoot : 0 < Real.sqrt (oddCosineScaleMidpoint dimension ^ 2 - 4) := by
      apply Real.sqrt_pos.2
      nlinarith
    apply mul_nonneg
    · exact mul_nonneg (pow_nonneg (by positivity) _)
        (div_nonneg hroot.le hmidRoot.le)
    · apply Finset.prod_nonneg
      intro coordinate hcoordinate
      unfold weylCoordinateDominating
      positivity

theorem tendsto_integral_generalEvenWeylLocalRescaledIntegrand
    (dimension : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    Tendsto (fun index => ∫ coordinates : Fin dimension → ℝ,
        generalEvenWeylLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        generalEvenWeylLocalLimitIntegrand dimension coordinates)) := by
  exact tendsto_integral_of_dominated_convergence
    (generalEvenWeylLocalDominating dimension)
    (fun index => aestronglyMeasurable_generalEvenWeylLocalRescaledIntegrand
      dimension index hdimension)
    (integrable_generalEvenWeylLocalDominating dimension hdimension)
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_generalEvenWeylLocalRescaledIntegrand_le
        hdimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_generalEvenWeylLocalRescaledIntegrand
        hdimension coordinates)

theorem tendsto_integral_generalOddWeylLocalRescaledIntegrand
    (dimension : ℕ) (hdimension : 2 < (2 * dimension + 1 : ℝ)) :
    Tendsto (fun index => ∫ coordinates : Fin dimension → ℝ,
        oddWeylLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds (∫ coordinates : Fin dimension → ℝ,
        oddWeylLocalLimitIntegrand dimension coordinates)) := by
  exact tendsto_integral_of_dominated_convergence
    (generalOddWeylLocalDominating dimension)
    (fun index => aestronglyMeasurable_oddWeylLocalRescaledIntegrand
      dimension index)
    (integrable_generalOddWeylLocalDominating dimension hdimension)
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_generalOddWeylLocalRescaledIntegrand_le
        hdimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_oddWeylLocalRescaledIntegrand hdimension coordinates)

theorem cosineVandermondeWeight_le_four_pow
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    cosineVandermondeWeight dimension angles ≤
      (4 : ℝ) ^ weylPairCount dimension := by
  unfold cosineVandermondeWeight weylPairCount
  have hinner : ∀ upper : Fin dimension,
      (∏ lower ∈ Finset.Iio upper,
        (Real.cos (angles upper) - Real.cos (angles lower)) ^ 2) ≤
      (4 : ℝ) ^ (Finset.Iio upper).card := by
    intro upper
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro lower hlower
      positivity
    · intro lower hlower
      have huLower := Real.neg_one_le_cos (angles upper)
      have huUpper := Real.cos_le_one (angles upper)
      have hlLower := Real.neg_one_le_cos (angles lower)
      have hlUpper := Real.cos_le_one (angles lower)
      nlinarith [sq_nonneg
        (Real.cos (angles upper) - Real.cos (angles lower))]
  calc
    (∏ upper : Fin dimension,
      ∏ lower ∈ Finset.Iio upper,
        (Real.cos (angles upper) - Real.cos (angles lower)) ^ 2) ≤
      ∏ upper : Fin dimension,
        (4 : ℝ) ^ (Finset.Iio upper).card := by
          apply Finset.prod_le_prod
          · intro upper hupper
            positivity
          · intro upper hupper
            exact hinner upper
    _ = _ := by
      exact Finset.prod_pow_eq_pow_sum
        (Finset.univ : Finset (Fin dimension))
        (fun upper => (Finset.Iio upper).card) (4 : ℝ)

theorem evenWeylAngleWeight_le_constant
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    evenWeylAngleWeight dimension angles ≤
      (4 : ℝ) ^ weylPairCount dimension * (2 : ℝ) ^ dimension := by
  unfold evenWeylAngleWeight
  have hv := cosineVandermondeWeight_le_four_pow dimension angles
  have hc : (∏ coordinate,
      (1 + Real.cos (angles coordinate))) ≤ (2 : ℝ) ^ dimension := by
    calc
      (∏ coordinate, (1 + Real.cos (angles coordinate))) ≤
          ∏ _coordinate : Fin dimension, (2 : ℝ) := by
        apply Finset.prod_le_prod
        · intro coordinate hcoordinate
          linarith [Real.neg_one_le_cos (angles coordinate)]
        · intro coordinate hcoordinate
          linarith [Real.cos_le_one (angles coordinate)]
      _ = _ := by simp
  have hcNonneg : 0 ≤ ∏ coordinate,
      (1 + Real.cos (angles coordinate)) := by
    apply Finset.prod_nonneg
    intro coordinate hcoordinate
    linarith [Real.neg_one_le_cos (angles coordinate)]
  exact mul_le_mul hv hc hcNonneg (pow_nonneg (by norm_num) _)

theorem oddWeylAngleWeight_le_constant
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    oddWeylAngleWeight dimension angles ≤
      (4 : ℝ) ^ weylPairCount dimension := by
  unfold oddWeylAngleWeight
  have hv := cosineVandermondeWeight_le_four_pow dimension angles
  have hc : (∏ coordinate,
      (1 - Real.cos (angles coordinate)) *
        (1 + Real.cos (angles coordinate))) ≤ (1 : ℝ) := by
    calc
      (∏ coordinate,
        (1 - Real.cos (angles coordinate)) *
          (1 + Real.cos (angles coordinate))) ≤
        ∏ _coordinate : Fin dimension, (1 : ℝ) := by
          apply Finset.prod_le_prod
          · intro coordinate hcoordinate
            have hl := Real.neg_one_le_cos (angles coordinate)
            have hu := Real.cos_le_one (angles coordinate)
            nlinarith [sq_nonneg (Real.cos (angles coordinate))]
          · intro coordinate hcoordinate
            nlinarith [sq_nonneg (Real.cos (angles coordinate))]
      _ = 1 := by simp
  simpa only [mul_one] using
    mul_le_mul hv hc (by
      apply Finset.prod_nonneg
      intro coordinate hcoordinate
      have hl := Real.neg_one_le_cos (angles coordinate)
      have hu := Real.cos_le_one (angles coordinate)
      nlinarith) (pow_nonneg (by norm_num) _)

end FibonacciRibbonKernel
