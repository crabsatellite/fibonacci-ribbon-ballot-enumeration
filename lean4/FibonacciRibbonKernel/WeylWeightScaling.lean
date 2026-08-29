import FibonacciRibbonKernel.WeylAngleWeights

namespace FibonacciRibbonKernel

open scoped BigOperators

def weylPairScalingExponent (dimension : ℕ) : ℕ :=
  ∑ upper : Fin dimension, 2 * (Finset.Iio upper).card

theorem weylPairScalingExponent_eq (dimension : ℕ) :
    weylPairScalingExponent dimension = dimension * (dimension - 1) := by
  unfold weylPairScalingExponent
  simp only [Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range]
  calc
    ∑ upper ∈ Finset.range dimension, 2 * upper =
        2 * ∑ upper ∈ Finset.range dimension, upper := by
      rw [Finset.mul_sum]
    _ = (∑ upper ∈ Finset.range dimension, upper) * 2 := by
      rw [mul_comm]
    _ = dimension * (dimension - 1) :=
      Finset.sum_range_id_mul_two dimension

theorem scaledCosineVandermondeWeight_eq
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    scaledCosineVandermondeWeight dimension index coordinates =
      (index + 1 : ℝ) ^ weylPairScalingExponent dimension *
        cosineVandermondeWeight dimension
          (coordinateScalarLinearMap dimension
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) := by
  unfold scaledCosineVandermondeWeight cosineVandermondeWeight
  rw [coordinateInverseSqrt_apply]
  have hinner : ∀ upper : Fin dimension,
      (∏ lower ∈ Finset.Iio upper,
        ((index + 1 : ℝ) *
          (Real.cos (coordinates upper / Real.sqrt (index + 1 : ℝ)) -
            Real.cos (coordinates lower / Real.sqrt (index + 1 : ℝ)))) ^ 2) =
      (index + 1 : ℝ) ^ (2 * (Finset.Iio upper).card) *
        ∏ lower ∈ Finset.Iio upper,
          (Real.cos (coordinates upper / Real.sqrt (index + 1 : ℝ)) -
            Real.cos (coordinates lower / Real.sqrt (index + 1 : ℝ))) ^ 2 := by
    intro upper
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    congr 1
    calc
      ∏ _lower ∈ Finset.Iio upper, (index + 1 : ℝ) ^ 2 =
          ((index + 1 : ℝ) ^ 2) ^ (Finset.Iio upper).card := by simp
      _ = (index + 1 : ℝ) ^ (2 * (Finset.Iio upper).card) := by
        rw [← pow_mul]
  simp_rw [hinner]
  rw [Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_pow_eq_pow_sum
    (Finset.univ : Finset (Fin dimension))
    (fun upper => 2 * (Finset.Iio upper).card)
    (index + 1 : ℝ)

theorem evenScaledWeylWeight_eq
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    evenScaledWeylWeight dimension index coordinates =
      (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
        evenWeylAngleWeight dimension
          (coordinateScalarLinearMap dimension
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) := by
  unfold evenScaledWeylWeight evenWeylAngleWeight
  rw [scaledCosineVandermondeWeight_eq,
    weylPairScalingExponent_eq, coordinateInverseSqrt_apply]
  unfold allPlusScaledWeight
  ring

theorem oddScaledWeylWeight_eq
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    oddScaledWeylWeight dimension index coordinates =
      (index + 1 : ℝ) ^ (dimension ^ 2) *
        oddWeylAngleWeight dimension
          (coordinateScalarLinearMap dimension
            (1 / Real.sqrt (index + 1 : ℝ)) coordinates) := by
  unfold oddScaledWeylWeight oddWeylAngleWeight
  rw [scaledCosineVandermondeWeight_eq,
    weylPairScalingExponent_eq, coordinateInverseSqrt_apply]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_mul_distrib]
  have hconstant :
      (∏ _coordinate : Fin dimension, (index + 1 : ℝ)) =
        (index + 1 : ℝ) ^ dimension := by simp
  rw [hconstant]
  have hexponent : dimension * (dimension - 1) + dimension =
      dimension ^ 2 := by
    by_cases hzero : dimension = 0
    · simp [hzero]
    · have hpositive : 1 ≤ dimension := Nat.one_le_iff_ne_zero.2 hzero
      rw [pow_two]
      calc
        dimension * (dimension - 1) + dimension =
            dimension * ((dimension - 1) + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = dimension * dimension := by
          rw [Nat.sub_add_cancel hpositive]
  have hpow :
      (index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          (index + 1 : ℝ) ^ dimension =
        (index + 1 : ℝ) ^ (dimension ^ 2) := by
    rw [← pow_add, hexponent]
  calc
    ((index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          cosineVandermondeWeight dimension
            (fun coordinate =>
              coordinates coordinate / Real.sqrt (index + 1 : ℝ))) *
        (((index + 1 : ℝ) ^ dimension *
            ∏ coordinate,
              (1 - Real.cos
                (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) *
          ∏ coordinate,
            (1 + Real.cos
              (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) =
      ((index + 1 : ℝ) ^ (dimension * (dimension - 1)) *
          (index + 1 : ℝ) ^ dimension) *
        (cosineVandermondeWeight dimension
            (fun coordinate =>
              coordinates coordinate / Real.sqrt (index + 1 : ℝ)) *
          ((∏ coordinate,
              (1 - Real.cos
                (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) *
            ∏ coordinate,
              (1 + Real.cos
                (coordinates coordinate / Real.sqrt (index + 1 : ℝ))))) := by ring
    _ = _ := by rw [hpow]

end FibonacciRibbonKernel
