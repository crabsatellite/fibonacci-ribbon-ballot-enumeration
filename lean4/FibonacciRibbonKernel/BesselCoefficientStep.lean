import FibonacciRibbonKernel.BesselScaleSeparation

namespace FibonacciRibbonKernel

noncomputable def besselCoefficientStepRatio
    (degree coefficient : ℕ) (index : Fin (degree + 1)) : ℚ :=
  (coefficient + 1 : ℚ) /
    ((coefficient + 1 : ℚ) + ((degree : ℚ) - (index.val : ℚ)))

theorem besselCoefficientStepRatio_pos
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    0 < besselCoefficientStepRatio degree coefficient index := by
  unfold besselCoefficientStepRatio
  have hindex : (index.val : ℚ) ≤ degree := by
    exact_mod_cast (Nat.le_of_lt_succ index.isLt)
  have hcoefficient : (0 : ℚ) < coefficient + 1 := by positivity
  have htail : (0 : ℚ) ≤ (degree : ℚ) - index.val := sub_nonneg.mpr hindex
  exact div_pos hcoefficient (add_pos_of_pos_of_nonneg hcoefficient htail)

theorem besselCoefficientStepRatio_le_one
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    besselCoefficientStepRatio degree coefficient index ≤ 1 := by
  unfold besselCoefficientStepRatio
  have hdenominator :
      (0 : ℚ) < (coefficient + 1 : ℚ) +
        ((degree : ℚ) - (index.val : ℚ)) := by
    have hindex : (index.val : ℚ) ≤ degree := by
      exact_mod_cast (Nat.le_of_lt_succ index.isLt)
    have hcoefficient : (0 : ℚ) < coefficient + 1 := by positivity
    exact add_pos_of_pos_of_nonneg hcoefficient (sub_nonneg.mpr hindex)
  rw [div_le_one hdenominator]
  have hindex : (index.val : ℚ) ≤ degree := by
    exact_mod_cast (Nat.le_of_lt_succ index.isLt)
  linarith

theorem besselFactorialCoeff_succ_step
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    besselFactorialCoeff degree (coefficient + 1) index =
      besselCoefficientStepRatio degree coefficient index *
        besselM0CoeffAction degree
          (besselFactorialCoeff degree coefficient) index := by
  have hrec := bessel_factorial_coefficient_recurrence
    degree (coefficient + 1) index
  have hprevious : coefficient + 1 - 1 = coefficient := by omega
  rw [hprevious] at hrec
  unfold besselM1CoeffAction at hrec
  let denominator : ℚ :=
    (coefficient + 1 : ℚ) + ((degree : ℚ) - (index.val : ℚ))
  have hdenominator : denominator ≠ 0 := by
    dsimp only [denominator]
    have hindex : (index.val : ℚ) ≤ degree := by
      exact_mod_cast (Nat.le_of_lt_succ index.isLt)
    have hcoefficient : (0 : ℚ) < coefficient + 1 := by positivity
    exact (add_pos_of_pos_of_nonneg hcoefficient (sub_nonneg.mpr hindex)).ne'
  calc
    besselFactorialCoeff degree (coefficient + 1) index =
        ((coefficient + 1 : ℚ) *
          besselM0CoeffAction degree
            (besselFactorialCoeff degree coefficient) index) / denominator := by
      apply (eq_div_iff hdenominator).2
      dsimp only [denominator]
      push_cast at hrec ⊢
      linear_combination hrec
    _ = besselCoefficientStepRatio degree coefficient index *
        besselM0CoeffAction degree
          (besselFactorialCoeff degree coefficient) index := by
      unfold besselCoefficientStepRatio
      dsimp only [denominator]
      ring

theorem oddBesselFactorialCoeff_succ_step
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    oddBesselFactorialCoeff degree (coefficient + 1) index =
      besselCoefficientStepRatio degree coefficient index *
        oddBesselM0CoeffAction degree
          (oddBesselFactorialCoeff degree coefficient) index := by
  have hrec := odd_bessel_factorial_coefficient_recurrence
    degree (coefficient + 1) index
  have hprevious : coefficient + 1 - 1 = coefficient := by omega
  rw [hprevious] at hrec
  unfold besselM1CoeffAction at hrec
  let denominator : ℚ :=
    (coefficient + 1 : ℚ) + ((degree : ℚ) - (index.val : ℚ))
  have hdenominator : denominator ≠ 0 := by
    dsimp only [denominator]
    have hindex : (index.val : ℚ) ≤ degree := by
      exact_mod_cast (Nat.le_of_lt_succ index.isLt)
    have hcoefficient : (0 : ℚ) < coefficient + 1 := by positivity
    exact (add_pos_of_pos_of_nonneg hcoefficient (sub_nonneg.mpr hindex)).ne'
  calc
    oddBesselFactorialCoeff degree (coefficient + 1) index =
        ((coefficient + 1 : ℚ) *
          oddBesselM0CoeffAction degree
            (oddBesselFactorialCoeff degree coefficient) index) / denominator := by
      apply (eq_div_iff hdenominator).2
      dsimp only [denominator]
      push_cast at hrec ⊢
      linear_combination hrec
    _ = besselCoefficientStepRatio degree coefficient index *
        oddBesselM0CoeffAction degree
          (oddBesselFactorialCoeff degree coefficient) index := by
      unfold besselCoefficientStepRatio
      dsimp only [denominator]
      ring

end FibonacciRibbonKernel
