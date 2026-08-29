import FibonacciRibbonKernel.RibbonRationalChain

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def eulerOperatorLeftTheta
    (operator : Polynomial (Polynomial ℚ)) :
    Polynomial (Polynomial ℚ) :=
  operator.sum fun order coefficient =>
    Polynomial.monomial order
        (Polynomial.X * coefficient.derivative) +
      Polynomial.monomial (order + 1) coefficient

theorem eulerOperatorLeftTheta_zero :
    eulerOperatorLeftTheta 0 = 0 := by
  simp [eulerOperatorLeftTheta]

theorem eulerOperatorLeftTheta_add
    (left right : Polynomial (Polynomial ℚ)) :
    eulerOperatorLeftTheta (left + right) =
      eulerOperatorLeftTheta left + eulerOperatorLeftTheta right := by
  unfold eulerOperatorLeftTheta
  apply Polynomial.sum_add_index
  · intro order
    simp
  · intro order leftCoefficient rightCoefficient
    ext degree
    simp [Polynomial.coeff_monomial, Polynomial.derivative_add, mul_add]
    split_ifs <;> simp_all

theorem eulerOperatorApply_monomial_exact
    (order : ℕ) (coefficient : Polynomial ℚ) (series : ℚ⟦X⟧) :
    eulerOperatorApply (Polynomial.monomial order coefficient) series =
      (coefficient : ℚ⟦X⟧) *
        eulerDerivative^[order] series := by
  unfold eulerOperatorApply
  rw [Polynomial.sum_monomial_index]
  simp

theorem eulerOperatorApply_one (series : ℚ⟦X⟧) :
    eulerOperatorApply 1 series = series := by
  simpa using eulerOperatorApply_monomial_exact
    0 (1 : Polynomial ℚ) series

theorem eulerOperatorApply_leftTheta
    (operator : Polynomial (Polynomial ℚ)) (series : ℚ⟦X⟧) :
    eulerOperatorApply (eulerOperatorLeftTheta operator) series =
      eulerDerivative (eulerOperatorApply operator series) := by
  induction operator using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [eulerOperatorLeftTheta_add, eulerOperatorApply_add,
        leftIH, rightIH, eulerOperatorApply_add,
        eulerDerivative_add]
  | monomial order coefficient =>
      unfold eulerOperatorLeftTheta
      rw [Polynomial.sum_monomial_index]
      · rw [eulerOperatorApply_add,
          eulerOperatorApply_monomial_exact,
          eulerOperatorApply_monomial_exact,
          eulerOperatorApply_monomial_exact,
          eulerDerivative_mul, eulerDerivative_polynomial,
          Function.iterate_succ_apply']
      · simp

noncomputable def ribbonPullbackCorrection (order : ℕ) : Polynomial ℚ :=
  -((2 * order : ℕ) : Polynomial ℚ) * ribbonQuadraticPlus *
    (Polynomial.X * ribbonQuadraticMinus.derivative)

noncomputable def ribbonPullbackIterateOperator :
    ℕ → Polynomial (Polynomial ℚ)
  | 0 => 1
  | order + 1 =>
      Polynomial.C (ribbonQuadraticPlus * ribbonQuadraticMinus) *
          eulerOperatorLeftTheta (ribbonPullbackIterateOperator order) +
        Polynomial.C (ribbonPullbackCorrection order) *
          ribbonPullbackIterateOperator order

theorem eulerOperatorApply_ribbonPullbackIterate_succ
    (order : ℕ) (series : ℚ⟦X⟧) :
    eulerOperatorApply (ribbonPullbackIterateOperator (order + 1)) series =
      ((ribbonQuadraticPlus * ribbonQuadraticMinus : Polynomial ℚ) :
          ℚ⟦X⟧) *
          eulerDerivative
            (eulerOperatorApply (ribbonPullbackIterateOperator order) series) +
        (ribbonPullbackCorrection order : ℚ⟦X⟧) *
          eulerOperatorApply (ribbonPullbackIterateOperator order) series := by
  rw [ribbonPullbackIterateOperator, eulerOperatorApply_add,
    eulerOperatorApply_C_mul, eulerOperatorApply_C_mul,
    eulerOperatorApply_leftTheta]

theorem eulerDerivative_pow (series : ℚ⟦X⟧) (power : ℕ) :
    eulerDerivative (series ^ power) =
      (power : ℚ⟦X⟧) * series ^ (power - 1) *
        eulerDerivative series := by
  unfold eulerDerivative
  rw [PowerSeries.derivative_pow]
  ring

theorem series_mul_eulerDerivative_pow
    (series : ℚ⟦X⟧) (power : ℕ) :
    series * eulerDerivative (series ^ power) =
      (power : ℚ⟦X⟧) * series ^ power * eulerDerivative series := by
  rw [eulerDerivative_pow]
  cases power with
  | zero => simp
  | succ power =>
      rw [Nat.succ_sub_one, pow_succ']
      ring

theorem ribbonPullbackIterateOperator_exact
    (order : ℕ) (series : ℚ⟦X⟧) :
    (ribbonQuadraticMinus : ℚ⟦X⟧) ^ (2 * order) *
        PowerSeries.subst ribbonSubstitutionQ
          (eulerDerivative^[order] series) =
      eulerOperatorApply (ribbonPullbackIterateOperator order)
        (PowerSeries.subst ribbonSubstitutionQ series) := by
  induction order with
  | zero =>
      rw [ribbonPullbackIterateOperator, eulerOperatorApply_one]
      simp
  | succ order ih =>
      rw [Function.iterate_succ_apply']
      rw [eulerOperatorApply_ribbonPullbackIterate_succ]
      rw [← ih]
      rw [eulerDerivative_mul]
      have hchain := ribbonSubstitutionQ_euler_chain
        (eulerDerivative^[order] series)
      have hpower := series_mul_eulerDerivative_pow
        (ribbonQuadraticMinus : ℚ⟦X⟧) (2 * order)
      have hplus :
          ((ribbonQuadraticPlus * ribbonQuadraticMinus : Polynomial ℚ) :
              ℚ⟦X⟧) =
            (ribbonQuadraticPlus : ℚ⟦X⟧) *
              (ribbonQuadraticMinus : ℚ⟦X⟧) := by
        exact polynomial_coe_mul _ _
      rw [hplus]
      have hcorrection :
          (ribbonPullbackCorrection order : ℚ⟦X⟧) =
            -((2 * order : ℕ) : ℚ⟦X⟧) *
              (ribbonQuadraticPlus : ℚ⟦X⟧) *
              eulerDerivative (ribbonQuadraticMinus : ℚ⟦X⟧) := by
        unfold ribbonPullbackCorrection
        rw [eulerDerivative_polynomial]
        simp only [polynomial_coe_mul, polynomial_coe_neg,
          polynomial_coe_natCast]
      rw [hcorrection]
      rw [show 2 * (order + 1) = 2 * order + 2 by omega,
        pow_add, pow_two]
      linear_combination
        -((ribbonQuadraticPlus : ℚ⟦X⟧) *
          PowerSeries.subst ribbonSubstitutionQ
            (eulerDerivative^[order] series)) * hpower +
        -(ribbonQuadraticMinus : ℚ⟦X⟧) ^ (2 * order + 1) * hchain

end FibonacciRibbonKernel
