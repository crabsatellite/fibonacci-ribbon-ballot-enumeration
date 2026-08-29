import FibonacciRibbonKernel.BorelEulerPolynomial

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

/-- A polynomial in the Euler variable, with rational coefficients lifted to
polynomial coefficients in the ordinary variable. -/
noncomputable def liftEulerPolynomial
    (polynomial : Polynomial ℚ) : Polynomial (Polynomial ℚ) :=
  polynomial.map Polynomial.C

theorem liftEulerPolynomial_add (left right : Polynomial ℚ) :
    liftEulerPolynomial (left + right) =
      liftEulerPolynomial left + liftEulerPolynomial right := by
  simp [liftEulerPolynomial]

theorem eulerOperatorApply_liftEulerPolynomial
    (polynomial : Polynomial ℚ) (series : ℚ⟦X⟧) :
    eulerOperatorApply (liftEulerPolynomial polynomial) series =
      eulerPolynomialApply polynomial series := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [liftEulerPolynomial_add,
        eulerOperatorApply_add, leftIH, rightIH,
        eulerPolynomialApply_add]
  | monomial order coefficient =>
      unfold liftEulerPolynomial eulerOperatorApply eulerPolynomialApply
      rw [Polynomial.map_monomial,
        Polynomial.sum_monomial_index,
        Polynomial.sum_monomial_index]
      · rw [Polynomial.coe_C]
      · simp
      · simp

theorem eulerPolynomialApply_X_pow
    (order : ℕ) (series : ℚ⟦X⟧) :
    eulerPolynomialApply (Polynomial.X ^ order) series =
      eulerDerivative^[order] series := by
  ext degree
  rw [eulerPolynomialApply_coeff, eulerDerivative_iterate_coeff]
  simp

theorem eulerOperatorApply_lift_mul_X_pow
    (polynomial : Polynomial ℚ) (order : ℕ) (series : ℚ⟦X⟧) :
    eulerOperatorApply
        (liftEulerPolynomial (polynomial * Polynomial.X ^ order)) series =
      eulerPolynomialApply polynomial
        (eulerDerivative^[order] series) := by
  rw [eulerOperatorApply_liftEulerPolynomial,
    eulerPolynomialApply_mul, eulerPolynomialApply_X_pow]

/-- The transformed operator attached to a single Euler-order coefficient.
Each monomial `a X^s` becomes
`X^s a (θ+1)...(θ+s) θ^order`. -/
noncomputable def borelCoefficientOperator
    (order : ℕ) (coefficient : Polynomial ℚ) :
    Polynomial (Polynomial ℚ) :=
  coefficient.sum fun shift scalar =>
    Polynomial.C (Polynomial.X ^ shift) *
      liftEulerPolynomial
        (Polynomial.C scalar * risingEulerPolynomial shift *
          Polynomial.X ^ order)

theorem borelCoefficientOperator_zero (order : ℕ) :
    borelCoefficientOperator order 0 = 0 := by
  simp [borelCoefficientOperator]

theorem borelCoefficientOperator_add
    (order : ℕ) (left right : Polynomial ℚ) :
    borelCoefficientOperator order (left + right) =
      borelCoefficientOperator order left +
        borelCoefficientOperator order right := by
  unfold borelCoefficientOperator
  apply Polynomial.sum_add_index
  · intro shift
    simp [liftEulerPolynomial]
  · intro shift leftScalar rightScalar
    rw [Polynomial.C_add, add_mul, add_mul,
      liftEulerPolynomial_add, mul_add]

theorem eulerOperatorApply_borelCoefficientOperator
    (order : ℕ) (coefficient : Polynomial ℚ) (series : ℚ⟦X⟧) :
    eulerOperatorApply (borelCoefficientOperator order coefficient) series =
      borelPolynomialApply coefficient
        (eulerDerivative^[order] series) := by
  induction coefficient using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [borelCoefficientOperator_add, eulerOperatorApply_add,
        leftIH, rightIH, borelPolynomialApply_add]
  | monomial shift scalar =>
      unfold borelCoefficientOperator borelPolynomialApply
      rw [Polynomial.sum_monomial_index,
        Polynomial.sum_monomial_index]
      · rw [eulerOperatorApply_C_mul,
          eulerOperatorApply_lift_mul_X_pow]
        rw [show ((Polynomial.X ^ shift : Polynomial ℚ) : ℚ⟦X⟧) =
            X ^ shift by
          rw [polynomial_coe_pow_ps, Polynomial.coe_X]]
      · simp only [map_zero, zero_mul,
          eulerPolynomialApply_zero, mul_zero]
      · simp [liftEulerPolynomial]

/-- Borel/factorial-unscale transport of a finite Euler operator. -/
noncomputable def borelOperatorTransform
    (operator : Polynomial (Polynomial ℚ)) :
    Polynomial (Polynomial ℚ) :=
  operator.sum fun order coefficient =>
    borelCoefficientOperator order coefficient

theorem borelOperatorTransform_zero :
    borelOperatorTransform 0 = 0 := by
  simp [borelOperatorTransform]

theorem borelOperatorTransform_add
    (left right : Polynomial (Polynomial ℚ)) :
    borelOperatorTransform (left + right) =
      borelOperatorTransform left + borelOperatorTransform right := by
  unfold borelOperatorTransform
  apply Polynomial.sum_add_index
  · intro order
    exact borelCoefficientOperator_zero order
  · intro order leftCoefficient rightCoefficient
    exact borelCoefficientOperator_add order leftCoefficient rightCoefficient

theorem factorialUnscale_eulerOperatorApply
    (operator : Polynomial (Polynomial ℚ)) (series : ℚ⟦X⟧) :
    factorialUnscale (eulerOperatorApply operator series) =
      eulerOperatorApply (borelOperatorTransform operator)
        (factorialUnscale series) := by
  induction operator using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [eulerOperatorApply_add, factorialUnscale_add,
        leftIH, rightIH, borelOperatorTransform_add,
        eulerOperatorApply_add]
  | monomial order coefficient =>
      rw [show eulerOperatorApply
          (Polynomial.monomial order coefficient) series =
          (coefficient : ℚ⟦X⟧) *
            eulerDerivative^[order] series by
        unfold eulerOperatorApply
        rw [Polynomial.sum_monomial_index]
        simp]
      rw [show borelOperatorTransform
          (Polynomial.monomial order coefficient) =
          borelCoefficientOperator order coefficient by
        unfold borelOperatorTransform
        rw [Polynomial.sum_monomial_index]
        exact borelCoefficientOperator_zero order]
      rw [factorialUnscale_polynomial_mul,
        factorialUnscale_eulerDerivative_iterate,
        eulerOperatorApply_borelCoefficientOperator]

end FibonacciRibbonKernel
