import FibonacciRibbonKernel.BorelEulerOperator

namespace FibonacciRibbonKernel

open scoped Classical

/-- The coefficient polynomial in the Euler variable obtained by fixing one
ordinary-variable degree in a polynomial Euler operator. -/
noncomputable def innerCoefficient
    (ordinaryDegree : ℕ) (operator : Polynomial (Polynomial ℚ)) :
    Polynomial ℚ :=
  operator.sum fun eulerOrder coefficient =>
    Polynomial.monomial eulerOrder
      (coefficient.coeff ordinaryDegree)

@[simp] theorem innerCoefficient_coeff
    (ordinaryDegree : ℕ) (operator : Polynomial (Polynomial ℚ))
    (eulerOrder : ℕ) :
    (innerCoefficient ordinaryDegree operator).coeff eulerOrder =
      (operator.coeff eulerOrder).coeff ordinaryDegree := by
  unfold innerCoefficient
  rw [Polynomial.coeff_sum]
  by_cases hsupport : eulerOrder ∈ operator.support
  · simp [Polynomial.sum_def, Polynomial.coeff_monomial, hsupport]
  · have hcoefficient : operator.coeff eulerOrder = 0 := by
      simpa [Polynomial.mem_support_iff] using hsupport
    simp [Polynomial.sum_def, Polynomial.coeff_monomial,
      hsupport, hcoefficient]

theorem innerCoefficient_zero (ordinaryDegree : ℕ) :
    innerCoefficient ordinaryDegree 0 = 0 := by
  ext eulerOrder
  simp

theorem innerCoefficient_add
    (ordinaryDegree : ℕ)
    (left right : Polynomial (Polynomial ℚ)) :
    innerCoefficient ordinaryDegree (left + right) =
      innerCoefficient ordinaryDegree left +
        innerCoefficient ordinaryDegree right := by
  ext eulerOrder
  simp only [innerCoefficient_coeff, Polynomial.coeff_add]

theorem innerCoefficient_monomial
    (ordinaryDegree eulerOrder : ℕ) (coefficient : Polynomial ℚ) :
    innerCoefficient ordinaryDegree
        (Polynomial.monomial eulerOrder coefficient) =
      Polynomial.monomial eulerOrder
        (coefficient.coeff ordinaryDegree) := by
  ext currentOrder
  rw [innerCoefficient_coeff]
  simp only [Polynomial.coeff_monomial]
  split_ifs <;> simp_all

theorem innerCoefficient_nonzero_of_operator_nonzero
    {operator : Polynomial (Polynomial ℚ)} (hoperator : operator ≠ 0) :
    innerCoefficient
        (operator.coeff operator.natDegree).natDegree operator ≠ 0 := by
  intro hzero
  have houter : operator.coeff operator.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hoperator
  have hinner :
      (operator.coeff operator.natDegree).coeff
          (operator.coeff operator.natDegree).natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr houter
  apply hinner
  have hcoefficient := congrArg
    (fun polynomial : Polynomial ℚ =>
      polynomial.coeff operator.natDegree) hzero
  simpa using hcoefficient

theorem innerCoefficient_C_X_pow_mul_lift
    (ordinaryDegree shift : ℕ) (polynomial : Polynomial ℚ) :
    innerCoefficient ordinaryDegree
        (Polynomial.C (Polynomial.X ^ shift) *
          liftEulerPolynomial polynomial) =
      if ordinaryDegree = shift then polynomial else 0 := by
  ext eulerOrder
  rw [innerCoefficient_coeff]
  simp only [Polynomial.coeff_C_mul, liftEulerPolynomial,
    Polynomial.coeff_map]
  split_ifs with hdegree
  · subst ordinaryDegree
    simp
  · simp [hdegree]

theorem innerCoefficient_borelCoefficientOperator
    (ordinaryDegree eulerOrder : ℕ) (coefficient : Polynomial ℚ) :
    innerCoefficient ordinaryDegree
        (borelCoefficientOperator eulerOrder coefficient) =
      Polynomial.C (coefficient.coeff ordinaryDegree) *
        risingEulerPolynomial ordinaryDegree *
          Polynomial.X ^ eulerOrder := by
  induction coefficient using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [borelCoefficientOperator_add, innerCoefficient_add,
        leftIH, rightIH, Polynomial.coeff_add, Polynomial.C_add]
      ring
  | monomial shift scalar =>
      unfold borelCoefficientOperator
      rw [Polynomial.sum_monomial_index]
      · rw [innerCoefficient_C_X_pow_mul_lift]
        by_cases hdegree : ordinaryDegree = shift
        · subst ordinaryDegree
          simp
        · have hreverse : shift ≠ ordinaryDegree := Ne.symm hdegree
          simp [hdegree, hreverse, Polynomial.coeff_monomial]
      · simp [liftEulerPolynomial]

theorem innerCoefficient_borelOperatorTransform
    (ordinaryDegree : ℕ) (operator : Polynomial (Polynomial ℚ)) :
    innerCoefficient ordinaryDegree (borelOperatorTransform operator) =
      risingEulerPolynomial ordinaryDegree *
        innerCoefficient ordinaryDegree operator := by
  induction operator using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [borelOperatorTransform_add, innerCoefficient_add,
        leftIH, rightIH, innerCoefficient_add, mul_add]
  | monomial eulerOrder coefficient =>
      rw [show borelOperatorTransform
          (Polynomial.monomial eulerOrder coefficient) =
          borelCoefficientOperator eulerOrder coefficient by
        unfold borelOperatorTransform
        rw [Polynomial.sum_monomial_index]
        exact borelCoefficientOperator_zero eulerOrder]
      rw [innerCoefficient_borelCoefficientOperator,
        innerCoefficient_monomial]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      ring

theorem risingEulerPolynomial_ne_zero (ordinaryDegree : ℕ) :
    risingEulerPolynomial ordinaryDegree ≠ 0 := by
  unfold risingEulerPolynomial
  apply Finset.prod_ne_zero_iff.mpr
  intro offset hoffset
  exact Polynomial.X_add_C_ne_zero (offset + 1 : ℚ)

theorem borelOperatorTransform_ne_zero
    {operator : Polynomial (Polynomial ℚ)} (hoperator : operator ≠ 0) :
    borelOperatorTransform operator ≠ 0 := by
  let ordinaryDegree :=
    (operator.coeff operator.natDegree).natDegree
  have hslice : innerCoefficient ordinaryDegree operator ≠ 0 := by
    exact innerCoefficient_nonzero_of_operator_nonzero hoperator
  intro hzero
  have htransformedSlice :
      innerCoefficient ordinaryDegree (borelOperatorTransform operator) = 0 := by
    rw [hzero, innerCoefficient_zero]
  rw [innerCoefficient_borelOperatorTransform] at htransformedSlice
  exact hslice ((mul_eq_zero.mp htransformedSlice).resolve_left
    (risingEulerPolynomial_ne_zero ordinaryDegree))

end FibonacciRibbonKernel
