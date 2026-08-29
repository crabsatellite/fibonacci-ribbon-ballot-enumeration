import FibonacciRibbonKernel.RibbonRationalNumerator

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def ribbonOperatorCoefficientBound
    (operator : Polynomial (Polynomial ℚ)) : ℕ :=
  operator.sum fun _ coefficient => coefficient.natDegree

theorem operator_coefficient_natDegree_le_bound
    (operator : Polynomial (Polynomial ℚ)) (order : ℕ) :
    (operator.coeff order).natDegree ≤
      ribbonOperatorCoefficientBound operator := by
  by_cases hcoefficient : operator.coeff order = 0
  · simp [hcoefficient, ribbonOperatorCoefficientBound]
  · have hsupport : order ∈ operator.support :=
      Polynomial.mem_support_iff.mpr hcoefficient
    unfold ribbonOperatorCoefficientBound
    rw [Polynomial.sum_def]
    exact Finset.single_le_sum
      (fun index hindex => Nat.zero_le
        (operator.coeff index).natDegree) hsupport

theorem ribbonRationalNumerator_zero (bound : ℕ) :
    ribbonRationalNumerator bound 0 = 0 := by
  simp [ribbonRationalNumerator]

noncomputable def ribbonOperatorPullback
    (operator : Polynomial (Polynomial ℚ)) :
    Polynomial (Polynomial ℚ) :=
  let coefficientBound := ribbonOperatorCoefficientBound operator
  let operatorOrder := operator.natDegree
  operator.sum fun order coefficient =>
    Polynomial.C
        (ribbonRationalNumerator coefficientBound coefficient *
          ribbonQuadraticMinus ^ (2 * (operatorOrder - order))) *
      ribbonPullbackIterateOperator order

theorem ribbonOperatorPullback_coeff_natDegree
    {operator : Polynomial (Polynomial ℚ)} (hoperator : operator ≠ 0) :
    (ribbonOperatorPullback operator).coeff operator.natDegree =
      ribbonRationalNumerator
          (ribbonOperatorCoefficientBound operator)
          (operator.coeff operator.natDegree) *
        (ribbonQuadraticPlus * ribbonQuadraticMinus) ^
          operator.natDegree := by
  unfold ribbonOperatorPullback
  rw [Polynomial.coeff_sum, Polynomial.sum_def]
  rw [Finset.sum_eq_single operator.natDegree]
  · rw [Polynomial.coeff_C_mul,
      ribbonPullbackIterateOperator_coeff_order]
    simp
  · intro order hsupport hne
    have hle := Polynomial.le_natDegree_of_mem_supp order hsupport
    have hlt : order < operator.natDegree := lt_of_le_of_ne hle hne
    rw [Polynomial.coeff_C_mul,
      ribbonPullbackIterateOperator_coeff_above order
        operator.natDegree hlt,
      mul_zero]
  · intro hnotSupport
    exact (hnotSupport
      (Polynomial.natDegree_mem_support_of_nonzero hoperator)).elim

theorem ribbonOperatorPullback_ne_zero
    {operator : Polynomial (Polynomial ℚ)} (hoperator : operator ≠ 0) :
    ribbonOperatorPullback operator ≠ 0 := by
  have hleading : operator.coeff operator.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hoperator
  have hbound := operator_coefficient_natDegree_le_bound
    operator operator.natDegree
  have hnumerator := ribbonRationalNumerator_ne_zero hleading hbound
  have hquadratic : ribbonQuadraticPlus * ribbonQuadraticMinus ≠ 0 :=
    mul_ne_zero ribbonQuadraticPlus_ne_zero ribbonQuadraticMinus_ne_zero
  intro hzero
  have hcoefficient := congrArg
    (fun transformed : Polynomial (Polynomial ℚ) =>
      transformed.coeff operator.natDegree) hzero
  rw [ribbonOperatorPullback_coeff_natDegree hoperator] at hcoefficient
  exact (mul_ne_zero hnumerator
    (pow_ne_zero operator.natDegree hquadratic)) (by simpa using hcoefficient)

end FibonacciRibbonKernel
