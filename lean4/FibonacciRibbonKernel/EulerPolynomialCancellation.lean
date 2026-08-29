import FibonacciRibbonKernel.RibbonOperatorAction

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def polynomialMultiplierIterate
    (multiplier : Polynomial ℚ) : ℕ → Polynomial (Polynomial ℚ)
  | 0 => Polynomial.C multiplier
  | order + 1 =>
      eulerOperatorLeftTheta (polynomialMultiplierIterate multiplier order)

theorem polynomialMultiplierIterate_exact
    (multiplier : Polynomial ℚ) (order : ℕ) (series : ℚ⟦X⟧) :
    eulerOperatorApply (polynomialMultiplierIterate multiplier order) series =
      eulerDerivative^[order] ((multiplier : ℚ⟦X⟧) * series) := by
  induction order with
  | zero =>
      rw [polynomialMultiplierIterate,
        show Polynomial.C multiplier =
            Polynomial.C multiplier * 1 by simp,
        eulerOperatorApply_C_mul, eulerOperatorApply_one]
      simp
  | succ order ih =>
      rw [polynomialMultiplierIterate,
        eulerOperatorApply_leftTheta, ih,
        Function.iterate_succ_apply']

theorem polynomialMultiplierIterate_coeff_above
    (multiplier : Polynomial ℚ) (iterateOrder coefficientOrder : ℕ)
    (habove : iterateOrder < coefficientOrder) :
    (polynomialMultiplierIterate multiplier iterateOrder).coeff
      coefficientOrder = 0 := by
  induction iterateOrder generalizing coefficientOrder with
  | zero =>
      rw [polynomialMultiplierIterate]
      simp [Polynomial.coeff_C, Nat.ne_of_gt habove]
  | succ iterateOrder ih =>
      rw [polynomialMultiplierIterate, eulerOperatorLeftTheta_coeff]
      have hcurrent : iterateOrder < coefficientOrder := by omega
      have hprevious : iterateOrder < coefficientOrder - 1 := by omega
      rw [ih coefficientOrder hcurrent,
        ih (coefficientOrder - 1) hprevious]
      simp

theorem polynomialMultiplierIterate_coeff_order
    (multiplier : Polynomial ℚ) (iterateOrder : ℕ) :
    (polynomialMultiplierIterate multiplier iterateOrder).coeff
      iterateOrder = multiplier := by
  induction iterateOrder with
  | zero =>
      simp [polynomialMultiplierIterate]
  | succ iterateOrder ih =>
      rw [polynomialMultiplierIterate, eulerOperatorLeftTheta_coeff]
      have habove := polynomialMultiplierIterate_coeff_above
        multiplier iterateOrder (iterateOrder + 1) (by omega)
      rw [habove]
      simp only [Polynomial.derivative_zero, mul_zero, zero_add]
      rw [if_neg (by omega : iterateOrder + 1 ≠ 0),
        Nat.add_sub_cancel, ih]

noncomputable def cancelPolynomialOperator
    (multiplier : Polynomial ℚ)
    (operator : Polynomial (Polynomial ℚ)) :
    Polynomial (Polynomial ℚ) :=
  operator.sum fun order coefficient =>
    Polynomial.C coefficient *
      polynomialMultiplierIterate multiplier order

theorem cancelPolynomialOperator_exact
    (multiplier : Polynomial ℚ)
    (operator : Polynomial (Polynomial ℚ)) (series : ℚ⟦X⟧) :
    eulerOperatorApply (cancelPolynomialOperator multiplier operator) series =
      eulerOperatorApply operator ((multiplier : ℚ⟦X⟧) * series) := by
  unfold cancelPolynomialOperator
  rw [Polynomial.sum_def]
  rw [eulerOperatorApply_finsetSum]
  change (∑ order ∈ operator.support,
      eulerOperatorApply
        (Polynomial.C (operator.coeff order) *
          polynomialMultiplierIterate multiplier order) series) =
    operator.sum fun order coefficient =>
      (coefficient : ℚ⟦X⟧) *
        eulerDerivative^[order] ((multiplier : ℚ⟦X⟧) * series)
  rw [Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro order horder
  rw [eulerOperatorApply_C_mul,
    polynomialMultiplierIterate_exact]

theorem cancelPolynomialOperator_coeff_natDegree
    {operator : Polynomial (Polynomial ℚ)} (hoperator : operator ≠ 0)
    (multiplier : Polynomial ℚ) :
    (cancelPolynomialOperator multiplier operator).coeff operator.natDegree =
      operator.coeff operator.natDegree * multiplier := by
  unfold cancelPolynomialOperator
  rw [Polynomial.coeff_sum, Polynomial.sum_def]
  rw [Finset.sum_eq_single operator.natDegree]
  · rw [Polynomial.coeff_C_mul,
      polynomialMultiplierIterate_coeff_order]
  · intro order hsupport hne
    have hle := Polynomial.le_natDegree_of_mem_supp order hsupport
    have hlt : order < operator.natDegree := lt_of_le_of_ne hle hne
    rw [Polynomial.coeff_C_mul,
      polynomialMultiplierIterate_coeff_above multiplier order
        operator.natDegree hlt,
      mul_zero]
  · intro hnotSupport
    exact (hnotSupport
      (Polynomial.natDegree_mem_support_of_nonzero hoperator)).elim

theorem cancelPolynomialOperator_ne_zero
    {operator : Polynomial (Polynomial ℚ)} (hoperator : operator ≠ 0)
    {multiplier : Polynomial ℚ} (hmultiplier : multiplier ≠ 0) :
    cancelPolynomialOperator multiplier operator ≠ 0 := by
  have hleading : operator.coeff operator.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hoperator
  intro hzero
  have hcoefficient := congrArg
    (fun transformed : Polynomial (Polynomial ℚ) =>
      transformed.coeff operator.natDegree) hzero
  rw [cancelPolynomialOperator_coeff_natDegree hoperator] at hcoefficient
  exact (mul_ne_zero hleading hmultiplier) (by simpa using hcoefficient)

theorem EulerOperatorDFinite.cancel_polynomial_mul
    {series : ℚ⟦X⟧} {multiplier : Polynomial ℚ}
    (hmultiplier : multiplier ≠ 0)
    (hfinite : EulerOperatorDFinite ((multiplier : ℚ⟦X⟧) * series)) :
    EulerOperatorDFinite series := by
  obtain ⟨operator, hoperator, hrelation⟩ := hfinite
  refine ⟨cancelPolynomialOperator multiplier operator,
    cancelPolynomialOperator_ne_zero hoperator hmultiplier, ?_⟩
  rw [cancelPolynomialOperator_exact]
  exact hrelation

theorem EulerDFinite.cancel_polynomial_mul
    {series : ℚ⟦X⟧} {multiplier : Polynomial ℚ}
    (hmultiplier : multiplier ≠ 0)
    (hfinite : EulerDFinite ((multiplier : ℚ⟦X⟧) * series)) :
    EulerDFinite series := by
  rw [eulerDFinite_iff_operator] at hfinite ⊢
  exact EulerOperatorDFinite.cancel_polynomial_mul hmultiplier hfinite

end FibonacciRibbonKernel
