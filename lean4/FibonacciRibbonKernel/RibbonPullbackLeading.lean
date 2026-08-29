import FibonacciRibbonKernel.RibbonPullbackIterates

namespace FibonacciRibbonKernel

open scoped Classical

theorem eulerOperatorLeftTheta_coeff
    (operator : Polynomial (Polynomial ℚ)) (order : ℕ) :
    (eulerOperatorLeftTheta operator).coeff order =
      Polynomial.X * (operator.coeff order).derivative +
        if order = 0 then 0 else operator.coeff (order - 1) := by
  induction operator using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [eulerOperatorLeftTheta_add, Polynomial.coeff_add,
        leftIH, rightIH, Polynomial.coeff_add,
        Polynomial.derivative_add, mul_add]
      by_cases horder : order = 0
      · simp [horder]
      · simp [horder, Polynomial.coeff_add]
        abel
  | monomial sourceOrder coefficient =>
      unfold eulerOperatorLeftTheta
      rw [Polynomial.sum_monomial_index]
      · simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
        by_cases horder : order = 0
        · subst order
          by_cases hsource : sourceOrder = 0 <;> simp [hsource]
        · cases order with
          | zero => exact (horder rfl).elim
          | succ previousOrder =>
              simp only [Nat.succ_ne_zero, ↓reduceIte,
                Nat.succ_sub_one]
              split_ifs <;> simp_all
      · simp

theorem ribbonPullbackIterateOperator_coeff_above
    (iterateOrder coefficientOrder : ℕ)
    (habove : iterateOrder < coefficientOrder) :
    (ribbonPullbackIterateOperator iterateOrder).coeff coefficientOrder = 0 := by
  induction iterateOrder generalizing coefficientOrder with
  | zero =>
      simp [ribbonPullbackIterateOperator, Polynomial.coeff_one,
        Nat.ne_of_gt habove]
  | succ iterateOrder ih =>
      rw [ribbonPullbackIterateOperator, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
        eulerOperatorLeftTheta_coeff]
      have hcurrent : iterateOrder < coefficientOrder := by omega
      have hprevious : iterateOrder < coefficientOrder - 1 := by omega
      rw [ih coefficientOrder hcurrent,
        ih (coefficientOrder - 1) hprevious]
      simp

theorem ribbonPullbackIterateOperator_coeff_order (iterateOrder : ℕ) :
    (ribbonPullbackIterateOperator iterateOrder).coeff iterateOrder =
      (ribbonQuadraticPlus * ribbonQuadraticMinus) ^ iterateOrder := by
  induction iterateOrder with
  | zero =>
      simp [ribbonPullbackIterateOperator]
  | succ iterateOrder ih =>
      rw [ribbonPullbackIterateOperator, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
        eulerOperatorLeftTheta_coeff]
      have habove := ribbonPullbackIterateOperator_coeff_above
        iterateOrder (iterateOrder + 1) (by omega)
      rw [habove]
      simp only [Polynomial.derivative_zero, mul_zero, zero_add]
      rw [if_neg (by omega : iterateOrder + 1 ≠ 0),
        Nat.add_sub_cancel, ih]
      simp only [add_zero]
      rw [pow_succ]
      ring

theorem ribbonQuadraticPlus_ne_zero : ribbonQuadraticPlus ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun polynomial : Polynomial ℚ =>
    polynomial.coeff 0) hzero
  simp [ribbonQuadraticPlus] at hcoeff

theorem ribbonQuadraticMinus_ne_zero : ribbonQuadraticMinus ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun polynomial : Polynomial ℚ =>
    polynomial.coeff 0) hzero
  simp [ribbonQuadraticMinus] at hcoeff

theorem ribbonPullbackIterateOperator_ne_zero (iterateOrder : ℕ) :
    ribbonPullbackIterateOperator iterateOrder ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun operator : Polynomial (Polynomial ℚ) =>
      operator.coeff iterateOrder) hzero
  rw [ribbonPullbackIterateOperator_coeff_order] at hcoeff
  have hbase : ribbonQuadraticPlus * ribbonQuadraticMinus ≠ 0 :=
    mul_ne_zero ribbonQuadraticPlus_ne_zero ribbonQuadraticMinus_ne_zero
  exact (pow_ne_zero iterateOrder hbase) (by simpa using hcoeff)

end FibonacciRibbonKernel
