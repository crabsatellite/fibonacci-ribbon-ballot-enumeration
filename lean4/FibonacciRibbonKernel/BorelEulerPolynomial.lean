import FibonacciRibbonKernel.BorelFactorialTransport

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def eulerPolynomialApply
    (polynomial : Polynomial ℚ) (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  polynomial.sum fun order coefficient =>
    PowerSeries.C coefficient * eulerDerivative^[order] series

theorem eulerPolynomialApply_coeff
    (polynomial : Polynomial ℚ) (series : ℚ⟦X⟧) (degree : ℕ) :
    PowerSeries.coeff degree (eulerPolynomialApply polynomial series) =
      polynomial.eval (degree : ℚ) * PowerSeries.coeff degree series := by
  unfold eulerPolynomialApply
  rw [Polynomial.sum_def, map_sum]
  simp_rw [PowerSeries.coeff_C_mul, eulerDerivative_iterate_coeff]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro order horder
  ring

theorem eulerPolynomialApply_zero (series : ℚ⟦X⟧) :
    eulerPolynomialApply 0 series = 0 := by
  ext degree
  simp [eulerPolynomialApply_coeff]

theorem eulerPolynomialApply_add
    (left right : Polynomial ℚ) (series : ℚ⟦X⟧) :
    eulerPolynomialApply (left + right) series =
      eulerPolynomialApply left series + eulerPolynomialApply right series := by
  ext degree
  simp [eulerPolynomialApply_coeff, add_mul]

theorem eulerPolynomialApply_mul
    (left right : Polynomial ℚ) (series : ℚ⟦X⟧) :
    eulerPolynomialApply (left * right) series =
      eulerPolynomialApply left (eulerPolynomialApply right series) := by
  ext degree
  simp [eulerPolynomialApply_coeff]
  ring

theorem eulerPolynomialApply_C
    (coefficient : ℚ) (series : ℚ⟦X⟧) :
    eulerPolynomialApply (Polynomial.C coefficient) series =
      PowerSeries.C coefficient * series := by
  ext degree
  simp [eulerPolynomialApply_coeff, PowerSeries.coeff_C_mul]

noncomputable def risingEulerPolynomial (shift : ℕ) : Polynomial ℚ :=
  ∏ offset ∈ Finset.range shift,
    (Polynomial.X + Polynomial.C (offset + 1 : ℚ))

theorem risingEulerPolynomial_eval
    (shift degree : ℕ) :
    (risingEulerPolynomial shift).eval (degree : ℚ) =
      risingFactorialQ degree shift := by
  unfold risingEulerPolynomial risingFactorialQ
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro offset hoffset
  simp
  ring

theorem risingEulerApply_eq_polynomial
    (shift : ℕ) (series : ℚ⟦X⟧) :
    risingEulerApply shift series =
      eulerPolynomialApply (risingEulerPolynomial shift) series := by
  ext degree
  rw [risingEulerApply_coeff, eulerPolynomialApply_coeff,
    risingEulerPolynomial_eval]

theorem factorialUnscale_C_mul
    (coefficient : ℚ) (series : ℚ⟦X⟧) :
    factorialUnscale (PowerSeries.C coefficient * series) =
      PowerSeries.C coefficient * factorialUnscale series := by
  ext degree
  simp [factorialUnscale_coeff, mul_left_comm]

noncomputable def borelPolynomialApply
    (polynomial : Polynomial ℚ) (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  polynomial.sum fun shift coefficient =>
    X ^ shift * eulerPolynomialApply
      (Polynomial.C coefficient * risingEulerPolynomial shift) series

theorem borelPolynomialApply_zero (series : ℚ⟦X⟧) :
    borelPolynomialApply 0 series = 0 := by
  simp [borelPolynomialApply]

theorem borelPolynomialApply_add
    (left right : Polynomial ℚ) (series : ℚ⟦X⟧) :
    borelPolynomialApply (left + right) series =
      borelPolynomialApply left series + borelPolynomialApply right series := by
  unfold borelPolynomialApply
  apply Polynomial.sum_add_index
  · intro degree
    simp [eulerPolynomialApply_zero]
  · intro degree leftCoefficient rightCoefficient
    rw [Polynomial.C_add, add_mul, eulerPolynomialApply_add, mul_add]

theorem factorialUnscale_polynomial_mul
    (polynomial : Polynomial ℚ) (series : ℚ⟦X⟧) :
    factorialUnscale ((polynomial : ℚ⟦X⟧) * series) =
      borelPolynomialApply polynomial (factorialUnscale series) := by
  induction polynomial using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [polynomial_coe_add, add_mul, factorialUnscale_add,
        leftIH, rightIH, borelPolynomialApply_add]
  | monomial shift coefficient =>
      rw [show (Polynomial.monomial shift coefficient : ℚ⟦X⟧) =
          PowerSeries.C coefficient * X ^ shift by
        rw [Polynomial.coe_monomial,
          PowerSeries.monomial_eq_C_mul_X_pow]]
      rw [mul_assoc, factorialUnscale_C_mul,
        factorialUnscale_X_pow_mul, risingEulerApply_eq_polynomial]
      unfold borelPolynomialApply
      rw [Polynomial.sum_monomial_index]
      · rw [eulerPolynomialApply_mul, eulerPolynomialApply_C]
        ring
      · simp [eulerPolynomialApply_zero]

end FibonacciRibbonKernel
