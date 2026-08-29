import FibonacciRibbonKernel.WeylCountBridge
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

namespace FibonacciRibbonKernel

open Polynomial
open scoped BigOperators

theorem det_matrixOfPolynomials_eq_prod_leadingCoeff
    {dimension : ℕ} (polynomials : Fin dimension → ℝ[X])
    (hdegree : ∀ index, (polynomials index).natDegree = index) :
    (Matrix.of (fun (row column : Fin dimension) =>
      (polynomials column).coeff row)).det =
      ∏ index, (polynomials index).leadingCoeff := by
  rw [Matrix.det_of_upperTriangular
    (Matrix.matrixOfPolynomials_blockTriangular polynomials
      (fun index => Nat.le_of_eq (hdegree index)))]
  apply Finset.prod_congr rfl
  intro index _hindex
  rw [Matrix.of_apply, ← hdegree, Polynomial.coeff_natDegree]

theorem det_eval_matrixOfPolynomials_eq_vandermonde_mul_leading
    {dimension : ℕ} (values : Fin dimension → ℝ)
    (polynomials : Fin dimension → ℝ[X])
    (hdegree : ∀ index, (polynomials index).natDegree = index) :
    (Matrix.of (fun row column =>
      (polynomials column).eval (values row))).det =
      (Matrix.vandermonde values).det *
        ∏ index, (polynomials index).leadingCoeff := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
    values polynomials (fun index => Nat.le_of_eq (hdegree index)),
    Matrix.det_mul,
    det_matrixOfPolynomials_eq_prod_leadingCoeff polynomials hdegree]

noncomputable def oddChebyshevPolynomial (index : ℕ) : ℝ[X] :=
  Polynomial.Chebyshev.U ℝ index

theorem oddChebyshevPolynomial_natDegree (index : ℕ) :
    (oddChebyshevPolynomial index).natDegree = index := by
  unfold oddChebyshevPolynomial
  exact Polynomial.Chebyshev.natDegree_U_natCast ℝ index

theorem oddChebyshevPolynomial_leadingCoeff (index : ℕ) :
    (oddChebyshevPolynomial index).leadingCoeff = (2 : ℝ) ^ index := by
  unfold oddChebyshevPolynomial
  exact Polynomial.Chebyshev.leadingCoeff_U_natCast ℝ index

theorem oddChebyshevPolynomial_eval_mul_sin
    (index : ℕ) (angle : ℝ) :
    (oddChebyshevPolynomial index).eval (Real.cos angle) *
        Real.sin angle =
      Real.sin ((index + 1 : ℕ) * angle) := by
  unfold oddChebyshevPolynomial
  convert Polynomial.Chebyshev.U_real_cos angle (index : ℤ) using 1
  norm_num

theorem prod_two_pow_fin_eq (dimension : ℕ) :
    (∏ index : Fin dimension, (2 : ℝ) ^ index.val) =
      (2 : ℝ) ^ (dimension * (dimension - 1) / 2) := by
  rw [Fin.prod_univ_eq_prod_range]
  exact Finset.prod_pow_eq_pow_sum (Finset.range dimension)
    (fun index => index) (2 : ℝ) |>.trans (by
      rw [Finset.sum_range_id])

end FibonacciRibbonKernel
