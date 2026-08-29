import FibonacciRibbonKernel.BesselAnalyticGerm
import Mathlib.Algebra.Polynomial.Homogenize

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators Classical

noncomputable def besselHomogenizedPolynomialSeries
    (degree : ℕ) (polynomial : Polynomial ℚ) : ℚ⟦X⟧ :=
  MvPolynomial.eval₂ (PowerSeries.C : ℚ →+* ℚ⟦X⟧)
    ![besselJ0, besselJ1] (polynomial.homogenize degree)

theorem besselHomogenizedPolynomialSeries_eq_pairing
    (degree : ℕ) (polynomial : Polynomial ℚ) :
    besselHomogenizedPolynomialSeries degree polynomial =
      besselSeriesPairing (polynomialCoeffVector degree polynomial)
        (besselBasisVector degree) := by
  unfold besselHomogenizedPolynomialSeries Polynomial.homogenize
  rw [MvPolynomial.eval₂_sum]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold besselSeriesPairing polynomialCoeffVector besselBasisVector
  apply Finset.sum_congr rfl
  intro index _hindex
  rw [MvPolynomial.eval₂_monomial]
  unfold besselMonomial
  simp

theorem besselHomogenizedPolynomialSeries_signed
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    besselHomogenizedPolynomialSeries degree
        (signedBesselPolynomial (degree - scaleIndex.val) scaleIndex.val) =
      besselSeriesPairing (besselSignedEigenvector degree scaleIndex)
        (besselBasisVector degree) := by
  rw [besselHomogenizedPolynomialSeries_eq_pairing]
  rfl

end FibonacciRibbonKernel
