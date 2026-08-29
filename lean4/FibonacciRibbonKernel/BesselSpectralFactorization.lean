import FibonacciRibbonKernel.BesselHomogenizedPairing

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

theorem homogenize_X_add_one :
    (Polynomial.X + Polynomial.C (1 : ℚ)).homogenize 1 =
      MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) := by
  rw [Polynomial.homogenize_add, Polynomial.homogenize_X (by omega),
    Polynomial.homogenize_C]
  simp

theorem homogenize_X_sub_one :
    (Polynomial.X - Polynomial.C (1 : ℚ)).homogenize 1 =
      MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) := by
  rw [Polynomial.homogenize_sub, Polynomial.homogenize_X (by omega),
    Polynomial.homogenize_C]
  simp

theorem natDegree_X_add_one_pow_le (power : ℕ) :
    ((Polynomial.X + Polynomial.C (1 : ℚ)) ^ power).natDegree ≤ power := by
  calc
    _ ≤ power * (Polynomial.X + Polynomial.C (1 : ℚ)).natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ power * 1 := Nat.mul_le_mul_left power
      (Polynomial.natDegree_X_add_C (1 : ℚ)).le
    _ = power := by simp

theorem natDegree_X_sub_one_pow_le (power : ℕ) :
    ((Polynomial.X - Polynomial.C (1 : ℚ)) ^ power).natDegree ≤ power := by
  calc
    _ ≤ power * (Polynomial.X - Polynomial.C (1 : ℚ)).natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ power * 1 := Nat.mul_le_mul_left power
      (Polynomial.natDegree_X_sub_C (1 : ℚ)).le
    _ = power := by simp

theorem homogenize_X_add_one_pow (power : ℕ) :
    ((Polynomial.X + Polynomial.C (1 : ℚ)) ^ power).homogenize power =
      (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ power := by
  induction power with
  | zero => simp [Polynomial.homogenize_one]
  | succ power inductionHypothesis =>
      rw [pow_succ, Polynomial.homogenize_mul _ _
        (natDegree_X_add_one_pow_le power)
        (Polynomial.natDegree_X_add_C (1 : ℚ)).le,
        inductionHypothesis, homogenize_X_add_one, pow_succ]

theorem homogenize_X_sub_one_pow (power : ℕ) :
    ((Polynomial.X - Polynomial.C (1 : ℚ)) ^ power).homogenize power =
      (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2)) ^ power := by
  induction power with
  | zero => simp [Polynomial.homogenize_one]
  | succ power inductionHypothesis =>
      rw [pow_succ, Polynomial.homogenize_mul _ _
        (natDegree_X_sub_one_pow_le power)
        (Polynomial.natDegree_X_sub_C (1 : ℚ)).le,
        inductionHypothesis, homogenize_X_sub_one, pow_succ]

theorem signedBesselPolynomial_homogenize
    (plusPower minusPower : ℕ) :
    (signedBesselPolynomial plusPower minusPower).homogenize
        (plusPower + minusPower) =
      (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)) ^ plusPower *
        (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2)) ^ minusPower := by
  unfold signedBesselPolynomial
  rw [Polynomial.homogenize_mul _ _
    (natDegree_X_add_one_pow_le plusPower)
    (natDegree_X_sub_one_pow_le minusPower),
    homogenize_X_add_one_pow, homogenize_X_sub_one_pow]

theorem besselHomogenizedPolynomialSeries_signed_factorization
    (plusPower minusPower : ℕ) :
    besselHomogenizedPolynomialSeries (plusPower + minusPower)
        (signedBesselPolynomial plusPower minusPower) =
      (besselJ0 + besselJ1) ^ plusPower *
        (besselJ0 - besselJ1) ^ minusPower := by
  unfold besselHomogenizedPolynomialSeries
  rw [signedBesselPolynomial_homogenize]
  simp

theorem besselSeriesPairing_signed_factorization
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    besselSeriesPairing (besselSignedEigenvector degree scaleIndex)
        (besselBasisVector degree) =
      (besselJ0 + besselJ1) ^ (degree - scaleIndex.val) *
        (besselJ0 - besselJ1) ^ scaleIndex.val := by
  have hdegree : degree - scaleIndex.val + scaleIndex.val = degree := by omega
  rw [← besselHomogenizedPolynomialSeries_signed degree scaleIndex]
  have hfactor := besselHomogenizedPolynomialSeries_signed_factorization
    (degree - scaleIndex.val) scaleIndex.val
  rw [hdegree] at hfactor
  exact hfactor

end FibonacciRibbonKernel
