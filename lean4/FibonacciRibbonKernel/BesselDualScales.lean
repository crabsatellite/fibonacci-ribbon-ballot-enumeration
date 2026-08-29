import FibonacciRibbonKernel.ActualOrdinaryBesselCarrier
import FibonacciRibbonKernel.BesselScales
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace FibonacciRibbonKernel

open Module

def polynomialCoeffVector (degree : ℕ) (polynomial : Polynomial ℚ) :
    Fin (degree + 1) → ℚ :=
  fun index => polynomial.coeff index.val

def besselM0DualCoeffAction (degree : ℕ)
    (vector : Fin (degree + 1) → ℚ) : Fin (degree + 1) → ℚ :=
  fun index =>
    (if hbelow : index.val < degree then
      (2 * (index.val + 1) : ℚ) * vector ⟨index.val + 1, by omega⟩
    else 0) +
    (if hpositive : 0 < index.val then
      (2 * (degree - index.val + 1) : ℚ) *
        vector ⟨index.val - 1, by omega⟩
    else 0)

theorem besselScaleOperator_coeff_formula
    (degree : ℕ) (polynomial : Polynomial ℚ) (index : ℕ) :
    (besselScaleOperator degree polynomial).coeff index =
      2 * (index + 1 : ℚ) * polynomial.coeff (index + 1) +
        (if 0 < index then
          (2 * (degree - index + 1) : ℚ) * polynomial.coeff (index - 1)
        else 0) := by
  have hexpand : besselScaleOperator degree polynomial =
      Polynomial.C 2 * polynomial.derivative -
        Polynomial.C 2 * (Polynomial.X ^ 2 * polynomial.derivative) +
        Polynomial.C (2 * degree : ℚ) * (Polynomial.X ^ 1 * polynomial) := by
    unfold besselScaleOperator
    norm_num
    ring
  rw [hexpand, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_derivative]
  rw [Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  simp only [Polynomial.coeff_derivative]
  by_cases hzero : index = 0
  · subst index
    simp
  · have hpositive : 0 < index := Nat.pos_of_ne_zero hzero
    by_cases hone : index = 1
    · subst index
      simp
      ring
    · have htwo : 2 ≤ index := by omega
      rw [if_pos htwo, if_pos hpositive]
      have hsub : index - 2 + 1 = index - 1 := by omega
      rw [hsub]
      rw [if_pos (by omega : 1 ≤ index)]
      rw [Nat.cast_sub htwo]
      push_cast
      ring

theorem signedBesselPolynomial_natDegree_le
    (degree scaleIndex : ℕ) (hscale : scaleIndex ≤ degree) :
    (signedBesselPolynomial (degree - scaleIndex) scaleIndex).natDegree ≤ degree := by
  unfold signedBesselPolynomial
  calc
    ((Polynomial.X + Polynomial.C (1 : ℚ)) ^ (degree - scaleIndex) *
        (Polynomial.X - Polynomial.C (1 : ℚ)) ^ scaleIndex).natDegree ≤
      ((Polynomial.X + Polynomial.C (1 : ℚ)) ^ (degree - scaleIndex)).natDegree +
        ((Polynomial.X - Polynomial.C (1 : ℚ)) ^ scaleIndex).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (degree - scaleIndex) + scaleIndex := by
      apply Nat.add_le_add
      · calc
          ((Polynomial.X + Polynomial.C (1 : ℚ)) ^
              (degree - scaleIndex)).natDegree ≤
              (degree - scaleIndex) *
                (Polynomial.X + Polynomial.C (1 : ℚ)).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ (degree - scaleIndex) * 1 := by
            exact Nat.mul_le_mul_left _
              (Polynomial.natDegree_X_add_C (1 : ℚ)).le
          _ = degree - scaleIndex := by omega
      · calc
          ((Polynomial.X - Polynomial.C (1 : ℚ)) ^
              scaleIndex).natDegree ≤
              scaleIndex *
                (Polynomial.X - Polynomial.C (1 : ℚ)).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ scaleIndex * 1 := by
            exact Nat.mul_le_mul_left _
              (Polynomial.natDegree_X_sub_C (1 : ℚ)).le
          _ = scaleIndex := by omega
    _ = degree := Nat.sub_add_cancel hscale

theorem signedBesselPolynomial_dual_eigenvector
    (degree scaleIndex : ℕ) (hscale : scaleIndex ≤ degree) :
    besselM0DualCoeffAction degree
        (polynomialCoeffVector degree
          (signedBesselPolynomial (degree - scaleIndex) scaleIndex)) =
      fun index => (2 * degree - 4 * scaleIndex : ℚ) *
        polynomialCoeffVector degree
          (signedBesselPolynomial (degree - scaleIndex) scaleIndex) index := by
  funext index
  have heigen := signedBesselPolynomial_eigen degree scaleIndex hscale
  have hcoeff := congrArg (fun polynomial : Polynomial ℚ =>
    polynomial.coeff index.val) heigen
  rw [besselScaleOperator_coeff_formula] at hcoeff
  rw [Polynomial.coeff_C_mul] at hcoeff
  by_cases hbelow : index.val < degree
  · by_cases hpositive : 0 < index.val
    · simp only [besselM0DualCoeffAction, polynomialCoeffVector,
        dif_pos hbelow, dif_pos hpositive]
      simp only [if_pos hpositive] at hcoeff
      simpa only [add_zero, zero_add] using hcoeff
    · simp only [besselM0DualCoeffAction, polynomialCoeffVector,
        dif_pos hbelow, dif_neg hpositive]
      simp only [if_neg hpositive] at hcoeff
      simpa only [add_zero, zero_add] using hcoeff
  · have hzero :
        (signedBesselPolynomial (degree - scaleIndex) scaleIndex).coeff
          (index.val + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hdegree := signedBesselPolynomial_natDegree_le
        degree scaleIndex hscale
      omega
    rw [hzero] at hcoeff
    simp only [mul_zero, zero_add] at hcoeff
    by_cases hpositive : 0 < index.val
    · simp only [besselM0DualCoeffAction, polynomialCoeffVector,
        dif_neg hbelow, dif_pos hpositive]
      simp only [if_pos hpositive] at hcoeff
      simpa only [add_zero, zero_add] using hcoeff
    · simp only [besselM0DualCoeffAction, polynomialCoeffVector,
        dif_neg hbelow, dif_neg hpositive]
      simp only [if_neg hpositive] at hcoeff
      simpa only [add_zero, zero_add] using hcoeff

noncomputable def besselM0DualLinear (degree : ℕ) :
    Module.End ℚ (Fin (degree + 1) → ℚ) where
  toFun := besselM0DualCoeffAction degree
  map_add' := by
    intro left right
    funext index
    by_cases hbelow : index.val < degree
    · by_cases hpositive : 0 < index.val
      · simp only [besselM0DualCoeffAction, dif_pos hbelow,
          dif_pos hpositive, Pi.add_apply]
        ring
      · simp only [besselM0DualCoeffAction, dif_pos hbelow,
          dif_neg hpositive, Pi.add_apply]
        ring
    · by_cases hpositive : 0 < index.val
      · simp only [besselM0DualCoeffAction, dif_neg hbelow,
          dif_pos hpositive, Pi.add_apply]
        ring
      · simp only [besselM0DualCoeffAction, dif_neg hbelow,
          dif_neg hpositive, Pi.add_apply]
        ring
  map_smul' := by
    intro scalar vector
    funext index
    by_cases hbelow : index.val < degree
    · by_cases hpositive : 0 < index.val
      · simp only [besselM0DualCoeffAction, dif_pos hbelow,
          dif_pos hpositive, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      · simp only [besselM0DualCoeffAction, dif_pos hbelow,
          dif_neg hpositive, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
    · by_cases hpositive : 0 < index.val
      · simp only [besselM0DualCoeffAction, dif_neg hbelow,
          dif_pos hpositive, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      · simp only [besselM0DualCoeffAction, dif_neg hbelow,
          dif_neg hpositive, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring

noncomputable def besselSignedEigenvector
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    Fin (degree + 1) → ℚ :=
  polynomialCoeffVector degree
    (signedBesselPolynomial (degree - scaleIndex.val) scaleIndex.val)

def besselScaleEigenvalue
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) : ℚ :=
  2 * degree - 4 * scaleIndex.val

theorem signedBesselPolynomial_ne_zero
    (degree scaleIndex : ℕ) (_hscale : scaleIndex ≤ degree) :
    signedBesselPolynomial (degree - scaleIndex) scaleIndex ≠ 0 := by
  unfold signedBesselPolynomial
  exact mul_ne_zero
    (pow_ne_zero _ (Polynomial.X_add_C_ne_zero (1 : ℚ)))
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (1 : ℚ)))

theorem besselSignedEigenvector_ne_zero
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    besselSignedEigenvector degree scaleIndex ≠ 0 := by
  intro hzero
  have hcoeff : ∀ index : ℕ,
      (signedBesselPolynomial (degree - scaleIndex.val) scaleIndex.val).coeff
        index = 0 := by
    intro index
    by_cases hindex : index ≤ degree
    · have hcomponent := congrFun hzero ⟨index, by omega⟩
      exact hcomponent
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hdegree := signedBesselPolynomial_natDegree_le
        degree scaleIndex.val (by omega)
      omega
  apply signedBesselPolynomial_ne_zero degree scaleIndex.val (by omega)
  apply Polynomial.ext
  intro index
  rw [hcoeff index, Polynomial.coeff_zero]

theorem besselM0DualLinear_hasEigenvector
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    (besselM0DualLinear degree).HasEigenvector
      (besselScaleEigenvalue degree scaleIndex)
      (besselSignedEigenvector degree scaleIndex) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change besselM0DualCoeffAction degree
        (besselSignedEigenvector degree scaleIndex) =
      besselScaleEigenvalue degree scaleIndex •
        besselSignedEigenvector degree scaleIndex
    unfold besselSignedEigenvector besselScaleEigenvalue
    rw [signedBesselPolynomial_dual_eigenvector degree scaleIndex.val (by omega)]
    funext index
    simp [smul_eq_mul]
  · exact besselSignedEigenvector_ne_zero degree scaleIndex

theorem besselScaleEigenvalue_injective (degree : ℕ) :
    Function.Injective (besselScaleEigenvalue degree) := by
  intro left right heq
  unfold besselScaleEigenvalue at heq
  apply Fin.ext
  exact_mod_cast (by linarith : (left.val : ℚ) = right.val)

theorem besselSignedEigenvector_linearIndependent (degree : ℕ) :
    LinearIndependent ℚ (besselSignedEigenvector degree) := by
  exact (besselM0DualLinear degree).eigenvectors_linearIndependent'
    (besselScaleEigenvalue degree)
    (besselScaleEigenvalue_injective degree)
    (besselSignedEigenvector degree)
    (besselM0DualLinear_hasEigenvector degree)

noncomputable def besselSignedBasis (degree : ℕ) :
    Module.Basis (Fin (degree + 1)) ℚ (Fin (degree + 1) → ℚ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (besselSignedEigenvector_linearIndependent degree)
    (by simp)

theorem besselSignedBasis_apply (degree : ℕ)
    (scaleIndex : Fin (degree + 1)) :
    besselSignedBasis degree scaleIndex =
      besselSignedEigenvector degree scaleIndex := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
    (besselSignedEigenvector_linearIndependent degree) (by simp)) scaleIndex

end FibonacciRibbonKernel
