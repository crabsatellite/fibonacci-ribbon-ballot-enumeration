import FibonacciRibbonKernel.BesselDualPairing

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators Classical

noncomputable def besselSeriesPairing
    {degree : ℕ} (weight : Fin (degree + 1) → ℚ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) : ℚ⟦X⟧ :=
  ∑ index, PowerSeries.C (weight index) * vector index

theorem besselSeriesPairing_coeff
    {degree : ℕ} (weight : Fin (degree + 1) → ℚ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) (coefficient : ℕ) :
    PowerSeries.coeff coefficient (besselSeriesPairing weight vector) =
      besselPairing weight
        (fun index => PowerSeries.coeff coefficient (vector index)) := by
  unfold besselSeriesPairing besselPairing
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  rw [PowerSeries.coeff_C_mul]

theorem besselSeriesPairing_add
    {degree : ℕ} (weight : Fin (degree + 1) → ℚ)
    (left right : Fin (degree + 1) → ℚ⟦X⟧) :
    besselSeriesPairing weight (fun index => left index + right index) =
      besselSeriesPairing weight left + besselSeriesPairing weight right := by
  unfold besselSeriesPairing
  simp_rw [mul_add, Finset.sum_add_distrib]

theorem besselSeriesPairing_sub
    {degree : ℕ} (weight : Fin (degree + 1) → ℚ)
    (left right : Fin (degree + 1) → ℚ⟦X⟧) :
    besselSeriesPairing weight (fun index => left index - right index) =
      besselSeriesPairing weight left - besselSeriesPairing weight right := by
  unfold besselSeriesPairing
  simp_rw [mul_sub, Finset.sum_sub_distrib]

theorem besselSeriesPairing_X_mul
    {degree : ℕ} (weight : Fin (degree + 1) → ℚ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    besselSeriesPairing weight (fun index => PowerSeries.X * vector index) =
      PowerSeries.X * besselSeriesPairing weight vector := by
  unfold besselSeriesPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  ring

theorem besselSeriesPairing_derivative
    {degree : ℕ} (weight : Fin (degree + 1) → ℚ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    besselSeriesPairing weight
        (fun index => PowerSeries.derivative ℚ (vector index)) =
      PowerSeries.derivative ℚ (besselSeriesPairing weight vector) := by
  unfold besselSeriesPairing
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  simp only [Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_C, mul_zero, add_zero]

theorem besselSeriesPairing_M0_dual
    (degree : ℕ) (weight : Fin (degree + 1) → ℚ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    besselSeriesPairing weight (besselM0Action degree vector) =
      besselSeriesPairing (besselM0DualCoeffAction degree weight) vector := by
  ext coefficient
  rw [besselSeriesPairing_coeff, besselSeriesPairing_coeff]
  simp only [coeff_besselM0Action]
  exact besselPairing_M0_dual degree weight
    (fun index => PowerSeries.coeff coefficient (vector index))

theorem besselSeriesPairing_M0_signed
    (degree : ℕ) (scaleIndex : Fin (degree + 1))
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    besselSeriesPairing (besselSignedEigenvector degree scaleIndex)
        (besselM0Action degree vector) =
      PowerSeries.C (besselScaleEigenvalue degree scaleIndex) *
        besselSeriesPairing (besselSignedEigenvector degree scaleIndex) vector := by
  rw [besselSeriesPairing_M0_dual]
  have heigen := signedBesselPolynomial_dual_eigenvector
    degree scaleIndex.val (by omega)
  unfold besselSignedEigenvector at heigen ⊢
  unfold besselScaleEigenvalue
  rw [heigen]
  unfold besselSeriesPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  rw [map_mul]
  ring

theorem besselPairing_M1_dual
    (degree : ℕ) (weight vector : Fin (degree + 1) → ℚ) :
    besselPairing weight (besselM1CoeffAction degree vector) =
      besselPairing (besselM1CoeffAction degree weight) vector := by
  unfold besselPairing besselM1CoeffAction
  apply Finset.sum_congr rfl
  intro index hindex
  ring

theorem besselPairing_signedBasis_expansion
    (degree : ℕ) (weight vector : Fin (degree + 1) → ℚ) :
    besselPairing weight vector =
      ∑ scaleIndex,
        (besselSignedBasis degree).repr weight scaleIndex *
          besselPairing (besselSignedEigenvector degree scaleIndex) vector := by
  have hexpansion := (besselSignedBasis degree).sum_repr weight
  calc
    besselPairing weight vector =
        besselPairing
          (∑ scaleIndex,
            (besselSignedBasis degree).repr weight scaleIndex •
              besselSignedBasis degree scaleIndex) vector := by
          rw [hexpansion]
    _ = ∑ scaleIndex,
        (besselSignedBasis degree).repr weight scaleIndex *
          besselPairing (besselSignedBasis degree scaleIndex) vector := by
          unfold besselPairing
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro index _hindex
          ring
    _ = ∑ scaleIndex,
        (besselSignedBasis degree).repr weight scaleIndex *
          besselPairing (besselSignedEigenvector degree scaleIndex) vector := by
          apply Finset.sum_congr rfl
          intro scaleIndex _hscaleIndex
          rw [besselSignedBasis_apply]

noncomputable def besselSpectralM1
    (degree : ℕ) (scaleIndex target : Fin (degree + 1)) : ℚ :=
  (besselSignedBasis degree).repr
    (besselM1CoeffAction degree
      (besselSignedEigenvector degree scaleIndex)) target

theorem besselPairing_M1_spectral
    (degree : ℕ) (scaleIndex : Fin (degree + 1))
    (vector : Fin (degree + 1) → ℚ) :
    besselPairing (besselSignedEigenvector degree scaleIndex)
        (besselM1CoeffAction degree vector) =
      ∑ target, besselSpectralM1 degree scaleIndex target *
        besselPairing (besselSignedEigenvector degree target) vector := by
  rw [besselPairing_M1_dual]
  exact besselPairing_signedBasis_expansion degree
    (besselM1CoeffAction degree
      (besselSignedEigenvector degree scaleIndex)) vector

noncomputable def besselSpectralOrdinarySeries
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) : ℚ⟦X⟧ :=
  besselSeriesPairing (besselSignedEigenvector degree scaleIndex)
    (besselOrdinarySeries degree)

end FibonacciRibbonKernel
