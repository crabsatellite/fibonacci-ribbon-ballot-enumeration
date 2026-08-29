import FibonacciRibbonKernel.OddBesselSpectralSystem

namespace FibonacciRibbonKernel

open scoped BigOperators Classical

theorem besselPairing_sub_apply
    {degree : ℕ} (weight : Fin (degree + 1) → ℚ)
    (left right : Fin (degree + 1) → ℚ) :
    besselPairing weight (fun index => left index - right index) =
      besselPairing weight left - besselPairing weight right := by
  unfold besselPairing
  simp_rw [mul_sub, Finset.sum_sub_distrib]

theorem besselPairing_scalar_apply
    {degree : ℕ} (weight : Fin (degree + 1) → ℚ)
    (scalar : ℚ) (vector : Fin (degree + 1) → ℚ) :
    besselPairing weight (fun index => scalar * vector index) =
      scalar * besselPairing weight vector := by
  unfold besselPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  ring

noncomputable def besselSpectralFactorialCoeff
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) : ℚ :=
  besselPairing (besselSignedEigenvector degree scaleIndex)
    (besselFactorialCoeff degree coefficient)

noncomputable def oddBesselSpectralFactorialCoeff
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) : ℚ :=
  besselPairing (besselSignedEigenvector degree scaleIndex)
    (oddBesselFactorialCoeff degree coefficient)

theorem bessel_spectral_factorial_coefficient_recurrence
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) :
    (coefficient : ℚ) *
          besselSpectralFactorialCoeff degree coefficient scaleIndex -
        ∑ target,
          besselSpectralM1 degree scaleIndex target *
            besselSpectralFactorialCoeff degree coefficient target =
      (coefficient : ℚ) * besselScaleEigenvalue degree scaleIndex *
        besselSpectralFactorialCoeff degree (coefficient - 1) scaleIndex := by
  let weight := besselSignedEigenvector degree scaleIndex
  let current := besselFactorialCoeff degree coefficient
  let previous := besselFactorialCoeff degree (coefficient - 1)
  have hcomponent :
      (fun index : Fin (degree + 1) =>
        (coefficient : ℚ) * current index -
          besselM1CoeffAction degree current index) =
      (fun index : Fin (degree + 1) =>
        (coefficient : ℚ) * besselM0CoeffAction degree previous index) := by
    funext index
    exact bessel_factorial_coefficient_recurrence degree coefficient index
  have hpaired := congrArg (besselPairing weight) hcomponent
  rw [besselPairing_sub_apply, besselPairing_scalar_apply,
    besselPairing_scalar_apply] at hpaired
  rw [besselPairing_M1_spectral,
    besselPairing_M0_signed] at hpaired
  dsimp only [weight, current, previous] at hpaired
  unfold besselSpectralFactorialCoeff
  simpa only [mul_assoc] using hpaired

theorem besselPairing_oddM0_signed_coeff
    (degree : ℕ) (scaleIndex : Fin (degree + 1))
    (vector : Fin (degree + 1) → ℚ) :
    besselPairing (besselSignedEigenvector degree scaleIndex)
        (oddBesselM0CoeffAction degree vector) =
      oddBesselScaleEigenvalue degree scaleIndex *
        besselPairing (besselSignedEigenvector degree scaleIndex) vector := by
  unfold oddBesselM0CoeffAction
  rw [show besselPairing (besselSignedEigenvector degree scaleIndex)
      (fun index => vector index + besselM0CoeffAction degree vector index) =
      besselPairing (besselSignedEigenvector degree scaleIndex) vector +
        besselPairing (besselSignedEigenvector degree scaleIndex)
          (besselM0CoeffAction degree vector) by
    unfold besselPairing
    simp_rw [mul_add, Finset.sum_add_distrib]]
  rw [besselPairing_M0_signed]
  unfold oddBesselScaleEigenvalue besselScaleEigenvalue
  ring

theorem odd_bessel_spectral_factorial_coefficient_recurrence
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) :
    (coefficient : ℚ) *
          oddBesselSpectralFactorialCoeff degree coefficient scaleIndex -
        ∑ target,
          besselSpectralM1 degree scaleIndex target *
            oddBesselSpectralFactorialCoeff degree coefficient target =
      (coefficient : ℚ) * oddBesselScaleEigenvalue degree scaleIndex *
        oddBesselSpectralFactorialCoeff degree (coefficient - 1) scaleIndex := by
  let weight := besselSignedEigenvector degree scaleIndex
  let current := oddBesselFactorialCoeff degree coefficient
  let previous := oddBesselFactorialCoeff degree (coefficient - 1)
  have hcomponent :
      (fun index : Fin (degree + 1) =>
        (coefficient : ℚ) * current index -
          besselM1CoeffAction degree current index) =
      (fun index : Fin (degree + 1) =>
        (coefficient : ℚ) * oddBesselM0CoeffAction degree previous index) := by
    funext index
    exact odd_bessel_factorial_coefficient_recurrence degree coefficient index
  have hpaired := congrArg (besselPairing weight) hcomponent
  rw [besselPairing_sub_apply, besselPairing_scalar_apply,
    besselPairing_scalar_apply] at hpaired
  rw [besselPairing_M1_spectral,
    besselPairing_oddM0_signed_coeff] at hpaired
  dsimp only [weight, current, previous] at hpaired
  unfold oddBesselSpectralFactorialCoeff
  simpa only [mul_assoc] using hpaired

end FibonacciRibbonKernel
