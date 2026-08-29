import FibonacciRibbonKernel.FactorialCoefficientProduct

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators Classical

theorem besselSeriesPairing_factorialCoeff
    (degree coefficient : ℕ) (weight : Fin (degree + 1) → ℚ) :
    besselPairing weight (besselFactorialCoeff degree coefficient) =
      factorialScaledCoeffQ
        (besselSeriesPairing weight (besselBasisVector degree)) coefficient := by
  unfold factorialScaledCoeffQ besselFactorialCoeff
  rw [besselPairing_scalar_apply, besselSeriesPairing_coeff]

theorem besselSpectralFactorialCoeff_eq_signed_product
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) :
    besselSpectralFactorialCoeff degree coefficient scaleIndex =
      factorialScaledCoeffQ
        ((besselJ0 + besselJ1) ^ (degree - scaleIndex.val) *
          (besselJ0 - besselJ1) ^ scaleIndex.val) coefficient := by
  unfold besselSpectralFactorialCoeff
  rw [besselSeriesPairing_factorialCoeff,
    besselSeriesPairing_signed_factorization]

theorem besselSeriesPairing_oddBasis_signed_factorization
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    besselSeriesPairing (besselSignedEigenvector degree scaleIndex)
        (oddBesselBasisVector degree) =
      PowerSeries.exp ℚ *
        ((besselJ0 + besselJ1) ^ (degree - scaleIndex.val) *
          (besselJ0 - besselJ1) ^ scaleIndex.val) := by
  rw [← besselSeriesPairing_signed_factorization]
  unfold oddBesselBasisVector besselSeriesPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  ring

theorem oddBesselSeriesPairing_factorialCoeff
    (degree coefficient : ℕ) (weight : Fin (degree + 1) → ℚ) :
    besselPairing weight (oddBesselFactorialCoeff degree coefficient) =
      factorialScaledCoeffQ
        (besselSeriesPairing weight (oddBesselBasisVector degree)) coefficient := by
  unfold factorialScaledCoeffQ oddBesselFactorialCoeff
  rw [besselPairing_scalar_apply, besselSeriesPairing_coeff]

theorem oddBesselSpectralFactorialCoeff_eq_signed_product
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) :
    oddBesselSpectralFactorialCoeff degree coefficient scaleIndex =
      factorialScaledCoeffQ
        (PowerSeries.exp ℚ *
          ((besselJ0 + besselJ1) ^ (degree - scaleIndex.val) *
            (besselJ0 - besselJ1) ^ scaleIndex.val)) coefficient := by
  unfold oddBesselSpectralFactorialCoeff
  rw [oddBesselSeriesPairing_factorialCoeff,
    besselSeriesPairing_oddBasis_signed_factorization]

theorem factorialScaledCoeffQ_exp (coefficient : ℕ) :
    factorialScaledCoeffQ (PowerSeries.exp ℚ) coefficient = 1 := by
  unfold factorialScaledCoeffQ
  rw [PowerSeries.coeff_exp]
  have hfactorial : (coefficient.factorial : ℚ) ≠ 0 := by positivity
  change (coefficient.factorial : ℚ) *
    (1 / (coefficient.factorial : ℚ)) = 1
  simpa only [one_div] using mul_inv_cancel₀ hfactorial

end FibonacciRibbonKernel
