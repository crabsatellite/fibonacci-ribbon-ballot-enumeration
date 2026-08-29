import FibonacciRibbonKernel.BesselSpectralCoordinates

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators Classical

theorem besselSeriesPairing_M1_spectral
    (degree : ℕ) (scaleIndex : Fin (degree + 1))
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    besselSeriesPairing (besselSignedEigenvector degree scaleIndex)
        (besselM1Action degree vector) =
      ∑ target,
        PowerSeries.C (besselSpectralM1 degree scaleIndex target) *
          besselSeriesPairing (besselSignedEigenvector degree target) vector := by
  ext coefficient
  rw [besselSeriesPairing_coeff, map_sum]
  simp only [coeff_besselM1Action, PowerSeries.coeff_C_mul,
    besselSeriesPairing_coeff]
  exact besselPairing_M1_spectral degree scaleIndex
    (fun index => PowerSeries.coeff coefficient (vector index))

theorem besselSeriesPairing_constant
    {degree : ℕ} (weight vector : Fin (degree + 1) → ℚ) :
    besselSeriesPairing weight (fun index => PowerSeries.C (vector index)) =
      PowerSeries.C (besselPairing weight vector) := by
  ext coefficient
  rw [besselSeriesPairing_coeff]
  unfold besselPairing
  by_cases hcoefficient : coefficient = 0
  · subst coefficient
    simp
  · simp [PowerSeries.coeff_C, hcoefficient]

noncomputable def besselSpectralInitialM1
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) : ℚ :=
  besselPairing (besselSignedEigenvector degree scaleIndex)
    (besselM1CoeffAction degree (besselFactorialCoeff degree 0))

theorem bessel_spectral_ordinary_system
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    let spectral := besselSpectralOrdinarySeries degree
    let eigenvalue := besselScaleEigenvalue degree scaleIndex
    PowerSeries.X *
        (PowerSeries.derivative ℚ (spectral scaleIndex) -
          PowerSeries.X *
            (PowerSeries.C eigenvalue *
              PowerSeries.derivative ℚ (spectral scaleIndex))) =
      ((∑ target,
          PowerSeries.C (besselSpectralM1 degree scaleIndex target) *
            spectral target) +
        PowerSeries.X *
          (PowerSeries.C eigenvalue * spectral scaleIndex)) -
        PowerSeries.C (besselSpectralInitialM1 degree scaleIndex) := by
  dsimp only
  let weight := besselSignedEigenvector degree scaleIndex
  let vector := besselOrdinarySeries degree
  have hsystem :
      (fun index : Fin (degree + 1) =>
        PowerSeries.X *
          (PowerSeries.derivative ℚ (vector index) -
            PowerSeries.X * besselM0Action degree
              (fun coordinate => PowerSeries.derivative ℚ (vector coordinate)) index)) =
      (fun index : Fin (degree + 1) =>
        (besselM1Action degree vector index +
          PowerSeries.X * besselM0Action degree vector index) -
        PowerSeries.C
          (besselM1CoeffAction degree (besselFactorialCoeff degree 0) index)) := by
    funext index
    exact bessel_ordinary_system degree index
  have hpaired := congrArg (besselSeriesPairing weight) hsystem
  have hderivative :
      besselSeriesPairing weight
          (fun index => PowerSeries.derivative ℚ (vector index)) =
        PowerSeries.derivative ℚ
          (besselSpectralOrdinarySeries degree scaleIndex) := by
    exact besselSeriesPairing_derivative weight vector
  have hM0Derivative :
      besselSeriesPairing weight
          (besselM0Action degree
            (fun index => PowerSeries.derivative ℚ (vector index))) =
        PowerSeries.C (besselScaleEigenvalue degree scaleIndex) *
          PowerSeries.derivative ℚ
            (besselSpectralOrdinarySeries degree scaleIndex) := by
    rw [besselSeriesPairing_M0_signed]
    rw [besselSeriesPairing_derivative]
    unfold besselSpectralOrdinarySeries
    rfl
  have hM0 :
      besselSeriesPairing weight (besselM0Action degree vector) =
        PowerSeries.C (besselScaleEigenvalue degree scaleIndex) *
          besselSpectralOrdinarySeries degree scaleIndex :=
    besselSeriesPairing_M0_signed degree scaleIndex vector
  have hM1 :
      besselSeriesPairing weight (besselM1Action degree vector) =
        ∑ target,
          PowerSeries.C (besselSpectralM1 degree scaleIndex target) *
            besselSpectralOrdinarySeries degree target :=
    besselSeriesPairing_M1_spectral degree scaleIndex vector
  have hXM0Derivative :
      besselSeriesPairing weight
          (fun index => PowerSeries.X *
            besselM0Action degree
              (fun coordinate => PowerSeries.derivative ℚ (vector coordinate)) index) =
        PowerSeries.X *
          (PowerSeries.C (besselScaleEigenvalue degree scaleIndex) *
            PowerSeries.derivative ℚ
              (besselSpectralOrdinarySeries degree scaleIndex)) := by
    calc
      _ = PowerSeries.X * besselSeriesPairing weight
          (besselM0Action degree
            (fun coordinate => PowerSeries.derivative ℚ (vector coordinate))) :=
        besselSeriesPairing_X_mul weight _
      _ = _ := by rw [hM0Derivative]
  have hXM0 :
      besselSeriesPairing weight
          (fun index => PowerSeries.X * besselM0Action degree vector index) =
        PowerSeries.X *
          (PowerSeries.C (besselScaleEigenvalue degree scaleIndex) *
            besselSpectralOrdinarySeries degree scaleIndex) := by
    calc
      _ = PowerSeries.X *
          besselSeriesPairing weight (besselM0Action degree vector) :=
        besselSeriesPairing_X_mul weight _
      _ = _ := by rw [hM0]
  have hinitial :
      besselSeriesPairing weight
          (fun index => PowerSeries.C
            (besselM1CoeffAction degree (besselFactorialCoeff degree 0) index)) =
        PowerSeries.C (besselSpectralInitialM1 degree scaleIndex) := by
    exact besselSeriesPairing_constant weight
      (besselM1CoeffAction degree (besselFactorialCoeff degree 0))
  dsimp only [weight, vector] at hpaired hderivative hM0Derivative hM0 hM1 hXM0Derivative hXM0 hinitial
  simp_rw [besselSeriesPairing_X_mul, besselSeriesPairing_sub,
    besselSeriesPairing_add] at hpaired
  rw [hderivative, hXM0Derivative, hM1, hXM0, hinitial] at hpaired
  linear_combination hpaired

end FibonacciRibbonKernel
