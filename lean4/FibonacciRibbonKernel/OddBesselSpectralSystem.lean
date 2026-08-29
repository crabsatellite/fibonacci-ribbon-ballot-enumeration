import FibonacciRibbonKernel.BesselSpectralSystem

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators Classical

def oddBesselScaleEigenvalue
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) : ℚ :=
  2 * degree + 1 - 4 * scaleIndex.val

theorem besselSeriesPairing_oddM0_signed
    (degree : ℕ) (scaleIndex : Fin (degree + 1))
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    besselSeriesPairing (besselSignedEigenvector degree scaleIndex)
        (oddBesselM0Action degree vector) =
      PowerSeries.C (oddBesselScaleEigenvalue degree scaleIndex) *
        besselSeriesPairing (besselSignedEigenvector degree scaleIndex) vector := by
  unfold oddBesselM0Action
  rw [besselSeriesPairing_add, besselSeriesPairing_M0_signed]
  unfold oddBesselScaleEigenvalue besselScaleEigenvalue
  calc
    _ = ((1 : ℚ⟦X⟧) +
          PowerSeries.C ((2 : ℚ) * degree - 4 * scaleIndex.val)) *
        besselSeriesPairing (besselSignedEigenvector degree scaleIndex) vector := by
      rw [add_mul, one_mul]
    _ = PowerSeries.C ((1 : ℚ) + ((2 : ℚ) * degree - 4 * scaleIndex.val)) *
        besselSeriesPairing (besselSignedEigenvector degree scaleIndex) vector := by
      rw [map_add, map_one]
    _ = _ := by
      rw [show (1 : ℚ) + ((2 : ℚ) * degree - 4 * scaleIndex.val) =
        2 * degree + 1 - 4 * scaleIndex.val by ring]

noncomputable def oddBesselSpectralOrdinarySeries
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) : ℚ⟦X⟧ :=
  besselSeriesPairing (besselSignedEigenvector degree scaleIndex)
    (oddBesselOrdinarySeries degree)

noncomputable def oddBesselSpectralInitialM1
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) : ℚ :=
  besselPairing (besselSignedEigenvector degree scaleIndex)
    (besselM1CoeffAction degree (oddBesselFactorialCoeff degree 0))

theorem odd_bessel_spectral_ordinary_system
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    let spectral := oddBesselSpectralOrdinarySeries degree
    let eigenvalue := oddBesselScaleEigenvalue degree scaleIndex
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
        PowerSeries.C (oddBesselSpectralInitialM1 degree scaleIndex) := by
  dsimp only
  let weight := besselSignedEigenvector degree scaleIndex
  let vector := oddBesselOrdinarySeries degree
  have hsystem :
      (fun index : Fin (degree + 1) =>
        PowerSeries.X *
          (PowerSeries.derivative ℚ (vector index) -
            PowerSeries.X * oddBesselM0Action degree
              (fun coordinate => PowerSeries.derivative ℚ (vector coordinate)) index)) =
      (fun index : Fin (degree + 1) =>
        (besselM1Action degree vector index +
          PowerSeries.X * oddBesselM0Action degree vector index) -
        PowerSeries.C
          (besselM1CoeffAction degree (oddBesselFactorialCoeff degree 0) index)) := by
    funext index
    exact odd_bessel_ordinary_system degree index
  have hpaired := congrArg (besselSeriesPairing weight) hsystem
  have hderivative :
      besselSeriesPairing weight
          (fun index => PowerSeries.derivative ℚ (vector index)) =
        PowerSeries.derivative ℚ
          (oddBesselSpectralOrdinarySeries degree scaleIndex) := by
    exact besselSeriesPairing_derivative weight vector
  have hM0Derivative :
      besselSeriesPairing weight
          (oddBesselM0Action degree
            (fun index => PowerSeries.derivative ℚ (vector index))) =
        PowerSeries.C (oddBesselScaleEigenvalue degree scaleIndex) *
          PowerSeries.derivative ℚ
            (oddBesselSpectralOrdinarySeries degree scaleIndex) := by
    rw [besselSeriesPairing_oddM0_signed]
    rw [besselSeriesPairing_derivative]
    unfold oddBesselSpectralOrdinarySeries
    rfl
  have hM0 :
      besselSeriesPairing weight (oddBesselM0Action degree vector) =
        PowerSeries.C (oddBesselScaleEigenvalue degree scaleIndex) *
          oddBesselSpectralOrdinarySeries degree scaleIndex :=
    besselSeriesPairing_oddM0_signed degree scaleIndex vector
  have hM1 :
      besselSeriesPairing weight (besselM1Action degree vector) =
        ∑ target,
          PowerSeries.C (besselSpectralM1 degree scaleIndex target) *
            oddBesselSpectralOrdinarySeries degree target :=
    besselSeriesPairing_M1_spectral degree scaleIndex vector
  have hXM0Derivative :
      besselSeriesPairing weight
          (fun index => PowerSeries.X *
            oddBesselM0Action degree
              (fun coordinate => PowerSeries.derivative ℚ (vector coordinate)) index) =
        PowerSeries.X *
          (PowerSeries.C (oddBesselScaleEigenvalue degree scaleIndex) *
            PowerSeries.derivative ℚ
              (oddBesselSpectralOrdinarySeries degree scaleIndex)) := by
    calc
      _ = PowerSeries.X * besselSeriesPairing weight
          (oddBesselM0Action degree
            (fun coordinate => PowerSeries.derivative ℚ (vector coordinate))) :=
        besselSeriesPairing_X_mul weight _
      _ = _ := by rw [hM0Derivative]
  have hXM0 :
      besselSeriesPairing weight
          (fun index => PowerSeries.X * oddBesselM0Action degree vector index) =
        PowerSeries.X *
          (PowerSeries.C (oddBesselScaleEigenvalue degree scaleIndex) *
            oddBesselSpectralOrdinarySeries degree scaleIndex) := by
    calc
      _ = PowerSeries.X *
          besselSeriesPairing weight (oddBesselM0Action degree vector) :=
        besselSeriesPairing_X_mul weight _
      _ = _ := by rw [hM0]
  have hinitial :
      besselSeriesPairing weight
          (fun index => PowerSeries.C
            (besselM1CoeffAction degree (oddBesselFactorialCoeff degree 0) index)) =
        PowerSeries.C (oddBesselSpectralInitialM1 degree scaleIndex) := by
    exact besselSeriesPairing_constant weight
      (besselM1CoeffAction degree (oddBesselFactorialCoeff degree 0))
  dsimp only [weight, vector] at hpaired hderivative hM0Derivative hM0 hM1 hXM0Derivative hXM0 hinitial
  simp_rw [besselSeriesPairing_X_mul, besselSeriesPairing_sub,
    besselSeriesPairing_add] at hpaired
  rw [hderivative, hXM0Derivative, hM1, hXM0, hinitial] at hpaired
  linear_combination hpaired

end FibonacciRibbonKernel
