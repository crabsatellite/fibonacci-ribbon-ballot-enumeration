import FibonacciRibbonKernel.HeightFourRibbonDifferential

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def heightFourRibbonCoefficientA : ℤ⟦X⟧ :=
  X ^ 10 - 14 * X ^ 8 + 14 * X ^ 4 - X ^ 2

noncomputable def heightFourRibbonCoefficientC : ℤ⟦X⟧ :=
  -2 * X ^ 9 + 8 * X ^ 8 - 30 * X ^ 7 - 8 * X ^ 6 +
    34 * X ^ 5 - 8 * X ^ 4 + 54 * X ^ 3 + 8 * X ^ 2 - 8 * X

noncomputable def heightFourRibbonCoefficientD : ℤ⟦X⟧ :=
  2 * X ^ 8 - 4 * X ^ 7 - 14 * X ^ 6 + 28 * X ^ 5 +
    34 * X ^ 4 - 44 * X ^ 3 + 38 * X ^ 2 + 20 * X - 12

noncomputable def heightFourRibbonForcing : ℤ⟦X⟧ :=
  12 * (1 - X ^ 2) ^ 3

noncomputable def heightFourRibbonHomogeneousOperator
    (series : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  let derivativeOne := PowerSeries.derivative ℤ series
  let derivativeTwo := PowerSeries.derivative ℤ derivativeOne
  let derivativeThree := PowerSeries.derivative ℤ derivativeTwo
  let forcingDerivative := PowerSeries.derivative ℤ heightFourRibbonForcing
  let coefficientADerivative := PowerSeries.derivative ℤ heightFourRibbonCoefficientA
  let coefficientCDerivative := PowerSeries.derivative ℤ heightFourRibbonCoefficientC
  let coefficientDDerivative := PowerSeries.derivative ℤ heightFourRibbonCoefficientD
  heightFourRibbonForcing * heightFourRibbonCoefficientA * derivativeThree +
    (heightFourRibbonForcing *
          (coefficientADerivative + heightFourRibbonCoefficientC) -
        forcingDerivative * heightFourRibbonCoefficientA) * derivativeTwo +
    (heightFourRibbonForcing *
          (coefficientCDerivative + heightFourRibbonCoefficientD) -
        forcingDerivative * heightFourRibbonCoefficientC) * derivativeOne +
    (heightFourRibbonForcing * coefficientDDerivative -
        forcingDerivative * heightFourRibbonCoefficientD) * series

/-- A homogeneous third-order polynomial differential equation for the actual
four-letter ribbon OGF.  All coefficient series are explicit polynomials, so
this is a literal D-finite certificate. -/
theorem ribbonGeneratingSeries_three_homogeneous_differential :
    heightFourRibbonHomogeneousOperator (ribbonGeneratingSeries 3) = 0 := by
  let series := ribbonGeneratingSeries 3
  let derivativeOne := PowerSeries.derivative ℤ series
  let derivativeTwo := PowerSeries.derivative ℤ derivativeOne
  let derivativeThree := PowerSeries.derivative ℤ derivativeTwo
  have hzero := ribbonGeneratingSeries_three_differential
  unfold heightFourRibbonOrdinaryOperator at hzero
  change heightFourRibbonCoefficientA * derivativeTwo +
      heightFourRibbonCoefficientC * derivativeOne +
      heightFourRibbonCoefficientD * series +
      heightFourRibbonForcing = 0 at hzero
  have hone := congrArg (PowerSeries.derivative ℤ) hzero
  simp only [map_add, map_zero, Derivation.leibniz, smul_eq_mul] at hone
  unfold heightFourRibbonHomogeneousOperator
  dsimp only [series, derivativeOne, derivativeTwo, derivativeThree]
  linear_combination
    heightFourRibbonForcing * hone -
      (PowerSeries.derivative ℤ heightFourRibbonForcing) * hzero

end FibonacciRibbonKernel
