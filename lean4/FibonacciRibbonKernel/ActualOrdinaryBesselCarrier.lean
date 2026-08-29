import FibonacciRibbonKernel.OddOrdinaryBesselRepresentation

namespace FibonacciRibbonKernel

open PowerSeries

inductive OrdinaryBesselLaurentGenerated : ℕ → ℚ⟦X⟧ → Prop
  | direct {degree : ℕ} {value : ℚ⟦X⟧} :
      OrdinaryBesselGenerated degree value →
      OrdinaryBesselLaurentGenerated degree value
  | inverseShift (degree amount : ℕ) {value : ℚ⟦X⟧} :
      OrdinaryBesselGenerated degree
        (PowerSeries.X ^ amount * risingEulerApply amount value) →
      OrdinaryBesselLaurentGenerated degree value

inductive OddOrdinaryBesselLaurentGenerated : ℕ → ℚ⟦X⟧ → Prop
  | direct {degree : ℕ} {value : ℚ⟦X⟧} :
      OddOrdinaryBesselGenerated degree value →
      OddOrdinaryBesselLaurentGenerated degree value
  | inverseShift (degree amount : ℕ) {value : ℚ⟦X⟧} :
      OddOrdinaryBesselGenerated degree
        (PowerSeries.X ^ amount * risingEulerApply amount value) →
      OddOrdinaryBesselLaurentGenerated degree value

theorem actualEvenOrdinary_besselLaurentGenerated
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    OrdinaryBesselLaurentGenerated halfDimension
      (generalUnrestrictedOrdinarySeriesQ (2 * halfDimension - 1)) := by
  have hgenerated := actualEvenShiftedOrdinary_besselGenerated
    halfDimension hhalf
  rw [factorialUnscale_X_pow_mul,
    factorialUnscale_generalUnrestrictedFactorialSeries] at hgenerated
  exact OrdinaryBesselLaurentGenerated.inverseShift halfDimension
    (staircaseWeight (2 * halfDimension - 1)) hgenerated

theorem actualOddOrdinary_besselLaurentGenerated
    (halfDimension : ℕ) :
    OddOrdinaryBesselLaurentGenerated halfDimension
      (generalUnrestrictedOrdinarySeriesQ (2 * halfDimension)) := by
  have hgenerated := actualOddShiftedOrdinary_besselGenerated halfDimension
  rw [factorialUnscale_X_pow_mul,
    factorialUnscale_generalUnrestrictedFactorialSeries] at hgenerated
  exact OddOrdinaryBesselLaurentGenerated.inverseShift halfDimension
    (staircaseWeight (2 * halfDimension)) hgenerated

end FibonacciRibbonKernel
