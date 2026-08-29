import FibonacciRibbonKernel.GeneralExteriorTruncation

namespace FibonacciRibbonKernel

open PowerSeries

theorem scalarTruncationEquivalent_coeff
    {cutoff : ℕ} {left right : ℚ⟦X⟧}
    (h : ScalarTruncationEquivalent cutoff left right)
    (degree : ℕ) (hdegree : degree < cutoff) :
    PowerSeries.coeff degree left = PowerSeries.coeff degree right := by
  unfold ScalarTruncationEquivalent at h
  have hcoeff := congrArg (fun polynomial : Polynomial ℚ =>
    polynomial.coeff degree) h
  simpa [PowerSeries.coeff_trunc, hdegree] using hcoeff

theorem generalExteriorTruncation_self_coeff_eq_strictMinor
    (rank degree : ℕ) :
    PowerSeries.coeff degree
        (generalExteriorTruncation (rank + 1) (degree + 1)) =
      PowerSeries.coeff degree (generalStrictMinorSeries rank) := by
  by_cases hshift : staircaseWeight rank ≤ degree
  · let size := degree - staircaseWeight rank
    have hdegreeEq : degree = size + staircaseWeight rank := by
      dsimp only [size]
      omega
    rw [hdegreeEq]
    rw [generalExteriorTruncation_coeff_eq_unrestricted_of_bound
      rank size (size + staircaseWeight rank + 1) (by omega)]
    rw [generalStrictMinorSeries_coeff_shifted]
  · have hdegree : degree < staircaseWeight rank := by omega
    rw [generalExteriorTruncation_coeff_eq_zero_of_lt_staircase
      rank (degree + 1) degree hdegree]
    rw [generalStrictMinorSeries_coeff, if_neg hshift]

theorem generalExteriorTruncation_self_coeff_eq_strictMinor_mul_factorial
    (rank factor degree : ℕ) :
    PowerSeries.coeff degree
        ((factor.factorial : ℚ⟦X⟧) *
          generalExteriorTruncation (rank + 1) (degree + 1)) =
      PowerSeries.coeff degree
        ((factor.factorial : ℚ⟦X⟧) *
          generalStrictMinorSeries rank) := by
  rw [show (factor.factorial : ℚ⟦X⟧) =
      PowerSeries.C (factor.factorial : ℚ) by
        exact (map_natCast PowerSeries.C factor.factorial).symm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    generalExteriorTruncation_self_coeff_eq_strictMinor]

/-- Complete arbitrary-even-rank closed Bessel/Pfaffian bridge. -/
theorem generalStrictMinorSeries_even_eq_closed
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    (halfDimension.factorial : ℚ⟦X⟧) *
        generalStrictMinorSeries (2 * halfDimension - 1) =
      generalClosedEvenAssembly halfDimension := by
  ext degree
  let bound := degree + 1
  have hcoordinate := generalExteriorTruncation_even_coordinate_assembly
    halfDimension bound
  have hdimension : 2 * halfDimension - 1 + 1 = 2 * halfDimension := by omega
  have hcoordinate' :
      (halfDimension.factorial : ℚ⟦X⟧) *
          generalExteriorTruncation (2 * halfDimension - 1 + 1) bound =
        generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension)
          (generalTwoForm (fun i j : Fin (2 * halfDimension) =>
            generalPairSum (generalFactorialRows (2 * halfDimension) bound) i j) ^
              halfDimension) := by
    simpa [hdimension] using hcoordinate
  have hclosed := generalEvenAssembly_truncationEquivalent_closed
    halfDimension (degree + 1) bound (by rfl)
  have hfiniteCoeff := scalarTruncationEquivalent_coeff hclosed degree (by omega)
  rw [← hfiniteCoeff, ← hcoordinate']
  exact (generalExteriorTruncation_self_coeff_eq_strictMinor_mul_factorial
    (2 * halfDimension - 1) halfDimension degree).symm

/-- Complete arbitrary-odd-rank closed Bessel/bordered-Pfaffian bridge. -/
theorem generalStrictMinorSeries_odd_eq_closed (halfDimension : ℕ) :
    (halfDimension.factorial : ℚ⟦X⟧) *
        generalStrictMinorSeries (2 * halfDimension) =
      generalClosedOddAssembly halfDimension := by
  ext degree
  let bound := degree + 1
  have hcoordinate := generalExteriorTruncation_odd_coordinate_assembly
    halfDimension bound
  have hclosed := generalOddAssembly_truncationEquivalent_closed
    halfDimension (degree + 1) bound (by rfl)
  have hfiniteCoeff := scalarTruncationEquivalent_coeff hclosed degree (by omega)
  rw [← hfiniteCoeff, ← hcoordinate]
  exact (generalExteriorTruncation_self_coeff_eq_strictMinor_mul_factorial
    (2 * halfDimension) halfDimension degree).symm

theorem generalUnrestrictedFactorialSeries_even_closed
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    (halfDimension.factorial : ℚ⟦X⟧) *
        (X ^ staircaseWeight (2 * halfDimension - 1) *
          generalUnrestrictedFactorialSeries (2 * halfDimension - 1)) =
      generalClosedEvenAssembly halfDimension := by
  rw [X_staircase_mul_generalUnrestrictedFactorialSeries]
  exact generalStrictMinorSeries_even_eq_closed halfDimension hhalf

theorem generalUnrestrictedFactorialSeries_odd_closed
    (halfDimension : ℕ) :
    (halfDimension.factorial : ℚ⟦X⟧) *
        (X ^ staircaseWeight (2 * halfDimension) *
          generalUnrestrictedFactorialSeries (2 * halfDimension)) =
      generalClosedOddAssembly halfDimension := by
  rw [X_staircase_mul_generalUnrestrictedFactorialSeries]
  exact generalStrictMinorSeries_odd_eq_closed halfDimension

end FibonacciRibbonKernel
