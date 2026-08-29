import FibonacciRibbonKernel.GeneralExteriorMinor

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

/-- Uniform strict-minor series in arbitrary rank.  Its degree includes the
staircase shift, exactly as in the rank-4/5/6 exterior constructions. -/
noncomputable def generalStrictMinorSeries (rank : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if staircaseWeight rank ≤ degree then
      ∑ tuple : StrictShiftedTuple rank (degree - staircaseWeight rank),
        Matrix.det (generalFactorialScalarMatrix tuple.values)
    else 0

@[simp] theorem generalStrictMinorSeries_coeff
    (rank degree : ℕ) :
    PowerSeries.coeff degree (generalStrictMinorSeries rank) =
      if staircaseWeight rank ≤ degree then
        ∑ tuple : StrictShiftedTuple rank (degree - staircaseWeight rank),
          Matrix.det (generalFactorialScalarMatrix tuple.values)
      else 0 := by
  simp [generalStrictMinorSeries]

/-- Arbitrary-rank Frobenius minor bridge: after the literal staircase shift,
the actual bounded-tableau factorial EGF is the strict determinant series. -/
theorem X_staircase_mul_generalUnrestrictedFactorialSeries
    (rank : ℕ) :
    X ^ staircaseWeight rank * generalUnrestrictedFactorialSeries rank =
      generalStrictMinorSeries rank := by
  ext degree
  rw [PowerSeries.coeff_X_pow_mul', generalStrictMinorSeries_coeff]
  by_cases hdegree : staircaseWeight rank ≤ degree
  · rw [if_pos hdegree, if_pos hdegree]
    rw [generalUnrestrictedFactorialSeries_coeff_eq_strictShifted]
  · rw [if_neg hdegree, if_neg hdegree]

theorem generalStrictMinorSeries_coeff_shifted
    (rank size : ℕ) :
    PowerSeries.coeff (size + staircaseWeight rank)
        (generalStrictMinorSeries rank) =
      (unrestrictedCount rank size : ℚ) / (size.factorial : ℚ) := by
  rw [generalStrictMinorSeries_coeff,
    if_pos (by omega : staircaseWeight rank ≤
      size + staircaseWeight rank)]
  rw [show size + staircaseWeight rank - staircaseWeight rank = size by omega]
  exact (unrestrictedCount_div_factorial_eq_sum_strictShifted rank size).symm

end FibonacciRibbonKernel
