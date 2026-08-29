import FibonacciRibbonKernel.BorelOperatorNonzero

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

theorem EulerOperatorDFinite.factorialUnscale
    {series : ℚ⟦X⟧} (hfinite : EulerOperatorDFinite series) :
    EulerOperatorDFinite (factorialUnscale series) := by
  obtain ⟨operator, hoperator, hrelation⟩ := hfinite
  refine ⟨borelOperatorTransform operator,
    borelOperatorTransform_ne_zero hoperator, ?_⟩
  rw [← factorialUnscale_eulerOperatorApply, hrelation]
  ext degree
  simp [factorialUnscale_coeff]

theorem EulerDFinite.factorialUnscale
    {series : ℚ⟦X⟧} (hfinite : EulerDFinite series) :
    EulerDFinite (factorialUnscale series) := by
  rw [eulerDFinite_iff_operator] at hfinite ⊢
  exact EulerOperatorDFinite.factorialUnscale hfinite

theorem generalUnrestrictedFactorialSeries_eulerDFinite (rank : ℕ) :
    EulerDFinite (generalUnrestrictedFactorialSeries rank) := by
  obtain ⟨halfDimension, hrank | hrank⟩ := Nat.even_or_odd' rank
  · subst rank
    exact generalUnrestrictedFactorialSeries_odd_eulerDFinite halfDimension
  · subst rank
    have hhalf : 1 ≤ halfDimension + 1 := by omega
    have hindex :
        2 * (halfDimension + 1) - 1 = 2 * halfDimension + 1 := by omega
    rw [← hindex]
    exact generalUnrestrictedFactorialSeries_even_eulerDFinite
      (halfDimension + 1) hhalf

/-- Every fixed-rank unrestricted ordinary generating series is D-finite.
This is the premise-free EGF-to-OGF transport required by the manuscript. -/
theorem generalUnrestrictedOrdinarySeriesQ_eulerDFinite (rank : ℕ) :
    EulerDFinite (generalUnrestrictedOrdinarySeriesQ rank) := by
  rw [← factorialUnscale_generalUnrestrictedFactorialSeries]
  exact (generalUnrestrictedFactorialSeries_eulerDFinite rank).factorialUnscale

theorem unrestrictedGeneratingSeries_map_rat (rank : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ)
        (unrestrictedGeneratingSeries rank) =
      generalUnrestrictedOrdinarySeriesQ rank := by
  ext degree
  simp [generalUnrestrictedOrdinarySeriesQ_coeff,
    unrestrictedGeneratingSeries_coeff]

end FibonacciRibbonKernel
