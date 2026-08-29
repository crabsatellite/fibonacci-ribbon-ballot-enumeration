import FibonacciRibbonKernel.OddAssemblyHomogeneousBessel

namespace FibonacciRibbonKernel

open PowerSeries

/-!
# Actual unrestricted EGF in the homogeneous Bessel modules

The Pfaffian assemblies are now transported back to the literal unrestricted
factorial series.  The staircase monomial is retained exactly; it will become
the finite Euler/shift operator under factorial unscaling.
-/

theorem generalUnrestrictedFactorialSeries_even_shifted_homogeneous
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    HomogeneousBesselGenerated halfDimension
      (PowerSeries.X ^ staircaseWeight (2 * halfDimension - 1) *
        generalUnrestrictedFactorialSeries (2 * halfDimension - 1)) := by
  let shifted := PowerSeries.X ^ staircaseWeight (2 * halfDimension - 1) *
    generalUnrestrictedFactorialSeries (2 * halfDimension - 1)
  have hbridge := generalUnrestrictedFactorialSeries_even_closed
    halfDimension hhalf
  have hfactorial : (halfDimension.factorial : ℚ) ≠ 0 := by positivity
  have hsolve : shifted =
      PowerSeries.C ((halfDimension.factorial : ℚ)⁻¹) *
        generalClosedEvenAssembly halfDimension := by
    dsimp only [shifted]
    rw [← hbridge]
    rw [show (halfDimension.factorial : ℚ⟦X⟧) =
        PowerSeries.C (halfDimension.factorial : ℚ) by
      exact (map_natCast PowerSeries.C halfDimension.factorial).symm]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hfactorial,
      map_one, one_mul]
  change HomogeneousBesselGenerated halfDimension shifted
  rw [hsolve]
  have hscalar : HomogeneousBesselGenerated 0
      (PowerSeries.C ((halfDimension.factorial : ℚ)⁻¹)) := by
    simpa using homogeneousBessel_polynomial
      (Polynomial.C ((halfDimension.factorial : ℚ)⁻¹))
  simpa using hscalar.mul
    (generalClosedEvenAssembly_homogeneous halfDimension)

theorem generalUnrestrictedFactorialSeries_odd_shifted_exponentialHomogeneous
    (halfDimension : ℕ) :
    ExponentialHomogeneousBesselGenerated halfDimension
      (PowerSeries.X ^ staircaseWeight (2 * halfDimension) *
        generalUnrestrictedFactorialSeries (2 * halfDimension)) := by
  let shifted := PowerSeries.X ^ staircaseWeight (2 * halfDimension) *
    generalUnrestrictedFactorialSeries (2 * halfDimension)
  have hbridge := generalUnrestrictedFactorialSeries_odd_closed halfDimension
  have hfactorial : (halfDimension.factorial : ℚ) ≠ 0 := by positivity
  have hsolve : shifted =
      PowerSeries.C ((halfDimension.factorial : ℚ)⁻¹) *
        generalClosedOddAssembly halfDimension := by
    dsimp only [shifted]
    rw [← hbridge]
    rw [show (halfDimension.factorial : ℚ⟦X⟧) =
        PowerSeries.C (halfDimension.factorial : ℚ) by
      exact (map_natCast PowerSeries.C halfDimension.factorial).symm]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hfactorial,
      map_one, one_mul]
  change ExponentialHomogeneousBesselGenerated halfDimension shifted
  rw [hsolve]
  have hscalar : HomogeneousBesselGenerated 0
      (PowerSeries.C ((halfDimension.factorial : ℚ)⁻¹)) := by
    simpa using homogeneousBessel_polynomial
      (Polynomial.C ((halfDimension.factorial : ℚ)⁻¹))
  simpa using hscalar.mul_exponential
    (generalClosedOddAssembly_exponentialHomogeneous halfDimension)

end FibonacciRibbonKernel
