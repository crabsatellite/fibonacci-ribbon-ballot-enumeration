import FibonacciRibbonKernel.WeylMomentTransform

namespace FibonacciRibbonKernel

open PowerSeries

theorem ribbonCount_eq_finite_transformR
    {rank : ℕ} (hrank : 1 ≤ rank) (power : ℕ) :
    (ribbonCount rank power : ℝ) =
      ∑ degree ∈ Finset.range (power + 1),
        (unrestrictedCount rank degree : ℝ) *
          ribbonTransformBasisWeightR power degree := by
  have hcoefficient := congrArg (PowerSeries.coeff power)
    (exact_generating_substitutionR hrank)
  rw [ribbonGeneratingSeriesR_coeff, coeff_ribbonTransformR] at hcoefficient
  simpa only [generalUnrestrictedOrdinarySeriesR_coeff] using hcoefficient

theorem evenWeylMoment_count_transfer
    (dimension : ℕ) (hdimension : 1 ≤ dimension)
    (normalization : ℝ)
    (hgeometric : ∀ power : ℕ,
      normalization * evenWeylGeometricMoment dimension power =
        (unrestrictedCount (2 * dimension - 1) power : ℝ))
    (power : ℕ) :
    normalization * evenWeylFibonacciMoment dimension power =
      (ribbonCount (2 * dimension - 1) power : ℝ) := by
  rw [evenWeylFibonacciMoment_eq_finite_transform,
    Finset.mul_sum]
  rw [ribbonCount_eq_finite_transformR
    (rank := 2 * dimension - 1) (by omega) power]
  apply Finset.sum_congr rfl
  intro degree _hdegree
  rw [← hgeometric]
  ring

theorem oddWeylMoment_count_transfer
    (dimension : ℕ) (hdimension : 1 ≤ dimension) (normalization : ℝ)
    (hgeometric : ∀ power : ℕ,
      normalization * oddWeylGeometricMoment dimension power =
        (unrestrictedCount (2 * dimension) power : ℝ))
    (power : ℕ) :
    normalization * oddWeylFibonacciMoment dimension power =
      (ribbonCount (2 * dimension) power : ℝ) := by
  rw [oddWeylFibonacciMoment_eq_finite_transform,
    Finset.mul_sum]
  rw [ribbonCount_eq_finite_transformR
    (rank := 2 * dimension) (by omega) power]
  apply Finset.sum_congr rfl
  intro degree _hdegree
  rw [← hgeometric]
  ring

end FibonacciRibbonKernel
