import FibonacciRibbonKernel.RankFiveGeometricDominating

namespace FibonacciRibbonKernel

open Filter MeasureTheory

theorem tendsto_integral_rankFiveGeometricLocalRescaledIntegrand :
    Tendsto
      (fun index => ∫ coordinates : Fin 2 → ℝ,
        rankFiveGeometricLocalRescaledIntegrand index coordinates)
      atTop
      (nhds (∫ coordinates : Fin 2 → ℝ,
        rankFiveGeometricLocalLimitIntegrand coordinates)) := by
  exact tendsto_integral_of_dominated_convergence
    rankFiveGeometricLocalDominating
    aestronglyMeasurable_rankFiveGeometricLocalRescaledIntegrand
    integrable_rankFiveGeometricLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankFiveGeometricLocalRescaledIntegrand_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_rankFiveGeometricLocalRescaledIntegrand coordinates)

theorem tendsto_rankFiveGeometricAngleLocalIntegral :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) ^ 5 *
          rankFiveGeometricAngleLocalIntegral index)
      atTop
      (nhds (∫ coordinates : Fin 2 → ℝ,
        rankFiveGeometricLocalLimitIntegrand coordinates)) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 *
        rankFiveGeometricAngleLocalIntegral index) =
      fun index => ∫ coordinates : Fin 2 → ℝ,
        rankFiveGeometricLocalRescaledIntegrand index coordinates by
    funext index
    exact rankFiveGeometricLocalScalingIntegral_identity index]
  exact tendsto_integral_rankFiveGeometricLocalRescaledIntegrand

end FibonacciRibbonKernel
