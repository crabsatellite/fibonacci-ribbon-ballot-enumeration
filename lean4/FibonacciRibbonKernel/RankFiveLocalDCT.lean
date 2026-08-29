import FibonacciRibbonKernel.RankFiveDominating

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

theorem continuous_oddCosineSumScale
    (dimension index : ℕ) :
    Continuous (oddCosineSumScale (dimension := dimension) · index) := by
  unfold oddCosineSumScale
  exact continuous_const.add (continuous_cosineSumScale dimension index)

theorem continuous_normalizedOddFibonacciKernel
    (dimension index : ℕ) :
    Continuous (normalizedOddFibonacciKernel
      (dimension := dimension) · index) := by
  unfold normalizedOddFibonacciKernel
  exact ((continuous_fibonacciScaleKernel index).comp
    (continuous_oddCosineSumScale dimension index)).div_const _

theorem continuous_scaledCosineVandermondeWeight
    (dimension index : ℕ) :
    Continuous (scaledCosineVandermondeWeight dimension index) := by
  unfold scaledCosineVandermondeWeight
  apply continuous_finsetProd
  intro upper _hupper
  apply continuous_finsetProd
  intro lower _hlower
  fun_prop

theorem continuous_oddScaledWeylWeight
    (dimension index : ℕ) :
    Continuous (oddScaledWeylWeight dimension index) := by
  unfold oddScaledWeylWeight
  apply (continuous_scaledCosineVandermondeWeight dimension index).mul
  apply continuous_finsetProd
  intro coordinate _hcoordinate
  fun_prop

theorem measurableSet_positiveOddLocalScaledDomain
    (dimension index : ℕ) :
    MeasurableSet (positiveOddLocalScaledDomain dimension index) := by
  unfold positiveOddLocalScaledDomain
  apply (measurableSet_positiveScaledCube dimension index).inter
  exact measurableSet_Ici.preimage
    (continuous_oddCosineSumScale dimension index).measurable

theorem aestronglyMeasurable_oddWeylLocalRescaledIntegrand
    (dimension index : ℕ) :
    AEStronglyMeasurable
      (oddWeylLocalRescaledIntegrand dimension index) := by
  unfold oddWeylLocalRescaledIntegrand
  exact (((continuous_const.mul
    (continuous_normalizedOddFibonacciKernel dimension index)).mul
      (continuous_oddScaledWeylWeight dimension index)).stronglyMeasurable.indicator
        (measurableSet_positiveOddLocalScaledDomain dimension index)).aestronglyMeasurable

theorem tendsto_integral_rankFiveLocalRescaledIntegrand :
    Tendsto
      (fun index => ∫ coordinates : Fin 2 → ℝ,
        oddWeylLocalRescaledIntegrand 2 index coordinates)
      atTop
      (nhds (∫ coordinates : Fin 2 → ℝ,
        oddWeylLocalLimitIntegrand 2 coordinates)) := by
  exact tendsto_integral_of_dominated_convergence
    rankFiveLocalDominating
    (fun index =>
      aestronglyMeasurable_oddWeylLocalRescaledIntegrand 2 index)
    integrable_rankFiveLocalDominating
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_rankFiveLocalRescaledIntegrand_le index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_oddWeylLocalRescaledIntegrand (dimension := 2)
        (by norm_num) coordinates)

theorem tendsto_rankFiveOddWeylAngleLocalNormalizedIntegral :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) ^ 5 *
          oddWeylAngleLocalNormalizedIntegral 2 index)
      atTop
      (nhds (∫ coordinates : Fin 2 → ℝ,
        oddWeylLocalLimitIntegrand 2 coordinates)) := by
  rw [show (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 *
        oddWeylAngleLocalNormalizedIntegral 2 index) =
      fun index => ∫ coordinates : Fin 2 → ℝ,
        oddWeylLocalRescaledIntegrand 2 index coordinates by
    funext index
    exact rankFive_oddWeylLocalScalingIntegral_identity index]
  exact tendsto_integral_rankFiveLocalRescaledIntegrand

end FibonacciRibbonKernel
