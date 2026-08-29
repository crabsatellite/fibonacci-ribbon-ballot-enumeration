import FibonacciRibbonKernel.RegevMehtaChamberPullback
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

theorem map_mehtaCenterBlockLinearMap_volume (rank : ℕ) :
    Measure.map (mehtaCenterBlockLinearMap rank)
        (volume : Measure ((Fin rank ⊕ Fin 1) → ℝ)) =
      ENNReal.ofReal ((((rank + 1 : ℕ) : ℝ))⁻¹) • volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · rw [mehtaCenterBlockLinearMap_det]
    have hdimension : (0 : ℝ) < (rank + 1 : ℕ) := by positivity
    rw [abs_of_pos (inv_pos.mpr hdimension)]
  · rw [mehtaCenterBlockLinearMap_det]
    positivity

theorem measurable_mehtaCenterBlockLinearMap (rank : ℕ) :
    Measurable (mehtaCenterBlockLinearMap rank) := by
  exact (LinearMap.continuous_of_finiteDimensional
    (mehtaCenterBlockLinearMap rank)).measurable

theorem measurable_mehtaBlockOutput (rank : ℕ) :
    Measurable (mehtaBlockOutput rank) :=
  (measurableEmbedding_mehtaBlockOutput rank).measurable

/-- Jacobian change of variables from the centered block coordinates to the
standard ordered Mehta chamber. -/
theorem mehtaBlockInputChamberIntegral_eq_standard (rank : ℕ) :
    mehtaBlockInputChamberIntegral rank =
      (((rank + 1 : ℕ) : ℝ))⁻¹ *
        standardMehtaBlockChamberIntegral rank := by
  let integrand : ((Fin rank ⊕ Fin 1) → ℝ) → ℝ :=
    fun coordinates => standardMehtaIntegrand (rank + 1)
      (mehtaBlockOutput rank coordinates)
  let restricted : ((Fin rank ⊕ Fin 1) → ℝ) → ℝ :=
    (standardMehtaBlockChamber rank).indicator integrand
  have hintegrand : StronglyMeasurable integrand := by
    exact ((continuous_standardMehtaIntegrand (rank + 1)).measurable.comp
      (measurable_mehtaBlockOutput rank)).stronglyMeasurable
  have hrestricted : StronglyMeasurable restricted :=
    hintegrand.indicator (standardMehtaBlockChamber_measurableSet rank)
  have hmap :
      (∫ coordinates, restricted coordinates
        ∂Measure.map (mehtaCenterBlockLinearMap rank)
          (volume : Measure ((Fin rank ⊕ Fin 1) → ℝ))) =
        ∫ coordinates, restricted
          (mehtaCenterBlockLinearMap rank coordinates) :=
    MeasureTheory.integral_map
      (μ := (volume : Measure ((Fin rank ⊕ Fin 1) → ℝ)))
      (measurable_mehtaCenterBlockLinearMap rank).aemeasurable
      hrestricted.aestronglyMeasurable
  rw [map_mehtaCenterBlockLinearMap_volume] at hmap
  rw [integral_smul_measure] at hmap
  have hdimension : (0 : ℝ) < (rank + 1 : ℕ) := by positivity
  have htoReal :
      (ENNReal.ofReal ((((rank + 1 : ℕ) : ℝ))⁻¹)).toReal =
        (((rank + 1 : ℕ) : ℝ))⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    positivity
  rw [htoReal, smul_eq_mul] at hmap
  unfold restricted integrand at hmap
  rw [integral_indicator (standardMehtaBlockChamber_measurableSet rank)] at hmap
  rw [show (fun coordinates : (Fin rank ⊕ Fin 1) → ℝ =>
      (standardMehtaBlockChamber rank).indicator
        (fun coordinates => standardMehtaIntegrand (rank + 1)
          (mehtaBlockOutput rank coordinates))
        (mehtaCenterBlockLinearMap rank coordinates)) =
      (mehtaCenterBlockLinearMap rank ⁻¹'
        standardMehtaBlockChamber rank).indicator
          (fun coordinates => standardMehtaIntegrand (rank + 1)
            (mehtaBlockOutput rank
              (mehtaCenterBlockLinearMap rank coordinates))) by
    funext coordinates
    simp [Set.indicator, Set.mem_preimage]] at hmap
  rw [integral_indicator] at hmap
  · rw [mehtaCenterBlockLinearMap_preimage_chamber] at hmap
    exact hmap.symm
  · exact (measurable_mehtaCenterBlockLinearMap rank)
      (standardMehtaBlockChamber_measurableSet rank)

end FibonacciRibbonKernel
