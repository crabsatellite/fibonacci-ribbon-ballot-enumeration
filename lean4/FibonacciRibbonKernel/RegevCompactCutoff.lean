import FibonacciRibbonKernel.RegevIntegerBallRiemann

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical Topology

noncomputable def regevRadialCutoff
    {rank : ℕ} (radius : ℝ) (coordinates : Fin rank → ℝ) : ℝ :=
  max 0 (min 1 (radius + 1 - ‖coordinates‖))

theorem continuous_regevRadialCutoff
    {rank : ℕ} (radius : ℝ) :
    Continuous (regevRadialCutoff (rank := rank) radius) := by
  unfold regevRadialCutoff
  exact continuous_const.max
    (continuous_const.min
      ((continuous_const.add continuous_const).sub continuous_norm))

theorem regevRadialCutoff_nonneg
    {rank : ℕ} (radius : ℝ) (coordinates : Fin rank → ℝ) :
    0 ≤ regevRadialCutoff radius coordinates :=
  le_max_left _ _

theorem regevRadialCutoff_le_one
    {rank : ℕ} (radius : ℝ) (coordinates : Fin rank → ℝ) :
    regevRadialCutoff radius coordinates ≤ 1 := by
  unfold regevRadialCutoff
  exact max_le (by norm_num) (min_le_left _ _)

theorem regevRadialCutoff_eq_one_of_mem
    {rank : ℕ} {radius : ℝ} {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∈ Metric.closedBall 0 radius) :
    regevRadialCutoff radius coordinates = 1 := by
  have hnorm : ‖coordinates‖ ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hcoordinates
  unfold regevRadialCutoff
  rw [min_eq_left (by linarith)]
  norm_num

theorem regevRadialCutoff_eq_zero_of_not_mem
    {rank : ℕ} {radius : ℝ} {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∉ Metric.closedBall 0 (radius + 1)) :
    regevRadialCutoff radius coordinates = 0 := by
  have hnorm : radius + 1 < ‖coordinates‖ := by
    have hnot : ¬ dist coordinates 0 ≤ radius + 1 := by
      simpa only [Metric.mem_closedBall] using hcoordinates
    simpa only [dist_zero_right] using lt_of_not_ge hnot
  unfold regevRadialCutoff
  rw [max_eq_left]
  exact (min_le_right 1 (radius + 1 - ‖coordinates‖)).trans (by linarith)

noncomputable def regevCompactChamberExtension
    (rank : ℕ) (radius : ℝ) (coordinates : Fin rank → ℝ) : ℝ :=
  regevRadialCutoff radius coordinates *
    regevChamberExtension rank coordinates

theorem continuous_regevCompactChamberExtension
    (rank : ℕ) (radius : ℝ) :
    Continuous (regevCompactChamberExtension rank radius) :=
  (continuous_regevRadialCutoff radius).mul
    (continuous_regevChamberExtension rank)

theorem regevCompactChamberExtension_eq_extension_of_mem
    {rank : ℕ} {radius : ℝ} {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∈ Metric.closedBall 0 radius) :
    regevCompactChamberExtension rank radius coordinates =
      regevChamberExtension rank coordinates := by
  unfold regevCompactChamberExtension
  rw [regevRadialCutoff_eq_one_of_mem hcoordinates, one_mul]

theorem regevCompactChamberExtension_eq_zero_of_not_mem
    {rank : ℕ} {radius : ℝ} {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∉ Metric.closedBall 0 (radius + 1)) :
    regevCompactChamberExtension rank radius coordinates = 0 := by
  unfold regevCompactChamberExtension
  rw [regevRadialCutoff_eq_zero_of_not_mem hcoordinates, zero_mul]

noncomputable def regevCompactExtensionBound (rank : ℕ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
    regevCoordinateAbsorptionConstant rank

theorem regevCoordinateSeparableGaussian_le_one
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    regevCoordinateSeparableGaussian rank coordinates ≤ 1 := by
  unfold regevCoordinateSeparableGaussian
  apply Finset.prod_le_one
  · intro row hrow
    positivity
  · intro row hrow
    rw [Real.exp_le_one_iff]
    have hcoefficient := regevCoordinateGaussianCoefficient_pos rank
    nlinarith [sq_nonneg (coordinates row)]

theorem abs_regevChamberExtension_le_bound
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    |regevChamberExtension rank coordinates| ≤
      regevCompactExtensionBound rank := by
  by_cases hcoordinates : coordinates ∈ regevChamber rank
  · rw [regevChamberExtension_eq_local_of_mem hcoordinates]
    calc
      |regevLocalIntegrand rank coordinates| ≤
          (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
            regevCoordinateDominatingKernel rank coordinates :=
        abs_regevLocalIntegrand_le_coordinateDominatingKernel rank coordinates
      _ ≤ (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
          (regevCoordinateAbsorptionConstant rank *
            regevCoordinateSeparableGaussian rank coordinates) :=
        mul_le_mul_of_nonneg_left
          (regevCoordinateDominatingKernel_le_separableGaussian rank coordinates)
          (by positivity)
      _ ≤ (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
          regevCoordinateAbsorptionConstant rank := by
        have hprefix : 0 ≤
            (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
              regevCoordinateAbsorptionConstant rank := by
          unfold regevCoordinateAbsorptionConstant regevCoordinateEnvelopeConstant
          positivity
        calc
          _ = ((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
              regevCoordinateAbsorptionConstant rank) *
                regevCoordinateSeparableGaussian rank coordinates := by ring
          _ ≤ ((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
              regevCoordinateAbsorptionConstant rank) * 1 :=
            mul_le_mul_of_nonneg_left
              (regevCoordinateSeparableGaussian_le_one rank coordinates) hprefix
          _ = _ := by ring
      _ = regevCompactExtensionBound rank := rfl
  · rw [regevChamberExtension_eq_zero_of_not_mem hcoordinates, abs_zero]
    unfold regevCompactExtensionBound regevCoordinateAbsorptionConstant
    unfold regevCoordinateEnvelopeConstant
    positivity

theorem abs_regevCompactChamberExtension_le_bound
    (rank : ℕ) (radius : ℝ) (coordinates : Fin rank → ℝ) :
    |regevCompactChamberExtension rank radius coordinates| ≤
      regevCompactExtensionBound rank := by
  unfold regevCompactChamberExtension
  rw [abs_mul, abs_of_nonneg (regevRadialCutoff_nonneg radius coordinates)]
  calc
    regevRadialCutoff radius coordinates *
        |regevChamberExtension rank coordinates| ≤
      1 * regevCompactExtensionBound rank := by
      apply mul_le_mul
      · exact regevRadialCutoff_le_one radius coordinates
      · exact abs_regevChamberExtension_le_bound rank coordinates
      · exact abs_nonneg _
      · norm_num
    _ = _ := one_mul _

theorem compact_extension_integer_riemann_tendsto
    (rank : ℕ) (radius : ℝ) :
    Tendsto
      (fun mesh : ℕ =>
        (∑' coordinates : Fin rank → ℤ,
          regevCompactChamberExtension rank radius
            (quadraticIntegerPoint mesh coordinates)) /
          mesh ^ rank)
      atTop
      (nhds (∫ coordinates,
        regevCompactChamberExtension rank radius coordinates)) :=
  integer_full_riemann_sum_tendsto rank (radius + 1)
    (regevCompactChamberExtension rank radius)
    (continuous_regevCompactChamberExtension rank radius)
    (fun _coordinates hcoordinates =>
      regevCompactChamberExtension_eq_zero_of_not_mem hcoordinates)

end FibonacciRibbonKernel
