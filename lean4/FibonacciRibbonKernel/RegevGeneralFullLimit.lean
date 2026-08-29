import FibonacciRibbonKernel.RegevGeneralCompactLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical Topology

noncomputable def generalFullNormalizedAverage
    (rank size : ℕ) : ℝ :=
  (∑ shape : BoundedPartition rank size,
    matsumotoLocalNormalizedTableau shape) /
      generalRegevScale rank size ^ rank

theorem abs_generalFull_sub_weighted_le_tail
    (rank : ℕ) {size : ℕ} (hsize : 1 ≤ size)
    (radius : ℝ) :
    |generalFullNormalizedAverage rank size -
        generalWeightedCompactTableauAverage rank size radius| ≤
      generalTailAbsoluteNormalizedAverage rank size radius := by
  have hscalePowerPos : (0 : ℝ) < generalRegevScale rank size ^ rank := by
    positivity [generalRegevScale_pos (rank := rank) hsize]
  have hraw :
      |(∑ shape : BoundedPartition rank size,
          matsumotoLocalNormalizedTableau shape) -
        ∑ shape : BoundedPartition rank size,
          regevRadialCutoff radius (generalShapePoint shape) *
            matsumotoLocalNormalizedTableau shape| ≤
      ∑ shape : GeneralTailShape rank size radius,
        |matsumotoLocalNormalizedTableau shape.1| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ shape : BoundedPartition rank size,
        (matsumotoLocalNormalizedTableau shape -
          regevRadialCutoff radius (generalShapePoint shape) *
            matsumotoLocalNormalizedTableau shape)| ≤
        ∑ shape : BoundedPartition rank size,
          |matsumotoLocalNormalizedTableau shape -
            regevRadialCutoff radius (generalShapePoint shape) *
              matsumotoLocalNormalizedTableau shape| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ shape : BoundedPartition rank size,
          if generalShapePoint shape ∈ Metric.closedBall 0 radius
            then 0 else |matsumotoLocalNormalizedTableau shape| := by
        apply Finset.sum_le_sum
        intro shape hshape
        by_cases hball : generalShapePoint shape ∈ Metric.closedBall 0 radius
        · rw [if_pos hball,
            regevRadialCutoff_eq_one_of_mem hball, one_mul, sub_self, abs_zero]
        · rw [if_neg hball, ← one_sub_mul, abs_mul]
          have hcutoffNonneg := regevRadialCutoff_nonneg radius
            (generalShapePoint shape)
          have hcutoffLe := regevRadialCutoff_le_one radius
            (generalShapePoint shape)
          rw [abs_of_nonneg (by linarith :
            0 ≤ 1 - regevRadialCutoff radius (generalShapePoint shape))]
          exact mul_le_of_le_one_left (abs_nonneg _)
            (by linarith : 1 - regevRadialCutoff radius
              (generalShapePoint shape) ≤ 1)
      _ = ∑ shape : GeneralTailShape rank size radius,
          |matsumotoLocalNormalizedTableau shape.1| := by
        have hpartition := Fintype.sum_subtype_add_sum_subtype
          (fun shape : BoundedPartition rank size =>
            generalShapePoint shape ∈ Metric.closedBall 0 radius)
          (fun shape => if generalShapePoint shape ∈ Metric.closedBall 0 radius
            then 0 else |matsumotoLocalNormalizedTableau shape|)
        have hinside :
            (∑ shape : {shape : BoundedPartition rank size //
              generalShapePoint shape ∈ Metric.closedBall 0 radius},
              if generalShapePoint shape.1 ∈ Metric.closedBall 0 radius
                then 0 else |matsumotoLocalNormalizedTableau shape.1|) = 0 := by
          apply Finset.sum_eq_zero
          intro shape hshape
          rw [if_pos shape.2]
        have houtside :
            (∑ shape : {shape : BoundedPartition rank size //
              ¬ generalShapePoint shape ∈ Metric.closedBall 0 radius},
              if generalShapePoint shape.1 ∈ Metric.closedBall 0 radius
                then 0 else |matsumotoLocalNormalizedTableau shape.1|) =
              ∑ shape : GeneralTailShape rank size radius,
                |matsumotoLocalNormalizedTableau shape.1| := by
          apply Finset.sum_congr rfl
          intro shape hshape
          rw [if_neg shape.2]
        rw [← hpartition, hinside, zero_add, houtside]
  unfold generalFullNormalizedAverage
  unfold generalWeightedCompactTableauAverage
  unfold generalTailAbsoluteNormalizedAverage
  rw [← sub_div, abs_div, abs_of_pos hscalePowerPos]
  exact div_le_div_of_nonneg_right hraw hscalePowerPos.le

theorem regevCompactChamberExtension_tendsto_pointwise
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    Tendsto (fun radius : ℕ =>
      regevCompactChamberExtension rank radius coordinates)
      atTop (nhds (regevChamberExtension rank coordinates)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ⌈‖coordinates‖⌉₊] with radius hradius
  have hnorm : ‖coordinates‖ ≤ (radius : ℝ) :=
    (Nat.le_ceil ‖coordinates‖).trans (Nat.cast_le.mpr hradius)
  have hball : coordinates ∈ Metric.closedBall 0 (radius : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right]
  exact (regevCompactChamberExtension_eq_extension_of_mem hball).symm

theorem integral_regevCompactChamberExtension_tendsto (rank : ℕ) :
    Tendsto (fun radius : ℕ =>
      ∫ coordinates, regevCompactChamberExtension rank radius coordinates)
      atTop (nhds (regevFullChamberIntegral rank)) := by
  have hdominated := tendsto_integral_of_dominated_convergence
    (fun coordinates : Fin rank → ℝ =>
      |regevChamberExtension rank coordinates|)
    (fun radius =>
      (continuous_regevCompactChamberExtension rank radius).aestronglyMeasurable)
    (integrable_regevChamberExtension rank).abs
    (fun radius => by
      filter_upwards with coordinates
      rw [Real.norm_eq_abs]
      unfold regevCompactChamberExtension
      rw [abs_mul, abs_of_nonneg (regevRadialCutoff_nonneg radius coordinates)]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (regevRadialCutoff_le_one radius coordinates))
    (by
      filter_upwards with coordinates
      exact regevCompactChamberExtension_tendsto_pointwise rank coordinates)
  rw [integral_regevChamberExtension rank] at hdominated
  exact hdominated

noncomputable def generalTailControl (rank : ℕ) (radius : ℝ) : ℝ :=
  regevCoordinateAbsorptionConstant rank *
    (Real.exp (-((regevCoordinateGaussianCoefficient rank / 2) / 2) *
        radius ^ 2) *
      (Real.exp ((regevCoordinateGaussianCoefficient rank / 2) / 2) *
        (2 + 2 * Real.sqrt (Real.pi /
          ((regevCoordinateGaussianCoefficient rank / 2) / 4)))) ^ rank)

theorem generalTailControl_tendsto_zero (rank : ℕ) :
    Tendsto (fun radius : ℕ => generalTailControl rank radius)
      atTop (nhds 0) := by
  let coefficient := (regevCoordinateGaussianCoefficient rank / 2) / 2
  let amplitude := (Real.exp coefficient *
    (2 + 2 * Real.sqrt (Real.pi /
      ((regevCoordinateGaussianCoefficient rank / 2) / 4)))) ^ rank
  let outer := regevCoordinateAbsorptionConstant rank
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity [regevCoordinateGaussianCoefficient_pos rank]
  have hsquare : Tendsto
      (fun radius : ℕ => (radius : ℝ) * (radius : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      tendsto_natCast_atTop_atTop
  have hquadratic : Tendsto
      (fun radius : ℕ => -coefficient * ((radius : ℝ) * (radius : ℝ)))
      atTop atBot :=
    hsquare.const_mul_atTop_of_neg (neg_neg_iff_pos.2 hcoefficient)
  have hexponential : Tendsto
      (fun radius : ℕ => Real.exp (-coefficient * (radius : ℝ) ^ 2))
      atTop (nhds 0) := by
    have h := Real.tendsto_exp_atBot.comp hquadratic
    exact h.congr' (Eventually.of_forall fun radius => by
      dsimp only [Function.comp_apply]
      congr 1
      ring)
  have hscaled : Tendsto
      (fun radius : ℕ => outer *
        (Real.exp (-coefficient * (radius : ℝ) ^ 2) * amplitude))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hexponential.mul_const amplitude)
  simpa [generalTailControl, coefficient, amplitude, outer] using hscaled

/-- Full all-size Regev limit before evaluation of the traceless Mehta
integral. -/
theorem general_full_normalizedAverage_tendsto (rank : ℕ) :
    Tendsto (fun size => generalFullNormalizedAverage rank size)
      atTop (nhds (regevFullChamberIntegral rank)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  rw [← Filter.eventually_atTop]
  have hthird : 0 < ε / 3 := by positivity
  have htailEventually : ∀ᶠ radius : ℕ in atTop,
      generalTailControl rank radius < ε / 3 :=
    (generalTailControl_tendsto_zero rank).eventually
      (Iio_mem_nhds hthird)
  have hintegralEventually : ∀ᶠ radius : ℕ in atTop,
      dist
        (∫ coordinates,
          regevCompactChamberExtension rank radius coordinates)
        (regevFullChamberIntegral rank) < ε / 3 :=
    (integral_regevCompactChamberExtension_tendsto rank).eventually
      (Metric.ball_mem_nhds _ hthird)
  obtain ⟨radius, htailRadius, hintegralRadius⟩ :=
    (htailEventually.and hintegralEventually).exists
  have hweighted := generalWeightedCompactTableauAverage_tendsto
    rank radius (Nat.cast_nonneg radius)
  have hweightedEventually : ∀ᶠ size : ℕ in atTop,
      dist (generalWeightedCompactTableauAverage rank size radius)
        (∫ coordinates,
          regevCompactChamberExtension rank radius coordinates) < ε / 3 :=
    hweighted.eventually (Metric.ball_mem_nhds _ hthird)
  have hsizeEventually : ∀ᶠ size : ℕ in atTop, rank + 1 ≤ size :=
    eventually_ge_atTop (rank + 1)
  filter_upwards [hweightedEventually, hsizeEventually]
    with size hweightedSize hsize
  have hsizeOne : 1 ≤ size :=
    (Nat.succ_le_succ (Nat.zero_le rank)).trans hsize
  have htailSize :
      dist (generalFullNormalizedAverage rank size)
        (generalWeightedCompactTableauAverage rank size radius) < ε / 3 := by
    rw [Real.dist_eq]
    exact (abs_generalFull_sub_weighted_le_tail rank hsizeOne radius).trans_lt
      ((generalTailAbsoluteNormalizedAverage_bound rank hsize radius
        (Nat.cast_nonneg radius)).trans_lt (by
          simpa [generalTailControl] using htailRadius))
  calc
    dist (generalFullNormalizedAverage rank size)
        (regevFullChamberIntegral rank) ≤
      dist (generalFullNormalizedAverage rank size)
          (generalWeightedCompactTableauAverage rank size radius) +
        dist (generalWeightedCompactTableauAverage rank size radius)
          (regevFullChamberIntegral rank) := dist_triangle _ _ _
    _ ≤ dist (generalFullNormalizedAverage rank size)
          (generalWeightedCompactTableauAverage rank size radius) +
        (dist (generalWeightedCompactTableauAverage rank size radius)
            (∫ coordinates,
              regevCompactChamberExtension rank radius coordinates) +
          dist
            (∫ coordinates,
              regevCompactChamberExtension rank radius coordinates)
            (regevFullChamberIntegral rank)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by linarith

end FibonacciRibbonKernel
