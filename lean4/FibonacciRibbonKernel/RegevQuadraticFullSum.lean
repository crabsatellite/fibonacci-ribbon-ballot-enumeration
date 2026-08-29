import FibonacciRibbonKernel.RegevQuadraticTail

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def quadraticFullNormalizedSum
    (rank mesh : ℕ) : ℝ :=
  ∑ shape : BoundedPartition rank (quadraticSize rank mesh),
    matsumotoLocalNormalizedTableau shape

noncomputable def quadraticFullNormalizedAverage
    (rank mesh : ℕ) : ℝ :=
  quadraticFullNormalizedSum rank mesh / mesh ^ rank

noncomputable def quadraticTailNormalizedSum
    (rank mesh : ℕ) (radius : ℝ) : ℝ :=
  ∑ shape : QuadraticTailShape rank mesh radius,
    matsumotoLocalNormalizedTableau shape.1

noncomputable def quadraticTailNormalizedAverage
    (rank mesh : ℕ) (radius : ℝ) : ℝ :=
  quadraticTailNormalizedSum rank mesh radius / mesh ^ rank

theorem quadratic_full_sum_eq_truncated_add_tail
    (rank mesh : ℕ) (radius : ℝ) :
    quadraticFullNormalizedSum rank mesh =
      quadraticTruncatedNormalizedSum rank mesh radius +
        quadraticTailNormalizedSum rank mesh radius := by
  have hpartition := Fintype.sum_subtype_add_sum_subtype
    (fun shape : BoundedPartition rank (quadraticSize rank mesh) =>
      quadraticShapePoint shape ∈ Metric.closedBall 0 radius)
    (fun shape => matsumotoLocalNormalizedTableau shape)
  unfold quadraticFullNormalizedSum quadraticTruncatedNormalizedSum
  unfold quadraticTailNormalizedSum QuadraticTruncatedShape QuadraticTailShape
  exact hpartition.symm

theorem quadratic_full_average_sub_truncated
    (rank mesh : ℕ) (radius : ℝ) :
    quadraticFullNormalizedAverage rank mesh -
        quadraticTruncatedNormalizedAverage rank mesh radius =
      quadraticTailNormalizedAverage rank mesh radius := by
  unfold quadraticFullNormalizedAverage
  unfold quadraticTruncatedNormalizedAverage
  unfold quadraticTailNormalizedAverage
  rw [quadratic_full_sum_eq_truncated_add_tail]
  ring

theorem abs_quadraticTailNormalizedAverage_le
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh) (radius : ℝ) :
    |quadraticTailNormalizedAverage rank mesh radius| ≤
      quadraticTailAbsoluteNormalizedAverage rank mesh radius := by
  have hmeshPowerPos : (0 : ℝ) < mesh ^ rank := by positivity
  unfold quadraticTailNormalizedAverage
  unfold quadraticTailAbsoluteNormalizedAverage
  rw [abs_div, abs_of_pos hmeshPowerPos]
  apply div_le_div_of_nonneg_right _ hmeshPowerPos.le
  unfold quadraticTailNormalizedSum
  exact Finset.abs_sum_le_sum_abs _ _

/-- Quantitative truncation-removal estimate for the exact quadratic
subsequence normalized average. -/
theorem abs_quadraticFull_sub_truncated_bound
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh)
    (radius : ℝ) (hradius : 0 ≤ radius) :
    |quadraticFullNormalizedAverage rank mesh -
        quadraticTruncatedNormalizedAverage rank mesh radius| ≤
      regevCoordinateAbsorptionConstant rank *
        (Real.exp (-((regevCoordinateGaussianCoefficient rank / 2) / 2) *
            radius ^ 2) *
          (2 + 2 * Real.sqrt (Real.pi /
            ((regevCoordinateGaussianCoefficient rank / 2) / 2))) ^ rank) := by
  rw [quadratic_full_average_sub_truncated]
  exact (abs_quadraticTailNormalizedAverage_le rank hmesh radius).trans
    (quadraticTailAbsoluteNormalizedAverage_bound
      rank hmesh radius hradius)

end FibonacciRibbonKernel
