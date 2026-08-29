import FibonacciRibbonKernel.RegevVectorGaussianTail

namespace FibonacciRibbonKernel

open Set
open scoped Classical

def QuadraticTailShape (rank mesh : ℕ) (radius : ℝ) :=
  {shape : BoundedPartition rank (quadraticSize rank mesh) //
    quadraticShapePoint shape ∉ Metric.closedBall 0 radius}

noncomputable instance quadraticTailShapeFintype
    (rank mesh : ℕ) (radius : ℝ) :
    Fintype (QuadraticTailShape rank mesh radius) := by
  unfold QuadraticTailShape
  infer_instance

noncomputable def quadraticTailShapeToGaussianTail
    (rank mesh : ℕ) (radius : ℝ) :
    QuadraticTailShape rank mesh radius →
      regevScaledPiGaussianTailIndex rank mesh radius :=
  fun shape =>
    ⟨((boundedPartitionQuadraticChartEquiv rank mesh) shape.1).coordinates,
      by
        have hnot : ¬ dist (quadraticShapePoint shape.1) 0 ≤ radius := by
          simpa only [Metric.mem_closedBall] using shape.2
        have hstrict : radius < ‖quadraticShapePoint shape.1‖ := by
          simpa only [dist_zero_right] using lt_of_not_ge hnot
        exact hstrict⟩

theorem quadraticTailShapeToGaussianTail_injective
    (rank mesh : ℕ) (radius : ℝ) :
    Function.Injective
      (quadraticTailShapeToGaussianTail rank mesh radius) := by
  intro first second heq
  apply Subtype.ext
  apply (boundedPartitionQuadraticChartEquiv rank mesh).injective
  apply QuadraticChartTuple.ext
  exact congrArg Subtype.val heq

theorem regevCoordinateSeparableGaussian_quadratic_eq_scaledPi
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh)) :
    regevCoordinateSeparableGaussian rank (quadraticShapePoint shape) =
      regevScaledPiGaussian
        (regevCoordinateGaussianCoefficient rank / 2) rank mesh
        ((boundedPartitionQuadraticChartEquiv rank mesh) shape).coordinates := by
  unfold regevCoordinateSeparableGaussian regevScaledPiGaussian
  unfold regevPiProduct regevScaledGaussianLine regevScaledGaussianReal
  unfold quadraticShapePoint quadraticCenteredPoint
  rfl

theorem abs_matsumoto_quadratic_le_scaledPiGaussian
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh))
    (hmesh : 1 ≤ mesh) :
    |matsumotoLocalNormalizedTableau shape| ≤
      regevCoordinateAbsorptionConstant rank *
        regevScaledPiGaussian
          (regevCoordinateGaussianCoefficient rank / 2) rank mesh
          ((boundedPartitionQuadraticChartEquiv rank mesh) shape).coordinates := by
  calc
    |matsumotoLocalNormalizedTableau shape| ≤
        regevCoordinateDominatingKernel rank (quadraticShapePoint shape) :=
      abs_matsumoto_quadratic_le_coordinateDominatingKernel shape hmesh
    _ ≤ regevCoordinateAbsorptionConstant rank *
        regevCoordinateSeparableGaussian rank (quadraticShapePoint shape) :=
      regevCoordinateDominatingKernel_le_separableGaussian rank _
    _ = _ := by
      rw [regevCoordinateSeparableGaussian_quadratic_eq_scaledPi shape]

noncomputable def quadraticTailAbsoluteNormalizedAverage
    (rank mesh : ℕ) (radius : ℝ) : ℝ :=
  (∑ shape : QuadraticTailShape rank mesh radius,
    |matsumotoLocalNormalizedTableau shape.1|) / mesh ^ rank

/-- The complete quadratic-subsequence tableau tail is exponentially small,
uniformly in the mesh.  This closes the domination obligation needed to remove
the compact truncation from the Riemann-sum limit. -/
theorem quadraticTailAbsoluteNormalizedAverage_bound
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh)
    (radius : ℝ) (hradius : 0 ≤ radius) :
    quadraticTailAbsoluteNormalizedAverage rank mesh radius ≤
      regevCoordinateAbsorptionConstant rank *
        (Real.exp (-((regevCoordinateGaussianCoefficient rank / 2) / 2) *
            radius ^ 2) *
          (2 + 2 * Real.sqrt (Real.pi /
            ((regevCoordinateGaussianCoefficient rank / 2) / 2))) ^ rank) := by
  let coefficient := regevCoordinateGaussianCoefficient rank / 2
  let map := quadraticTailShapeToGaussianTail rank mesh radius
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity [regevCoordinateGaussianCoefficient_pos rank]
  have hconstantNonneg : 0 ≤ regevCoordinateAbsorptionConstant rank := by
    unfold regevCoordinateAbsorptionConstant
    unfold regevCoordinateEnvelopeConstant
    positivity
  have hleft : Summable (fun shape : QuadraticTailShape rank mesh radius =>
      |matsumotoLocalNormalizedTableau shape.1|) :=
    Summable.of_finite
  have hgaussian := summable_regevScaledPiGaussian
    hcoefficient rank hmesh
  have hgaussianTail := hgaussian.subtype
    (regevScaledPiGaussianTailIndex rank mesh radius)
  have hright := hgaussianTail.mul_left
    (regevCoordinateAbsorptionConstant rank)
  have hsum :
      (∑' shape : QuadraticTailShape rank mesh radius,
        |matsumotoLocalNormalizedTableau shape.1|) ≤
      ∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
        regevCoordinateAbsorptionConstant rank *
          regevScaledPiGaussian coefficient rank mesh point.1 := by
    exact hleft.tsum_le_tsum_of_inj map
      (quadraticTailShapeToGaussianTail_injective rank mesh radius)
      (fun point _ => mul_nonneg hconstantNonneg
        (regevScaledPiGaussian_nonneg coefficient rank mesh point.1))
      (fun shape => by
        exact abs_matsumoto_quadratic_le_scaledPiGaussian shape.1 hmesh)
      hright
  have hmeshPowerNonneg : (0 : ℝ) ≤ mesh ^ rank := by positivity
  have hnormalized := div_le_div_of_nonneg_right hsum hmeshPowerNonneg
  have htail := regevScaledPiGaussian_tail_bound
    hcoefficient hradius rank hmesh
  unfold quadraticTailAbsoluteNormalizedAverage
  calc
    (∑ shape : QuadraticTailShape rank mesh radius,
        |matsumotoLocalNormalizedTableau shape.1|) / mesh ^ rank =
      (∑' shape : QuadraticTailShape rank mesh radius,
        |matsumotoLocalNormalizedTableau shape.1|) / mesh ^ rank := by
      rw [tsum_fintype]
    _ ≤ (∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
        regevCoordinateAbsorptionConstant rank *
          regevScaledPiGaussian coefficient rank mesh point.1) /
          mesh ^ rank := hnormalized
    _ = regevCoordinateAbsorptionConstant rank *
        ((∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
          regevScaledPiGaussian coefficient rank mesh point.1) /
            mesh ^ rank) := by
      rw [tsum_mul_left]
      ring
    _ ≤ regevCoordinateAbsorptionConstant rank *
        (Real.exp (-(coefficient / 2) * radius ^ 2) *
          (2 + 2 * Real.sqrt (Real.pi / (coefficient / 2))) ^ rank) :=
      mul_le_mul_of_nonneg_left htail hconstantNonneg
    _ = _ := by rfl

end FibonacciRibbonKernel
