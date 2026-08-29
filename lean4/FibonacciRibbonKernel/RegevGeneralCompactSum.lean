import FibonacciRibbonKernel.RegevGeneralCompactCarrier

namespace FibonacciRibbonKernel

open Set
open scoped Classical

noncomputable def generalWeightedCompactTableauAverage
    (rank size : ℕ) (radius : ℝ) : ℝ :=
  (∑ shape : BoundedPartition rank size,
    regevRadialCutoff radius (generalShapePoint shape) *
      matsumotoLocalNormalizedTableau shape) /
        generalRegevScale rank size ^ rank

noncomputable def generalWeightedCompactLocalAverage
    (rank size : ℕ) (radius : ℝ) : ℝ :=
  (∑ shape : BoundedPartition rank size,
    regevRadialCutoff radius (generalShapePoint shape) *
      regevLocalIntegrand rank (generalShapePoint shape)) /
        generalRegevScale rank size ^ rank

theorem generalAffine_compact_support_mem
    {rank size : ℕ} (radius : ℝ)
    {coordinates : Fin rank → ℤ}
    (hnonzero : regevCompactChamberExtension rank radius
      (generalAffineLatticePoint rank size coordinates) ≠ 0) :
    generalAffineLatticePoint rank size coordinates ∈ regevChamber rank ∧
      generalAffineLatticePoint rank size coordinates ∈
        Metric.closedBall 0 (radius + 1) := by
  constructor
  · by_contra hnot
    exact hnonzero (by
      unfold regevCompactChamberExtension
      rw [regevChamberExtension_eq_zero_of_not_mem hnot, mul_zero])
  · by_contra hnot
    exact hnonzero
      (regevCompactChamberExtension_eq_zero_of_not_mem hnot)

theorem general_affine_compact_sum_eq_local_shape_sum
    (rank size : ℕ) (hsize : 1 ≤ size)
    (hmesh : 1 ≤ generalRegevMesh rank size)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hscale : (rank : ℝ) * (radius + 1) ≤ generalRegevScale rank size) :
    (∑' coordinates : Fin rank → ℤ,
      regevCompactChamberExtension rank radius
        (generalAffineTransform rank size
          (quadraticIntegerPoint (generalRegevMesh rank size) coordinates))) =
      ∑ shape : BoundedPartition rank size,
        regevRadialCutoff radius (generalShapePoint shape) *
          regevLocalIntegrand rank (generalShapePoint shape) := by
  let latticeEquiv := generalCompactShapeLatticeEquiv
    rank size hsize (radius + 1) (by linarith) hscale
  have htransform (coordinates : Fin rank → ℤ) :
      generalAffineTransform rank size
          (quadraticIntegerPoint (generalRegevMesh rank size) coordinates) =
        generalAffineLatticePoint rank size coordinates :=
    generalAffineTransform_integerPoint hsize hmesh coordinates
  rw [show (∑' coordinates : Fin rank → ℤ,
      regevCompactChamberExtension rank radius
        (generalAffineTransform rank size
          (quadraticIntegerPoint (generalRegevMesh rank size) coordinates))) =
      ∑' coordinates : Fin rank → ℤ,
        regevCompactChamberExtension rank radius
          (generalAffineLatticePoint rank size coordinates) by
    apply tsum_congr
    intro coordinates
    rw [htransform]]
  have hsupport : Function.support
      (fun coordinates : Fin rank → ℤ =>
        regevCompactChamberExtension rank radius
          (generalAffineLatticePoint rank size coordinates)) ⊆
      {coordinates |
        generalAffineLatticePoint rank size coordinates ∈ regevChamber rank ∧
        generalAffineLatticePoint rank size coordinates ∈
          Metric.closedBall 0 (radius + 1)} := by
    intro coordinates hnonzero
    exact generalAffine_compact_support_mem radius hnonzero
  rw [← tsum_subtype_eq_of_support_subset hsupport]
  change (∑' point : GeneralCompactLatticePoint rank size (radius + 1),
      regevCompactChamberExtension rank radius
        (generalAffineLatticePoint rank size point.1)) = _
  rw [show (∑' point : GeneralCompactLatticePoint rank size (radius + 1),
      regevCompactChamberExtension rank radius
        (generalAffineLatticePoint rank size point.1)) =
      ∑' shape : GeneralCompactShape rank size (radius + 1),
        regevCompactChamberExtension rank radius
          (generalAffineLatticePoint rank size (latticeEquiv shape).1) by
    exact (latticeEquiv.tsum_eq
      (fun point => regevCompactChamberExtension rank radius
        (generalAffineLatticePoint rank size point.1))).symm]
  rw [tsum_fintype]
  have hfullPartition := Fintype.sum_subtype_add_sum_subtype
    (fun shape : BoundedPartition rank size =>
      generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1))
    (fun shape => regevRadialCutoff radius (generalShapePoint shape) *
      regevLocalIntegrand rank (generalShapePoint shape))
  have houtsideZero :
      (∑ shape : {shape : BoundedPartition rank size //
        ¬ generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)},
        regevRadialCutoff radius (generalShapePoint shape.1) *
          regevLocalIntegrand rank (generalShapePoint shape.1)) = 0 := by
    apply Finset.sum_eq_zero
    intro shape hshape
    rw [regevRadialCutoff_eq_zero_of_not_mem shape.2, zero_mul]
  have hinside :
      (∑ shape : GeneralCompactShape rank size (radius + 1),
        regevCompactChamberExtension rank radius
          (generalAffineLatticePoint rank size (latticeEquiv shape).1)) =
      ∑ shape : GeneralCompactShape rank size (radius + 1),
        regevRadialCutoff radius (generalShapePoint shape.1) *
          regevLocalIntegrand rank (generalShapePoint shape.1) := by
    apply Finset.sum_congr rfl
    intro shape hshape
    have hpoint : generalAffineLatticePoint rank size
        (latticeEquiv shape).1 = generalShapePoint shape.1 := by
      rw [generalShapePoint_eq_affineLatticePoint hsize]
      rfl
    rw [hpoint]
    unfold regevCompactChamberExtension
    rw [regevChamberExtension_eq_local_of_mem]
    exact generalShapePoint_mem_chamber hsize shape.1
  rw [hinside]
  have hpartition := hfullPartition
  rw [houtsideZero, add_zero] at hpartition
  exact hpartition

theorem generalWeightedCompactLocalAverage_eq_affine
    (rank size : ℕ) (hsize : 1 ≤ size)
    (hmesh : 1 ≤ generalRegevMesh rank size)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hscale : (rank : ℝ) * (radius + 1) ≤ generalRegevScale rank size) :
    generalWeightedCompactLocalAverage rank size radius =
      generalAffineScaleCompactAverage rank size radius := by
  unfold generalWeightedCompactLocalAverage
  unfold generalAffineScaleCompactAverage
  rw [general_affine_compact_sum_eq_local_shape_sum
    rank size hsize hmesh radius hradius hscale]

end FibonacciRibbonKernel
