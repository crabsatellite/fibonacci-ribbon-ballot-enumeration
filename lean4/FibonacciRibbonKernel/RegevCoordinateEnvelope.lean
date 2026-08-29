import FibonacciRibbonKernel.RegevGaussianTail

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def regevCoordinateRowEnvelope
    (rank : ℕ) (coordinates : Fin rank → ℝ) : ℝ :=
  ∏ row : Fin (rank + 1),
    2 * (1 + |tracelessExtend coordinates row| + (row.rev.val : ℝ))

noncomputable def regevCoordinatePairEnvelope
    (rank : ℕ) (coordinates : Fin rank → ℝ) : ℝ :=
  ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
    (|tracelessExtend coordinates row| +
      |tracelessExtend coordinates next| +
      (rank : ℝ) * (rank + 1 : ℕ))

noncomputable def regevCoordinateDominatingKernel
    (rank : ℕ) (coordinates : Fin rank → ℝ) : ℝ :=
  Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
    regevCoordinateRowEnvelope rank coordinates *
    regevCoordinatePairEnvelope rank coordinates *
    Real.exp (-(∑ row : Fin (rank + 1),
      tracelessExtend coordinates row ^ 2 /
        (2 * regevEntropyDenominator rank)))

theorem regevRowEnvelopeProduct_eq_coordinate
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh))
    (hmesh : 1 ≤ mesh) :
    regevRowEnvelopeProduct shape =
      regevCoordinateRowEnvelope rank (quadraticShapePoint shape) := by
  unfold regevRowEnvelopeProduct regevCoordinateRowEnvelope
  apply Finset.prod_congr rfl
  intro row hrow
  unfold quadraticShapePoint
  rw [quadraticCenteredPoint_eq_regevCenteredRow_full shape hmesh row]

theorem regevPairEnvelopeProduct_eq_coordinate
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh))
    (hmesh : 1 ≤ mesh) :
    regevPairEnvelopeProduct shape =
      regevCoordinatePairEnvelope rank (quadraticShapePoint shape) := by
  unfold regevPairEnvelopeProduct regevCoordinatePairEnvelope
  apply Finset.prod_congr rfl
  intro row hrow
  apply Finset.prod_congr rfl
  intro next hnext
  unfold quadraticShapePoint
  rw [quadraticCenteredPoint_eq_regevCenteredRow_full shape hmesh row]
  rw [quadraticCenteredPoint_eq_regevCenteredRow_full shape hmesh next]

theorem regevCenteredGaussianSum_eq_coordinate
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh))
    (hmesh : 1 ≤ mesh) :
    (∑ row : Fin (rank + 1),
        regevCenteredRow shape row ^ 2 /
          (2 * regevEntropyDenominator rank)) =
      ∑ row : Fin (rank + 1),
        tracelessExtend (quadraticShapePoint shape) row ^ 2 /
          (2 * regevEntropyDenominator rank) := by
  apply Finset.sum_congr rfl
  intro row hrow
  unfold quadraticShapePoint
  rw [quadraticCenteredPoint_eq_regevCenteredRow_full shape hmesh row]

/-- Exact transport of the complete Matsumoto summand majorant to the
traceless coordinate chart used by the Riemann lattice. -/
theorem abs_matsumoto_quadratic_le_coordinateDominatingKernel
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh))
    (hmesh : 1 ≤ mesh) :
    |matsumotoLocalNormalizedTableau shape| ≤
      regevCoordinateDominatingKernel rank (quadraticShapePoint shape) := by
  have hmeshPositive : 0 < mesh := lt_of_lt_of_le Nat.zero_lt_one hmesh
  have hsize : 1 ≤ quadraticSize rank mesh := by
    unfold quadraticSize
    exact Nat.mul_pos (Nat.succ_pos rank) (pow_pos hmeshPositive 2)
  have hbound :=
    abs_matsumotoLocalNormalizedTableau_gaussian_bound shape
      hsize
  rw [regevRowEnvelopeProduct_eq_coordinate shape hmesh] at hbound
  rw [regevPairEnvelopeProduct_eq_coordinate shape hmesh] at hbound
  rw [regevCenteredGaussianSum_eq_coordinate shape hmesh] at hbound
  exact hbound

end FibonacciRibbonKernel
