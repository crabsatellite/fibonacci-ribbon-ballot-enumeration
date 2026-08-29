import FibonacciRibbonKernel.RegevProductLatticeTsum

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def regevScaledCoordinateGaussian
    (rank mesh : ℕ) (point : Fin rank → ℤ) : ℝ :=
  regevCoordinateSeparableGaussian rank
    (fun row => (point row : ℝ) / mesh)

theorem regevScaledCoordinateGaussian_eq_piProduct
    (rank mesh : ℕ) (point : Fin rank → ℤ) :
    regevScaledCoordinateGaussian rank mesh point =
      regevPiProduct
        (regevScaledGaussianLine
          (regevCoordinateGaussianCoefficient rank / 2) mesh)
        rank point := by
  unfold regevScaledCoordinateGaussian
  unfold regevCoordinateSeparableGaussian regevPiProduct
  apply Finset.prod_congr rfl
  intro row hrow
  rfl

theorem summable_regevScaledCoordinateGaussian
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    Summable (regevScaledCoordinateGaussian rank mesh) := by
  let coefficient := regevCoordinateGaussianCoefficient rank / 2
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity [regevCoordinateGaussianCoefficient_pos rank]
  have hline := summable_regevScaledGaussianLine hcoefficient hmesh
  have hproduct := summable_regevPiProduct
    (fun index => regevScaledGaussianLine_nonneg coefficient mesh index)
    hline rank
  refine hproduct.congr (fun point => ?_)
  exact (regevScaledCoordinateGaussian_eq_piProduct rank mesh point).symm

theorem tsum_regevScaledCoordinateGaussian
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    (∑' point : Fin rank → ℤ,
      regevScaledCoordinateGaussian rank mesh point) =
      (∑' index : ℤ,
        regevScaledGaussianLine
          (regevCoordinateGaussianCoefficient rank / 2) mesh index) ^ rank := by
  let coefficient := regevCoordinateGaussianCoefficient rank / 2
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity [regevCoordinateGaussianCoefficient_pos rank]
  have hline := summable_regevScaledGaussianLine hcoefficient hmesh
  rw [show (∑' point : Fin rank → ℤ,
      regevScaledCoordinateGaussian rank mesh point) =
      ∑' point : Fin rank → ℤ,
        regevPiProduct (regevScaledGaussianLine coefficient mesh)
          rank point by
    apply tsum_congr
    intro point
    exact regevScaledCoordinateGaussian_eq_piProduct rank mesh point]
  exact tsum_regevPiProduct
    (fun index => regevScaledGaussianLine_nonneg coefficient mesh index)
    hline rank

/-- Mesh-independent total-mass bound for the rank-dimensional separable
Gaussian sampled on the exact integer lattice. -/
theorem regevScaledCoordinateGaussian_total_bound
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    (∑' point : Fin rank → ℤ,
      regevScaledCoordinateGaussian rank mesh point) / mesh ^ rank ≤
      (2 + 2 * Real.sqrt (Real.pi /
        (regevCoordinateGaussianCoefficient rank / 2))) ^ rank := by
  let coefficient := regevCoordinateGaussianCoefficient rank / 2
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity [regevCoordinateGaussianCoefficient_pos rank]
  rw [tsum_regevScaledCoordinateGaussian rank hmesh]
  rw [← div_pow]
  apply pow_le_pow_left₀
  · exact div_nonneg
      (tsum_nonneg fun index =>
        regevScaledGaussianLine_nonneg coefficient mesh index)
      (Nat.cast_nonneg mesh)
  · exact regevScaledGaussianLine_total_bound hcoefficient hmesh

end FibonacciRibbonKernel
