import FibonacciRibbonKernel.RegevGaussianLineBase

namespace FibonacciRibbonKernel

/-- The one-dimensional Gaussian sampled on the exact `mesh⁻¹ ℤ` lattice. -/
noncomputable def regevScaledGaussianLine
    (coefficient : ℝ) (mesh : ℕ) (index : ℤ) : ℝ :=
  regevScaledGaussianReal coefficient mesh index

theorem regevScaledGaussianLine_nonneg
    (coefficient : ℝ) (mesh : ℕ) (index : ℤ) :
    0 ≤ regevScaledGaussianLine coefficient mesh index :=
  (Real.exp_pos _).le

/-- Gaussian samples on every nonzero mesh are genuinely summable; this is
proved by the integral test, not inserted as an analytic premise. -/
theorem summable_regevScaledGaussianLine
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    Summable (regevScaledGaussianLine coefficient mesh) := by
  have hnat := summable_nat_regevScaledGaussianReal hcoefficient hmesh
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [regevScaledGaussianLine] using hnat
  · refine hnat.congr (fun index => ?_)
    simpa [regevScaledGaussianLine] using
      (regevScaledGaussianReal_neg coefficient mesh
        (index : ℝ)).symm

end FibonacciRibbonKernel
