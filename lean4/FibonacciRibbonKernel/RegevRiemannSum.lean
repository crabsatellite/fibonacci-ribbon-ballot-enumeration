import FibonacciRibbonKernel.RegevRiemannDomain

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Submodule Pointwise
open scoped Classical Topology Pointwise

noncomputable def regevIntegerLattice (rank : ℕ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin rank)))

noncomputable def regevVandermonde (rank : ℕ)
    (coordinates : Fin rank → ℝ) : ℝ :=
  ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
    (tracelessExtend coordinates row - tracelessExtend coordinates next)

noncomputable def regevGaussianKernel (rank : ℕ)
    (coordinates : Fin rank → ℝ) : ℝ :=
  Real.exp (-(∑ row : Fin (rank + 1),
    tracelessExtend coordinates row ^ 2 / 2))

noncomputable def regevLocalIntegrand (rank : ℕ)
    (coordinates : Fin rank → ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
    regevGaussianKernel rank coordinates *
    regevVandermonde rank coordinates

theorem continuous_regevVandermonde (rank : ℕ) :
    Continuous (regevVandermonde rank) := by
  unfold regevVandermonde
  apply continuous_finsetProd Finset.univ
  intro row hrow
  apply continuous_finsetProd (Finset.Ioi row)
  intro next hnext
  exact (continuous_tracelessExtend_apply row).sub
    (continuous_tracelessExtend_apply next)

theorem continuous_regevGaussianKernel (rank : ℕ) :
    Continuous (regevGaussianKernel rank) := by
  unfold regevGaussianKernel
  apply Real.continuous_exp.comp
  apply Continuous.neg
  apply continuous_finsetSum Finset.univ
  intro row hrow
  exact ((continuous_tracelessExtend_apply row).pow 2).div_const 2

theorem continuous_regevLocalIntegrand (rank : ℕ) :
    Continuous (regevLocalIntegrand rank) := by
  unfold regevLocalIntegrand
  exact (continuous_const.mul (continuous_regevGaussianKernel rank)).mul
    (continuous_regevVandermonde rank)

/-- The bounded piece of Matsumoto's lattice sum is a literal unit-lattice
Riemann sum in the traceless coordinate chart. -/
theorem regev_truncated_riemann_sum_tendsto
    (rank : ℕ) (radius : ℝ) :
    Tendsto
      (fun mesh : ℕ =>
        (∑' point : ↑(regevTruncatedChamber rank radius ∩
            (mesh : ℝ)⁻¹ • regevIntegerLattice rank),
          regevLocalIntegrand rank point) /
            mesh ^ Fintype.card (Fin rank))
      atTop
      (nhds (∫ coordinates in regevTruncatedChamber rank radius,
        regevLocalIntegrand rank coordinates)) :=
  tendsto_tsum_div_pow_atTop_integral
    (regevTruncatedChamber rank radius)
    (regevLocalIntegrand rank)
    (continuous_regevLocalIntegrand rank)
    (regevTruncatedChamber_isBounded rank radius)
    (regevTruncatedChamber_measurableSet rank radius)
    (regevTruncatedChamber_null_frontier rank radius)

end FibonacciRibbonKernel
