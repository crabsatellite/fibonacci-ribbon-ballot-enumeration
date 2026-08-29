import FibonacciRibbonKernel.RegevGaussianLattice

namespace FibonacciRibbonKernel

open Set
open scoped Classical

def regevGaussianTailIndex (mesh : ℕ) (radius : ℝ) : Set ℤ :=
  {index | radius ≤ |(index : ℝ) / mesh|}

theorem regevScaledGaussianLine_tail_pointwise
    {coefficient radius : ℝ} (hcoefficient : 0 < coefficient)
    (hradius : 0 ≤ radius) {mesh : ℕ}
    (index : regevGaussianTailIndex mesh radius) :
    regevScaledGaussianLine coefficient mesh index.1 ≤
      Real.exp (-(coefficient / 2) * radius ^ 2) *
        regevScaledGaussianLine (coefficient / 2) mesh index.1 := by
  have hradiusLe : radius ≤ |(index.1 : ℝ) / mesh| := by
    exact index.2
  have habsNonneg : 0 ≤ |(index.1 : ℝ) / mesh| := abs_nonneg _
  have hsquare : radius ^ 2 ≤ |(index.1 : ℝ) / mesh| ^ 2 := by
    nlinarith [hradiusLe]
  have habsSquare : |(index.1 : ℝ) / mesh| ^ 2 =
      ((index.1 : ℝ) / mesh) ^ 2 := sq_abs _
  unfold regevScaledGaussianLine regevScaledGaussianReal
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [habsSquare] at hsquare
  nlinarith

/-- Uniform one-dimensional Gaussian tail bound on every nonzero mesh. -/
theorem regevScaledGaussianLine_tail_bound
    {coefficient radius : ℝ} (hcoefficient : 0 < coefficient)
    (hradius : 0 ≤ radius) {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    (∑' index : regevGaussianTailIndex mesh radius,
        regevScaledGaussianLine coefficient mesh index.1) / mesh ≤
      Real.exp (-(coefficient / 2) * radius ^ 2) *
        (2 + 2 * Real.sqrt (Real.pi / (coefficient / 2))) := by
  let factor := Real.exp (-(coefficient / 2) * radius ^ 2)
  have hhalfPositive : 0 < coefficient / 2 := by positivity
  have hfactorNonneg : 0 ≤ factor := (Real.exp_pos _).le
  have hleft :=
    (summable_regevScaledGaussianLine hcoefficient hmesh).subtype
      (regevGaussianTailIndex mesh radius)
  have hhalf := summable_regevScaledGaussianLine hhalfPositive hmesh
  have hhalfSubtype := hhalf.subtype (regevGaussianTailIndex mesh radius)
  have hsumBound :
      (∑' index : regevGaussianTailIndex mesh radius,
          regevScaledGaussianLine coefficient mesh index.1) ≤
        factor *
          ∑' index : ℤ,
            regevScaledGaussianLine (coefficient / 2) mesh index := by
    calc
      (∑' index : regevGaussianTailIndex mesh radius,
          regevScaledGaussianLine coefficient mesh index.1) ≤
        ∑' index : regevGaussianTailIndex mesh radius,
          factor * regevScaledGaussianLine
            (coefficient / 2) mesh index.1 :=
          hleft.tsum_le_tsum
            (fun index => regevScaledGaussianLine_tail_pointwise
              hcoefficient hradius index)
            (hhalfSubtype.mul_left factor)
      _ = factor *
          ∑' index : regevGaussianTailIndex mesh radius,
            regevScaledGaussianLine (coefficient / 2) mesh index.1 :=
        tsum_mul_left
      _ ≤ factor *
          ∑' index : ℤ,
            regevScaledGaussianLine (coefficient / 2) mesh index := by
        apply mul_le_mul_of_nonneg_left _ hfactorNonneg
        exact Summable.tsum_subtype_le
          (regevScaledGaussianLine (coefficient / 2) mesh)
          (regevGaussianTailIndex mesh radius)
          (fun _ => regevScaledGaussianLine_nonneg _ _ _)
          hhalf
  have hmeshReal : (0 : ℝ) < mesh := by exact_mod_cast hmesh
  have hnormalized :=
    div_le_div_of_nonneg_right hsumBound hmeshReal.le
  calc
    (∑' index : regevGaussianTailIndex mesh radius,
        regevScaledGaussianLine coefficient mesh index.1) / mesh ≤
      (factor * ∑' index : ℤ,
        regevScaledGaussianLine (coefficient / 2) mesh index) / mesh :=
      hnormalized
    _ = factor *
        ((∑' index : ℤ,
          regevScaledGaussianLine (coefficient / 2) mesh index) / mesh) := by
      ring
    _ ≤ factor *
        (2 + 2 * Real.sqrt (Real.pi / (coefficient / 2))) :=
      mul_le_mul_of_nonneg_left
        (regevScaledGaussianLine_total_bound hhalfPositive hmesh)
        hfactorNonneg

end FibonacciRibbonKernel
