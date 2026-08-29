import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace FibonacciRibbonKernel

open MeasureTheory Set

/-- The real Gaussian sampled later on the mesh `mesh⁻¹ ℤ`. -/
noncomputable def regevScaledGaussianReal
    (coefficient : ℝ) (mesh : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-coefficient * (x / mesh) ^ 2)

theorem regevScaledGaussianReal_nonneg
    (coefficient : ℝ) (mesh : ℕ) (x : ℝ) :
    0 ≤ regevScaledGaussianReal coefficient mesh x :=
  (Real.exp_pos _).le

theorem regevScaledGaussianReal_neg
    (coefficient : ℝ) (mesh : ℕ) (x : ℝ) :
    regevScaledGaussianReal coefficient mesh (-x) =
      regevScaledGaussianReal coefficient mesh x := by
  unfold regevScaledGaussianReal
  apply congrArg Real.exp
  ring

theorem antitoneOn_regevScaledGaussianReal
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    AntitoneOn (regevScaledGaussianReal coefficient mesh) (Ici 0) := by
  have hmeshReal : (0 : ℝ) < mesh := by exact_mod_cast hmesh
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  have hxdiv : 0 ≤ x / (mesh : ℝ) := div_nonneg hx hmeshReal.le
  have hydiv : 0 ≤ y / (mesh : ℝ) := div_nonneg hy hmeshReal.le
  have hdiv : x / (mesh : ℝ) ≤ y / (mesh : ℝ) :=
    (div_le_div_iff_of_pos_right hmeshReal).2 hxy
  have hsquare : (x / (mesh : ℝ)) ^ 2 ≤
      (y / (mesh : ℝ)) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsquare hcoefficient.le]

theorem integrable_regevScaledGaussianReal
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    Integrable (regevScaledGaussianReal coefficient mesh) := by
  have hmeshReal : (0 : ℝ) < mesh := by exact_mod_cast hmesh
  exact (integrable_exp_neg_mul_sq hcoefficient).comp_div hmeshReal.ne'

theorem summable_nat_regevScaledGaussianReal
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    Summable (fun index : ℕ =>
      regevScaledGaussianReal coefficient mesh index) := by
  exact (antitoneOn_regevScaledGaussianReal hcoefficient hmesh).summable_of_integrableOn_Ioi_zero
      (integrable_regevScaledGaussianReal hcoefficient hmesh).integrableOn
      (fun _ _ => regevScaledGaussianReal_nonneg coefficient mesh _)

end FibonacciRibbonKernel
