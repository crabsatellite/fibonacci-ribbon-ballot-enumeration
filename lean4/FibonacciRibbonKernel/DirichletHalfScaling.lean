import FibonacciRibbonKernel.DirichletHalfGeometry

namespace FibonacciRibbonKernel

open Set
open scoped Classical

theorem dirichletConsTransform_residual (dimension : ℕ)
    (input : ℝ × (Fin dimension → ℝ)) :
    1 - ∑ index, dirichletConsTransform dimension input index =
      (1 - input.1) * (1 - ∑ index, input.2 index) := by
  rw [dirichletConsTransform_sum]
  ring

theorem dirichletHalf_tail_product_scale
    (dimension : ℕ) (scale : ℝ) (coordinates : Fin dimension → ℝ)
    (hscale : 0 ≤ scale) (hcoordinates : ∀ index, 0 ≤ coordinates index) :
    (∏ index, (scale * coordinates index) ^ (-1 / 2 : ℝ)) =
      (scale ^ (-1 / 2 : ℝ)) ^ dimension *
        ∏ index, coordinates index ^ (-1 / 2 : ℝ) := by
  simp_rw [Real.mul_rpow hscale (hcoordinates _)]
  rw [Finset.prod_mul_distrib]
  simp

theorem dirichletHalf_scale_power (dimension : ℕ) {scale : ℝ}
    (hscale : 0 < scale) :
    (scale ^ (-1 / 2 : ℝ)) ^ dimension *
        scale ^ (-1 / 2 : ℝ) =
      scale ^ (-((dimension + 1 : ℕ) : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hscale.le]
  rw [← Real.rpow_add hscale]
  congr 1
  push_cast
  ring

theorem dirichletHalfIntegrand_cons_scale
    (dimension : ℕ) (input : ℝ × (Fin dimension → ℝ))
    (hfirst : input.1 ∈ Set.Ioo (0 : ℝ) 1)
    (htail : input.2 ∈ dirichletOpenSimplex dimension) :
    dirichletHalfIntegrand (dimension + 1)
        (dirichletConsTransform dimension input) =
      input.1 ^ (-1 / 2 : ℝ) *
        (1 - input.1) ^ (-((dimension + 1 : ℕ) : ℝ) / 2) *
          dirichletHalfIntegrand dimension input.2 := by
  have hscale : 0 < 1 - input.1 := sub_pos.mpr hfirst.2
  have hcoordinates : ∀ index, 0 ≤ input.2 index :=
    fun index => (htail.1 index).le
  have hresidual : 0 < 1 - ∑ index, input.2 index :=
    sub_pos.mpr htail.2
  unfold dirichletHalfIntegrand
  rw [Fin.prod_univ_succ]
  simp only [dirichletConsTransform_zero,
    dirichletConsTransform_succ]
  rw [dirichletHalf_tail_product_scale dimension
    (1 - input.1) input.2 hscale.le hcoordinates]
  rw [dirichletConsTransform_residual]
  rw [Real.mul_rpow hscale.le hresidual.le]
  have hpower := dirichletHalf_scale_power dimension hscale
  linear_combination
    input.1 ^ (-1 / 2 : ℝ) *
      (∏ index, input.2 index ^ (-1 / 2 : ℝ)) *
      (1 - ∑ index, input.2 index) ^ (-1 / 2 : ℝ) * hpower

end FibonacciRibbonKernel
