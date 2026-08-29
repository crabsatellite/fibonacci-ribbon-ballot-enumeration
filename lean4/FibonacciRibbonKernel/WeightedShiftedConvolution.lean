import FibonacciRibbonKernel.RibbonLogPullback
import Mathlib.Analysis.Normed.Group.Tannery

namespace FibonacciRibbonKernel

open Filter

/-!
# Dominated transfer for weighted shifted convolutions

This is the Tannery-theorem core of the power--logarithm transfer.  It is
stated for an arbitrary countable multiplier carrier; in the ribbon
application that carrier is `(i,j)` and its exact degree shift is `i+2j`.
-/

noncomputable def shiftedCoefficientRatio
    (source comparison : ℕ → ℝ) (shift index : ℕ) : ℝ :=
  if shift ≤ index then source (index - shift) / comparison index else 0

noncomputable def weightedShiftedConvolutionRatio
    {carrier : Type*} (weight : carrier → ℝ) (shift : carrier → ℕ)
    (source comparison : ℕ → ℝ) (index : ℕ) : ℝ :=
  ∑' point : carrier,
    weight point *
      shiftedCoefficientRatio source comparison (shift point) index

theorem tendsto_weightedShiftedConvolutionRatio
    {carrier : Type*}
    (weight : carrier → ℝ) (shift : carrier → ℕ)
    (source comparison : ℕ → ℝ) (limitWeight bound : carrier → ℝ)
    (hpoint : ∀ point : carrier,
      Tendsto
        (shiftedCoefficientRatio source comparison (shift point))
        atTop (nhds (limitWeight point)))
    (hsummable : Summable (fun point : carrier => |weight point| * bound point))
    (hbound : ∀ᶠ index : ℕ in atTop, ∀ point : carrier,
      ‖shiftedCoefficientRatio source comparison (shift point) index‖ ≤
        bound point) :
    Tendsto
      (weightedShiftedConvolutionRatio weight shift source comparison)
      atTop
      (nhds (∑' point : carrier, weight point * limitWeight point)) := by
  unfold weightedShiftedConvolutionRatio
  apply tendsto_tsum_of_dominated_convergence hsummable
  · intro point
    exact tendsto_const_nhds.mul (hpoint point)
  · filter_upwards [hbound] with index hindex
    intro point
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hindex point) (abs_nonneg _)

end FibonacciRibbonKernel
