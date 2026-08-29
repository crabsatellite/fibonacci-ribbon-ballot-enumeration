import FibonacciRibbonKernel.RibbonAnalyticMultiplier
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.ConvergenceRadius

namespace FibonacciRibbonKernel

open Filter

/-!
# Kernel convergence of generalized-binomial coefficient series

The formal power-series identities used by the pullback are paired here with
their analytic meaning strictly inside the unit disk, including absolute
summability.  These are the inputs needed by the coefficient-convolution
transfer theorem.
-/

theorem generalizedBinomial_hasSum
    (parameter x : ℝ) (hx : |x| < 1) :
    HasSum (fun index : ℕ => Ring.choose parameter index * x ^ index)
      ((1 + x) ^ parameter) := by
  have hxBall : x ∈ Metric.eball (0 : ℝ) (1 : ENNReal) := by
    simpa [Metric.mem_eball, edist_dist, dist_zero_right,
      Real.norm_eq_abs, ENNReal.ofReal_lt_one] using hx
  have hsum :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
      (a := parameter)).hasSum_sub hxBall
  have hcoeff : ∀ index : ℕ,
      (binomialSeries ℝ parameter).coeff index =
        Ring.choose parameter index := by
    intro index
    simp [binomialSeries]
  simpa [binomialSeries_apply, hcoeff, mul_comm] using hsum

theorem generalizedBinomial_summable_abs
    (parameter x : ℝ) (hx : |x| < 1) :
    Summable (fun index : ℕ =>
      |Ring.choose parameter index * x ^ index|) := by
  let series := binomialSeries ℝ parameter
  have hpower := Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := parameter)
  have hxBall : x ∈ Metric.eball (0 : ℝ) (1 : ENNReal) := by
    simpa [Metric.mem_eball, edist_dist, dist_zero_right,
      Real.norm_eq_abs, ENNReal.ofReal_lt_one] using hx
  have hxRadius : x ∈ Metric.eball (0 : ℝ) series.radius :=
    Metric.eball_subset_eball hpower.r_le hxBall
  have hsummable := series.summable_norm_apply hxRadius
  have hcoeff : ∀ index : ℕ,
      series.coeff index = Ring.choose parameter index := by
    intro index
    simp [series, binomialSeries]
  simpa [series, binomialSeries_apply, hcoeff,
    Real.norm_eq_abs, abs_mul, mul_comm] using hsummable

theorem generalizedBinomial_summable
    (parameter x : ℝ) (hx : |x| < 1) :
    Summable (fun index : ℕ => Ring.choose parameter index * x ^ index) := by
  apply Summable.of_norm
  simpa [Real.norm_eq_abs] using
    generalizedBinomial_summable_abs parameter x hx

end FibonacciRibbonKernel
