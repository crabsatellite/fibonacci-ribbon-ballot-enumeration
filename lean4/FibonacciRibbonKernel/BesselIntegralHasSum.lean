import FibonacciRibbonKernel.OddGesselFormalSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace FibonacciRibbonKernel

open MeasureTheory
open NormedSpace

noncomputable def realBesselSeriesTerm
    (order : ℤ) (parameter : ℝ) (power : ℕ) (angle : ℝ) : ℝ :=
  ((2 * Real.cos angle) ^ power *
      Real.cos ((order : ℝ) * angle) /
        (power.factorial : ℝ)) * parameter ^ power

theorem integrable_realBesselSeriesTerm
    (order : ℤ) (parameter : ℝ) (power : ℕ) :
    Integrable (realBesselSeriesTerm order parameter power)
      cosineIntervalMeasure := by
  apply integrable_continuous_cosineInterval
  unfold realBesselSeriesTerm
  fun_prop

theorem norm_realBesselSeriesTerm_le
    (order : ℤ) (parameter : ℝ) (power : ℕ) (angle : ℝ) :
    ‖realBesselSeriesTerm order parameter power angle‖ ≤
      (2 * |parameter|) ^ power / (power.factorial : ℝ) := by
  unfold realBesselSeriesTerm
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_pow]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ power.factorial)]
  have hcos := Real.abs_cos_le_one angle
  calc
    (|2| * |Real.cos angle|) ^ power *
          |Real.cos ((order : ℝ) * angle)| /
        (power.factorial : ℝ) * |parameter| ^ power ≤
      (2 : ℝ) ^ power * 1 /
        (power.factorial : ℝ) * |parameter| ^ power := by
        gcongr
        · norm_num
          exact hcos
        · exact Real.abs_cos_le_one _
    _ = (2 * |parameter|) ^ power / (power.factorial : ℝ) := by
      rw [mul_pow]
      ring

theorem summable_realBesselSeriesBound (parameter : ℝ) :
    Summable (fun power : ℕ =>
      (2 * |parameter|) ^ power / (power.factorial : ℝ)) :=
  (NormedSpace.expSeries_div_hasSum_exp (2 * |parameter|)).summable

theorem hasSum_realBesselSeriesTerm_pointwise
    (order : ℤ) (parameter angle : ℝ) :
    HasSum (fun power => realBesselSeriesTerm order parameter power angle)
      (Real.exp (2 * parameter * Real.cos angle) *
        Real.cos ((order : ℝ) * angle)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    (2 * parameter * Real.cos angle)).mul_right
      (Real.cos ((order : ℝ) * angle))
  rw [show (fun power => realBesselSeriesTerm order parameter power angle) =
      fun power =>
        (2 * parameter * Real.cos angle) ^ power /
          (power.factorial : ℝ) * Real.cos ((order : ℝ) * angle) by
    funext power
    unfold realBesselSeriesTerm
    rw [mul_pow]
    ring]
  simpa only [Real.exp_eq_exp_ℝ] using h

theorem integral_realBesselSeriesTerm
    (order : ℤ) (parameter : ℝ) (power : ℕ) :
    (∫ angle : ℝ, realBesselSeriesTerm order parameter power angle
      ∂cosineIntervalMeasure) =
      PowerSeries.coeff power (realBesselIntegralSeries order) *
        parameter ^ power := by
  rw [realBesselIntegralSeries_coeff]
  unfold realBesselSeriesTerm
  rw [show (fun angle : ℝ =>
      ((2 * Real.cos angle) ^ power *
        Real.cos ((order : ℝ) * angle) /
          (power.factorial : ℝ)) * parameter ^ power) =
      fun angle => (parameter ^ power / (power.factorial : ℝ)) *
        ((2 * Real.cos angle) ^ power *
          Real.cos ((order : ℝ) * angle)) by
    funext angle
    ring]
  rw [integral_const_mul, integral_cosineIntervalMeasure_eq_interval]
  ring

theorem realBesselIntegralSeries_hasSum
    (order : ℤ) (parameter : ℝ) :
    HasSum (fun power =>
      PowerSeries.coeff power (realBesselIntegralSeries order) *
        parameter ^ power)
      (realBesselCosineIntegral order parameter) := by
  have hsum := hasSum_integral_of_dominated_convergence
    (fun power : ℕ => fun _angle : ℝ =>
      (2 * |parameter|) ^ power / (power.factorial : ℝ))
    (fun power =>
      (integrable_realBesselSeriesTerm order parameter power).aestronglyMeasurable)
    (fun power => Filter.Eventually.of_forall fun angle =>
      norm_realBesselSeriesTerm_le order parameter power angle)
    (Filter.Eventually.of_forall fun _angle =>
      summable_realBesselSeriesBound parameter)
    (by
      have hsumValue := (NormedSpace.expSeries_div_hasSum_exp
        (2 * |parameter|)).tsum_eq
      rw [show (fun _angle : ℝ =>
          ∑' power : ℕ,
            (2 * |parameter|) ^ power / (power.factorial : ℝ)) =
        fun _angle => Real.exp (2 * |parameter|) by
          funext angle
          simpa only [Real.exp_eq_exp_ℝ] using hsumValue]
      exact integrable_const _)
    (Filter.Eventually.of_forall fun angle =>
      hasSum_realBesselSeriesTerm_pointwise order parameter angle)
  unfold realBesselCosineIntegral
  rw [show (fun power =>
      PowerSeries.coeff power (realBesselIntegralSeries order) *
        parameter ^ power) =
      fun power => ∫ angle : ℝ,
        realBesselSeriesTerm order parameter power angle
        ∂cosineIntervalMeasure by
    funext power
    exact (integral_realBesselSeriesTerm order parameter power).symm]
  exact hsum

end FibonacciRibbonKernel
