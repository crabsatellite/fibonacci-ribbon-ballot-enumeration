import FibonacciRibbonKernel.BesselOneFactorMoment

namespace FibonacciRibbonKernel

open PowerSeries Real
open MeasureTheory
open scoped Interval

noncomputable def besselPlusFactorialCoeffReal (power : ℕ) : ℝ :=
  (((power.factorial : ℚ) *
    PowerSeries.coeff power (besselJ0 + besselJ1) : ℚ) : ℝ)

noncomputable def besselMinusFactorialCoeffReal (power : ℕ) : ℝ :=
  (((power.factorial : ℚ) *
    PowerSeries.coeff power (besselJ0 - besselJ1) : ℚ) : ℝ)

theorem besselJ0FactorialCoeffReal_eq_integral (power : ℕ) :
    besselJ0FactorialCoeffReal power =
      (1 / Real.pi) *
        ∫ angle in (0 : ℝ)..Real.pi, (2 * Real.cos angle) ^ power := by
  rw [besselJ0FactorialCoeffReal_eq_cosineMoment,
    cosineMoment_eq_integral]

theorem besselJ1FactorialCoeffReal_eq_integral (power : ℕ) :
    besselJ1FactorialCoeffReal power =
      (1 / Real.pi) *
        ∫ angle in (0 : ℝ)..Real.pi,
          (2 * Real.cos angle) ^ power * Real.cos angle := by
  rw [besselJ1FactorialCoeffReal_eq_half_succ_cosineMoment,
    cosineMoment_eq_integral]
  have hfunction :
      (fun angle : ℝ => (2 * Real.cos angle) ^ (power + 1)) =
        fun angle : ℝ => 2 *
          ((2 * Real.cos angle) ^ power * Real.cos angle) := by
    funext angle
    rw [pow_succ]
    ring
  rw [hfunction, intervalIntegral.integral_const_mul]
  ring

theorem besselPlusFactorialCoeffReal_eq_sum (power : ℕ) :
    besselPlusFactorialCoeffReal power =
      besselJ0FactorialCoeffReal power + besselJ1FactorialCoeffReal power := by
  unfold besselPlusFactorialCoeffReal besselJ0FactorialCoeffReal
  unfold besselJ1FactorialCoeffReal besselJ0FactorialCoeffQ
  unfold besselJ1FactorialCoeffQ
  rw [map_add]
  push_cast
  ring

theorem besselMinusFactorialCoeffReal_eq_sub (power : ℕ) :
    besselMinusFactorialCoeffReal power =
      besselJ0FactorialCoeffReal power - besselJ1FactorialCoeffReal power := by
  unfold besselMinusFactorialCoeffReal besselJ0FactorialCoeffReal
  unfold besselJ1FactorialCoeffReal besselJ0FactorialCoeffQ
  unfold besselJ1FactorialCoeffQ
  rw [map_sub]
  push_cast
  ring

theorem besselPlusFactorialCoeffReal_eq_integral (power : ℕ) :
    besselPlusFactorialCoeffReal power =
      (1 / Real.pi) *
        ∫ angle in (0 : ℝ)..Real.pi,
          (2 * Real.cos angle) ^ power * (1 + Real.cos angle) := by
  rw [besselPlusFactorialCoeffReal_eq_sum,
    besselJ0FactorialCoeffReal_eq_integral,
    besselJ1FactorialCoeffReal_eq_integral]
  have hbaseContinuous : Continuous
      (fun angle : ℝ => (2 * Real.cos angle) ^ power) :=
    (continuous_const.mul Real.continuous_cos).pow power
  have hcosContinuous : Continuous
      (fun angle : ℝ => (2 * Real.cos angle) ^ power * Real.cos angle)
      := hbaseContinuous.mul Real.continuous_cos
  have hbase : IntervalIntegrable
      (fun angle : ℝ => (2 * Real.cos angle) ^ power) volume 0 Real.pi :=
    hbaseContinuous.intervalIntegrable 0 Real.pi
  have hcos : IntervalIntegrable
      (fun angle : ℝ => (2 * Real.cos angle) ^ power * Real.cos angle)
      volume 0 Real.pi := hcosContinuous.intervalIntegrable 0 Real.pi
  have hfunction : (fun angle : ℝ =>
      (2 * Real.cos angle) ^ power * (1 + Real.cos angle)) =
      ((fun angle : ℝ => (2 * Real.cos angle) ^ power) +
        fun angle : ℝ => (2 * Real.cos angle) ^ power * Real.cos angle) := by
    funext angle
    simp only [Pi.add_apply]
    ring
  rw [hfunction]
  change (1 / Real.pi) *
      (∫ angle in (0 : ℝ)..Real.pi, (2 * Real.cos angle) ^ power) +
      (1 / Real.pi) *
        (∫ angle in (0 : ℝ)..Real.pi,
          (2 * Real.cos angle) ^ power * Real.cos angle) =
    (1 / Real.pi) *
      (∫ angle in (0 : ℝ)..Real.pi,
        (2 * Real.cos angle) ^ power +
          (2 * Real.cos angle) ^ power * Real.cos angle)
  rw [intervalIntegral.integral_add hbase hcos]
  ring

theorem besselMinusFactorialCoeffReal_eq_integral (power : ℕ) :
    besselMinusFactorialCoeffReal power =
      (1 / Real.pi) *
        ∫ angle in (0 : ℝ)..Real.pi,
          (2 * Real.cos angle) ^ power * (1 - Real.cos angle) := by
  rw [besselMinusFactorialCoeffReal_eq_sub,
    besselJ0FactorialCoeffReal_eq_integral,
    besselJ1FactorialCoeffReal_eq_integral]
  have hbaseContinuous : Continuous
      (fun angle : ℝ => (2 * Real.cos angle) ^ power) :=
    (continuous_const.mul Real.continuous_cos).pow power
  have hcosContinuous : Continuous
      (fun angle : ℝ => (2 * Real.cos angle) ^ power * Real.cos angle)
      := hbaseContinuous.mul Real.continuous_cos
  have hbase : IntervalIntegrable
      (fun angle : ℝ => (2 * Real.cos angle) ^ power) volume 0 Real.pi :=
    hbaseContinuous.intervalIntegrable 0 Real.pi
  have hcos : IntervalIntegrable
      (fun angle : ℝ => (2 * Real.cos angle) ^ power * Real.cos angle)
      volume 0 Real.pi := hcosContinuous.intervalIntegrable 0 Real.pi
  have hfunction : (fun angle : ℝ =>
      (2 * Real.cos angle) ^ power * (1 - Real.cos angle)) =
      ((fun angle : ℝ => (2 * Real.cos angle) ^ power) -
        fun angle : ℝ => (2 * Real.cos angle) ^ power * Real.cos angle) := by
    funext angle
    simp only [Pi.sub_apply]
    ring
  rw [hfunction]
  change (1 / Real.pi) *
      (∫ angle in (0 : ℝ)..Real.pi, (2 * Real.cos angle) ^ power) -
      (1 / Real.pi) *
        (∫ angle in (0 : ℝ)..Real.pi,
          (2 * Real.cos angle) ^ power * Real.cos angle) =
    (1 / Real.pi) *
      (∫ angle in (0 : ℝ)..Real.pi,
        (2 * Real.cos angle) ^ power -
          (2 * Real.cos angle) ^ power * Real.cos angle)
  rw [intervalIntegral.integral_sub hbase hcos]
  ring

end FibonacciRibbonKernel
