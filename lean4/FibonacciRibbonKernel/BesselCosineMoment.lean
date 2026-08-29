import FibonacciRibbonKernel.BesselSpectralFactorization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace FibonacciRibbonKernel

open Real
open scoped Interval

noncomputable def cosinePowerIntegral (power : ℕ) : ℝ :=
  ∫ angle in (0 : ℝ)..Real.pi, Real.cos angle ^ power

noncomputable def cosineMoment (power : ℕ) : ℝ :=
  (2 : ℝ) ^ power / Real.pi * cosinePowerIntegral power

theorem cosinePowerIntegral_zero : cosinePowerIntegral 0 = Real.pi := by
  unfold cosinePowerIntegral
  simp

theorem cosinePowerIntegral_one : cosinePowerIntegral 1 = 0 := by
  unfold cosinePowerIntegral
  simp only [pow_one]
  rw [integral_cos]
  simp

theorem cosinePowerIntegral_succ_succ (power : ℕ) :
    cosinePowerIntegral (power + 2) =
      (power + 1 : ℝ) / (power + 2 : ℝ) * cosinePowerIntegral power := by
  unfold cosinePowerIntegral
  rw [integral_cos_pow]
  simp

theorem cosineMoment_zero : cosineMoment 0 = 1 := by
  rw [cosineMoment, cosinePowerIntegral_zero]
  field_simp [Real.pi_ne_zero]

theorem cosineMoment_one : cosineMoment 1 = 0 := by
  rw [cosineMoment, cosinePowerIntegral_one, mul_zero]

theorem cosineMoment_succ_succ (power : ℕ) :
    cosineMoment (power + 2) =
      (4 : ℝ) * (power + 1 : ℝ) / (power + 2 : ℝ) *
        cosineMoment power := by
  rw [cosineMoment, cosineMoment, cosinePowerIntegral_succ_succ]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpower : (power + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem cosineMoment_eq_integral (power : ℕ) :
    cosineMoment power =
      (1 / Real.pi) *
        ∫ angle in (0 : ℝ)..Real.pi, (2 * Real.cos angle) ^ power := by
  unfold cosineMoment cosinePowerIntegral
  have hfunction : (fun angle : ℝ => (2 * Real.cos angle) ^ power) =
      (fun angle : ℝ => (2 : ℝ) ^ power * Real.cos angle ^ power) := by
    funext angle
    rw [mul_pow]
  rw [hfunction, intervalIntegral.integral_const_mul]
  ring

end FibonacciRibbonKernel
