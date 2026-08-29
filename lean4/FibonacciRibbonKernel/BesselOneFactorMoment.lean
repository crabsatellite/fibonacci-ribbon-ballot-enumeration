import FibonacciRibbonKernel.BesselCosineMoment

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def besselJ0FactorialCoeffQ (power : ℕ) : ℚ :=
  (power.factorial : ℚ) * PowerSeries.coeff power besselJ0

noncomputable def besselJ1FactorialCoeffQ (power : ℕ) : ℚ :=
  (power.factorial : ℚ) * PowerSeries.coeff power besselJ1

noncomputable def besselJ0FactorialCoeffReal (power : ℕ) : ℝ :=
  (besselJ0FactorialCoeffQ power : ℝ)

noncomputable def besselJ1FactorialCoeffReal (power : ℕ) : ℝ :=
  (besselJ1FactorialCoeffQ power : ℝ)

theorem besselJ0FactorialCoeffQ_zero : besselJ0FactorialCoeffQ 0 = 1 := by
  simp [besselJ0FactorialCoeffQ, besselJ0]

theorem besselJ0FactorialCoeffQ_one : besselJ0FactorialCoeffQ 1 = 0 := by
  simp [besselJ0FactorialCoeffQ, besselJ0]

theorem besselJ0FactorialCoeffQ_succ_succ (power : ℕ) :
    besselJ0FactorialCoeffQ (power + 2) =
      (4 : ℚ) * (power + 1 : ℚ) / (power + 2 : ℚ) *
        besselJ0FactorialCoeffQ power := by
  obtain ⟨half, rfl | rfl⟩ := Nat.even_or_odd' power
  · unfold besselJ0FactorialCoeffQ
    rw [show 2 * half + 2 = 2 * (half + 1) by omega,
      besselJ0_coeff_even, besselJ0_coeff_even]
    rw [show 2 * (half + 1) = (2 * half + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · unfold besselJ0FactorialCoeffQ
    rw [show 2 * half + 1 + 2 = 2 * (half + 1) + 1 by omega,
      besselJ0_coeff_odd, besselJ0_coeff_odd]
    simp

theorem besselJ0FactorialCoeffReal_zero :
    besselJ0FactorialCoeffReal 0 = 1 := by
  norm_num [besselJ0FactorialCoeffReal, besselJ0FactorialCoeffQ_zero]

theorem besselJ0FactorialCoeffReal_one :
    besselJ0FactorialCoeffReal 1 = 0 := by
  norm_num [besselJ0FactorialCoeffReal, besselJ0FactorialCoeffQ_one]

theorem besselJ0FactorialCoeffReal_succ_succ (power : ℕ) :
    besselJ0FactorialCoeffReal (power + 2) =
      (4 : ℝ) * (power + 1 : ℝ) / (power + 2 : ℝ) *
        besselJ0FactorialCoeffReal power := by
  unfold besselJ0FactorialCoeffReal
  have hreal := congrArg (fun value : ℚ => (value : ℝ))
    (besselJ0FactorialCoeffQ_succ_succ power)
  push_cast at hreal
  exact hreal

theorem besselJ0FactorialCoeffReal_eq_cosineMoment (power : ℕ) :
    besselJ0FactorialCoeffReal power = cosineMoment power := by
  induction power using Nat.twoStepInduction with
  | zero => rw [besselJ0FactorialCoeffReal_zero, cosineMoment_zero]
  | one => rw [besselJ0FactorialCoeffReal_one, cosineMoment_one]
  | more power hzero _hone =>
      rw [besselJ0FactorialCoeffReal_succ_succ,
        cosineMoment_succ_succ, hzero]

theorem besselJ1FactorialCoeffQ_eq_half_succ_J0 (power : ℕ) :
    besselJ1FactorialCoeffQ power =
      besselJ0FactorialCoeffQ (power + 1) / 2 := by
  have hderivative := congrArg (PowerSeries.coeff power) derivative_besselJ0
  rw [PowerSeries.coeff_derivative, coeff_two_mul] at hderivative
  unfold besselJ1FactorialCoeffQ besselJ0FactorialCoeffQ
  rw [Nat.factorial_succ]
  push_cast
  have hcoefficient :
      PowerSeries.coeff power besselJ1 =
        PowerSeries.coeff (power + 1) besselJ0 * (power + 1 : ℚ) / 2 := by
    linarith [hderivative]
  rw [hcoefficient]
  ring

theorem besselJ1FactorialCoeffReal_eq_half_succ_cosineMoment (power : ℕ) :
    besselJ1FactorialCoeffReal power = cosineMoment (power + 1) / 2 := by
  unfold besselJ1FactorialCoeffReal
  rw [besselJ1FactorialCoeffQ_eq_half_succ_J0]
  push_cast
  change besselJ0FactorialCoeffReal (power + 1) / 2 =
    cosineMoment (power + 1) / 2
  rw [besselJ0FactorialCoeffReal_eq_cosineMoment]

end FibonacciRibbonKernel
