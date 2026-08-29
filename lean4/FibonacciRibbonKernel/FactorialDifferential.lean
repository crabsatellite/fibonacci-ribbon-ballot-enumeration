import FibonacciRibbonKernel.SpecialRankSums
import Mathlib.RingTheory.PowerSeries.Derivative

namespace FibonacciRibbonKernel

open PowerSeries

/-- Exponential generating series with rational sequence coefficients. -/
noncomputable def factorialSeries (sequence : ℕ → ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun index => sequence index / (index.factorial : ℚ)

@[simp] theorem factorialSeries_coeff (sequence : ℕ → ℚ) (index : ℕ) :
    PowerSeries.coeff index (factorialSeries sequence) =
      sequence index / (index.factorial : ℚ) := by
  simp [factorialSeries]

/-- Formal differentiation shifts an exponential-generating sequence. -/
theorem derivative_factorialSeries (sequence : ℕ → ℚ) :
    PowerSeries.derivative ℚ (factorialSeries sequence) =
      factorialSeries (fun index => sequence (index + 1)) := by
  ext index
  rw [PowerSeries.coeff_derivative]
  simp only [factorialSeries_coeff]
  rw [Nat.factorial_succ]
  push_cast
  have hfactorial : (index.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem derivative_two_factorialSeries (sequence : ℕ → ℚ) :
    PowerSeries.derivative ℚ
        (PowerSeries.derivative ℚ (factorialSeries sequence)) =
      factorialSeries (fun index => sequence (index + 2)) := by
  rw [derivative_factorialSeries, derivative_factorialSeries]

theorem derivative_three_factorialSeries (sequence : ℕ → ℚ) :
    PowerSeries.derivative ℚ
        (PowerSeries.derivative ℚ
          (PowerSeries.derivative ℚ (factorialSeries sequence))) =
      factorialSeries (fun index => sequence (index + 3)) := by
  rw [derivative_two_factorialSeries, derivative_factorialSeries]

theorem derivative_four_factorialSeries (sequence : ℕ → ℚ) :
    PowerSeries.derivative ℚ
        (PowerSeries.derivative ℚ
          (PowerSeries.derivative ℚ
            (PowerSeries.derivative ℚ (factorialSeries sequence)))) =
      factorialSeries (fun index => sequence (index + 4)) := by
  rw [derivative_three_factorialSeries, derivative_factorialSeries]

/-- Coefficient normalized by `m!`; on an EGF this recovers the sequence. -/
noncomputable def factorialScaledCoeff (index : ℕ) (series : ℚ⟦X⟧) : ℚ :=
  (index.factorial : ℚ) * PowerSeries.coeff index series

@[simp] theorem factorialScaledCoeff_factorialSeries
    (sequence : ℕ → ℚ) (index : ℕ) :
    factorialScaledCoeff index (factorialSeries sequence) = sequence index := by
  rw [factorialScaledCoeff, factorialSeries_coeff]
  have hfactorial : (index.factorial : ℚ) ≠ 0 := by positivity
  field_simp

@[simp] theorem factorialScaledCoeff_zero (index : ℕ) :
    factorialScaledCoeff index (0 : ℚ⟦X⟧) = 0 := by
  simp [factorialScaledCoeff]

@[simp] theorem factorialScaledCoeff_add
    (index : ℕ) (left right : ℚ⟦X⟧) :
    factorialScaledCoeff index (left + right) =
      factorialScaledCoeff index left + factorialScaledCoeff index right := by
  simp [factorialScaledCoeff, mul_add]

@[simp] theorem factorialScaledCoeff_sub
    (index : ℕ) (left right : ℚ⟦X⟧) :
    factorialScaledCoeff index (left - right) =
      factorialScaledCoeff index left - factorialScaledCoeff index right := by
  simp [factorialScaledCoeff, mul_sub]

@[simp] theorem factorialScaledCoeff_C_mul
    (index : ℕ) (scalar : ℚ) (series : ℚ⟦X⟧) :
    factorialScaledCoeff index (PowerSeries.C scalar * series) =
      scalar * factorialScaledCoeff index series := by
  simp [factorialScaledCoeff, mul_comm, mul_left_comm]

theorem factorialScaledCoeff_X_mul
    (index : ℕ) (series : ℚ⟦X⟧) :
    factorialScaledCoeff (index + 1) (X * series) =
      (index + 1 : ℚ) * factorialScaledCoeff index series := by
  rw [factorialScaledCoeff, show (X : ℚ⟦X⟧) = X ^ 1 by simp]
  rw [PowerSeries.coeff_X_pow_mul]
  rw [Nat.factorial_succ]
  push_cast
  rw [factorialScaledCoeff]
  ring

theorem factorialScaledCoeff_X_sq_mul
    (index : ℕ) (series : ℚ⟦X⟧) :
    factorialScaledCoeff (index + 2) (X ^ 2 * series) =
      (index + 2 : ℚ) * (index + 1 : ℚ) *
        factorialScaledCoeff index series := by
  rw [show X ^ 2 * series = X * (X * series) by ring]
  rw [show index + 2 = (index + 1) + 1 by omega,
    factorialScaledCoeff_X_mul, factorialScaledCoeff_X_mul]
  push_cast
  ring

theorem factorialScaledCoeff_X_cube_mul
    (index : ℕ) (series : ℚ⟦X⟧) :
    factorialScaledCoeff (index + 3) (X ^ 3 * series) =
      (index + 3 : ℚ) * (index + 2 : ℚ) * (index + 1 : ℚ) *
        factorialScaledCoeff index series := by
  rw [show X ^ 3 * series = X * (X ^ 2 * series) by ring]
  rw [show index + 3 = (index + 2) + 1 by omega,
    factorialScaledCoeff_X_mul, factorialScaledCoeff_X_sq_mul]
  push_cast
  ring

/-- The exact expanded Bergeron--Gascon differential operator for height
four. -/
noncomputable def heightFourDifferentialOperator (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  let derivativeOne := PowerSeries.derivative ℚ series
  let derivativeTwo := PowerSeries.derivative ℚ derivativeOne
  let derivativeThree := PowerSeries.derivative ℚ derivativeTwo
  X ^ 2 * derivativeThree +
    PowerSeries.C 10 * (X * derivativeTwo) -
    PowerSeries.C 16 * (X ^ 2 * derivativeOne) -
    PowerSeries.C 8 * (X * derivativeOne) +
    PowerSeries.C 20 * derivativeOne -
    PowerSeries.C 32 * (X * series) -
    PowerSeries.C 20 * series

theorem heightFour_recurrence_of_differential_equation
    (sequence : ℕ → ℚ)
    (hODE : heightFourDifferentialOperator (factorialSeries sequence) = 0)
    (index : ℕ) (hindex : 2 ≤ index) :
    (index + 3 : ℚ) * (index + 4 : ℚ) * sequence index -
        (8 * index + 12 : ℚ) * sequence (index - 1) -
        16 * (index : ℚ) * (index - 1 : ℚ) * sequence (index - 2) = 0 := by
  by_cases htwo : index = 2
  · subst index
    have hcoeff := congrArg (factorialScaledCoeff 1) hODE
    simp only [heightFourDifferentialOperator] at hcoeff
    rw [derivative_three_factorialSeries, derivative_two_factorialSeries,
      derivative_factorialSeries] at hcoeff
    simp only [factorialScaledCoeff_add, factorialScaledCoeff_sub,
      factorialScaledCoeff_C_mul, factorialScaledCoeff_zero] at hcoeff
    simp [factorialScaledCoeff, PowerSeries.coeff_X_pow_mul',
      factorialSeries_coeff] at hcoeff
    norm_num at hcoeff ⊢
    linear_combination hcoeff
  · have hthree : 3 ≤ index := by omega
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hthree
    have hcoeff := congrArg (factorialScaledCoeff (offset + 2)) hODE
    simp only [heightFourDifferentialOperator] at hcoeff
    rw [derivative_three_factorialSeries, derivative_two_factorialSeries,
      derivative_factorialSeries] at hcoeff
    simp only [factorialScaledCoeff_add, factorialScaledCoeff_sub,
      factorialScaledCoeff_C_mul, factorialScaledCoeff_zero] at hcoeff
    rw [factorialScaledCoeff_X_sq_mul offset,
      show offset + 2 = (offset + 1) + 1 by omega,
      factorialScaledCoeff_X_mul,
      factorialScaledCoeff_X_sq_mul offset,
      show offset + 2 = (offset + 1) + 1 by omega,
      factorialScaledCoeff_X_mul,
      show offset + 2 = (offset + 1) + 1 by omega,
      factorialScaledCoeff_X_mul] at hcoeff
    simp only [factorialScaledCoeff_factorialSeries] at hcoeff
    norm_num [Nat.add_assoc] at hcoeff
    have hindexSelf : 3 + offset = offset + 3 := by omega
    have hindexOne : offset + 3 - 1 = offset + 2 := by omega
    have hindexTwo : offset + 3 - 2 = offset + 1 := by omega
    rw [hindexSelf, hindexOne, hindexTwo]
    push_cast at hcoeff ⊢
    linear_combination hcoeff

/-- The exact expanded Bergeron--Gascon differential operator for height five. -/
noncomputable def heightFiveDifferentialOperator (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  let derivativeOne := PowerSeries.derivative ℚ series
  let derivativeTwo := PowerSeries.derivative ℚ derivativeOne
  let derivativeThree := PowerSeries.derivative ℚ derivativeTwo
  X ^ 2 * derivativeThree -
    PowerSeries.C 3 * (X ^ 2 * derivativeTwo) +
    PowerSeries.C 13 * (X * derivativeTwo) -
    PowerSeries.C 13 * (X ^ 2 * derivativeOne) -
    PowerSeries.C 26 * (X * derivativeOne) +
    PowerSeries.C 35 * derivativeOne +
    PowerSeries.C 15 * (X ^ 2 * series) -
    PowerSeries.C 35 * (X * series) -
    PowerSeries.C 35 * series

/-- Literal coefficient extraction from the height-five ODE. -/
theorem heightFive_recurrence_of_differential_equation
    (sequence : ℕ → ℚ)
    (hODE : heightFiveDifferentialOperator (factorialSeries sequence) = 0)
    (index : ℕ) (hindex : 3 ≤ index) :
    (index + 4 : ℚ) * (index + 6 : ℚ) * sequence index -
        (3 * index ^ 2 + 17 * index + 15 : ℚ) * sequence (index - 1) -
        (index - 1 : ℚ) * (13 * index + 9 : ℚ) * sequence (index - 2) +
        15 * (index - 1 : ℚ) * (index - 2 : ℚ) * sequence (index - 3) = 0 := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hindex
  have hcoeff := congrArg (factorialScaledCoeff (offset + 2)) hODE
  simp only [heightFiveDifferentialOperator] at hcoeff
  rw [derivative_three_factorialSeries, derivative_two_factorialSeries,
    derivative_factorialSeries] at hcoeff
  simp only [factorialScaledCoeff_add, factorialScaledCoeff_sub,
    factorialScaledCoeff_C_mul, factorialScaledCoeff_zero] at hcoeff
  rw [factorialScaledCoeff_X_sq_mul offset,
    show offset + 2 = (offset + 1) + 1 by omega,
    factorialScaledCoeff_X_mul,
    factorialScaledCoeff_X_sq_mul offset,
    show offset + 2 = (offset + 1) + 1 by omega,
    factorialScaledCoeff_X_mul,
    factorialScaledCoeff_X_sq_mul offset,
    show offset + 2 = (offset + 1) + 1 by omega,
    factorialScaledCoeff_X_mul,
    factorialScaledCoeff_X_sq_mul offset] at hcoeff
  simp only [factorialScaledCoeff_factorialSeries] at hcoeff
  have h0 : 3 + offset = offset + 3 := by omega
  have h1 : 3 + offset - 1 = offset + 2 := by omega
  have h2 : 3 + offset - 2 = offset + 1 := by omega
  have h3 : 3 + offset - 3 = offset := by omega
  rw [h1, h2, h3, h0]
  norm_num [Nat.add_assoc] at hcoeff
  push_cast at hcoeff ⊢
  linear_combination hcoeff

/-- The exact expanded Bergeron--Gascon differential operator for height six. -/
noncomputable def heightSixDifferentialOperator (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  let derivativeOne := PowerSeries.derivative ℚ series
  let derivativeTwo := PowerSeries.derivative ℚ derivativeOne
  let derivativeThree := PowerSeries.derivative ℚ derivativeTwo
  let derivativeFour := PowerSeries.derivative ℚ derivativeThree
  X ^ 3 * derivativeFour +
    PowerSeries.C 28 * (X ^ 2 * derivativeThree) -
    PowerSeries.C 40 * (X ^ 3 * derivativeTwo) -
    PowerSeries.C 20 * (X ^ 2 * derivativeTwo) +
    PowerSeries.C 230 * (X * derivativeTwo) -
    PowerSeries.C 432 * (X ^ 2 * derivativeOne) -
    PowerSeries.C 244 * (X * derivativeOne) +
    PowerSeries.C 540 * derivativeOne +
    PowerSeries.C 144 * (X ^ 3 * series) +
    PowerSeries.C 144 * (X ^ 2 * series) -
    PowerSeries.C 756 * (X * series) -
    PowerSeries.C 540 * series

/-- Literal coefficient extraction from the height-six ODE. -/
theorem heightSix_recurrence_of_differential_equation
    (sequence : ℕ → ℚ)
    (hODE : heightSixDifferentialOperator (factorialSeries sequence) = 0)
    (index : ℕ) (hindex : 4 ≤ index) :
    (index + 5 : ℚ) * (index + 8 : ℚ) * (index + 9 : ℚ) * sequence index -
        4 * (5 * index ^ 2 + 46 * index + 84 : ℚ) * sequence (index - 1) -
        4 * (index - 1 : ℚ) * (10 * index ^ 2 + 58 * index + 33 : ℚ) *
          sequence (index - 2) +
        144 * (index - 1 : ℚ) * (index - 2 : ℚ) * sequence (index - 3) +
        144 * (index - 1 : ℚ) * (index - 2 : ℚ) * (index - 3 : ℚ) *
          sequence (index - 4) = 0 := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hindex
  have hcoeff := congrArg (factorialScaledCoeff (offset + 3)) hODE
  simp only [heightSixDifferentialOperator] at hcoeff
  rw [derivative_four_factorialSeries, derivative_three_factorialSeries,
    derivative_two_factorialSeries, derivative_factorialSeries] at hcoeff
  simp only [factorialScaledCoeff_add, factorialScaledCoeff_sub,
    factorialScaledCoeff_C_mul, factorialScaledCoeff_zero] at hcoeff
  rw [factorialScaledCoeff_X_cube_mul offset,
    show offset + 3 = (offset + 1) + 2 by omega,
    factorialScaledCoeff_X_sq_mul,
    factorialScaledCoeff_X_cube_mul offset,
    show offset + 3 = (offset + 1) + 2 by omega,
    factorialScaledCoeff_X_sq_mul,
    show offset + 3 = (offset + 2) + 1 by omega,
    factorialScaledCoeff_X_mul,
    show offset + 3 = (offset + 1) + 2 by omega,
    factorialScaledCoeff_X_sq_mul,
    show offset + 3 = (offset + 2) + 1 by omega,
    factorialScaledCoeff_X_mul,
    factorialScaledCoeff_X_cube_mul offset,
    show offset + 3 = (offset + 1) + 2 by omega,
    factorialScaledCoeff_X_sq_mul,
    show offset + 3 = (offset + 2) + 1 by omega,
    factorialScaledCoeff_X_mul] at hcoeff
  simp only [factorialScaledCoeff_factorialSeries] at hcoeff
  have h0 : 4 + offset = offset + 4 := by omega
  have h1 : 4 + offset - 1 = offset + 3 := by omega
  have h2 : 4 + offset - 2 = offset + 2 := by omega
  have h3 : 4 + offset - 3 = offset + 1 := by omega
  have h4 : 4 + offset - 4 = offset := by omega
  rw [h1, h2, h3, h4, h0]
  norm_num [Nat.add_assoc] at hcoeff
  push_cast at hcoeff ⊢
  linear_combination hcoeff

end FibonacciRibbonKernel
