import FibonacciRibbonKernel.BesselSystem
import FibonacciRibbonKernel.FactorialDifferential

namespace FibonacciRibbonKernel

open PowerSeries

@[simp] theorem derivative_powerSeries_one :
    PowerSeries.derivative ℚ (1 : ℚ⟦X⟧) = 0 := by
  have hconstant : PowerSeries.C (1 : ℚ) = (1 : ℚ⟦X⟧) :=
    map_one (PowerSeries.C : ℚ →+* ℚ⟦X⟧)
  rw [← hconstant, PowerSeries.derivative_C]

@[simp] theorem derivative_powerSeries_two :
    PowerSeries.derivative ℚ (2 : ℚ⟦X⟧) = 0 := by
  rw [show (2 : ℚ⟦X⟧) = 1 + 1 by norm_num, map_add,
    derivative_powerSeries_one]
  simp

@[simp] theorem derivative_powerSeries_four :
    PowerSeries.derivative ℚ (4 : ℚ⟦X⟧) = 0 := by
  rw [show (4 : ℚ⟦X⟧) = 2 + 2 by norm_num, map_add,
    derivative_powerSeries_two]
  simp

@[simp] theorem derivative_powerSeries_three :
    PowerSeries.derivative ℚ (3 : ℚ⟦X⟧) = 0 := by
  rw [show (3 : ℚ⟦X⟧) = 2 + 1 by norm_num, map_add,
    derivative_powerSeries_two, derivative_powerSeries_one]
  simp

@[simp] theorem constantCoeff_powerSeries_two :
    PowerSeries.constantCoeff (2 : ℚ⟦X⟧) = 2 := by
  have hconstant : PowerSeries.C (2 : ℚ) = (2 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2
  rw [← hconstant]
  simp

@[simp] theorem constantCoeff_powerSeries_four :
    PowerSeries.constantCoeff (4 : ℚ⟦X⟧) = 4 := by
  have hconstant : PowerSeries.C (4 : ℚ) = (4 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 4
  rw [← hconstant]
  simp

@[simp] theorem coeff_one_powerSeries_two :
    PowerSeries.coeff 1 (2 : ℚ⟦X⟧) = 0 := by
  have hconstant : PowerSeries.C (2 : ℚ) = (2 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2
  rw [← hconstant]
  simp

@[simp] theorem coeff_one_powerSeries_four :
    PowerSeries.coeff 1 (4 : ℚ⟦X⟧) = 0 := by
  have hconstant : PowerSeries.C (4 : ℚ) = (4 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 4
  rw [← hconstant]
  simp

/-- Second differentiated consequence of the literal `J₁` first-order
identity, kept in a form with no negative powers of `X`. -/
theorem X_sq_mul_derivative_two_besselJ1 :
    X ^ 2 *
        PowerSeries.derivative ℚ (PowerSeries.derivative ℚ besselJ1) =
      4 * X ^ 2 * besselJ1 - 2 * X * besselJ0 + 2 * besselJ1 := by
  let D := PowerSeries.derivative ℚ
  have hfirst := X_mul_derivative_besselJ1
  have hdifferentiated := congrArg D hfirst
  simp only [D, map_sub, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_X, derivative_powerSeries_two,
    derivative_besselJ0] at hdifferentiated
  norm_num at hdifferentiated
  linear_combination X * hdifferentiated - 2 * hfirst

/-- Third differentiated consequence of the literal `J₁` first-order
identity, again cleared of every negative power. -/
theorem X_cube_mul_derivative_three_besselJ1 :
    X ^ 3 *
        PowerSeries.derivative ℚ
          (PowerSeries.derivative ℚ (PowerSeries.derivative ℚ besselJ1)) =
      8 * X ^ 3 * besselJ0 - 8 * X ^ 2 * besselJ1 +
        6 * X * besselJ0 - 6 * besselJ1 := by
  let D := PowerSeries.derivative ℚ
  have hsecond := X_sq_mul_derivative_two_besselJ1
  have hdifferentiated := congrArg D hsecond
  simp only [D, map_add, map_sub, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_X, PowerSeries.derivative_pow,
    derivative_powerSeries_two, derivative_powerSeries_four,
    derivative_besselJ0] at hdifferentiated
  norm_num at hdifferentiated
  have hfirst := X_mul_derivative_besselJ1
  linear_combination X * hdifferentiated - 2 * hsecond +
    (4 * X ^ 2 + 2) * hfirst

/-- Coefficient shift down by a fixed number of powers. -/
noncomputable def powerSeriesShiftDown (shift : ℕ) (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  PowerSeries.mk fun index => PowerSeries.coeff (index + shift) series

@[simp] theorem powerSeriesShiftDown_coeff
    (shift index : ℕ) (series : ℚ⟦X⟧) :
    PowerSeries.coeff index (powerSeriesShiftDown shift series) =
      PowerSeries.coeff (index + shift) series := by
  simp [powerSeriesShiftDown]

theorem X_pow_mul_powerSeriesShiftDown
    (shift : ℕ) (series : ℚ⟦X⟧)
    (hvanish : ∀ index < shift, PowerSeries.coeff index series = 0) :
    X ^ shift * powerSeriesShiftDown shift series = series := by
  ext index
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hindex
  · rw [powerSeriesShiftDown_coeff, Nat.sub_add_cancel hindex]
  · exact (hvanish index (lt_of_not_ge hindex)).symm

/-- Regular quotient `J₁/X`. -/
noncomputable def besselJ1DivX : ℚ⟦X⟧ :=
  powerSeriesShiftDown 1 besselJ1

theorem X_mul_besselJ1DivX :
    X * besselJ1DivX = besselJ1 := by
  rw [show X = X ^ 1 by simp]
  apply X_pow_mul_powerSeriesShiftDown
  intro index hindex
  have hzero : index = 0 := by omega
  subst index
  exact besselJ1_coeff_even 0

@[simp] theorem besselJ1DivX_coeff_zero :
    PowerSeries.coeff 0 besselJ1DivX = 1 := by
  rw [besselJ1DivX, powerSeriesShiftDown_coeff]
  simpa using besselJ1_coeff_odd 0

@[simp] theorem besselJ1DivX_coeff_one :
    PowerSeries.coeff 1 besselJ1DivX = 0 := by
  rw [besselJ1DivX, powerSeriesShiftDown_coeff]
  exact besselJ1_coeff_even 1

/-- The regular core remaining after the first visible `X²` in the height-five
Bessel numerator. -/
noncomputable def heightFiveBesselCore : ℚ⟦X⟧ :=
  -4 * besselJ0 ^ 2 +
    2 * besselJ0 * besselJ1DivX +
    2 * (2 * X ^ 2 + 1) * besselJ1DivX ^ 2

theorem heightFiveBesselCore_coeff_zero :
    PowerSeries.coeff 0 heightFiveBesselCore = 0 := by
  have hA0 : PowerSeries.constantCoeff besselJ0 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa using besselJ0_coeff_even 0
  have hH0 : PowerSeries.constantCoeff besselJ1DivX = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact besselJ1DivX_coeff_zero
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [heightFiveBesselCore, hA0, hH0]
  ring

theorem heightFiveBesselCore_coeff_one :
    PowerSeries.coeff 1 heightFiveBesselCore = 0 := by
  have hA0 : PowerSeries.constantCoeff besselJ0 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa using besselJ0_coeff_even 0
  have hH0 : PowerSeries.constantCoeff besselJ1DivX = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact besselJ1DivX_coeff_zero
  have hA1 : PowerSeries.coeff 1 besselJ0 = 0 :=
    besselJ0_coeff_odd 0
  have hH1 : PowerSeries.coeff 1 besselJ1DivX = 0 :=
    besselJ1DivX_coeff_one
  simp [heightFiveBesselCore, PowerSeries.coeff_one_mul, pow_two,
    hA0, hH0, hA1, hH1]

/-- The regular height-five Bessel EGF obtained after removing all four
vanishing numerator powers. -/
noncomputable def heightFiveBesselSeries : ℚ⟦X⟧ :=
  PowerSeries.exp ℚ * powerSeriesShiftDown 2 heightFiveBesselCore

/-- Numerator of the simplified height-five Bessel formula.  The source
identity is `X⁴ Y₅ = heightFiveBesselNumerator`. -/
noncomputable def heightFiveBesselNumerator : ℚ⟦X⟧ :=
  PowerSeries.exp ℚ *
    (-4 * X ^ 2 * besselJ0 ^ 2 +
      2 * X * besselJ0 * besselJ1 +
      2 * (2 * X ^ 2 + 1) * besselJ1 ^ 2)

theorem heightFiveBesselNumerator_factor :
    X ^ 4 * heightFiveBesselSeries = heightFiveBesselNumerator := by
  have hcore :
      X ^ 2 * powerSeriesShiftDown 2 heightFiveBesselCore =
        heightFiveBesselCore :=
    X_pow_mul_powerSeriesShiftDown 2 heightFiveBesselCore (by
      intro index hindex
      have hcases : index = 0 ∨ index = 1 := by omega
      rcases hcases with rfl | rfl
      · exact heightFiveBesselCore_coeff_zero
      · exact heightFiveBesselCore_coeff_one)
  rw [heightFiveBesselSeries]
  calc
    X ^ 4 *
        (PowerSeries.exp ℚ * powerSeriesShiftDown 2 heightFiveBesselCore) =
      PowerSeries.exp ℚ *
        (X ^ 2 * (X ^ 2 * powerSeriesShiftDown 2 heightFiveBesselCore)) := by
          ring
    _ = PowerSeries.exp ℚ * (X ^ 2 * heightFiveBesselCore) := by rw [hcore]
    _ = heightFiveBesselNumerator := by
      rw [heightFiveBesselNumerator, heightFiveBesselCore,
        ← X_mul_besselJ1DivX]
      ring

/-- The differential operator obtained after writing `N=X⁴Y₅` and clearing
the four negative powers in the height-five ODE. -/
noncomputable def heightFiveNumeratorDifferentialOperator
    (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  let derivativeOne := PowerSeries.derivative ℚ series
  let derivativeTwo := PowerSeries.derivative ℚ derivativeOne
  let derivativeThree := PowerSeries.derivative ℚ derivativeTwo
  X ^ 2 * derivativeThree +
    (-3 * X ^ 2 + X) * derivativeTwo +
    (-13 * X ^ 2 - 2 * X - 9) * derivativeOne +
    (15 * X ^ 2 + 17 * X + 9) * series

/-- The simplified Bergeron--Gascon height-five Bessel numerator satisfies
the exact transformed differential equation. -/
theorem heightFiveBesselNumerator_differential_equation :
    heightFiveNumeratorDifferentialOperator heightFiveBesselNumerator = 0 := by
  let D := PowerSeries.derivative ℚ
  let A := besselJ0
  let B := besselJ1
  let G1 := D B
  let G2 := D G1
  let G3 := D G2
  have h1 : X * G1 - (2 * X * A - B) = 0 := by
    dsimp only [G1, A, B, D]
    exact sub_eq_zero.mpr X_mul_derivative_besselJ1
  have h2 : X ^ 2 * G2 -
      (4 * X ^ 2 * B - 2 * X * A + 2 * B) = 0 := by
    dsimp only [G2, G1, A, B, D]
    exact sub_eq_zero.mpr X_sq_mul_derivative_two_besselJ1
  have h3 : X ^ 3 * G3 -
      (8 * X ^ 3 * A - 8 * X ^ 2 * B + 6 * X * A - 6 * B) = 0 := by
    dsimp only [G3, G2, G1, A, B, D]
    exact sub_eq_zero.mpr X_cube_mul_derivative_three_besselJ1
  have hexpanded :
      X * heightFiveNumeratorDifferentialOperator heightFiveBesselNumerator =
        PowerSeries.exp ℚ *
          (2 * (A * X + 4 * B * X ^ 2 + 2 * B) *
              (X ^ 3 * G3 -
                (8 * X ^ 3 * A - 8 * X ^ 2 * B + 6 * X * A - 6 * B)) +
            4 *
              (-4 * A * X ^ 3 + 2 * A * X + 18 * B * X ^ 2 + B +
                6 * G1 * X ^ 3 + 3 * G1 * X) *
              (X ^ 2 * G2 -
                (4 * X ^ 2 * B - 2 * X * A + 2 * B)) -
            2 *
              (28 * A * X ^ 3 + 15 * A * X + 64 * B * X ^ 4 -
                10 * B * X ^ 2 + 8 * B - 34 * G1 * X ^ 3 - 2 * G1 * X) *
              (X * G1 - (2 * X * A - B))) := by
    dsimp only [heightFiveNumeratorDifferentialOperator,
      heightFiveBesselNumerator, A, B, G1, G2, G3, D]
    simp only [map_add, map_neg, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_X, PowerSeries.derivative_pow,
      derivative_powerSeries_one, derivative_powerSeries_two,
      derivative_powerSeries_four,
      PowerSeries.derivative_exp, derivative_besselJ0]
    norm_num
    ring
  have hmul :
      X * heightFiveNumeratorDifferentialOperator heightFiveBesselNumerator = 0 := by
    rw [hexpanded, h1, h2, h3]
    ring
  exact (mul_eq_zero.mp hmul).resolve_left PowerSeries.X_ne_zero

/-- Exact conjugation of the source height-five ODE under `N=X⁴Y`. -/
theorem heightFive_differential_conjugation (series : ℚ⟦X⟧) :
    X ^ 5 * heightFiveDifferentialOperator series =
      X * heightFiveNumeratorDifferentialOperator (X ^ 4 * series) := by
  simp only [heightFiveDifferentialOperator,
    heightFiveNumeratorDifferentialOperator, map_add,
    Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, derivative_powerSeries_one, map_ofNat]
  norm_num
  ring

theorem heightFiveBesselSeries_differential_equation :
    heightFiveDifferentialOperator heightFiveBesselSeries = 0 := by
  have hconjugation := heightFive_differential_conjugation heightFiveBesselSeries
  rw [heightFiveBesselNumerator_factor,
    heightFiveBesselNumerator_differential_equation, mul_zero] at hconjugation
  exact (mul_eq_zero.mp hconjugation).resolve_left
    (pow_ne_zero 5 PowerSeries.X_ne_zero)

/-- Factorial coefficients of the literal height-five Bessel EGF. -/
noncomputable def heightFiveBesselSequence (index : ℕ) : ℚ :=
  (index.factorial : ℚ) *
    PowerSeries.coeff index heightFiveBesselSeries

theorem factorialSeries_heightFiveBesselSequence :
    factorialSeries heightFiveBesselSequence = heightFiveBesselSeries := by
  ext index
  rw [factorialSeries_coeff]
  unfold heightFiveBesselSequence
  have hfactorial : (index.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem heightFiveBesselSequence_recurrence
    (index : ℕ) (hindex : 3 ≤ index) :
    (index + 4 : ℚ) * (index + 6 : ℚ) * heightFiveBesselSequence index -
        (3 * index ^ 2 + 17 * index + 15 : ℚ) *
          heightFiveBesselSequence (index - 1) -
        (index - 1 : ℚ) * (13 * index + 9 : ℚ) *
          heightFiveBesselSequence (index - 2) +
        15 * (index - 1 : ℚ) * (index - 2 : ℚ) *
          heightFiveBesselSequence (index - 3) = 0 := by
  apply heightFive_recurrence_of_differential_equation
  rw [factorialSeries_heightFiveBesselSequence]
  exact heightFiveBesselSeries_differential_equation
  exact hindex

end FibonacciRibbonKernel
