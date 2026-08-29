import FibonacciRibbonKernel.FourPfaffianBessel

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def heightFourNumerator : ℚ⟦X⟧ :=
  -2 * X * besselJ0 ^ 2 +
    2 * besselJ0 * besselJ1 +
    (2 * X + 1) * besselJ1 ^ 2

theorem X_sq_mul_gesselHeightFourSeries :
    X ^ 2 * gesselHeightFourSeries = heightFourNumerator := by
  have hrec0 := literalBesselJ_recurrence 0
  norm_num at hrec0
  have hrec1 := X_sq_mul_literalBesselJ_three
  unfold gesselHeightFourSeries pairQ1 pairQ2 pairQ3 heightFourNumerator
  rw [literalBesselJ_zero, literalBesselJ_one] at hrec0 hrec1 ⊢
  linear_combination
    (besselJ0 + besselJ1) * hrec1 +
      (-besselJ0 * X - 2 * besselJ1 * X + besselJ1 -
        literalBesselJ 2 * X) * hrec0

noncomputable def heightFourNumeratorDifferentialOperator
    (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  let derivativeOne := PowerSeries.derivative ℚ series
  let derivativeTwo := PowerSeries.derivative ℚ derivativeOne
  let derivativeThree := PowerSeries.derivative ℚ derivativeTwo
  X ^ 3 * derivativeThree +
    4 * X ^ 2 * derivativeTwo +
    (-16 * X ^ 3 - 8 * X ^ 2 - 2 * X) * derivativeOne +
    (-4 * X - 4) * series

theorem heightFourNumerator_differential_equation :
    heightFourNumeratorDifferentialOperator heightFourNumerator = 0 := by
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
      heightFourNumeratorDifferentialOperator heightFourNumerator =
        2 * (A + 2 * B * X + B) *
            (X ^ 3 * G3 -
              (8 * X ^ 3 * A - 8 * X ^ 2 * B + 6 * X * A - 6 * B)) +
          2 * (-4 * A * X ^ 2 + 4 * A + 22 * B * X + 4 * B +
              6 * G1 * X ^ 2 + 3 * G1 * X) *
            (X ^ 2 * G2 -
              (4 * X ^ 2 * B - 2 * X * A + 2 * B)) -
          4 * (28 * A * X ^ 2 + 7 * A * X + A + 16 * B * X ^ 3 +
              10 * B * X ^ 2 - 20 * B * X - 2 * B -
              20 * G1 * X ^ 2 - 4 * G1 * X) *
            (X * G1 - (2 * X * A - B)) -
          8 * (5 * X + 1) * (X * G1 - (2 * X * A - B)) ^ 2 := by
    dsimp only [heightFourNumeratorDifferentialOperator,
      heightFourNumerator, A, B, G1, G2, G3, D]
    simp only [map_add, map_neg, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_X, PowerSeries.derivative_pow,
      derivative_powerSeries_one, derivative_powerSeries_two,
      derivative_besselJ0]
    norm_num
    ring
  rw [hexpanded, h1, h2, h3]
  ring

theorem heightFour_differential_conjugation (series : ℚ⟦X⟧) :
    X ^ 3 * heightFourDifferentialOperator series =
      heightFourNumeratorDifferentialOperator (X ^ 2 * series) := by
  simp only [heightFourDifferentialOperator,
    heightFourNumeratorDifferentialOperator, map_add,
    Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, derivative_powerSeries_one,
    map_ofNat]
  norm_num
  ring

theorem gesselHeightFourSeries_differential_equation :
    heightFourDifferentialOperator gesselHeightFourSeries = 0 := by
  have hconjugation := heightFour_differential_conjugation gesselHeightFourSeries
  rw [X_sq_mul_gesselHeightFourSeries,
    heightFourNumerator_differential_equation] at hconjugation
  exact (mul_eq_zero.mp hconjugation).resolve_left
    (pow_ne_zero 3 PowerSeries.X_ne_zero)

theorem heightFourTableauCount_recurrence
    (index : ℕ) (hindex : 2 ≤ index) :
    (index + 3 : ℚ) * (index + 4 : ℚ) * heightFourTableauCount index -
        (8 * index + 12 : ℚ) * heightFourTableauCount (index - 1) -
        16 * (index : ℚ) * (index - 1 : ℚ) *
          heightFourTableauCount (index - 2) = 0 := by
  apply heightFour_recurrence_of_differential_equation
    (fun size => (heightFourTableauCount size : ℚ)) _ index hindex
  rw [factorialSeries_heightFourTableauCount_eq_gessel]
  exact gesselHeightFourSeries_differential_equation

end FibonacciRibbonKernel
