import FibonacciRibbonKernel.HeightFiveBessel
import Mathlib.Tactic.FinCases

namespace FibonacciRibbonKernel

open PowerSeries

abbrev DegreeThreePolynomialVector := Fin 4 → Polynomial ℚ

/-- Polynomial linear combination of the degree-three even Bessel basis. -/
noncomputable def degreeThreeBesselSeries
    (coefficients : DegreeThreePolynomialVector) : ℚ⟦X⟧ :=
  ∑ index : Fin 4,
    (coefficients index : ℚ⟦X⟧) * besselBasisVector 3 index

noncomputable def degreeThreeBesselSeriesLinear :
    DegreeThreePolynomialVector →ₗ[Polynomial ℚ] ℚ⟦X⟧ where
  toFun := degreeThreeBesselSeries
  map_add' left right := by
    unfold degreeThreeBesselSeries
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index hindex
    change ((left index + right index : Polynomial ℚ) : ℚ⟦X⟧) *
        besselBasisVector 3 index =
      (left index : ℚ⟦X⟧) * besselBasisVector 3 index +
        (right index : ℚ⟦X⟧) * besselBasisVector 3 index
    rw [Polynomial.coe_add]
    ring

  map_smul' scalar vector := by
    unfold degreeThreeBesselSeries
    change (∑ index : Fin 4,
        ((scalar * vector index : Polynomial ℚ) : ℚ⟦X⟧) *
          besselBasisVector 3 index) =
      (scalar : ℚ⟦X⟧) *
        ∑ index : Fin 4,
          (vector index : ℚ⟦X⟧) * besselBasisVector 3 index
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index hindex
    ring

@[simp] theorem algebraMap_polynomial_powerSeries_eq_coe
    (polynomial : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) ℚ⟦X⟧ polynomial =
      (polynomial : ℚ⟦X⟧) := by
  ext index
  simp [PowerSeries.algebraMap_apply']

@[simp] theorem powerSeries_C_natCast (value : ℕ) :
    PowerSeries.C (value : ℚ) = (value : ℚ⟦X⟧) :=
  map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) value

@[simp] theorem algebraMap_rational_natCast_powerSeries (value : ℕ) :
    algebraMap ℚ ℚ⟦X⟧ (value : ℚ) = (value : ℚ⟦X⟧) :=
  map_natCast (algebraMap ℚ ℚ⟦X⟧) value

/-- Coefficient-vector action induced by the Euler operator `X d/dX` on the
degree-three even Bessel module. -/
noncomputable def degreeThreeEuler
    (coefficients : DegreeThreePolynomialVector) :
    DegreeThreePolynomialVector := fun index =>
  match index.val with
  | 0 =>
      Polynomial.X * (coefficients 0).derivative -
        Polynomial.C 3 * coefficients 0 +
        Polynomial.C 2 * Polynomial.X * coefficients 1
  | 1 =>
      Polynomial.X * (coefficients 1).derivative -
        Polynomial.C 2 * coefficients 1 +
        Polynomial.C 6 * Polynomial.X * coefficients 0 +
        Polynomial.C 4 * Polynomial.X * coefficients 2
  | 2 =>
      Polynomial.X * (coefficients 2).derivative - coefficients 2 +
        Polynomial.C 4 * Polynomial.X * coefficients 1 +
        Polynomial.C 6 * Polynomial.X * coefficients 3
  | _ =>
      Polynomial.X * (coefficients 3).derivative +
        Polynomial.C 2 * Polynomial.X * coefficients 2

theorem degreeThreeBesselSeries_euler
    (coefficients : DegreeThreePolynomialVector) :
    X * PowerSeries.derivative ℚ (degreeThreeBesselSeries coefficients) =
      degreeThreeBesselSeries (degreeThreeEuler coefficients) := by
  have h0 := bessel_finite_system 3 (0 : Fin 4)
  have h1 := bessel_finite_system 3 (1 : Fin 4)
  have h2 := bessel_finite_system 3 (2 : Fin 4)
  have h3 := bessel_finite_system 3 (3 : Fin 4)
  have hC2 : PowerSeries.C (2 : ℚ) = (2 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2
  have hC3 : PowerSeries.C (3 : ℚ) = (3 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 3
  have hC4 : PowerSeries.C (4 : ℚ) = (4 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 4
  have hC6 : PowerSeries.C (6 : ℚ) = (6 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 6
  have hP2 : ((2 : Polynomial ℚ) : ℚ⟦X⟧) = (2 : ℚ⟦X⟧) := by
    rw [← map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 2,
      Polynomial.coe_C, hC2]
  have hP3 : ((3 : Polynomial ℚ) : ℚ⟦X⟧) = (3 : ℚ⟦X⟧) := by
    rw [← map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 3,
      Polynomial.coe_C, hC3]
  have hP4 : ((4 : Polynomial ℚ) : ℚ⟦X⟧) = (4 : ℚ⟦X⟧) := by
    rw [← map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 4,
      Polynomial.coe_C, hC4]
  have hP6 : ((6 : Polynomial ℚ) : ℚ⟦X⟧) = (6 : ℚ⟦X⟧) := by
    rw [← map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 6,
      Polynomial.coe_C, hC6]
  norm_num [besselBasisVector, besselM0Action, besselM1Action,
    besselMonomial] at h0 h1 h2 h3
  simp only [degreeThreeBesselSeries, Fin.sum_univ_succ,
    degreeThreeEuler, besselBasisVector, besselMonomial,
    map_add, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_coe, map_ofNat]
  norm_num
  simp only [hC2, hC3, hC4, hC6] at h0 h1 h2 h3 ⊢
  push_cast
  simp only [hP2, hP3, hP4, hP6]
  linear_combination
    (coefficients 0 : ℚ⟦X⟧) * h0 +
    (coefficients 1 : ℚ⟦X⟧) * h1 +
    (coefficients 2 : ℚ⟦X⟧) * h2 +
    (X * (coefficients 3 : ℚ⟦X⟧)) * h3

/-- Literal coefficient vector of the simplified height-six Bessel
numerator. -/
noncomputable def heightSixBesselVector : DegreeThreePolynomialVector :=
  fun index =>
    match index.val with
    | 0 =>
        Polynomial.C 4 *
          (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.X ^ 2 +
            Polynomial.C 5 * Polynomial.X + 1)
    | 1 =>
        Polynomial.C 4 *
          (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.X ^ 2 + 3)
    | 2 =>
        -Polynomial.C 4 * Polynomial.X *
          (Polynomial.C 4 * Polynomial.X ^ 2 -
            Polynomial.C 3 * Polynomial.X + 6)
    | _ =>
        -Polynomial.C 4 * Polynomial.X ^ 2 *
          (Polynomial.C 4 * Polynomial.X - 3)

noncomputable def heightSixEulerOne : DegreeThreePolynomialVector :=
  degreeThreeEuler heightSixBesselVector

noncomputable def heightSixEulerTwo : DegreeThreePolynomialVector :=
  degreeThreeEuler heightSixEulerOne

noncomputable def heightSixEulerThree : DegreeThreePolynomialVector :=
  degreeThreeEuler heightSixEulerTwo

noncomputable def heightSixEulerFour : DegreeThreePolynomialVector :=
  degreeThreeEuler heightSixEulerThree

/-- Polynomial-vector certificate for the complete conjugated height-six
differential equation. -/
noncomputable def heightSixEulerCertificate : DegreeThreePolynomialVector :=
  fun index =>
    heightSixEulerFour index -
      Polynomial.C 2 * heightSixEulerThree index -
      heightSixEulerTwo index +
      Polynomial.C 2 * heightSixEulerOne index +
      (-Polynomial.C 40 * Polynomial.X ^ 2 -
          Polynomial.C 20 * Polynomial.X - 22) *
        (heightSixEulerTwo index - heightSixEulerOne index) +
      (Polynomial.C 48 * Polynomial.X ^ 2 -
          Polynomial.C 4 * Polynomial.X - 36) *
        heightSixEulerOne index +
      (Polynomial.C 144 * Polynomial.X ^ 4 +
          Polynomial.C 144 * Polynomial.X ^ 3 +
          Polynomial.C 156 * Polynomial.X ^ 2 +
          Polynomial.C 84 * Polynomial.X + 36) *
        heightSixBesselVector index

theorem heightSixEulerCertificate_vector_formula :
    heightSixEulerCertificate =
      heightSixEulerFour -
        (Polynomial.C 2 : Polynomial ℚ) • heightSixEulerThree -
        heightSixEulerTwo +
        (Polynomial.C 2 : Polynomial ℚ) • heightSixEulerOne +
        (-Polynomial.C (40 : ℚ) * Polynomial.X ^ 2 -
            Polynomial.C (20 : ℚ) * Polynomial.X - 22) •
          (heightSixEulerTwo - heightSixEulerOne) +
        (Polynomial.C (48 : ℚ) * Polynomial.X ^ 2 -
            Polynomial.C (4 : ℚ) * Polynomial.X - 36) •
          heightSixEulerOne +
        (Polynomial.C (144 : ℚ) * Polynomial.X ^ 4 +
            Polynomial.C (144 : ℚ) * Polynomial.X ^ 3 +
            Polynomial.C (156 : ℚ) * Polynomial.X ^ 2 +
            Polynomial.C (84 : ℚ) * Polynomial.X + 36) •
          heightSixBesselVector := by
  funext index
  simp [heightSixEulerCertificate, smul_eq_mul]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem heightSixEulerCertificate_zero :
    heightSixEulerCertificate = 0 := by
  funext index
  fin_cases index <;>
    norm_num [heightSixEulerCertificate, heightSixEulerFour,
      heightSixEulerThree, heightSixEulerTwo, heightSixEulerOne,
      degreeThreeEuler, heightSixBesselVector, map_ofNat] <;>
    ring

/-- Literal simplified height-six Bessel numerator. -/
noncomputable def heightSixBesselNumerator : ℚ⟦X⟧ :=
  degreeThreeBesselSeries heightSixBesselVector

@[simp] theorem besselJ0_coeff_zero :
    PowerSeries.coeff 0 besselJ0 = 1 := by
  simpa using besselJ0_coeff_even 0

@[simp] theorem besselJ0_coeff_one :
    PowerSeries.coeff 1 besselJ0 = 0 :=
  besselJ0_coeff_odd 0

@[simp] theorem besselJ0_coeff_two :
    PowerSeries.coeff 2 besselJ0 = 1 := by
  simpa using besselJ0_coeff_even 1

@[simp] theorem besselJ0_coeff_three :
    PowerSeries.coeff 3 besselJ0 = 0 :=
  besselJ0_coeff_odd 1

@[simp] theorem besselJ1DivX_coeff_two :
    PowerSeries.coeff 2 besselJ1DivX = 1 / 2 := by
  rw [besselJ1DivX, powerSeriesShiftDown_coeff]
  simpa using besselJ1_coeff_odd 1

@[simp] theorem besselJ1DivX_coeff_three :
    PowerSeries.coeff 3 besselJ1DivX = 0 := by
  rw [besselJ1DivX, powerSeriesShiftDown_coeff]
  exact besselJ1_coeff_even 2

@[simp] theorem coeff_powerSeries_three (index : ℕ) :
    PowerSeries.coeff index (3 : ℚ⟦X⟧) = if index = 0 then 3 else 0 := by
  have hconstant : PowerSeries.C (3 : ℚ) = (3 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 3
  rw [← hconstant, PowerSeries.coeff_C]

@[simp] theorem coeff_powerSeries_four (index : ℕ) :
    PowerSeries.coeff index (4 : ℚ⟦X⟧) = if index = 0 then 4 else 0 := by
  have hconstant : PowerSeries.C (4 : ℚ) = (4 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 4
  rw [← hconstant, PowerSeries.coeff_C]

@[simp] theorem coeff_powerSeries_five (index : ℕ) :
    PowerSeries.coeff index (5 : ℚ⟦X⟧) = if index = 0 then 5 else 0 := by
  have hconstant : PowerSeries.C (5 : ℚ) = (5 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 5
  rw [← hconstant, PowerSeries.coeff_C]

@[simp] theorem coeff_powerSeries_six (index : ℕ) :
    PowerSeries.coeff index (6 : ℚ⟦X⟧) = if index = 0 then 6 else 0 := by
  have hconstant : PowerSeries.C (6 : ℚ) = (6 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 6
  rw [← hconstant, PowerSeries.coeff_C]

@[simp] theorem constantCoeff_powerSeries_three :
    PowerSeries.constantCoeff (3 : ℚ⟦X⟧) = 3 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

@[simp] theorem constantCoeff_powerSeries_five :
    PowerSeries.constantCoeff (5 : ℚ⟦X⟧) = 5 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

@[simp] theorem constantCoeff_powerSeries_six :
    PowerSeries.constantCoeff (6 : ℚ⟦X⟧) = 6 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

@[simp] theorem polynomial_three_toPowerSeries :
    ((3 : Polynomial ℚ) : ℚ⟦X⟧) = (3 : ℚ⟦X⟧) := by
  rw [← map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 3,
    Polynomial.coe_C]
  exact map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 3

@[simp] theorem polynomial_four_toPowerSeries :
    ((4 : Polynomial ℚ) : ℚ⟦X⟧) = (4 : ℚ⟦X⟧) := by
  rw [← map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 4,
    Polynomial.coe_C]
  exact map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 4

@[simp] theorem polynomial_five_toPowerSeries :
    ((5 : Polynomial ℚ) : ℚ⟦X⟧) = (5 : ℚ⟦X⟧) := by
  rw [← map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 5,
    Polynomial.coe_C]
  exact map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 5

@[simp] theorem polynomial_six_toPowerSeries :
    ((6 : Polynomial ℚ) : ℚ⟦X⟧) = (6 : ℚ⟦X⟧) := by
  rw [← map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 6,
    Polynomial.coe_C]
  exact map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 6

@[simp] theorem polynomial_natCast_toPowerSeries (value : ℕ) :
    ((value : Polynomial ℚ) : ℚ⟦X⟧) = (value : ℚ⟦X⟧) := by
  have hpoly : Polynomial.C (value : ℚ) = (value : Polynomial ℚ) :=
    map_natCast (Polynomial.C : ℚ →+* Polynomial ℚ) value
  have hseries : PowerSeries.C (value : ℚ) = (value : ℚ⟦X⟧) :=
    map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) value
  rw [← hpoly, Polynomial.coe_C, hseries]

/-- Regular core after extracting the first visible `X²` from the height-six
numerator. -/
noncomputable def heightSixBesselCore : ℚ⟦X⟧ :=
  -4 * (4 * X - 3) * besselJ0 ^ 3 -
    4 * (4 * X ^ 2 - 3 * X + 6) * besselJ0 ^ 2 * besselJ1DivX +
    4 * (4 * X ^ 3 - X ^ 2 + 3) * besselJ0 * besselJ1DivX ^ 2 +
    4 * X * (4 * X ^ 3 - X ^ 2 + 5 * X + 1) * besselJ1DivX ^ 3

theorem heightSixBesselNumerator_eq_X_sq_core :
    heightSixBesselNumerator = X ^ 2 * heightSixBesselCore := by
  rw [heightSixBesselNumerator, degreeThreeBesselSeries,
    heightSixBesselCore]
  simp only [Fin.sum_univ_succ, besselBasisVector, besselMonomial]
  norm_num [heightSixBesselVector, Polynomial.coe_C,
    Polynomial.coe_X, map_ofNat]
  rw [← X_mul_besselJ1DivX]
  ring

theorem heightSixBesselCore_coeff_zero :
    PowerSeries.coeff 0 heightSixBesselCore = 0 := by
  have hA0 : PowerSeries.constantCoeff besselJ0 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact besselJ0_coeff_zero
  have hH0 : PowerSeries.constantCoeff besselJ1DivX = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact besselJ1DivX_coeff_zero
  norm_num [heightSixBesselCore, PowerSeries.coeff_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X,
    Finset.antidiagonal, pow_succ]
  rw [hA0, hH0]
  ring

theorem heightSixBesselCore_coeff_one :
    PowerSeries.coeff 1 heightSixBesselCore = 0 := by
  norm_num [heightSixBesselCore, PowerSeries.coeff_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X,
    Finset.antidiagonal, pow_succ]

theorem heightSixBesselCore_coeff_two :
    PowerSeries.coeff 2 heightSixBesselCore = 0 := by
  norm_num [heightSixBesselCore, PowerSeries.coeff_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X,
    Finset.antidiagonal, pow_succ]

theorem heightSixBesselCore_coeff_three :
    PowerSeries.coeff 3 heightSixBesselCore = 0 := by
  norm_num [heightSixBesselCore, PowerSeries.coeff_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X,
    Finset.antidiagonal, pow_succ]

noncomputable def heightSixBesselSeries : ℚ⟦X⟧ :=
  powerSeriesShiftDown 4 heightSixBesselCore

theorem heightSixBesselNumerator_factor :
    X ^ 6 * heightSixBesselSeries = heightSixBesselNumerator := by
  have hcore :
      X ^ 4 * powerSeriesShiftDown 4 heightSixBesselCore =
        heightSixBesselCore :=
    X_pow_mul_powerSeriesShiftDown 4 heightSixBesselCore (by
      intro index hindex
      have hcases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · exact heightSixBesselCore_coeff_zero
      · exact heightSixBesselCore_coeff_one
      · exact heightSixBesselCore_coeff_two
      · exact heightSixBesselCore_coeff_three)
  rw [heightSixBesselSeries, heightSixBesselNumerator_eq_X_sq_core]
  calc
    X ^ 6 * powerSeriesShiftDown 4 heightSixBesselCore =
        X ^ 2 *
          (X ^ 4 * powerSeriesShiftDown 4 heightSixBesselCore) := by ring
    _ = X ^ 2 * heightSixBesselCore := by rw [hcore]

/-- Euler operator on formal power series. -/
noncomputable def besselTheta (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  X * PowerSeries.derivative ℚ series

noncomputable def besselThetaTwo (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  besselTheta (besselTheta series)

noncomputable def besselThetaThree (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  besselTheta (besselThetaTwo series)

noncomputable def besselThetaFour (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  besselTheta (besselThetaThree series)

theorem besselTheta_heightSixBesselNumerator :
    besselTheta heightSixBesselNumerator =
      degreeThreeBesselSeries heightSixEulerOne := by
  exact degreeThreeBesselSeries_euler heightSixBesselVector

theorem besselThetaTwo_heightSixBesselNumerator :
    besselThetaTwo heightSixBesselNumerator =
      degreeThreeBesselSeries heightSixEulerTwo := by
  rw [besselThetaTwo, besselTheta_heightSixBesselNumerator]
  exact degreeThreeBesselSeries_euler heightSixEulerOne

theorem besselThetaThree_heightSixBesselNumerator :
    besselThetaThree heightSixBesselNumerator =
      degreeThreeBesselSeries heightSixEulerThree := by
  rw [besselThetaThree, besselThetaTwo_heightSixBesselNumerator]
  exact degreeThreeBesselSeries_euler heightSixEulerTwo

theorem besselThetaFour_heightSixBesselNumerator :
    besselThetaFour heightSixBesselNumerator =
      degreeThreeBesselSeries heightSixEulerFour := by
  rw [besselThetaFour, besselThetaThree_heightSixBesselNumerator]
  exact degreeThreeBesselSeries_euler heightSixEulerThree

/-- Differential operator after conjugating the height-six ODE by `N=X⁶Y`. -/
noncomputable def heightSixNumeratorDifferentialOperator
    (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  let derivativeOne := PowerSeries.derivative ℚ series
  let derivativeTwo := PowerSeries.derivative ℚ derivativeOne
  let derivativeThree := PowerSeries.derivative ℚ derivativeTwo
  let derivativeFour := PowerSeries.derivative ℚ derivativeThree
  X ^ 4 * derivativeFour +
    4 * X ^ 3 * derivativeThree +
    (-40 * X ^ 4 - 20 * X ^ 3 - 22 * X ^ 2) * derivativeTwo +
    (48 * X ^ 3 - 4 * X ^ 2 - 36 * X) * derivativeOne +
    (144 * X ^ 4 + 144 * X ^ 3 + 156 * X ^ 2 + 84 * X + 36) * series

theorem heightSixNumeratorDifferentialOperator_euler
    (series : ℚ⟦X⟧) :
    heightSixNumeratorDifferentialOperator series =
      besselThetaFour series - 2 * besselThetaThree series -
        besselThetaTwo series + 2 * besselTheta series +
        (-40 * X ^ 2 - 20 * X - 22) *
          (besselThetaTwo series - besselTheta series) +
        (48 * X ^ 2 - 4 * X - 36) * besselTheta series +
        (144 * X ^ 4 + 144 * X ^ 3 + 156 * X ^ 2 +
          84 * X + 36) * series := by
  simp only [heightSixNumeratorDifferentialOperator, besselThetaFour,
    besselThetaThree, besselThetaTwo, besselTheta,
    Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    derivative_powerSeries_one, map_add]
  norm_num
  ring

theorem degreeThreeBesselSeries_heightSixEulerCertificate :
    degreeThreeBesselSeries heightSixEulerCertificate = 0 := by
  rw [heightSixEulerCertificate_zero]
  simp [degreeThreeBesselSeries]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem heightSixBesselNumerator_differential_equation :
    heightSixNumeratorDifferentialOperator heightSixBesselNumerator = 0 := by
  rw [heightSixNumeratorDifferentialOperator_euler,
    besselThetaFour_heightSixBesselNumerator,
    besselThetaThree_heightSixBesselNumerator,
    besselThetaTwo_heightSixBesselNumerator,
    besselTheta_heightSixBesselNumerator]
  have hrepresentation :
      degreeThreeBesselSeries heightSixEulerFour -
            2 * degreeThreeBesselSeries heightSixEulerThree -
          degreeThreeBesselSeries heightSixEulerTwo +
          2 * degreeThreeBesselSeries heightSixEulerOne +
          (-40 * X ^ 2 - 20 * X - 22) *
            (degreeThreeBesselSeries heightSixEulerTwo -
              degreeThreeBesselSeries heightSixEulerOne) +
          (48 * X ^ 2 - 4 * X - 36) *
            degreeThreeBesselSeries heightSixEulerOne +
          (144 * X ^ 4 + 144 * X ^ 3 + 156 * X ^ 2 +
            84 * X + 36) * heightSixBesselNumerator =
        degreeThreeBesselSeries heightSixEulerCertificate := by
    have hvector := congrArg degreeThreeBesselSeriesLinear
      heightSixEulerCertificate_vector_formula
    simp only [map_add, map_sub, map_smul] at hvector
    dsimp only [degreeThreeBesselSeriesLinear] at hvector
    simp [Algebra.smul_def, algebraMap_polynomial_powerSeries_eq_coe] at hvector
    have hC2 : PowerSeries.C (2 : ℚ) = (2 : ℚ⟦X⟧) :=
      map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2
    have hC4 : PowerSeries.C (4 : ℚ) = (4 : ℚ⟦X⟧) :=
      map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 4
    have hC20 : PowerSeries.C (20 : ℚ) = (20 : ℚ⟦X⟧) :=
      map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 20
    have hC40 : PowerSeries.C (40 : ℚ) = (40 : ℚ⟦X⟧) :=
      map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 40
    have hC48 : PowerSeries.C (48 : ℚ) = (48 : ℚ⟦X⟧) :=
      map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 48
    have hC84 : PowerSeries.C (84 : ℚ) = (84 : ℚ⟦X⟧) :=
      map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 84
    have hC144 : PowerSeries.C (144 : ℚ) = (144 : ℚ⟦X⟧) :=
      map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 144
    have hC156 : PowerSeries.C (156 : ℚ) = (156 : ℚ⟦X⟧) :=
      map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 156
    rw [hC2, hC4, hC20, hC40, hC48, hC84, hC144, hC156] at hvector
    have hP22 : ((22 : Polynomial ℚ) : ℚ⟦X⟧) = (22 : ℚ⟦X⟧) :=
      polynomial_natCast_toPowerSeries 22
    have hP36 : ((36 : Polynomial ℚ) : ℚ⟦X⟧) = (36 : ℚ⟦X⟧) :=
      polynomial_natCast_toPowerSeries 36
    rw [hP22, hP36] at hvector
    rw [heightSixBesselNumerator]
    change _ = degreeThreeBesselSeries heightSixEulerCertificate
    rw [hvector]
    ring
  rw [hrepresentation, degreeThreeBesselSeries_heightSixEulerCertificate]

@[simp] theorem derivative_powerSeries_five :
    PowerSeries.derivative ℚ (5 : ℚ⟦X⟧) = 0 := by
  rw [show (5 : ℚ⟦X⟧) = 4 + 1 by norm_num, map_add,
    derivative_powerSeries_four, derivative_powerSeries_one]
  simp

@[simp] theorem derivative_powerSeries_six :
    PowerSeries.derivative ℚ (6 : ℚ⟦X⟧) = 0 := by
  rw [show (6 : ℚ⟦X⟧) = 4 + 2 by norm_num, map_add,
    derivative_powerSeries_four, derivative_powerSeries_two]
  simp

/-- Exact conjugation of the source height-six ODE under `N=X⁶Y`. -/
theorem heightSix_differential_conjugation (series : ℚ⟦X⟧) :
    X ^ 7 * heightSixDifferentialOperator series =
      heightSixNumeratorDifferentialOperator (X ^ 6 * series) := by
  simp only [heightSixDifferentialOperator,
    heightSixNumeratorDifferentialOperator, map_add,
    Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, derivative_powerSeries_one,
    map_ofNat]
  norm_num
  ring

theorem heightSixBesselSeries_differential_equation :
    heightSixDifferentialOperator heightSixBesselSeries = 0 := by
  have hconjugation := heightSix_differential_conjugation heightSixBesselSeries
  rw [heightSixBesselNumerator_factor,
    heightSixBesselNumerator_differential_equation] at hconjugation
  exact (mul_eq_zero.mp hconjugation).resolve_left
    (pow_ne_zero 7 PowerSeries.X_ne_zero)

noncomputable def heightSixBesselSequence (index : ℕ) : ℚ :=
  (index.factorial : ℚ) * PowerSeries.coeff index heightSixBesselSeries

theorem factorialSeries_heightSixBesselSequence :
    factorialSeries heightSixBesselSequence = heightSixBesselSeries := by
  ext index
  rw [factorialSeries_coeff]
  unfold heightSixBesselSequence
  have hfactorial : (index.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem heightSixBesselSequence_recurrence
    (index : ℕ) (hindex : 4 ≤ index) :
    (index + 5 : ℚ) * (index + 8 : ℚ) * (index + 9 : ℚ) *
          heightSixBesselSequence index -
        4 * (5 * index ^ 2 + 46 * index + 84 : ℚ) *
          heightSixBesselSequence (index - 1) -
        4 * (index - 1 : ℚ) *
          (10 * index ^ 2 + 58 * index + 33 : ℚ) *
          heightSixBesselSequence (index - 2) +
        144 * (index - 1 : ℚ) * (index - 2 : ℚ) *
          heightSixBesselSequence (index - 3) +
        144 * (index - 1 : ℚ) * (index - 2 : ℚ) *
          (index - 3 : ℚ) * heightSixBesselSequence (index - 4) = 0 := by
  apply heightSix_recurrence_of_differential_equation
  rw [factorialSeries_heightSixBesselSequence]
  exact heightSixBesselSeries_differential_equation
  exact hindex

end FibonacciRibbonKernel
