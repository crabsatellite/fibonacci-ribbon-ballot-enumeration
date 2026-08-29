import FibonacciRibbonKernel.RibbonMultiplierEvaluation
import Mathlib.RingTheory.PowerSeries.Log

namespace FibonacciRibbonKernel

open PowerSeries

/-!
# Multiplicativity of the formal logarithm

The integral-exponent regular-singular branch contains
`u^m log u`.  This file proves, inside the formal power-series ring, that
`logOf (uv) = logOf u + logOf v` for units with constant coefficient one.
The proof uses the exact logarithmic differential equation and formal ODE
uniqueness, not an assumed analytic logarithm identity.
-/

noncomputable def alternatingGeometricSeries : ℝ⟦X⟧ :=
  PowerSeries.rescale (-1 : ℝ) (PowerSeries.invOneSubPow ℝ 1).val

theorem alternatingGeometricSeries_mul_one_add_X :
    alternatingGeometricSeries * (1 + PowerSeries.X) = 1 := by
  have hunit := Units.val_inv (PowerSeries.invOneSubPow ℝ 1)
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at hunit
  simp only [pow_one] at hunit
  have hscaled := congrArg (PowerSeries.rescale (-1 : ℝ)) hunit
  simpa [alternatingGeometricSeries, map_mul, map_sub,
    PowerSeries.rescale_neg_one_X] using hscaled

theorem derivative_log_eq_alternatingGeometric :
    PowerSeries.derivative ℝ (PowerSeries.log ℝ) =
      alternatingGeometricSeries := by
  rw [PowerSeries.deriv_log]
  ext index
  rw [PowerSeries.coeff_mk, alternatingGeometricSeries,
    PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp

theorem one_add_X_mul_derivative_log :
    (1 + PowerSeries.X) *
        PowerSeries.derivative ℝ (PowerSeries.log ℝ) = 1 := by
  rw [derivative_log_eq_alternatingGeometric]
  rw [mul_comm, alternatingGeometricSeries_mul_one_add_X]

theorem logOf_differential
    {unit : ℝ⟦X⟧} (hunit : PowerSeries.constantCoeff unit = 1) :
    unit * PowerSeries.derivative ℝ (PowerSeries.logOf unit) =
      PowerSeries.derivative ℝ unit := by
  let deviation := unit - 1
  have hdeviation : PowerSeries.constantCoeff deviation = 0 := by
    dsimp only [deviation]
    rw [map_sub, hunit, map_one, sub_self]
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hdeviation
  have hpulled := congrArg (PowerSeries.substAlgHom hsubst)
    one_add_X_mul_derivative_log
  rw [PowerSeries.coe_substAlgHom] at hpulled
  have hOne : PowerSeries.subst deviation (1 : ℝ⟦X⟧) = 1 := by
    change PowerSeries.subst deviation (PowerSeries.C (R := ℝ) 1) = 1
    simpa using PowerSeries.subst_C (a := deviation) (1 : ℝ)
  simp only [PowerSeries.subst_mul hsubst,
    PowerSeries.subst_add hsubst, hOne, PowerSeries.subst_X hsubst] at hpulled
  have hunitDeviation : 1 + deviation = unit := by
    dsimp only [deviation]
    ring
  rw [hunitDeviation] at hpulled
  unfold PowerSeries.logOf
  rw [PowerSeries.derivative_subst ℝ hsubst]
  have hderivativeDeviation :
      PowerSeries.derivative ℝ deviation = PowerSeries.derivative ℝ unit := by
    dsimp only [deviation]
    simp [map_sub, Derivation.map_one_eq_zero]
  rw [hderivativeDeviation]
  linear_combination PowerSeries.derivative ℝ unit * hpulled

theorem logOf_mul
    {left right : ℝ⟦X⟧}
    (hleft : PowerSeries.constantCoeff left = 1)
    (hright : PowerSeries.constantCoeff right = 1) :
    PowerSeries.logOf (left * right) =
      PowerSeries.logOf left + PowerSeries.logOf right := by
  have hproduct : PowerSeries.constantCoeff (left * right) = 1 := by
    rw [map_mul, hleft, hright, one_mul]
  have hprodODE := logOf_differential hproduct
  have hleftODE := logOf_differential hleft
  have hrightODE := logOf_differential hright
  have hsumODE :
      (left * right) *
          PowerSeries.derivative ℝ
            (PowerSeries.logOf left + PowerSeries.logOf right) =
        PowerSeries.derivative ℝ (left * right) := by
    rw [map_add, Derivation.leibniz]
    simp only [smul_eq_mul]
    linear_combination right * hleftODE + left * hrightODE
  let difference := PowerSeries.logOf (left * right) -
    (PowerSeries.logOf left + PowerSeries.logOf right)
  have hdifferenceConst : PowerSeries.constantCoeff difference = 0 := by
    dsimp only [difference]
    rw [map_sub, map_add,
      PowerSeries.constantCoeff_logOf hproduct,
      PowerSeries.constantCoeff_logOf hleft,
      PowerSeries.constantCoeff_logOf hright]
    ring
  have hunitNe : PowerSeries.constantCoeff (left * right) ≠ 0 := by
    rw [hproduct]
    norm_num
  have hinverse : (left * right)⁻¹ * (left * right) = 1 :=
    PowerSeries.inv_mul_cancel (left * right) hunitNe
  have hdifferenceDerivative :
      PowerSeries.derivative ℝ difference = 0 := by
    have hmulZero :
        (left * right) * PowerSeries.derivative ℝ difference = 0 := by
      dsimp only [difference]
      rw [map_sub]
      linear_combination hprodODE - hsumODE
    calc
      PowerSeries.derivative ℝ difference =
          ((left * right)⁻¹ * (left * right)) *
            PowerSeries.derivative ℝ difference := by rw [hinverse, one_mul]
      _ = (left * right)⁻¹ *
          ((left * right) * PowerSeries.derivative ℝ difference) := by ring
      _ = 0 := by rw [hmulZero, mul_zero]
  have hzeroODE :
      PowerSeries.derivative ℝ difference = (0 : ℝ⟦X⟧) * difference := by
    rw [hdifferenceDerivative, zero_mul]
  have hzero := formalLinearODE_zero 0 difference
    hdifferenceConst hzeroODE
  exact sub_eq_zero.mp hzero

end FibonacciRibbonKernel
