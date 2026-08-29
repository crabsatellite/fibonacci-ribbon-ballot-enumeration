import FibonacciRibbonKernel.HalfPowerCoefficient
import Mathlib.RingTheory.PowerSeries.Derivative

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators

/-!
# Multiplicativity of formal binomial powers

For a zero-constant series `q`, substitution into the generalized binomial
series is the literal formal expansion of `(1+q)^a`.  The fixed-rank pullback
factorization needs the base-multiplicativity identity

`((1+q)(1+r))^a = (1+q)^a (1+r)^a`.

Rather than postulating this identity, we derive it from the binomial
differential equation and uniqueness of first-order formal ODEs.
-/

theorem coeff_X_mul_derivative (series : ℝ⟦X⟧) (index : ℕ) :
    PowerSeries.coeff index
        (PowerSeries.X * PowerSeries.derivative ℝ series) =
      (index : ℝ) * PowerSeries.coeff index series := by
  cases index with
  | zero => simp
  | succ index =>
      rw [← pow_one PowerSeries.X, PowerSeries.coeff_X_pow_mul,
        PowerSeries.coeff_derivative]
      push_cast
      ring

/-- Differential equation `(1+X)F'=aF` for the generalized binomial series. -/
theorem binomialSeries_differential (parameter : ℝ) :
    (1 + PowerSeries.X) *
        PowerSeries.derivative ℝ (PowerSeries.binomialSeries ℝ parameter) =
      PowerSeries.C parameter *
        PowerSeries.binomialSeries ℝ parameter := by
  ext index
  rw [show (1 + PowerSeries.X) *
      PowerSeries.derivative ℝ (PowerSeries.binomialSeries ℝ parameter) =
        PowerSeries.derivative ℝ (PowerSeries.binomialSeries ℝ parameter) +
          PowerSeries.X *
            PowerSeries.derivative ℝ
              (PowerSeries.binomialSeries ℝ parameter) by ring]
  rw [map_add, PowerSeries.coeff_derivative,
    coeff_X_mul_derivative, PowerSeries.coeff_C_mul]
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  have hratio := ringChoose_succ_right_ratio parameter index
  linear_combination hratio

/-- A zero-initial solution of a first-order linear formal ODE is zero. -/
theorem formalLinearODE_zero
    (coefficient solution : ℝ⟦X⟧)
    (hzero : PowerSeries.constantCoeff solution = 0)
    (hode : PowerSeries.derivative ℝ solution = coefficient * solution) :
    solution = 0 := by
  rw [PowerSeries.ext_iff]
  intro index
  induction index using Nat.strong_induction_on with
  | h index ih =>
      cases index with
      | zero =>
          simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero
      | succ index =>
          have hcoeff := congrArg
            (fun value : ℝ⟦X⟧ => PowerSeries.coeff index value) hode
          rw [PowerSeries.coeff_derivative] at hcoeff
          have hproductCoeff :
              PowerSeries.coeff index (coefficient * solution) = 0 := by
            rw [PowerSeries.coeff_mul]
            apply Finset.sum_eq_zero
            intro pair hpair
            have hsumEq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
            rw [ih pair.2 (by omega)]
            simp
          rw [hproductCoeff] at hcoeff
          have hnonzero : (index + 1 : ℝ) ≠ 0 := by positivity
          exact (mul_eq_zero.mp hcoeff).resolve_right hnonzero

/-- Generalized binomial power of the unit `1+deviation`. -/
noncomputable def formalBinomialPow
    (parameter : ℝ) (deviation : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  PowerSeries.subst deviation (PowerSeries.binomialSeries ℝ parameter)

theorem formalBinomialPow_constantCoeff
    (parameter : ℝ) {deviation : ℝ⟦X⟧}
    (hzero : PowerSeries.constantCoeff deviation = 0) :
    PowerSeries.constantCoeff (formalBinomialPow parameter deviation) = 1 := by
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hzero
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold formalBinomialPow
  rw [PowerSeries.coeff_subst' hsubst]
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [finsum_eq_single _ 0]
  · simp
  · intro index hindex
    simp [hindex]
    exact Or.inr hzero

theorem formalBinomialPow_differential
    (parameter : ℝ) {deviation : ℝ⟦X⟧}
    (hsubst : PowerSeries.HasSubst deviation) :
    (1 + deviation) *
        PowerSeries.derivative ℝ (formalBinomialPow parameter deviation) =
      PowerSeries.C parameter * PowerSeries.derivative ℝ deviation *
        formalBinomialPow parameter deviation := by
  have hbase := binomialSeries_differential parameter
  have hpulled := congrArg (PowerSeries.substAlgHom hsubst) hbase
  rw [PowerSeries.coe_substAlgHom] at hpulled
  have hOne :
      PowerSeries.subst deviation (1 : ℝ⟦X⟧) = 1 := by
    change PowerSeries.subst deviation (PowerSeries.C (R := ℝ) 1) = 1
    simpa using PowerSeries.subst_C (a := deviation) (1 : ℝ)
  simp only [PowerSeries.subst_mul hsubst,
    PowerSeries.subst_add hsubst, hOne, PowerSeries.subst_X hsubst,
    PowerSeries.subst_C] at hpulled
  change (1 + deviation) *
      PowerSeries.subst deviation
        (PowerSeries.derivative ℝ (PowerSeries.binomialSeries ℝ parameter)) =
    PowerSeries.C parameter *
      PowerSeries.subst deviation (PowerSeries.binomialSeries ℝ parameter)
    at hpulled
  unfold formalBinomialPow
  rw [PowerSeries.derivative_subst ℝ hsubst]
  linear_combination PowerSeries.derivative ℝ deviation * hpulled

/-- Uniqueness for the unit-form equation `uF'=a u'F`. -/
theorem formalUnitODE_unique
    (parameter : ℝ) (unit first second : ℝ⟦X⟧)
    (hunit : PowerSeries.constantCoeff unit ≠ 0)
    (hfirst : PowerSeries.constantCoeff first = 1)
    (hsecond : PowerSeries.constantCoeff second = 1)
    (hfirstODE : unit * PowerSeries.derivative ℝ first =
      PowerSeries.C parameter * PowerSeries.derivative ℝ unit * first)
    (hsecondODE : unit * PowerSeries.derivative ℝ second =
      PowerSeries.C parameter * PowerSeries.derivative ℝ unit * second) :
    first = second := by
  have hunitInv : unit⁻¹ * unit = 1 :=
    PowerSeries.inv_mul_cancel unit hunit
  have hfirstSolved :
      PowerSeries.derivative ℝ first =
        (unit⁻¹ * PowerSeries.C parameter *
          PowerSeries.derivative ℝ unit) * first := by
    calc
      PowerSeries.derivative ℝ first =
          (unit⁻¹ * unit) * PowerSeries.derivative ℝ first := by
            rw [hunitInv, one_mul]
      _ = unit⁻¹ * (unit * PowerSeries.derivative ℝ first) := by ring
      _ = unit⁻¹ *
          (PowerSeries.C parameter * PowerSeries.derivative ℝ unit * first) := by
            rw [hfirstODE]
      _ = (unit⁻¹ * PowerSeries.C parameter *
          PowerSeries.derivative ℝ unit) * first := by ring
  have hsecondSolved :
      PowerSeries.derivative ℝ second =
        (unit⁻¹ * PowerSeries.C parameter *
          PowerSeries.derivative ℝ unit) * second := by
    calc
      PowerSeries.derivative ℝ second =
          (unit⁻¹ * unit) * PowerSeries.derivative ℝ second := by
            rw [hunitInv, one_mul]
      _ = unit⁻¹ * (unit * PowerSeries.derivative ℝ second) := by ring
      _ = unit⁻¹ *
          (PowerSeries.C parameter * PowerSeries.derivative ℝ unit * second) := by
            rw [hsecondODE]
      _ = (unit⁻¹ * PowerSeries.C parameter *
          PowerSeries.derivative ℝ unit) * second := by ring
  have hzero : PowerSeries.constantCoeff (first - second) = 0 := by
    rw [map_sub, hfirst, hsecond, sub_self]
  have hdiff :
      PowerSeries.derivative ℝ (first - second) =
        (unit⁻¹ * PowerSeries.C parameter *
          PowerSeries.derivative ℝ unit) * (first - second) := by
    rw [map_sub, hfirstSolved, hsecondSolved]
    ring
  have hz := formalLinearODE_zero
    (unit⁻¹ * PowerSeries.C parameter * PowerSeries.derivative ℝ unit)
    (first - second) hzero hdiff
  exact sub_eq_zero.mp hz

/-- Deviation of the product `(1+left)(1+right)`. -/
noncomputable def productDeviation
    (left right : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  left + right + left * right

theorem productDeviation_constantCoeff
    {left right : ℝ⟦X⟧}
    (hleft : PowerSeries.constantCoeff left = 0)
    (hright : PowerSeries.constantCoeff right = 0) :
    PowerSeries.constantCoeff (productDeviation left right) = 0 := by
  unfold productDeviation
  simp [hleft, hright]

/-- Base-multiplicativity of generalized formal binomial powers. -/
theorem formalBinomialPow_product
    (parameter : ℝ) {left right : ℝ⟦X⟧}
    (hleft : PowerSeries.constantCoeff left = 0)
    (hright : PowerSeries.constantCoeff right = 0) :
    formalBinomialPow parameter (productDeviation left right) =
      formalBinomialPow parameter left * formalBinomialPow parameter right := by
  let combined := productDeviation left right
  let first := formalBinomialPow parameter combined
  let leftPow := formalBinomialPow parameter left
  let rightPow := formalBinomialPow parameter right
  let second := leftPow * rightPow
  let unit := 1 + combined
  have hcombinedZero : PowerSeries.constantCoeff combined = 0 := by
    exact productDeviation_constantCoeff hleft hright
  have hcombinedSubst :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hcombinedZero
  have hleftSubst := PowerSeries.HasSubst.of_constantCoeff_zero' hleft
  have hrightSubst := PowerSeries.HasSubst.of_constantCoeff_zero' hright
  have hunitConst : PowerSeries.constantCoeff unit ≠ 0 := by
    dsimp only [unit]
    simp [hcombinedZero]
  have hfirstConst : PowerSeries.constantCoeff first = 1 := by
    exact formalBinomialPow_constantCoeff parameter hcombinedZero
  have hleftConst : PowerSeries.constantCoeff leftPow = 1 := by
    exact formalBinomialPow_constantCoeff parameter hleft
  have hrightConst : PowerSeries.constantCoeff rightPow = 1 := by
    exact formalBinomialPow_constantCoeff parameter hright
  have hsecondConst : PowerSeries.constantCoeff second = 1 := by
    dsimp only [second]
    rw [map_mul, hleftConst, hrightConst, one_mul]
  have hfirstODE :
      unit * PowerSeries.derivative ℝ first =
        PowerSeries.C parameter * PowerSeries.derivative ℝ unit * first := by
    dsimp only [unit, first]
    rw [show PowerSeries.derivative ℝ (1 + combined) =
        PowerSeries.derivative ℝ combined by
      simp [map_add, Derivation.map_one_eq_zero]]
    exact formalBinomialPow_differential parameter hcombinedSubst
  have hleftODE := formalBinomialPow_differential parameter hleftSubst
  have hrightODE := formalBinomialPow_differential parameter hrightSubst
  have hunitFactor : unit = (1 + left) * (1 + right) := by
    dsimp only [unit, combined]
    unfold productDeviation
    ring
  have hsecondODE :
      unit * PowerSeries.derivative ℝ second =
        PowerSeries.C parameter * PowerSeries.derivative ℝ unit * second := by
    dsimp only [second, leftPow, rightPow]
    rw [hunitFactor]
    have hunitDerivative :
        PowerSeries.derivative ℝ ((1 + left) * (1 + right)) =
          (1 + right) * PowerSeries.derivative ℝ left +
            (1 + left) * PowerSeries.derivative ℝ right := by
      simp [Derivation.leibniz, smul_eq_mul, map_add,
        Derivation.map_one_eq_zero]
      ring
    rw [Derivation.leibniz, hunitDerivative]
    simp only [smul_eq_mul]
    linear_combination
      (1 + right) * formalBinomialPow parameter right * hleftODE +
      (1 + left) * formalBinomialPow parameter left * hrightODE
  have heq := formalUnitODE_unique parameter unit first second hunitConst
    hfirstConst hsecondConst hfirstODE hsecondODE
  exact heq

end FibonacciRibbonKernel
