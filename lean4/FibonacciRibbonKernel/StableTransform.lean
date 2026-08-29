import FibonacciRibbonKernel.GeneratingSubstitution
import FibonacciRibbonKernel.InvolutionCycles
import Mathlib.RingTheory.PowerSeries.Derivative

namespace FibonacciRibbonKernel

open PowerSeries

/-- Ordinary generating series of the canonical involution numbers. -/
noncomputable def involutionGeneratingSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun size => (involutionNumber size : ℤ)

@[simp] theorem involutionGeneratingSeries_coeff (size : ℕ) :
    PowerSeries.coeff size involutionGeneratingSeries =
      (involutionNumber size : ℤ) := by
  simp [involutionGeneratingSeries]

/-- Stable no-adjacent-cycle transform of the involution series. -/
noncomputable def stableGeneratingSeries : ℤ⟦X⟧ :=
  substitutionDenominator *
    PowerSeries.subst ribbonSubstitution involutionGeneratingSeries

/-- The signed inclusion--exclusion expression in `eq:stable-ie`. -/
noncomputable def stableSignedNumber (size : ℕ) : ℤ :=
  ∑ edges ∈ Finset.range (size / 2 + 1),
    (-1 : ℤ) ^ edges *
      (Nat.choose (size - edges) edges : ℤ) *
      (involutionNumber (size - 2 * edges) : ℤ)

theorem stableGeneratingSeries_coeff (size : ℕ) :
    PowerSeries.coeff size stableGeneratingSeries = stableSignedNumber size := by
  unfold stableGeneratingSeries stableSignedNumber
  rw [coeff_denominator_mul_subst]
  simp only [involutionGeneratingSeries_coeff]
  calc
    (∑ degree ∈ Finset.range (size + 1),
        (involutionNumber degree : ℤ) *
          PowerSeries.coeff size
            (substitutionDenominator * ribbonSubstitution ^ degree)) =
      ∑ degree ∈ Finset.range (size + 1),
        if 2 ∣ size - degree then
          (involutionNumber degree : ℤ) *
            ((-1 : ℤ) ^ ((size - degree) / 2) *
              (Nat.choose (degree + (size - degree) / 2) degree : ℤ))
        else 0 := by
          apply Finset.sum_congr rfl
          intro degree hdegree
          have hle : degree ≤ size := by
            simp only [Finset.mem_range] at hdegree
            omega
          rw [coeff_denominator_mul_substitution_pow]
          by_cases heven : 2 ∣ size - degree <;> simp [hle, heven]
    _ = ∑ degree ∈
        (Finset.range (size + 1)).filter
          (fun degree => 2 ∣ size - degree),
        (involutionNumber degree : ℤ) *
          ((-1 : ℤ) ^ ((size - degree) / 2) *
            (Nat.choose (degree + (size - degree) / 2) degree : ℤ)) := by
      rw [Finset.sum_filter]
    _ = ∑ edges ∈ Finset.range (size / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (involutionNumber (size - 2 * edges) : ℤ) := by
      apply Finset.sum_bij
        (fun degree _ => (size - degree) / 2)
      · intro degree hdegree
        simp only [Finset.mem_filter, Finset.mem_range] at hdegree
        simp only [Finset.mem_range]
        omega
      · intro left hleft right hright heq
        simp only [Finset.mem_filter, Finset.mem_range] at hleft hright
        obtain ⟨leftHalf, hleftHalf⟩ := hleft.2
        obtain ⟨rightHalf, hrightHalf⟩ := hright.2
        omega
      · intro edges hedges
        simp only [Finset.mem_range] at hedges
        let degree := size - 2 * edges
        have hdegree : degree ∈
            (Finset.range (size + 1)).filter
              (fun degree => 2 ∣ size - degree) := by
          simp only [Finset.mem_filter, Finset.mem_range, degree]
          constructor
          · omega
          · use edges
            omega
        refine ⟨degree, hdegree, ?_⟩
        dsimp [degree]
        omega
      · intro degree hdegree
        simp only [Finset.mem_filter, Finset.mem_range] at hdegree
        obtain ⟨half, hhalf⟩ := hdegree.2
        rw [show size - 2 * ((size - degree) / 2) = degree by omega]
        rw [show size - (size - degree) / 2 =
          degree + (size - degree) / 2 by omega]
        rw [Nat.choose_symm_add]
        ring

/-- Formal OGF differential equation equivalent to the telephone recurrence. -/
theorem involutionGeneratingSeries_differential :
    X ^ 3 * PowerSeries.derivative ℤ involutionGeneratingSeries +
      (X + X ^ 2 - 1) * involutionGeneratingSeries + 1 = 0 := by
  rw [show (X + X ^ 2 - 1) * involutionGeneratingSeries =
      X ^ 1 * involutionGeneratingSeries + X ^ 2 * involutionGeneratingSeries -
        involutionGeneratingSeries by ring]
  ext coefficient
  simp only [map_add, map_sub, map_zero,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_derivative,
    involutionGeneratingSeries_coeff, PowerSeries.coeff_one]
  rcases coefficient with _ | _ | _ | coefficient
  · simp [involutionNumber_zero]
  · simp [involutionNumber_zero, involutionNumber_one]
  · simp [involutionNumber_zero, involutionNumber_one, involutionNumber_two]
  · simp only [if_pos (by omega : 3 ≤ coefficient + 1 + 1 + 1),
      if_pos (by omega : 1 ≤ coefficient + 1 + 1 + 1),
      if_pos (by omega : 2 ≤ coefficient + 1 + 1 + 1),
      if_neg (by omega : ¬coefficient + 1 + 1 + 1 = 0)]
    norm_num at ⊢
    rw [show coefficient + 1 + 1 + 1 - 3 + 1 = coefficient + 1 by omega]
    rw [show coefficient + 1 + 1 = coefficient + 2 by omega]
    rw [show coefficient + 1 + 1 + 1 - 2 = coefficient + 1 by omega]
    rw [show coefficient + 1 + 1 + 1 = coefficient + 3 by omega]
    have hrec := involutionNumber_succ (coefficient + 2)
    have hrecZ : (involutionNumber (coefficient + 3) : ℤ) =
        involutionNumber (coefficient + 2) +
          (coefficient + 2) * involutionNumber (coefficient + 1) := by
      exact_mod_cast hrec
    rw [hrecZ]
    ring

theorem substitutionDenominator_derivative :
    PowerSeries.derivative ℤ substitutionDenominator =
      -2 * X * substitutionDenominator ^ 2 := by
  have hderivative := congrArg (PowerSeries.derivative ℤ)
    substitutionDenominator_mul_one_add_X_sq
  change PowerSeries.derivativeFun
      (substitutionDenominator * (1 + X ^ 2)) =
    PowerSeries.derivativeFun 1 at hderivative
  rw [PowerSeries.derivativeFun_mul, PowerSeries.derivativeFun_one,
    PowerSeries.derivativeFun_add, PowerSeries.derivativeFun_one] at hderivative
  have hX : PowerSeries.derivativeFun (X : ℤ⟦X⟧) = 1 :=
    PowerSeries.derivative_X
  rw [pow_two, PowerSeries.derivativeFun_mul, hX] at hderivative
  simp only [smul_eq_mul, zero_add, mul_one] at hderivative
  change PowerSeries.derivativeFun substitutionDenominator = _
  calc
    PowerSeries.derivativeFun substitutionDenominator =
        PowerSeries.derivativeFun substitutionDenominator *
          (substitutionDenominator * (1 + X ^ 2)) := by
      rw [substitutionDenominator_mul_one_add_X_sq, mul_one]
    _ = substitutionDenominator *
        (PowerSeries.derivativeFun substitutionDenominator * (1 + X ^ 2)) := by
      ring
    _ = substitutionDenominator *
        (-(substitutionDenominator * (2 * X))) := by
      have hpart : PowerSeries.derivativeFun substitutionDenominator * (1 + X ^ 2) =
          -(substitutionDenominator * (2 * X)) := by
        linear_combination hderivative
      rw [hpart]
    _ = -2 * X * substitutionDenominator ^ 2 := by ring

theorem ribbonSubstitution_derivative :
    PowerSeries.derivative ℤ ribbonSubstitution =
      substitutionDenominator ^ 2 * (1 - X ^ 2) := by
  unfold ribbonSubstitution
  change PowerSeries.derivativeFun (X * substitutionDenominator) = _
  rw [PowerSeries.derivativeFun_mul]
  have hX : PowerSeries.derivativeFun (X : ℤ⟦X⟧) = 1 :=
    PowerSeries.derivative_X
  rw [hX]
  change X * PowerSeries.derivative ℤ substitutionDenominator +
    substitutionDenominator * 1 = _
  rw [substitutionDenominator_derivative]
  have hdenominator := substitutionDenominator_mul_one_add_X_sq
  have hdenominatorSquared : substitutionDenominator =
      substitutionDenominator ^ 2 * (1 + X ^ 2) := by
    calc
      substitutionDenominator = substitutionDenominator *
          (substitutionDenominator * (1 + X ^ 2)) := by
        rw [hdenominator, mul_one]
      _ = substitutionDenominator ^ 2 * (1 + X ^ 2) := by ring
  calc
    X * (-2 * X * substitutionDenominator ^ 2) + substitutionDenominator * 1 =
        X * (-2 * X * substitutionDenominator ^ 2) +
          (substitutionDenominator ^ 2 * (1 + X ^ 2)) * 1 := by
      rw [← hdenominatorSquared]
    _ = substitutionDenominator ^ 2 * (1 - X ^ 2) := by ring

theorem substituted_involution_differential :
    ribbonSubstitution ^ 3 *
          PowerSeries.subst ribbonSubstitution
            (PowerSeries.derivative ℤ involutionGeneratingSeries) +
        (ribbonSubstitution + ribbonSubstitution ^ 2 - 1) *
          PowerSeries.subst ribbonSubstitution involutionGeneratingSeries + 1 = 0 := by
  let hsubst := ribbonSubstitution_hasSubst
  have h := congrArg (PowerSeries.substAlgHom hsubst)
    involutionGeneratingSeries_differential
  simpa only [map_add, map_mul, map_sub, map_pow, map_one, map_zero,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hsubst] using h

theorem stableGeneratingSeries_derivative :
    PowerSeries.derivative ℤ stableGeneratingSeries =
      PowerSeries.derivative ℤ substitutionDenominator *
          PowerSeries.subst ribbonSubstitution involutionGeneratingSeries +
        substitutionDenominator *
          (PowerSeries.subst ribbonSubstitution
              (PowerSeries.derivative ℤ involutionGeneratingSeries) *
            PowerSeries.derivative ℤ ribbonSubstitution) := by
  unfold stableGeneratingSeries
  change PowerSeries.derivativeFun
      (substitutionDenominator *
        PowerSeries.subst ribbonSubstitution involutionGeneratingSeries) = _
  rw [PowerSeries.derivativeFun_mul]
  change substitutionDenominator *
        PowerSeries.derivative ℤ
          (PowerSeries.subst ribbonSubstitution involutionGeneratingSeries) +
      PowerSeries.subst ribbonSubstitution involutionGeneratingSeries *
        PowerSeries.derivative ℤ substitutionDenominator = _
  rw [PowerSeries.derivative_subst ℤ ribbonSubstitution_hasSubst]
  ring

/-- Differential equation of the stable transformed involution series. -/
theorem stableGeneratingSeries_differential :
    X ^ 3 * PowerSeries.derivative ℤ stableGeneratingSeries +
        (-1 + X + X ^ 2 - X ^ 3 + X ^ 4) * stableGeneratingSeries +
      1 - X ^ 2 = 0 := by
  let J := PowerSeries.subst ribbonSubstitution involutionGeneratingSeries
  let Jprime := PowerSeries.subst ribbonSubstitution
    (PowerSeries.derivative ℤ involutionGeneratingSeries)
  have hJ : ribbonSubstitution ^ 3 * Jprime +
        (ribbonSubstitution + ribbonSubstitution ^ 2 - 1) * J + 1 = 0 := by
    exact substituted_involution_differential
  have hdenominator := substitutionDenominator_mul_one_add_X_sq
  rw [stableGeneratingSeries_derivative,
    substitutionDenominator_derivative, ribbonSubstitution_derivative]
  change X ^ 3 *
        ((-2 * X * substitutionDenominator ^ 2) * J +
          substitutionDenominator *
            (Jprime * (substitutionDenominator ^ 2 * (1 - X ^ 2)))) +
      (-1 + X + X ^ 2 - X ^ 3 + X ^ 4) *
        (substitutionDenominator * J) + 1 - X ^ 2 = 0
  have halgebra :
      X ^ 3 *
          ((-2 * X * substitutionDenominator ^ 2) * J +
            substitutionDenominator *
              (Jprime * (substitutionDenominator ^ 2 * (1 - X ^ 2)))) +
        (-1 + X + X ^ 2 - X ^ 3 + X ^ 4) *
          (substitutionDenominator * J) + 1 - X ^ 2 =
        (1 - X ^ 2) *
            (ribbonSubstitution ^ 3 * Jprime +
              (ribbonSubstitution + ribbonSubstitution ^ 2 - 1) * J + 1) -
          J * (substitutionDenominator * (1 + X ^ 2) - 1) *
            (substitutionDenominator * X ^ 2 - X ^ 2 + 1) := by
    unfold ribbonSubstitution
    ring
  rw [halgebra, hJ, hdenominator]
  ring

theorem involutionNumber_three : involutionNumber 3 = 4 := by
  rw [show 3 = 2 + 1 by omega, involutionNumber_succ]
  simp [involutionNumber_one, involutionNumber_two]

theorem stableSignedNumber_zero : stableSignedNumber 0 = 1 := by
  simp [stableSignedNumber, involutionNumber_zero]

theorem stableSignedNumber_one : stableSignedNumber 1 = 1 := by
  simp [stableSignedNumber, involutionNumber_one]

theorem stableSignedNumber_two : stableSignedNumber 2 = 1 := by
  norm_num [stableSignedNumber, Finset.sum_range_succ,
    involutionNumber_zero, involutionNumber_two]

theorem stableSignedNumber_three : stableSignedNumber 3 = 2 := by
  norm_num [stableSignedNumber, Finset.sum_range_succ,
    involutionNumber_one, involutionNumber_three]

/-- The order-four recurrence displayed as `eq:stable-recurrence`. -/
theorem stableSignedNumber_recurrence
    (size : ℕ) (hsize : 3 ≤ size) :
    stableSignedNumber (size + 1) =
      stableSignedNumber size + size * stableSignedNumber (size - 1) -
        stableSignedNumber (size - 2) + stableSignedNumber (size - 3) := by
  have hODE :
      X ^ 3 * PowerSeries.derivative ℤ stableGeneratingSeries -
          stableGeneratingSeries + X ^ 1 * stableGeneratingSeries +
          X ^ 2 * stableGeneratingSeries - X ^ 3 * stableGeneratingSeries +
          X ^ 4 * stableGeneratingSeries + 1 - X ^ 2 = 0 := by
    linear_combination stableGeneratingSeries_differential
  have hcoeff := congrArg (PowerSeries.coeff (size + 1)) hODE
  simp only [map_add, map_sub, map_zero, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_derivative, stableGeneratingSeries_coeff,
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow] at hcoeff
  simp only [if_pos (by omega : 3 ≤ size + 1),
    if_pos (by omega : 1 ≤ size + 1),
    if_pos (by omega : 2 ≤ size + 1),
    if_pos (by omega : 4 ≤ size + 1),
    if_neg (by omega : ¬size + 1 = 0)] at hcoeff
  have hsub1 : size + 1 - 3 + 1 = size - 1 := by omega
  have hsub2 : size + 1 - 1 = size := by omega
  have hsub3 : size + 1 - 2 = size - 1 := by omega
  have hsub4 : size + 1 - 3 = size - 2 := by omega
  have hsub5 : size + 1 - 4 = size - 3 := by omega
  rw [hsub1, hsub2, hsub3, hsub4, hsub5] at hcoeff
  simp only [if_neg (by omega : ¬size + 1 = 2)] at hcoeff
  have hcast : (((size - 2 : ℕ) : ℤ) + 2) = (size : ℤ) := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 2 ≤ size))
  have hterm :
      stableSignedNumber (size - 1) * (((size - 2 : ℕ) : ℤ) + 1) +
          stableSignedNumber (size - 1) =
        (size : ℤ) * stableSignedNumber (size - 1) := by
    rw [← hcast]
    ring
  have hcoeff' :
      -stableSignedNumber (size + 1) + stableSignedNumber size +
          (stableSignedNumber (size - 1) * (((size - 2 : ℕ) : ℤ) + 1) +
            stableSignedNumber (size - 1)) -
        stableSignedNumber (size - 2) + stableSignedNumber (size - 3) = 0 := by
    linear_combination hcoeff
  rw [hterm] at hcoeff'
  linear_combination -hcoeff'

end FibonacciRibbonKernel
