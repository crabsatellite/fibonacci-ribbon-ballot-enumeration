import FibonacciRibbonKernel.ExteriorPfaffianSix
import FibonacciRibbonKernel.SixClosedCoordinates

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def sixTruncatedPfaffian (bound : ℕ) : ℚ⟦X⟧ :=
  let rows := (List.range bound).reverse.map sixFactorialPowerSeriesRow
  pfaffianSix (sixPairSum rows)

theorem sixTruncatedCubic_eq_six_mul_pfaffian (bound : ℕ) :
    sixTruncatedCubic bound = 6 * sixTruncatedPfaffian bound := by
  let rows := (List.range bound).reverse.map sixFactorialPowerSeriesRow
  have h := topSixDeterminant_exteriorElementary_two_cube_eq_pfaffian
    (R := ℚ⟦X⟧) rows
  change sixTruncatedCubic bound = 6 * sixTruncatedPfaffian bound at h
  exact h

noncomputable def sixClosedPfaffian : ℚ⟦X⟧ :=
  pfaffianSix sixClosedPair

theorem pfaffianSix_truncationEquivalent
    {cutoff : ℕ} {pairLeft pairRight : Fin 6 → Fin 6 → ℚ⟦X⟧}
    (hpair : ∀ left right,
      TruncationEquivalent cutoff (pairLeft left right) (pairRight left right)) :
    TruncationEquivalent cutoff
      (pfaffianSix pairLeft) (pfaffianSix pairRight) := by
  unfold pfaffianSix
  repeat
    first
    | apply truncationEquivalent_add
    | apply truncationEquivalent_sub
  all_goals
    apply truncationEquivalent_mul_three
    all_goals apply hpair

theorem sixTruncatedPfaffian_coeff_eq_closed
    (bound degree : ℕ) (hbound : degree < bound) :
    PowerSeries.coeff degree (sixTruncatedPfaffian bound) =
      PowerSeries.coeff degree sixClosedPfaffian := by
  have hequivalent := pfaffianSix_truncationEquivalent
    (cutoff := degree + 1)
    (pairLeft := sixPairSum (sixFactorialRows bound))
    (pairRight := sixClosedPair)
    (fun left right => sixPairSum_truncationEquivalent
      bound degree hbound left right)
  change PowerSeries.coeff degree
      (pfaffianSix (sixPairSum (sixFactorialRows bound))) =
    PowerSeries.coeff degree sixClosedPfaffian
  unfold sixClosedPfaffian
  unfold TruncationEquivalent at hequivalent
  have hcoeff := congrArg (Polynomial.coeff · degree) hequivalent
  simpa [PowerSeries.coeff_trunc] using hcoeff

noncomputable def sixPfaffianLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 15 ≤ degree then
      PowerSeries.coeff degree (sixTruncatedPfaffian (degree + 1))
    else 0

noncomputable def sixClosedPfaffianLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 15 ≤ degree then PowerSeries.coeff degree sixClosedPfaffian else 0

theorem sixCubicLimitSeries_eq_six_mul_pfaffianLimit :
    sixCubicLimitSeries = 6 * sixPfaffianLimitSeries := by
  ext degree
  rw [sixCubicLimitSeries, sixPfaffianLimitSeries,
    PowerSeries.coeff_mk]
  have hcast : (6 : ℚ⟦X⟧) = PowerSeries.C (6 : ℚ) := by
    exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 6).symm
  rw [hcast, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  by_cases hdegree : 15 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree,
      sixTruncatedCubic_eq_six_mul_pfaffian]
    rw [hcast, PowerSeries.coeff_C_mul]
  · rw [if_neg hdegree, if_neg hdegree]
    simp

theorem sixPfaffianLimitSeries_eq_closed :
    sixPfaffianLimitSeries = sixClosedPfaffianLimitSeries := by
  ext degree
  rw [sixPfaffianLimitSeries, sixClosedPfaffianLimitSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hdegree : 15 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree]
    exact sixTruncatedPfaffian_coeff_eq_closed (degree + 1) degree (by omega)
  · rw [if_neg hdegree, if_neg hdegree]

theorem X_fifteen_heightSix_factorialSeries_eq_closedPfaffianLimit :
    X ^ 15 * factorialSeries (fun size => (heightSixTableauCount size : ℚ)) =
      sixClosedPfaffianLimitSeries := by
  have hcubic := six_mul_X_fifteen_heightSix_factorialSeries_eq_cubicLimit
  rw [sixCubicLimitSeries_eq_six_mul_pfaffianLimit,
    sixPfaffianLimitSeries_eq_closed] at hcubic
  have hsix : (6 : ℚ⟦X⟧) ≠ 0 := by
    intro hzero
    have hcast : (6 : ℚ⟦X⟧) = PowerSeries.C (6 : ℚ) := by
      exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 6).symm
    rw [hcast] at hzero
    have hC : PowerSeries.C (6 : ℚ) = PowerSeries.C 0 :=
      hzero.trans (map_zero PowerSeries.C).symm
    have := PowerSeries.C_injective hC
    norm_num at this
  exact mul_left_cancel₀ hsix hcubic

end FibonacciRibbonKernel
