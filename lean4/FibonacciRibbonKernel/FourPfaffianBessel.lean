import FibonacciRibbonKernel.FourExteriorBridge

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def fourFactorialRows (bound : ℕ) : List (FourRow ℚ⟦X⟧) :=
  (List.range bound).reverse.map fourFactorialPowerSeriesRow

theorem fourFactorialPowerSeriesRow_eq_five
    (index : ℕ) (column : Fin 4) :
    fourFactorialPowerSeriesRow index column =
      fiveFactorialPowerSeriesRow index column.succ := by
  unfold fourFactorialPowerSeriesRow fiveFactorialPowerSeriesRow
    fourFactorialScalarRow fiveFactorialScalarRow
  congr 2
  simp [Fin.rev]

theorem fourRowSum_eq_five (bound : ℕ) (column : Fin 4) :
    fourRowSum (fourFactorialRows bound) column =
      fiveRowSum (fiveFactorialRows bound) column.succ := by
  induction bound with
  | zero => simp [fourFactorialRows, fiveFactorialRows]
  | succ bound ih =>
      have hfour : fourRowSum (fourFactorialRows (bound + 1)) =
          fourFactorialPowerSeriesRow bound +
            fourRowSum (fourFactorialRows bound) := by
        simp [fourFactorialRows, List.range_succ]
      rw [hfour, fiveRowSum_succ, Pi.add_apply, Pi.add_apply,
        fourFactorialPowerSeriesRow_eq_five, ih]

theorem fourPairSum_eq_five (bound : ℕ) (left right : Fin 4) :
    fourPairSum (fourFactorialRows bound) left right =
      fivePairSum (fiveFactorialRows bound) left.succ right.succ := by
  induction bound with
  | zero => simp [fourFactorialRows, fiveFactorialRows]
  | succ bound ih =>
      have hfour : fourPairSum (fourFactorialRows (bound + 1)) left right =
          fourFactorialPowerSeriesRow bound left *
              fourRowSum (fourFactorialRows bound) right -
            fourFactorialPowerSeriesRow bound right *
              fourRowSum (fourFactorialRows bound) left +
            fourPairSum (fourFactorialRows bound) left right := by
        simp [fourFactorialRows, List.range_succ]
      rw [hfour, fivePairSum_succ,
        fourFactorialPowerSeriesRow_eq_five,
        fourFactorialPowerSeriesRow_eq_five,
        fourRowSum_eq_five, fourRowSum_eq_five, ih]

noncomputable def fourClosedPair (left right : Fin 4) : ℚ⟦X⟧ :=
  fiveClosedPair left.succ right.succ

theorem fourPairSum_truncationEquivalent
    (bound degree : ℕ) (hbound : degree < bound) (left right : Fin 4) :
    TruncationEquivalent (degree + 1)
      (fourPairSum (fourFactorialRows bound) left right)
      (fourClosedPair left right) := by
  rw [fourPairSum_eq_five]
  exact fivePairSum_truncationEquivalent bound degree hbound left.succ right.succ

noncomputable def fourClosedPfaffian : ℚ⟦X⟧ :=
  pfaffianFour fourClosedPair

theorem pfaffianFour_truncationEquivalent
    {cutoff : ℕ} {pairLeft pairRight : Fin 4 → Fin 4 → ℚ⟦X⟧}
    (hpair : ∀ left right,
      TruncationEquivalent cutoff (pairLeft left right) (pairRight left right)) :
    TruncationEquivalent cutoff
      (pfaffianFour pairLeft) (pfaffianFour pairRight) := by
  unfold pfaffianFour
  repeat
    first
    | apply truncationEquivalent_add
    | apply truncationEquivalent_sub
  all_goals
    apply truncationEquivalent_mul
    all_goals apply hpair

theorem fourTruncatedPfaffian_coeff_eq_closed
    (bound degree : ℕ) (hbound : degree < bound) :
    PowerSeries.coeff degree (fourTruncatedPfaffian bound) =
      PowerSeries.coeff degree fourClosedPfaffian := by
  have hequivalent := pfaffianFour_truncationEquivalent
    (cutoff := degree + 1)
    (pairLeft := fourPairSum (fourFactorialRows bound))
    (pairRight := fourClosedPair)
    (fun left right => fourPairSum_truncationEquivalent
      bound degree hbound left right)
  change PowerSeries.coeff degree
      (pfaffianFour (fourPairSum (fourFactorialRows bound))) =
    PowerSeries.coeff degree fourClosedPfaffian
  unfold fourClosedPfaffian
  unfold TruncationEquivalent at hequivalent
  have hcoeff := congrArg (Polynomial.coeff · degree) hequivalent
  simpa [PowerSeries.coeff_trunc] using hcoeff

noncomputable def fourPfaffianLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 6 ≤ degree then
      PowerSeries.coeff degree (fourTruncatedPfaffian (degree + 1)) else 0

noncomputable def fourClosedPfaffianLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 6 ≤ degree then PowerSeries.coeff degree fourClosedPfaffian else 0

theorem fourExteriorLimitSeries_eq_pfaffianLimit :
    fourExteriorLimitSeries = fourPfaffianLimitSeries := by
  ext degree
  rw [fourExteriorLimitSeries, fourPfaffianLimitSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hdegree : 6 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree, fourExteriorTruncation_eq_pfaffian]
  · rw [if_neg hdegree, if_neg hdegree]

theorem fourPfaffianLimitSeries_eq_closed :
    fourPfaffianLimitSeries = fourClosedPfaffianLimitSeries := by
  ext degree
  rw [fourPfaffianLimitSeries, fourClosedPfaffianLimitSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hdegree : 6 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree]
    exact fourTruncatedPfaffian_coeff_eq_closed (degree + 1) degree (by omega)
  · rw [if_neg hdegree, if_neg hdegree]

theorem X_six_heightFour_factorialSeries_eq_closedPfaffianLimit :
    X ^ 6 * factorialSeries (fun size => (heightFourTableauCount size : ℚ)) =
      fourClosedPfaffianLimitSeries := by
  rw [X_six_mul_heightFour_factorialSeries_eq_exteriorLimit,
    fourExteriorLimitSeries_eq_pfaffianLimit,
    fourPfaffianLimitSeries_eq_closed]

noncomputable def gesselHeightFourSeries : ℚ⟦X⟧ :=
  pairQ1 ^ 2 - pairQ2 ^ 2 + pairQ3 * pairQ1

theorem fourClosedPfaffian_eq_X_six_gessel :
    fourClosedPfaffian = X ^ 6 * gesselHeightFourSeries := by
  unfold fourClosedPfaffian pfaffianFour fourClosedPair
  change fiveClosedPair (1 : Fin 5) 2 * fiveClosedPair 3 4 -
      fiveClosedPair 1 3 * fiveClosedPair 2 4 +
        fiveClosedPair 1 4 * fiveClosedPair 2 3 =
    X ^ 6 * gesselHeightFourSeries
  rw [fiveClosedPair_one_two_explicit,
    fiveClosedPair_three_four_explicit,
    fiveClosedPair_one_three_explicit,
    fiveClosedPair_two_four_explicit,
    fiveClosedPair_one_four_explicit,
    fiveClosedPair_two_three_explicit]
  unfold gesselHeightFourSeries
  ring

theorem fourClosedPfaffianLimitSeries_eq_X_six_gessel :
    fourClosedPfaffianLimitSeries = X ^ 6 * gesselHeightFourSeries := by
  ext degree
  rw [fourClosedPfaffianLimitSeries, PowerSeries.coeff_mk]
  by_cases hdegree : 6 ≤ degree
  · rw [if_pos hdegree, fourClosedPfaffian_eq_X_six_gessel]
  · rw [if_neg hdegree, PowerSeries.coeff_X_pow_mul', if_neg hdegree]

theorem factorialSeries_heightFourTableauCount_eq_gessel :
    factorialSeries (fun size => (heightFourTableauCount size : ℚ)) =
      gesselHeightFourSeries := by
  apply PowerSeries.X_pow_mul_cancel (k := 6)
  rw [X_six_heightFour_factorialSeries_eq_closedPfaffianLimit,
    fourClosedPfaffianLimitSeries_eq_X_six_gessel]

end FibonacciRibbonKernel
