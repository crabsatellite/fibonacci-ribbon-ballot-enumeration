import FibonacciRibbonKernel.ExteriorCoordinatesSix
import FibonacciRibbonKernel.SixExteriorLimit
import FibonacciRibbonKernel.FiveClosedCoordinates

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def sixFactorialRows (bound : ℕ) : List (SixRow ℚ⟦X⟧) :=
  (List.range bound).reverse.map sixFactorialPowerSeriesRow

theorem sixRowSum_succ (bound : ℕ) :
    sixRowSum (sixFactorialRows (bound + 1)) =
      sixFactorialPowerSeriesRow bound +
        sixRowSum (sixFactorialRows bound) := by
  simp [sixFactorialRows, List.range_succ]

theorem sixPairSum_succ (bound : ℕ) (left right : Fin 6) :
    sixPairSum (sixFactorialRows (bound + 1)) left right =
      sixFactorialPowerSeriesRow bound left *
          sixRowSum (sixFactorialRows bound) right -
        sixFactorialPowerSeriesRow bound right *
          sixRowSum (sixFactorialRows bound) left +
        sixPairSum (sixFactorialRows bound) left right := by
  simp [sixFactorialRows, List.range_succ]

theorem sixRowSum_coeff (bound degree : ℕ) (column : Fin 6) :
    PowerSeries.coeff degree
        (sixRowSum (sixFactorialRows bound) column) =
      if degree < bound then sixFactorialScalarRow degree column else 0 := by
  induction bound with
  | zero => simp [sixFactorialRows]
  | succ bound ih =>
      rw [show bound + 1 = Nat.succ bound by omega, sixRowSum_succ]
      rw [Pi.add_apply, map_add, ih]
      unfold sixFactorialPowerSeriesRow
      rw [PowerSeries.coeff_monomial]
      by_cases heq : degree = bound
      · subst degree
        simp
      · by_cases hlt : degree < bound
        · have hsucc : degree < Nat.succ bound := by omega
          simp [hlt, heq, hsucc]
        · have hgt : bound < degree := by omega
          simp [heq, hlt, hgt]

noncomputable def sixClosedPair (left right : Fin 6) : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    PowerSeries.coeff degree
      (sixPairSum (sixFactorialRows (degree + 1)) left right)

theorem sixClosedPair_coeff (degree : ℕ) (left right : Fin 6) :
    PowerSeries.coeff degree (sixClosedPair left right) =
      PowerSeries.coeff degree
        (sixPairSum (sixFactorialRows (degree + 1)) left right) := by
  simp [sixClosedPair]

theorem sixPairSum_coeff_formula
    (bound degree : ℕ) (left right : Fin 6) :
    PowerSeries.coeff degree
        (sixPairSum (sixFactorialRows bound) left right) =
      ∑ high ∈ Finset.range bound,
        if high ≤ degree ∧ degree - high < high then
          sixFactorialScalarRow high left *
              sixFactorialScalarRow (degree - high) right -
            sixFactorialScalarRow high right *
              sixFactorialScalarRow (degree - high) left
        else 0 := by
  induction bound with
  | zero => simp [sixFactorialRows]
  | succ bound ih =>
      rw [sixPairSum_succ, map_add, map_sub]
      rw [show sixFactorialPowerSeriesRow bound left =
          PowerSeries.monomial bound
            (sixFactorialScalarRow bound left) by rfl,
        show sixFactorialPowerSeriesRow bound right =
          PowerSeries.monomial bound
            (sixFactorialScalarRow bound right) by rfl,
        coeff_monomial_mul_series, coeff_monomial_mul_series,
        sixRowSum_coeff, sixRowSum_coeff, ih,
        Finset.sum_range_succ]
      by_cases hboundDegree : bound ≤ degree
      · by_cases hlow : degree - bound < bound
        · simp [hboundDegree, hlow]
          ring
        · simp [hboundDegree, hlow]
      · simp [hboundDegree]

theorem sixClosedPair_coeff_formula
    (degree : ℕ) (left right : Fin 6) :
    PowerSeries.coeff degree (sixClosedPair left right) =
      ∑ high ∈ Finset.range (degree + 1),
        if degree - high < high then
          sixFactorialScalarRow high left *
              sixFactorialScalarRow (degree - high) right -
            sixFactorialScalarRow high right *
              sixFactorialScalarRow (degree - high) left
        else 0 := by
  rw [sixClosedPair_coeff, sixPairSum_coeff_formula]
  apply Finset.sum_congr rfl
  intro high hhigh
  have hle : high ≤ degree := by
    simpa [Finset.mem_range] using hhigh
  simp [hle]

theorem sixPairSum_coeff_stable
    (bound degree : ℕ) (hdegree : degree < bound)
    (left right : Fin 6) :
    PowerSeries.coeff degree
        (sixPairSum (sixFactorialRows bound) left right) =
      PowerSeries.coeff degree (sixClosedPair left right) := by
  induction bound with
  | zero => omega
  | succ bound ih =>
      by_cases heq : degree = bound
      · subst degree
        rw [sixClosedPair_coeff]
      · have hlt : degree < bound := by omega
        rw [sixPairSum_succ, map_add, map_sub]
        rw [show sixFactorialPowerSeriesRow bound left =
            PowerSeries.monomial bound
              (sixFactorialScalarRow bound left) by rfl,
          show sixFactorialPowerSeriesRow bound right =
            PowerSeries.monomial bound
              (sixFactorialScalarRow bound right) by rfl,
          coeff_monomial_mul_series, coeff_monomial_mul_series]
        rw [if_neg (by omega : ¬bound ≤ degree),
          if_neg (by omega : ¬bound ≤ degree)]
        simp only [zero_sub, neg_zero, zero_add]
        exact ih hlt

theorem sixFactorialScalarRow_succ_eq_five
    (index : ℕ) (column : Fin 5) :
    sixFactorialScalarRow index column.succ =
      fiveFactorialScalarRow index column := by
  unfold sixFactorialScalarRow fiveFactorialScalarRow
  congr 1
  simp [Fin.rev]

theorem sixFactorialPowerSeriesRow_succ_eq_five
    (index : ℕ) (column : Fin 5) :
    sixFactorialPowerSeriesRow index column.succ =
      fiveFactorialPowerSeriesRow index column := by
  unfold sixFactorialPowerSeriesRow fiveFactorialPowerSeriesRow
  rw [sixFactorialScalarRow_succ_eq_five]

theorem sixRowSum_succColumn_eq_five
    (bound : ℕ) (column : Fin 5) :
    sixRowSum (sixFactorialRows bound) column.succ =
      fiveRowSum (fiveFactorialRows bound) column := by
  induction bound with
  | zero => simp [sixFactorialRows, fiveFactorialRows]
  | succ bound ih =>
      rw [sixRowSum_succ, fiveRowSum_succ, Pi.add_apply, Pi.add_apply,
        sixFactorialPowerSeriesRow_succ_eq_five, ih]

theorem sixPairSum_succColumns_eq_five
    (bound : ℕ) (left right : Fin 5) :
    sixPairSum (sixFactorialRows bound) left.succ right.succ =
      fivePairSum (fiveFactorialRows bound) left right := by
  induction bound with
  | zero => simp [sixFactorialRows, fiveFactorialRows]
  | succ bound ih =>
      rw [sixPairSum_succ, fivePairSum_succ,
        sixFactorialPowerSeriesRow_succ_eq_five,
        sixFactorialPowerSeriesRow_succ_eq_five,
        sixRowSum_succColumn_eq_five,
        sixRowSum_succColumn_eq_five, ih]

theorem sixClosedPair_succColumns_eq_five
    (left right : Fin 5) :
    sixClosedPair left.succ right.succ = fiveClosedPair left right := by
  ext degree
  rw [sixClosedPair_coeff, fiveClosedPair_coeff,
    sixPairSum_succColumns_eq_five]

theorem sixPairSum_truncationEquivalent
    (bound degree : ℕ) (hbound : degree < bound) (left right : Fin 6) :
    TruncationEquivalent (degree + 1)
      (sixPairSum (sixFactorialRows bound) left right)
      (sixClosedPair left right) := by
  unfold TruncationEquivalent
  apply Polynomial.ext
  intro current
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hcurrent : current < degree + 1
  · rw [if_pos hcurrent, if_pos hcurrent]
    exact sixPairSum_coeff_stable bound current (by omega) left right
  · rw [if_neg hcurrent, if_neg hcurrent]

end FibonacciRibbonKernel
