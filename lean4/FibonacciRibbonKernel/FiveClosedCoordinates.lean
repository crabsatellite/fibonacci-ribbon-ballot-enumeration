import FibonacciRibbonKernel.FiveExteriorLimit
import Mathlib.RingTheory.PowerSeries.Trunc

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def fiveFactorialRows (bound : ℕ) : List (FiveRow ℚ⟦X⟧) :=
  (List.range bound).reverse.map fiveFactorialPowerSeriesRow

theorem fiveRowSum_succ (bound : ℕ) :
    fiveRowSum (fiveFactorialRows (bound + 1)) =
      fiveFactorialPowerSeriesRow bound +
        fiveRowSum (fiveFactorialRows bound) := by
  simp [fiveFactorialRows, List.range_succ]

theorem fivePairSum_succ (bound : ℕ) (left right : Fin 5) :
    fivePairSum (fiveFactorialRows (bound + 1)) left right =
      fiveFactorialPowerSeriesRow bound left *
          fiveRowSum (fiveFactorialRows bound) right -
        fiveFactorialPowerSeriesRow bound right *
          fiveRowSum (fiveFactorialRows bound) left +
        fivePairSum (fiveFactorialRows bound) left right := by
  simp [fiveFactorialRows, List.range_succ]

theorem coeff_monomial_mul_series
    (degree index : ℕ) (coefficient : ℚ) (series : ℚ⟦X⟧) :
    PowerSeries.coeff degree
        (PowerSeries.monomial index coefficient * series) =
      if index ≤ degree then
        coefficient * PowerSeries.coeff (degree - index) series
      else 0 := by
  rw [monomial_eq_monomial_one_mul_C]
  rw [← PowerSeries.X_pow_eq]
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
  split_ifs with hindex
  · rw [PowerSeries.coeff_C_mul]
  · rfl

theorem fiveRowSum_coeff (bound degree : ℕ) (column : Fin 5) :
    PowerSeries.coeff degree
        (fiveRowSum (fiveFactorialRows bound) column) =
      if degree < bound then fiveFactorialScalarRow degree column else 0 := by
  induction bound with
  | zero => simp [fiveFactorialRows]
  | succ bound ih =>
      rw [show bound + 1 = Nat.succ bound by omega, fiveRowSum_succ]
      rw [Pi.add_apply, map_add, ih]
      unfold fiveFactorialPowerSeriesRow
      rw [PowerSeries.coeff_monomial]
      by_cases heq : degree = bound
      · subst degree
        simp
      · by_cases hlt : degree < bound
        · have hne : degree ≠ bound := heq
          have hsucc : degree < Nat.succ bound := by omega
          simp [hlt, hne, hsucc]
        · have hgt : bound < degree := by omega
          simp [heq, hlt, hgt]

noncomputable def fiveClosedSingle (column : Fin 5) : ℚ⟦X⟧ :=
  X ^ column.rev.val * PowerSeries.exp ℚ

theorem fiveClosedSingle_coeff (degree : ℕ) (column : Fin 5) :
    PowerSeries.coeff degree (fiveClosedSingle column) =
      fiveFactorialScalarRow degree column := by
  unfold fiveClosedSingle fiveFactorialScalarRow
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hcolumn : column.rev.val ≤ degree
  · rw [if_pos hcolumn, PowerSeries.coeff_exp,
      reciprocalFactorialInt_nat_sub hcolumn]
    simp
  · have hlt : degree < column.rev.val := by omega
    rw [if_neg hcolumn,
      reciprocalFactorialInt_nat_sub_eq_zero hlt]

theorem fiveRowSum_coeff_eq_closed
    (bound degree : ℕ) (hdegree : degree < bound) (column : Fin 5) :
    PowerSeries.coeff degree
        (fiveRowSum (fiveFactorialRows bound) column) =
      PowerSeries.coeff degree (fiveClosedSingle column) := by
  rw [fiveRowSum_coeff, if_pos hdegree, fiveClosedSingle_coeff]

noncomputable def fiveClosedPair (left right : Fin 5) : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    PowerSeries.coeff degree
      (fivePairSum (fiveFactorialRows (degree + 1)) left right)

theorem fiveClosedPair_coeff (degree : ℕ) (left right : Fin 5) :
    PowerSeries.coeff degree (fiveClosedPair left right) =
      PowerSeries.coeff degree
        (fivePairSum (fiveFactorialRows (degree + 1)) left right) := by
  simp [fiveClosedPair]

theorem fivePairSum_coeff_formula
    (bound degree : ℕ) (left right : Fin 5) :
    PowerSeries.coeff degree
        (fivePairSum (fiveFactorialRows bound) left right) =
      ∑ high ∈ Finset.range bound,
        if high ≤ degree ∧ degree - high < high then
          fiveFactorialScalarRow high left *
              fiveFactorialScalarRow (degree - high) right -
            fiveFactorialScalarRow high right *
              fiveFactorialScalarRow (degree - high) left
        else 0 := by
  induction bound with
  | zero => simp [fiveFactorialRows]
  | succ bound ih =>
      rw [fivePairSum_succ,
        map_add, map_sub]
      rw [show fiveFactorialPowerSeriesRow bound left =
          PowerSeries.monomial bound
            (fiveFactorialScalarRow bound left) by rfl,
        show fiveFactorialPowerSeriesRow bound right =
          PowerSeries.monomial bound
            (fiveFactorialScalarRow bound right) by rfl,
        coeff_monomial_mul_series, coeff_monomial_mul_series,
        fiveRowSum_coeff, fiveRowSum_coeff, ih,
        Finset.sum_range_succ]
      by_cases hboundDegree : bound ≤ degree
      · by_cases hlow : degree - bound < bound
        · simp [hboundDegree, hlow]
          ring
        · simp [hboundDegree, hlow]
      · simp [hboundDegree]

theorem fiveClosedPair_coeff_formula
    (degree : ℕ) (left right : Fin 5) :
    PowerSeries.coeff degree (fiveClosedPair left right) =
      ∑ high ∈ Finset.range (degree + 1),
        if degree - high < high then
          fiveFactorialScalarRow high left *
              fiveFactorialScalarRow (degree - high) right -
            fiveFactorialScalarRow high right *
              fiveFactorialScalarRow (degree - high) left
        else 0 := by
  rw [fiveClosedPair_coeff, fivePairSum_coeff_formula]
  apply Finset.sum_congr rfl
  intro high hhigh
  have hle : high ≤ degree := by
    simpa [Finset.mem_range] using hhigh
  simp [hle]

theorem fivePairSum_coeff_stable
    (bound degree : ℕ) (hdegree : degree < bound)
    (left right : Fin 5) :
    PowerSeries.coeff degree
        (fivePairSum (fiveFactorialRows bound) left right) =
      PowerSeries.coeff degree (fiveClosedPair left right) := by
  induction bound with
  | zero => omega
  | succ bound ih =>
      by_cases heq : degree = bound
      · subst degree
        rw [fiveClosedPair_coeff]
      · have hlt : degree < bound := by omega
        rw [fivePairSum_succ, map_add, map_sub]
        rw [show fiveFactorialPowerSeriesRow bound left =
            PowerSeries.monomial bound
              (fiveFactorialScalarRow bound left) by rfl,
          show fiveFactorialPowerSeriesRow bound right =
            PowerSeries.monomial bound
              (fiveFactorialScalarRow bound right) by rfl,
          coeff_monomial_mul_series, coeff_monomial_mul_series]
        rw [if_neg (by omega : ¬bound ≤ degree),
          if_neg (by omega : ¬bound ≤ degree)]
        simp only [zero_sub, neg_zero, zero_add]
        exact ih hlt

def TruncationEquivalent (cutoff : ℕ) (left right : ℚ⟦X⟧) : Prop :=
  PowerSeries.trunc cutoff left = PowerSeries.trunc cutoff right

theorem truncationEquivalent_add {cutoff : ℕ} {a b c d : ℚ⟦X⟧}
    (hab : TruncationEquivalent cutoff a b)
    (hcd : TruncationEquivalent cutoff c d) :
    TruncationEquivalent cutoff (a + c) (b + d) := by
  unfold TruncationEquivalent at *
  simpa using congrArg₂ (· + ·) hab hcd

theorem truncationEquivalent_sub {cutoff : ℕ} {a b c d : ℚ⟦X⟧}
    (hab : TruncationEquivalent cutoff a b)
    (hcd : TruncationEquivalent cutoff c d) :
    TruncationEquivalent cutoff (a - c) (b - d) := by
  unfold TruncationEquivalent at *
  simpa using congrArg₂ (· - ·) hab hcd

theorem truncationEquivalent_mul {cutoff : ℕ} {a b c d : ℚ⟦X⟧}
    (hab : TruncationEquivalent cutoff a b)
    (hcd : TruncationEquivalent cutoff c d) :
    TruncationEquivalent cutoff (a * c) (b * d) := by
  unfold TruncationEquivalent at *
  calc
    PowerSeries.trunc cutoff (a * c) =
        PowerSeries.trunc cutoff
          ((PowerSeries.trunc cutoff a : ℚ⟦X⟧) *
            (PowerSeries.trunc cutoff c : ℚ⟦X⟧)) :=
      (PowerSeries.trunc_trunc_mul_trunc a c).symm
    _ = PowerSeries.trunc cutoff
          ((PowerSeries.trunc cutoff b : ℚ⟦X⟧) *
            (PowerSeries.trunc cutoff d : ℚ⟦X⟧)) := by rw [hab, hcd]
    _ = PowerSeries.trunc cutoff (b * d) :=
      PowerSeries.trunc_trunc_mul_trunc b d

theorem truncationEquivalent_mul_three
    {cutoff : ℕ} {a b c d e f : ℚ⟦X⟧}
    (hab : TruncationEquivalent cutoff a b)
    (hcd : TruncationEquivalent cutoff c d)
    (hef : TruncationEquivalent cutoff e f) :
    TruncationEquivalent cutoff (a * c * e) (b * d * f) :=
  truncationEquivalent_mul (truncationEquivalent_mul hab hcd) hef

theorem fiveRowSum_truncationEquivalent
    (bound degree : ℕ) (hbound : degree < bound) (column : Fin 5) :
    TruncationEquivalent (degree + 1)
      (fiveRowSum (fiveFactorialRows bound) column)
      (fiveClosedSingle column) := by
  unfold TruncationEquivalent
  apply Polynomial.ext
  intro current
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hcurrent : current < degree + 1
  · rw [if_pos hcurrent, if_pos hcurrent]
    exact fiveRowSum_coeff_eq_closed bound current
      (by omega) column
  · rw [if_neg hcurrent, if_neg hcurrent]

theorem fivePairSum_truncationEquivalent
    (bound degree : ℕ) (hbound : degree < bound) (left right : Fin 5) :
    TruncationEquivalent (degree + 1)
      (fivePairSum (fiveFactorialRows bound) left right)
      (fiveClosedPair left right) := by
  unfold TruncationEquivalent
  apply Polynomial.ext
  intro current
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hcurrent : current < degree + 1
  · rw [if_pos hcurrent, if_pos hcurrent]
    exact fivePairSum_coeff_stable bound current (by omega) left right
  · rw [if_neg hcurrent, if_neg hcurrent]

noncomputable def fiveClosedPfaffian : ℚ⟦X⟧ :=
  borderedPfaffianFive fiveClosedPair fiveClosedSingle

theorem borderedPfaffian_truncationEquivalent
    {cutoff : ℕ} {pairLeft pairRight : Fin 5 → Fin 5 → ℚ⟦X⟧}
    {singleLeft singleRight : Fin 5 → ℚ⟦X⟧}
    (hpair : ∀ left right,
      TruncationEquivalent cutoff (pairLeft left right) (pairRight left right))
    (hsingle : ∀ index,
      TruncationEquivalent cutoff (singleLeft index) (singleRight index)) :
    TruncationEquivalent cutoff
      (borderedPfaffianFive pairLeft singleLeft)
      (borderedPfaffianFive pairRight singleRight) := by
  unfold borderedPfaffianFive
  repeat
    first
    | apply truncationEquivalent_add
    | apply truncationEquivalent_sub
  all_goals
    apply truncationEquivalent_mul_three
    all_goals first | apply hpair | apply hsingle

theorem fiveTruncatedPfaffian_coeff_eq_closed
    (bound degree : ℕ) (hbound : degree < bound) :
    PowerSeries.coeff degree (fiveTruncatedPfaffian bound) =
      PowerSeries.coeff degree fiveClosedPfaffian := by
  have hequivalent := borderedPfaffian_truncationEquivalent
    (cutoff := degree + 1)
    (pairLeft := fivePairSum (fiveFactorialRows bound))
    (pairRight := fiveClosedPair)
    (singleLeft := fiveRowSum (fiveFactorialRows bound))
    (singleRight := fiveClosedSingle)
    (fun left right => fivePairSum_truncationEquivalent
      bound degree hbound left right)
    (fun index => fiveRowSum_truncationEquivalent
      bound degree hbound index)
  change PowerSeries.coeff degree
      (borderedPfaffianFive
        (fivePairSum (fiveFactorialRows bound))
        (fiveRowSum (fiveFactorialRows bound))) =
    PowerSeries.coeff degree fiveClosedPfaffian
  unfold fiveClosedPfaffian
  unfold TruncationEquivalent at hequivalent
  have hcoeff := congrArg (Polynomial.coeff · degree) hequivalent
  simpa [PowerSeries.coeff_trunc] using hcoeff

noncomputable def fiveClosedPfaffianLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 10 ≤ degree then PowerSeries.coeff degree fiveClosedPfaffian else 0

theorem fivePfaffianLimitSeries_eq_closedPfaffianLimit :
    fivePfaffianLimitSeries = fiveClosedPfaffianLimitSeries := by
  ext degree
  rw [fivePfaffianLimitSeries, fiveClosedPfaffianLimitSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hdegree : 10 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree]
    exact fiveTruncatedPfaffian_coeff_eq_closed (degree + 1) degree (by omega)
  · rw [if_neg hdegree, if_neg hdegree]

end FibonacciRibbonKernel
