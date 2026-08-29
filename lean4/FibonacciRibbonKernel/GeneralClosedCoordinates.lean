import FibonacciRibbonKernel.GeneralMinorSeries
import Mathlib.RingTheory.PowerSeries.Trunc

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

variable {R : Type*} [CommRing R]

def generalRowSum {dimension : ℕ} :
    List (GeneralRow dimension R) → GeneralRow dimension R
  | [] => 0
  | head :: tail => head + generalRowSum tail

def generalPairSum {dimension : ℕ} :
    List (GeneralRow dimension R) → Fin dimension → Fin dimension → R
  | [], _, _ => 0
  | head :: tail, left, right =>
      head left * generalRowSum tail right -
        head right * generalRowSum tail left +
        generalPairSum tail left right

@[simp] theorem generalRowSum_nil {dimension : ℕ} :
    generalRowSum ([] : List (GeneralRow dimension R)) = 0 := rfl

@[simp] theorem generalRowSum_cons
    {dimension : ℕ} (head : GeneralRow dimension R)
    (tail : List (GeneralRow dimension R)) :
    generalRowSum (head :: tail) = head + generalRowSum tail := rfl

@[simp] theorem generalPairSum_nil
    {dimension : ℕ} (left right : Fin dimension) :
    generalPairSum ([] : List (GeneralRow dimension R)) left right = 0 := rfl

@[simp] theorem generalPairSum_cons
    {dimension : ℕ} (head : GeneralRow dimension R)
    (tail : List (GeneralRow dimension R)) (left right : Fin dimension) :
    generalPairSum (head :: tail) left right =
      head left * generalRowSum tail right -
        head right * generalRowSum tail left +
        generalPairSum tail left right := rfl

noncomputable def generalFactorialRows (dimension bound : ℕ) :
    List (GeneralRow dimension ℚ⟦X⟧) :=
  (List.range bound).reverse.map
    (generalFactorialPowerSeriesRow dimension)

theorem generalRowSum_succ (dimension bound : ℕ) :
    generalRowSum (generalFactorialRows dimension (bound + 1)) =
      generalFactorialPowerSeriesRow dimension bound +
        generalRowSum (generalFactorialRows dimension bound) := by
  simp [generalFactorialRows, List.range_succ]

theorem generalPairSum_succ
    {dimension : ℕ} (bound : ℕ) (left right : Fin dimension) :
    generalPairSum (generalFactorialRows dimension (bound + 1)) left right =
      generalFactorialPowerSeriesRow dimension bound left *
          generalRowSum (generalFactorialRows dimension bound) right -
        generalFactorialPowerSeriesRow dimension bound right *
          generalRowSum (generalFactorialRows dimension bound) left +
        generalPairSum (generalFactorialRows dimension bound) left right := by
  simp [generalFactorialRows, List.range_succ]

theorem general_coeff_monomial_mul_series
    (degree index : ℕ) (coefficient : ℚ) (series : ℚ⟦X⟧) :
    PowerSeries.coeff degree
        (PowerSeries.monomial index coefficient * series) =
      if index ≤ degree then
        coefficient * PowerSeries.coeff (degree - index) series
      else 0 := by
  rw [general_monomial_eq_monomial_one_mul_C]
  rw [← PowerSeries.X_pow_eq]
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
  split_ifs with hindex
  · rw [PowerSeries.coeff_C_mul]
  · rfl

theorem generalRowSum_coeff
    (dimension bound degree : ℕ) (column : Fin dimension) :
    PowerSeries.coeff degree
        (generalRowSum (generalFactorialRows dimension bound) column) =
      if degree < bound then
        generalFactorialScalarRow dimension degree column
      else 0 := by
  induction bound with
  | zero => simp [generalFactorialRows]
  | succ bound ih =>
      rw [show bound + 1 = Nat.succ bound by omega,
        generalRowSum_succ, Pi.add_apply, map_add, ih]
      unfold generalFactorialPowerSeriesRow
      rw [PowerSeries.coeff_monomial]
      by_cases heq : degree = bound
      · subst degree
        simp
      · by_cases hlt : degree < bound
        · have hsucc : degree < Nat.succ bound := by omega
          simp [hlt, heq, hsucc]
        · have hgt : bound < degree := by omega
          simp [hlt, heq, hgt]

noncomputable def generalClosedSingle
    {dimension : ℕ} (column : Fin dimension) : ℚ⟦X⟧ :=
  X ^ column.rev.val * PowerSeries.exp ℚ

theorem generalClosedSingle_coeff
    {dimension : ℕ} (degree : ℕ) (column : Fin dimension) :
    PowerSeries.coeff degree (generalClosedSingle column) =
      generalFactorialScalarRow dimension degree column := by
  unfold generalClosedSingle generalFactorialScalarRow
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hcolumn : column.rev.val ≤ degree
  · rw [if_pos hcolumn, PowerSeries.coeff_exp,
      reciprocalFactorialInt_nat_sub hcolumn]
    simp
  · have hlt : degree < column.rev.val := by omega
    rw [if_neg hcolumn, reciprocalFactorialInt_nat_sub_eq_zero hlt]

theorem generalRowSum_coeff_eq_closed
    (dimension bound degree : ℕ) (hdegree : degree < bound)
    (column : Fin dimension) :
    PowerSeries.coeff degree
        (generalRowSum (generalFactorialRows dimension bound) column) =
      PowerSeries.coeff degree (generalClosedSingle column) := by
  rw [generalRowSum_coeff, if_pos hdegree, generalClosedSingle_coeff]

noncomputable def generalClosedPair
    {dimension : ℕ} (left right : Fin dimension) : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    PowerSeries.coeff degree
      (generalPairSum (generalFactorialRows dimension (degree + 1)) left right)

theorem generalClosedPair_coeff
    {dimension : ℕ} (degree : ℕ) (left right : Fin dimension) :
    PowerSeries.coeff degree (generalClosedPair left right) =
      PowerSeries.coeff degree
        (generalPairSum (generalFactorialRows dimension (degree + 1))
          left right) := by
  simp [generalClosedPair]

theorem generalPairSum_coeff_formula
    {dimension : ℕ} (bound degree : ℕ) (left right : Fin dimension) :
    PowerSeries.coeff degree
        (generalPairSum (generalFactorialRows dimension bound) left right) =
      ∑ high ∈ Finset.range bound,
        if high ≤ degree ∧ degree - high < high then
          generalFactorialScalarRow dimension high left *
              generalFactorialScalarRow dimension (degree - high) right -
            generalFactorialScalarRow dimension high right *
              generalFactorialScalarRow dimension (degree - high) left
        else 0 := by
  induction bound with
  | zero => simp [generalFactorialRows]
  | succ bound ih =>
      rw [generalPairSum_succ, map_add, map_sub]
      rw [show generalFactorialPowerSeriesRow dimension bound left =
          PowerSeries.monomial bound
            (generalFactorialScalarRow dimension bound left) by rfl,
        show generalFactorialPowerSeriesRow dimension bound right =
          PowerSeries.monomial bound
            (generalFactorialScalarRow dimension bound right) by rfl,
        general_coeff_monomial_mul_series,
        general_coeff_monomial_mul_series,
        generalRowSum_coeff, generalRowSum_coeff, ih,
        Finset.sum_range_succ]
      by_cases hboundDegree : bound ≤ degree
      · by_cases hlow : degree - bound < bound
        · simp [hboundDegree, hlow]
          ring
        · simp [hboundDegree, hlow]
      · simp [hboundDegree]

theorem generalClosedPair_coeff_formula
    {dimension : ℕ} (degree : ℕ) (left right : Fin dimension) :
    PowerSeries.coeff degree (generalClosedPair left right) =
      ∑ high ∈ Finset.range (degree + 1),
        if degree - high < high then
          generalFactorialScalarRow dimension high left *
              generalFactorialScalarRow dimension (degree - high) right -
            generalFactorialScalarRow dimension high right *
              generalFactorialScalarRow dimension (degree - high) left
        else 0 := by
  rw [generalClosedPair_coeff, generalPairSum_coeff_formula]
  apply Finset.sum_congr rfl
  intro high hhigh
  have hle : high ≤ degree := by
    simpa [Finset.mem_range] using hhigh
  simp [hle]

theorem generalPairSum_coeff_stable
    {dimension : ℕ} (bound degree : ℕ) (hdegree : degree < bound)
    (left right : Fin dimension) :
    PowerSeries.coeff degree
        (generalPairSum (generalFactorialRows dimension bound) left right) =
      PowerSeries.coeff degree (generalClosedPair left right) := by
  induction bound with
  | zero => omega
  | succ bound ih =>
      by_cases heq : degree = bound
      · subst degree
        rw [generalClosedPair_coeff]
      · have hlt : degree < bound := by omega
        rw [generalPairSum_succ, map_add, map_sub]
        rw [show generalFactorialPowerSeriesRow dimension bound left =
            PowerSeries.monomial bound
              (generalFactorialScalarRow dimension bound left) by rfl,
          show generalFactorialPowerSeriesRow dimension bound right =
            PowerSeries.monomial bound
              (generalFactorialScalarRow dimension bound right) by rfl,
          general_coeff_monomial_mul_series,
          general_coeff_monomial_mul_series]
        rw [if_neg (by omega : ¬bound ≤ degree),
          if_neg (by omega : ¬bound ≤ degree)]
        simp only [zero_sub, neg_zero, zero_add]
        exact ih hlt

end FibonacciRibbonKernel
