import FibonacciRibbonKernel.GeneralPairBesselOne

namespace FibonacciRibbonKernel

open PowerSeries

theorem generalFactorialScalarRow_shift
    {dimension : ℕ} (shift index : ℕ)
    (shifted base : Fin dimension)
    (hrev : shifted.rev.val = base.rev.val + shift) :
    generalFactorialScalarRow dimension (index + shift) shifted =
      generalFactorialScalarRow dimension index base := by
  unfold generalFactorialScalarRow
  rw [hrev]
  congr 1
  push_cast
  ring

theorem generalFactorialPowerSeriesRow_shift
    {dimension : ℕ} (shift index : ℕ)
    (shifted base : Fin dimension)
    (hrev : shifted.rev.val = base.rev.val + shift) :
    generalFactorialPowerSeriesRow dimension (index + shift) shifted =
      X ^ shift * generalFactorialPowerSeriesRow dimension index base := by
  unfold generalFactorialPowerSeriesRow
  rw [generalFactorialScalarRow_shift shift index shifted base hrev]
  rw [PowerSeries.X_pow_eq, PowerSeries.monomial_mul_monomial]
  simp only [one_mul]
  apply congrArg (fun degree => PowerSeries.monomial degree
    (generalFactorialScalarRow dimension index base))
  omega

theorem generalFactorialPowerSeriesRow_eq_zero_of_lt_rev
    {dimension : ℕ} (index : ℕ) (column : Fin dimension)
    (hlt : index < column.rev.val) :
    generalFactorialPowerSeriesRow dimension index column = 0 := by
  unfold generalFactorialPowerSeriesRow generalFactorialScalarRow
  rw [reciprocalFactorialInt_nat_sub_eq_zero hlt]
  exact map_zero (PowerSeries.monomial index)

theorem generalFactorialScalarRow_eq_zero_of_lt_rev
    {dimension : ℕ} (index : ℕ) (column : Fin dimension)
    (hlt : index < column.rev.val) :
    generalFactorialScalarRow dimension index column = 0 := by
  unfold generalFactorialScalarRow
  exact reciprocalFactorialInt_nat_sub_eq_zero hlt

theorem generalRowSum_below_shift_eq_zero
    {dimension : ℕ} (shift : ℕ) (column : Fin dimension)
    (hcolumn : shift ≤ column.rev.val) :
    generalRowSum (generalFactorialRows dimension shift) column = 0 := by
  induction shift with
  | zero => simp [generalFactorialRows]
  | succ shift ih =>
      rw [generalRowSum_succ, Pi.add_apply]
      rw [generalFactorialPowerSeriesRow_eq_zero_of_lt_rev shift column
        (by omega), ih (by omega)]
      exact zero_add 0

theorem generalRowSum_shift
    {dimension : ℕ} (shift bound : ℕ)
    (shifted base : Fin dimension)
    (hrev : shifted.rev.val = base.rev.val + shift) :
    generalRowSum (generalFactorialRows dimension (bound + shift)) shifted =
      X ^ shift * generalRowSum (generalFactorialRows dimension bound) base := by
  induction bound with
  | zero =>
      rw [zero_add]
      rw [generalRowSum_below_shift_eq_zero shift shifted (by omega)]
      simp [generalFactorialRows]
  | succ bound ih =>
      rw [show bound + 1 + shift = (bound + shift) + 1 by omega]
      rw [generalRowSum_succ dimension (bound + shift), Pi.add_apply,
        generalRowSum_succ dimension bound, Pi.add_apply]
      rw [generalFactorialPowerSeriesRow_shift shift bound shifted base hrev,
        ih]
      ring

theorem generalPairSum_below_shift_eq_zero
    {dimension : ℕ} (shift : ℕ) (left right : Fin dimension)
    (hleft : shift ≤ left.rev.val) (hright : shift ≤ right.rev.val) :
    generalPairSum (generalFactorialRows dimension shift) left right = 0 := by
  induction shift with
  | zero => simp [generalFactorialRows]
  | succ shift ih =>
      rw [generalPairSum_succ]
      rw [generalFactorialPowerSeriesRow_eq_zero_of_lt_rev shift left
          (by omega),
        generalFactorialPowerSeriesRow_eq_zero_of_lt_rev shift right
          (by omega), ih (by omega) (by omega)]
      ring

theorem generalPairSum_shift
    {dimension : ℕ} (shift bound : ℕ)
    (leftShifted rightShifted leftBase rightBase : Fin dimension)
    (hleft : leftShifted.rev.val = leftBase.rev.val + shift)
    (hright : rightShifted.rev.val = rightBase.rev.val + shift) :
    generalPairSum (generalFactorialRows dimension (bound + shift))
        leftShifted rightShifted =
      X ^ (2 * shift) *
        generalPairSum (generalFactorialRows dimension bound)
          leftBase rightBase := by
  induction bound with
  | zero =>
      rw [zero_add]
      rw [generalPairSum_below_shift_eq_zero shift leftShifted rightShifted
        (by omega) (by omega)]
      simp [generalFactorialRows]
  | succ bound ih =>
      rw [show bound + 1 + shift = (bound + shift) + 1 by omega]
      rw [generalPairSum_succ (bound + shift) leftShifted rightShifted,
        generalPairSum_succ bound leftBase rightBase]
      rw [generalFactorialPowerSeriesRow_shift shift bound
          leftShifted leftBase hleft,
        generalFactorialPowerSeriesRow_shift shift bound
          rightShifted rightBase hright,
        generalRowSum_shift shift bound rightShifted rightBase hright,
        generalRowSum_shift shift bound leftShifted leftBase hleft,
        ih]
      rw [show X ^ (2 * shift) = (X ^ shift) ^ 2 by
        rw [two_mul, pow_add, pow_two]]
      ring

theorem generalClosedPair_shift
    {dimension : ℕ} (shift : ℕ)
    (leftShifted rightShifted leftBase rightBase : Fin dimension)
    (hleft : leftShifted.rev.val = leftBase.rev.val + shift)
    (hright : rightShifted.rev.val = rightBase.rev.val + shift) :
    generalClosedPair leftShifted rightShifted =
      X ^ (2 * shift) * generalClosedPair leftBase rightBase := by
  ext degree
  by_cases hdegree : 2 * shift ≤ degree
  · rw [PowerSeries.coeff_X_pow_mul', if_pos hdegree]
    rw [generalClosedPair_coeff, generalClosedPair_coeff]
    let reduced := degree - 2 * shift
    have hdegreeEq : degree = reduced + 2 * shift := by
      dsimp only [reduced]
      omega
    rw [hdegreeEq]
    rw [show reduced + 2 * shift + 1 =
        (reduced + 1 + shift) + shift by omega,
      show reduced + 2 * shift - 2 * shift = reduced by omega]
    rw [generalPairSum_shift shift (reduced + 1 + shift)
      leftShifted rightShifted leftBase rightBase hleft hright]
    rw [PowerSeries.coeff_X_pow_mul]
    exact (generalPairSum_coeff_stable (reduced + 1 + shift) reduced
      (by omega) leftBase rightBase).trans
        (generalClosedPair_coeff reduced leftBase rightBase)
  · rw [PowerSeries.coeff_X_pow_mul', if_neg hdegree]
    rw [generalClosedPair_coeff, generalPairSum_coeff_formula]
    apply Finset.sum_eq_zero
    intro high hhigh
    split_ifs with hcondition
    · have hsum : high + (degree - high) = degree := by
        have hle : high ≤ degree := by
          have := Finset.mem_range.mp hhigh
          omega
        omega
      have hfirst : generalFactorialScalarRow dimension high leftShifted *
          generalFactorialScalarRow dimension (degree - high) rightShifted = 0 := by
        by_cases hfirstLeft : high < leftShifted.rev.val
        · rw [generalFactorialScalarRow_eq_zero_of_lt_rev _ _ hfirstLeft,
            zero_mul]
        · have hlow : degree - high < rightShifted.rev.val := by omega
          rw [generalFactorialScalarRow_eq_zero_of_lt_rev _ _ hlow,
            mul_zero]
      have hsecond : generalFactorialScalarRow dimension high rightShifted *
          generalFactorialScalarRow dimension (degree - high) leftShifted = 0 := by
        by_cases hsecondHigh : high < rightShifted.rev.val
        · rw [generalFactorialScalarRow_eq_zero_of_lt_rev _ _ hsecondHigh,
            zero_mul]
        · have hlow : degree - high < leftShifted.rev.val := by omega
          rw [generalFactorialScalarRow_eq_zero_of_lt_rev _ _ hlow,
            mul_zero]
      rw [hfirst, hsecond, sub_self]
    · rfl

/-- Every adjacent pair of columns is a monomial shift of the universal
`J₀+J₁` boundary coordinate. -/
theorem generalClosedPair_adjacent_eq_bessel
    {rank : ℕ} (left right : Fin (rank + 1))
    (hadjacent : left.rev.val = right.rev.val + 1) :
    generalClosedPair left right =
      X ^ (left.rev.val + right.rev.val) * generalPairQOne := by
  let leftBase : Fin (rank + 1) :=
    ⟨rank - 1, by
      have hleftPositive : 1 ≤ rank := by
        have := left.isLt
        have hrev := hadjacent
        simp [Fin.rev] at hrev
        omega
      omega⟩
  let rightBase : Fin (rank + 1) := Fin.last rank
  have hleftBase : leftBase.rev.val = 1 := by
    simp [leftBase, Fin.rev]
    omega
  have hrightBase : rightBase.rev.val = 0 := by simp [rightBase]
  have hshiftLeft : left.rev.val = leftBase.rev.val + right.rev.val := by
    rw [hleftBase]
    omega
  have hshiftRight : right.rev.val = rightBase.rev.val + right.rev.val := by
    rw [hrightBase, zero_add]
  rw [generalClosedPair_shift right.rev.val left right leftBase rightBase
    hshiftLeft hshiftRight]
  rw [generalClosedPair_rev_one_eq_bessel leftBase hleftBase]
  rw [show left.rev.val + right.rev.val = 2 * right.rev.val + 1 by omega]
  ring

end FibonacciRibbonKernel
