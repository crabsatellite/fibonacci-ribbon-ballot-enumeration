import FibonacciRibbonKernel.SixPairBesselFive

namespace FibonacciRibbonKernel

open PowerSeries

theorem sixFactorialScalarRow_shift
    (shift index : ℕ) (shifted base : Fin 6)
    (hrev : shifted.rev.val = base.rev.val + shift) :
    sixFactorialScalarRow (index + shift) shifted =
      sixFactorialScalarRow index base := by
  unfold sixFactorialScalarRow
  rw [hrev]
  congr 1
  push_cast
  ring

theorem sixFactorialPowerSeriesRow_shift
    (shift index : ℕ) (shifted base : Fin 6)
    (hrev : shifted.rev.val = base.rev.val + shift) :
    sixFactorialPowerSeriesRow (index + shift) shifted =
      X ^ shift * sixFactorialPowerSeriesRow index base := by
  unfold sixFactorialPowerSeriesRow
  rw [sixFactorialScalarRow_shift shift index shifted base hrev]
  rw [PowerSeries.X_pow_eq, PowerSeries.monomial_mul_monomial]
  simp only [one_mul]
  apply congrArg (fun degree => PowerSeries.monomial degree
    (sixFactorialScalarRow index base))
  omega

theorem sixFactorialPowerSeriesRow_eq_zero_of_lt_rev
    (index : ℕ) (column : Fin 6) (hlt : index < column.rev.val) :
    sixFactorialPowerSeriesRow index column = 0 := by
  unfold sixFactorialPowerSeriesRow sixFactorialScalarRow
  rw [reciprocalFactorialInt_nat_sub_eq_zero hlt]
  exact map_zero (PowerSeries.monomial index)

theorem sixFactorialScalarRow_eq_zero_of_lt_rev
    (index : ℕ) (column : Fin 6) (hlt : index < column.rev.val) :
    sixFactorialScalarRow index column = 0 := by
  unfold sixFactorialScalarRow
  exact reciprocalFactorialInt_nat_sub_eq_zero hlt

theorem sixRowSum_below_shift_eq_zero
    (shift : ℕ) (column : Fin 6) (hcolumn : shift ≤ column.rev.val) :
    sixRowSum (sixFactorialRows shift) column = 0 := by
  induction shift with
  | zero => simp [sixFactorialRows]
  | succ shift ih =>
      rw [sixRowSum_succ, Pi.add_apply]
      rw [sixFactorialPowerSeriesRow_eq_zero_of_lt_rev shift column
        (by omega), ih (by omega)]
      exact zero_add 0

theorem sixRowSum_shift
    (shift bound : ℕ) (shifted base : Fin 6)
    (hrev : shifted.rev.val = base.rev.val + shift) :
    sixRowSum (sixFactorialRows (bound + shift)) shifted =
      X ^ shift * sixRowSum (sixFactorialRows bound) base := by
  induction bound with
  | zero =>
      rw [zero_add]
      rw [sixRowSum_below_shift_eq_zero shift shifted (by omega)]
      simp [sixFactorialRows]
  | succ bound ih =>
      rw [show bound + 1 + shift = (bound + shift) + 1 by omega]
      rw [sixRowSum_succ (bound + shift), Pi.add_apply,
        sixRowSum_succ bound, Pi.add_apply]
      rw [sixFactorialPowerSeriesRow_shift shift bound shifted base hrev,
        ih]
      ring

theorem sixPairSum_below_shift_eq_zero
    (shift : ℕ) (left right : Fin 6)
    (hleft : shift ≤ left.rev.val) (hright : shift ≤ right.rev.val) :
    sixPairSum (sixFactorialRows shift) left right = 0 := by
  induction shift with
  | zero => simp [sixFactorialRows]
  | succ shift ih =>
      rw [sixPairSum_succ]
      rw [sixFactorialPowerSeriesRow_eq_zero_of_lt_rev shift left
          (by omega),
        sixFactorialPowerSeriesRow_eq_zero_of_lt_rev shift right
          (by omega), ih (by omega) (by omega)]
      ring

theorem sixPairSum_shift
    (shift bound : ℕ)
    (leftShifted rightShifted leftBase rightBase : Fin 6)
    (hleft : leftShifted.rev.val = leftBase.rev.val + shift)
    (hright : rightShifted.rev.val = rightBase.rev.val + shift) :
    sixPairSum (sixFactorialRows (bound + shift))
        leftShifted rightShifted =
      X ^ (2 * shift) *
        sixPairSum (sixFactorialRows bound) leftBase rightBase := by
  induction bound with
  | zero =>
      rw [zero_add]
      rw [sixPairSum_below_shift_eq_zero shift leftShifted rightShifted
        (by omega) (by omega)]
      simp [sixFactorialRows]
  | succ bound ih =>
      rw [show bound + 1 + shift = (bound + shift) + 1 by omega]
      rw [sixPairSum_succ (bound + shift), sixPairSum_succ bound]
      rw [sixFactorialPowerSeriesRow_shift shift bound
          leftShifted leftBase hleft,
        sixFactorialPowerSeriesRow_shift shift bound
          rightShifted rightBase hright,
        sixRowSum_shift shift bound rightShifted rightBase hright,
        sixRowSum_shift shift bound leftShifted leftBase hleft,
        ih]
      rw [show X ^ (2 * shift) = (X ^ shift) ^ 2 by
        rw [two_mul, pow_add, pow_two]]
      ring

theorem sixClosedPair_shift
    (shift : ℕ)
    (leftShifted rightShifted leftBase rightBase : Fin 6)
    (hleft : leftShifted.rev.val = leftBase.rev.val + shift)
    (hright : rightShifted.rev.val = rightBase.rev.val + shift) :
    sixClosedPair leftShifted rightShifted =
      X ^ (2 * shift) * sixClosedPair leftBase rightBase := by
  ext degree
  by_cases hdegree : 2 * shift ≤ degree
  · rw [PowerSeries.coeff_X_pow_mul', if_pos hdegree]
    rw [sixClosedPair_coeff, sixClosedPair_coeff]
    let reduced := degree - 2 * shift
    have hdegreeEq : degree = reduced + 2 * shift := by
      dsimp only [reduced]
      omega
    rw [hdegreeEq]
    rw [show reduced + 2 * shift + 1 =
        (reduced + 1 + shift) + shift by omega,
      show reduced + 2 * shift - 2 * shift = reduced by omega]
    rw [sixPairSum_shift shift (reduced + 1 + shift)
      leftShifted rightShifted leftBase rightBase hleft hright]
    rw [PowerSeries.coeff_X_pow_mul]
    exact (sixPairSum_coeff_stable (reduced + 1 + shift) reduced
      (by omega) leftBase rightBase).trans
        (sixClosedPair_coeff reduced leftBase rightBase)
  · rw [PowerSeries.coeff_X_pow_mul', if_neg hdegree]
    rw [sixClosedPair_coeff, sixPairSum_coeff_formula]
    apply Finset.sum_eq_zero
    intro high hhigh
    split_ifs with hcondition
    · have hsum : high + (degree - high) = degree := by
        have hle : high ≤ degree := by
          have := Finset.mem_range.mp hhigh
          omega
        omega
      have hfirst : sixFactorialScalarRow high leftShifted *
          sixFactorialScalarRow (degree - high) rightShifted = 0 := by
        by_cases hfirstLeft : high < leftShifted.rev.val
        · rw [sixFactorialScalarRow_eq_zero_of_lt_rev _ _ hfirstLeft,
            zero_mul]
        · have hhighLeft : leftShifted.rev.val ≤ high := by omega
          have hlow : degree - high < rightShifted.rev.val := by omega
          rw [sixFactorialScalarRow_eq_zero_of_lt_rev _ _ hlow,
            mul_zero]
      have hsecond : sixFactorialScalarRow high rightShifted *
          sixFactorialScalarRow (degree - high) leftShifted = 0 := by
        by_cases hsecondHigh : high < rightShifted.rev.val
        · rw [sixFactorialScalarRow_eq_zero_of_lt_rev _ _ hsecondHigh,
            zero_mul]
        · have hhighRight : rightShifted.rev.val ≤ high := by omega
          have hlow : degree - high < leftShifted.rev.val := by omega
          rw [sixFactorialScalarRow_eq_zero_of_lt_rev _ _ hlow,
            mul_zero]
      rw [hfirst, hsecond, sub_self]
    · rfl

end FibonacciRibbonKernel
