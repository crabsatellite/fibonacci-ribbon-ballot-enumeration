import FibonacciRibbonKernel.HeightFourRibbonDfinite

namespace FibonacciRibbonKernel

open PowerSeries

theorem coeff_X_pow_mul_derivative
    (series : ℤ⟦X⟧) (shift index : ℕ) :
    PowerSeries.coeff index
        (X ^ shift * PowerSeries.derivative ℤ series) =
      if shift ≤ index then
        ((index - shift + 1 : ℕ) : ℤ) *
          PowerSeries.coeff (index - shift + 1) series
      else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hshift : shift ≤ index
  · simp only [if_pos hshift, PowerSeries.coeff_derivative]
    rw [Nat.cast_add]
    ring
  · simp only [if_neg hshift]

theorem coeff_X_pow_mul_derivative_two
    (series : ℤ⟦X⟧) (shift index : ℕ) :
    PowerSeries.coeff index
        (X ^ shift * PowerSeries.derivative ℤ
          (PowerSeries.derivative ℤ series)) =
      if shift ≤ index then
        ((index - shift + 2 : ℕ) : ℤ) *
          ((index - shift + 1 : ℕ) : ℤ) *
          PowerSeries.coeff (index - shift + 2) series
      else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hshift : shift ≤ index
  · simp only [if_pos hshift, PowerSeries.coeff_derivative]
    rw [Nat.cast_add, Nat.cast_add]
    ring
  · simp only [if_neg hshift]

theorem coeff_X_pow_mul_plain
    (series : ℤ⟦X⟧) (shift index : ℕ) :
    PowerSeries.coeff index (X ^ shift * series) =
      if shift ≤ index then PowerSeries.coeff (index - shift) series else 0 :=
  PowerSeries.coeff_X_pow_mul' series shift index

theorem heightFourRibbonOrdinaryOperator_expanded
    (series : ℤ⟦X⟧) :
    heightFourRibbonOrdinaryOperator series =
      X ^ 10 * PowerSeries.derivative ℤ
          (PowerSeries.derivative ℤ series) -
      PowerSeries.C 14 * (X ^ 8 * PowerSeries.derivative ℤ
          (PowerSeries.derivative ℤ series)) +
      PowerSeries.C 14 * (X ^ 4 * PowerSeries.derivative ℤ
          (PowerSeries.derivative ℤ series)) -
      X ^ 2 * PowerSeries.derivative ℤ
          (PowerSeries.derivative ℤ series) -
      PowerSeries.C 2 * (X ^ 9 * PowerSeries.derivative ℤ series) +
      PowerSeries.C 8 * (X ^ 8 * PowerSeries.derivative ℤ series) -
      PowerSeries.C 30 * (X ^ 7 * PowerSeries.derivative ℤ series) -
      PowerSeries.C 8 * (X ^ 6 * PowerSeries.derivative ℤ series) +
      PowerSeries.C 34 * (X ^ 5 * PowerSeries.derivative ℤ series) -
      PowerSeries.C 8 * (X ^ 4 * PowerSeries.derivative ℤ series) +
      PowerSeries.C 54 * (X ^ 3 * PowerSeries.derivative ℤ series) +
      PowerSeries.C 8 * (X ^ 2 * PowerSeries.derivative ℤ series) -
      PowerSeries.C 8 * (X ^ 1 * PowerSeries.derivative ℤ series) +
      PowerSeries.C 2 * (X ^ 8 * series) -
      PowerSeries.C 4 * (X ^ 7 * series) -
      PowerSeries.C 14 * (X ^ 6 * series) +
      PowerSeries.C 28 * (X ^ 5 * series) +
      PowerSeries.C 34 * (X ^ 4 * series) -
      PowerSeries.C 44 * (X ^ 3 * series) +
      PowerSeries.C 38 * (X ^ 2 * series) +
      PowerSeries.C 20 * (X ^ 1 * series) -
      PowerSeries.C 12 * series +
      PowerSeries.C 12 - PowerSeries.C 36 * X ^ 2 +
      PowerSeries.C 36 * X ^ 4 - PowerSeries.C 12 * X ^ 6 := by
  unfold heightFourRibbonOrdinaryOperator
  norm_num
  ring

/-- Coefficient extraction from the ribbon OGF equation before collecting
equal shifts.  Keeping this literal producer separate makes the final
P-recursive normalization inexpensive. -/
theorem ribbonCount_rankThree_raw_recurrence (offset : ℕ) :
    ((offset + 2 : ℕ) : ℤ) * ((offset + 1 : ℕ) : ℤ) *
          ribbonCount 3 (offset + 2) -
        14 * (((offset + 4 : ℕ) : ℤ) * ((offset + 3 : ℕ) : ℤ) *
          ribbonCount 3 (offset + 4)) +
        14 * (((offset + 8 : ℕ) : ℤ) * ((offset + 7 : ℕ) : ℤ) *
          ribbonCount 3 (offset + 8)) -
        ((offset + 10 : ℕ) : ℤ) * ((offset + 9 : ℕ) : ℤ) *
          ribbonCount 3 (offset + 10) -
        2 * (((offset + 2 : ℕ) : ℤ) * ribbonCount 3 (offset + 2)) +
        8 * (((offset + 3 : ℕ) : ℤ) * ribbonCount 3 (offset + 3)) -
        30 * (((offset + 4 : ℕ) : ℤ) * ribbonCount 3 (offset + 4)) -
        8 * (((offset + 5 : ℕ) : ℤ) * ribbonCount 3 (offset + 5)) +
        34 * (((offset + 6 : ℕ) : ℤ) * ribbonCount 3 (offset + 6)) -
        8 * (((offset + 7 : ℕ) : ℤ) * ribbonCount 3 (offset + 7)) +
        54 * (((offset + 8 : ℕ) : ℤ) * ribbonCount 3 (offset + 8)) +
        8 * (((offset + 9 : ℕ) : ℤ) * ribbonCount 3 (offset + 9)) -
        8 * (((offset + 10 : ℕ) : ℤ) * ribbonCount 3 (offset + 10)) +
        2 * ribbonCount 3 (offset + 2) -
        4 * ribbonCount 3 (offset + 3) -
        14 * ribbonCount 3 (offset + 4) +
        28 * ribbonCount 3 (offset + 5) +
        34 * ribbonCount 3 (offset + 6) -
        44 * ribbonCount 3 (offset + 7) +
        38 * ribbonCount 3 (offset + 8) +
        20 * ribbonCount 3 (offset + 9) -
        12 * ribbonCount 3 (offset + 10) = 0 := by
  have h := congrArg (PowerSeries.coeff (10 + offset))
    ribbonGeneratingSeries_three_differential
  rw [heightFourRibbonOrdinaryOperator_expanded] at h
  simp only [map_add, map_sub, map_zero, PowerSeries.coeff_C_mul,
    coeff_X_pow_mul_derivative_two] at h
  simp only [coeff_X_pow_mul_derivative] at h
  simp only [coeff_X_pow_mul_plain, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_C, ribbonGeneratingSeries_coeff] at h
  simp only [if_pos (by omega : 10 ≤ 10 + offset),
    if_pos (by omega : 9 ≤ 10 + offset),
    if_pos (by omega : 8 ≤ 10 + offset),
    if_pos (by omega : 7 ≤ 10 + offset),
    if_pos (by omega : 6 ≤ 10 + offset),
    if_pos (by omega : 5 ≤ 10 + offset),
    if_pos (by omega : 4 ≤ 10 + offset),
    if_pos (by omega : 3 ≤ 10 + offset),
    if_pos (by omega : 2 ≤ 10 + offset),
    if_pos (by omega : 1 ≤ 10 + offset),
    if_neg (by omega : 10 + offset ≠ 0),
    if_neg (by omega : 10 + offset ≠ 2),
    if_neg (by omega : 10 + offset ≠ 4),
    if_neg (by omega : 10 + offset ≠ 6)] at h
  rw [show 10 + offset = offset + 10 by omega] at h
  have hsub10 : offset + 10 - 10 = offset := by omega
  have hsub9 : offset + 10 - 9 = offset + 1 := by omega
  have hsub8 : offset + 10 - 8 = offset + 2 := by omega
  have hsub7 : offset + 10 - 7 = offset + 3 := by omega
  have hsub6 : offset + 10 - 6 = offset + 4 := by omega
  have hsub5 : offset + 10 - 5 = offset + 5 := by omega
  have hsub4 : offset + 10 - 4 = offset + 6 := by omega
  have hsub3 : offset + 10 - 3 = offset + 7 := by omega
  have hsub2 : offset + 10 - 2 = offset + 8 := by omega
  have hsub1 : offset + 10 - 1 = offset + 9 := by omega
  rw [hsub10, hsub9, hsub8, hsub7, hsub6, hsub5, hsub4, hsub3,
    hsub2, hsub1] at h
  simp only [Nat.add_assoc, Nat.reduceAdd, mul_zero, add_zero,
    sub_zero] at h
  exact h

/-- Collected order-eight P-recursive certificate for the actual four-letter
ribbon count. -/
theorem ribbonCount_rankThree_recurrence (offset : ℕ) :
    ((offset : ℤ) + 13) * ((offset : ℤ) + 14) *
          ribbonCount 3 (offset + 10) -
        (8 * (offset : ℤ) + 92) * ribbonCount 3 (offset + 9) -
        (14 * (offset : ℤ) ^ 2 + 264 * offset + 1254) *
          ribbonCount 3 (offset + 8) +
        (8 * (offset : ℤ) + 100) * ribbonCount 3 (offset + 7) -
        34 * ((offset : ℤ) + 7) * ribbonCount 3 (offset + 6) +
        (8 * (offset : ℤ) + 12) * ribbonCount 3 (offset + 5) +
        (14 * (offset : ℤ) ^ 2 + 128 * offset + 302) *
          ribbonCount 3 (offset + 4) -
        (8 * (offset : ℤ) + 20) * ribbonCount 3 (offset + 3) -
        (offset : ℤ) * ((offset : ℤ) + 1) *
          ribbonCount 3 (offset + 2) = 0 := by
  have hraw := ribbonCount_rankThree_raw_recurrence offset
  push_cast at hraw ⊢
  linear_combination -hraw

end FibonacciRibbonKernel
