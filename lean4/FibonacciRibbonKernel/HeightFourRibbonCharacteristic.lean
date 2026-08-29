import FibonacciRibbonKernel.HeightFourRibbonRecurrence

namespace FibonacciRibbonKernel

/-- Characteristic polynomial obtained from the quadratic-in-index part of
the actual four-letter ribbon recurrence. -/
noncomputable def heightFourRibbonCharacteristicValue (root : ℝ) : ℝ :=
  root ^ 8 - 14 * root ^ 6 + 14 * root ^ 2 - 1

theorem heightFourRibbonCharacteristic_factorization (root : ℝ) :
    heightFourRibbonCharacteristicValue root =
      (root - 1) * (root + 1) * (root ^ 2 + 1) *
        (root ^ 2 - 4 * root + 1) *
        (root ^ 2 + 4 * root + 1) := by
  unfold heightFourRibbonCharacteristicValue
  ring

/-- First indicial polynomial of the same P-recursive equation. -/
noncomputable def heightFourRibbonIndicialValue
    (root exponent : ℝ) : ℝ :=
  10 * root ^ 8 * exponent + 27 * root ^ 8 - 8 * root ^ 7 -
    112 * root ^ 6 * exponent - 264 * root ^ 6 + 8 * root ^ 5 -
    34 * root ^ 4 + 8 * root ^ 3 + 56 * root ^ 2 * exponent +
    128 * root ^ 2 - 8 * root - 2 * exponent - 1

theorem heightFourRibbonIndicial_positive_root_reduction
    (root exponent : ℝ) (hroot : root ^ 2 - 4 * root + 1 = 0) :
    heightFourRibbonIndicialValue root exponent =
      384 * (56 * root - 15) * (exponent + 3) := by
  unfold heightFourRibbonIndicialValue
  linear_combination
    (root ^ 6 * (10 * exponent + 27) +
      root ^ 5 * (40 * exponent + 100) +
      root ^ 4 * (38 * exponent + 109) +
      root ^ 3 * (112 * exponent + 344) +
      root ^ 2 * (410 * exponent + 1233) +
      root * (1528 * exponent + 4596) +
      5758 * exponent + 17279) * hroot

theorem heightFourRibbonIndicial_negative_root_reduction
    (root exponent : ℝ) (hroot : root ^ 2 + 4 * root + 1 = 0) :
    heightFourRibbonIndicialValue root exponent =
      -384 * (56 * root + 15) * (exponent + 5) := by
  unfold heightFourRibbonIndicialValue
  linear_combination
    (root ^ 6 * (10 * exponent + 27) +
      root ^ 5 * (-40 * exponent - 116) +
      root ^ 4 * (38 * exponent + 173) +
      root ^ 3 * (-112 * exponent - 568) +
      root ^ 2 * (410 * exponent + 2065) +
      root * (-1528 * exponent - 7684) +
      5758 * exponent + 28799) * hroot

theorem fixedRankGrowth_four_quadratic :
    fixedRankGrowth 4 ^ 2 - 4 * fixedRankGrowth 4 + 1 = 0 := by
  rw [fixedRankGrowth_four]
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by positivity)
  nlinarith

theorem neg_fixedRankGrowth_four_quadratic :
    (-fixedRankGrowth 4) ^ 2 + 4 * (-fixedRankGrowth 4) + 1 = 0 := by
  have h := fixedRankGrowth_four_quadratic
  nlinarith

theorem fixedRankGrowth_four_gt_one : 1 < fixedRankGrowth 4 := by
  rw [fixedRankGrowth_four]
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  nlinarith

theorem heightFourRibbonCharacteristic_positive_growth :
    heightFourRibbonCharacteristicValue (fixedRankGrowth 4) = 0 := by
  rw [heightFourRibbonCharacteristic_factorization,
    fixedRankGrowth_four_quadratic]
  ring

theorem heightFourRibbonCharacteristic_negative_growth :
    heightFourRibbonCharacteristicValue (-fixedRankGrowth 4) = 0 := by
  rw [heightFourRibbonCharacteristic_factorization,
    neg_fixedRankGrowth_four_quadratic]
  ring

/-- The dominant positive characteristic root has indicial exponent exactly
`-3`, matching the manuscript's power `k^{-3}`. -/
theorem heightFourRibbon_positive_indicial_iff (exponent : ℝ) :
    heightFourRibbonIndicialValue (fixedRankGrowth 4) exponent = 0 ↔
      exponent = -3 := by
  rw [heightFourRibbonIndicial_positive_root_reduction _ _
    fixedRankGrowth_four_quadratic]
  have hfactor : 56 * fixedRankGrowth 4 - 15 ≠ 0 := by
    have halpha := fixedRankGrowth_four_gt_one
    nlinarith
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hproduct | hexponent
    · rcases mul_eq_zero.mp hproduct with hconstant | hroot
      · norm_num at hconstant
      · exact (hfactor hroot).elim
    · linarith
  · intro h
    rw [h]
    norm_num

/-- The equally large negative characteristic root is two powers lower,
with exponent `-5`; hence it cannot contribute to the `k^{-3}` leading term. -/
theorem heightFourRibbon_negative_indicial_iff (exponent : ℝ) :
    heightFourRibbonIndicialValue (-fixedRankGrowth 4) exponent = 0 ↔
      exponent = -5 := by
  rw [heightFourRibbonIndicial_negative_root_reduction _ _
    neg_fixedRankGrowth_four_quadratic]
  have hfactor : 56 * (-fixedRankGrowth 4) + 15 ≠ 0 := by
    have halpha := fixedRankGrowth_four_gt_one
    nlinarith
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hproduct | hexponent
    · rcases mul_eq_zero.mp hproduct with hconstant | hroot
      · norm_num at hconstant
      · exact (hfactor hroot).elim
    · linarith
  · intro h
    rw [h]
    norm_num

end FibonacciRibbonKernel
