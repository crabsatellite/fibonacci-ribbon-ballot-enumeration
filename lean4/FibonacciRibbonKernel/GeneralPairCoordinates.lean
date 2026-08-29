import FibonacciRibbonKernel.GeneralPairShift

namespace FibonacciRibbonKernel

open PowerSeries

theorem generalFactorialScalarRow_eq_of_rev
    {leftDimension rightDimension : ℕ} (index : ℕ)
    (left : Fin leftDimension) (right : Fin rightDimension)
    (hrev : left.rev.val = right.rev.val) :
    generalFactorialScalarRow leftDimension index left =
      generalFactorialScalarRow rightDimension index right := by
  unfold generalFactorialScalarRow
  rw [hrev]

theorem generalClosedPair_eq_of_revs
    {leftDimension rightDimension : ℕ}
    (leftOne rightOne : Fin leftDimension)
    (leftTwo rightTwo : Fin rightDimension)
    (hleft : leftOne.rev.val = leftTwo.rev.val)
    (hright : rightOne.rev.val = rightTwo.rev.val) :
    generalClosedPair leftOne rightOne =
      generalClosedPair leftTwo rightTwo := by
  ext degree
  rw [generalClosedPair_coeff_formula, generalClosedPair_coeff_formula]
  apply Finset.sum_congr rfl
  intro high hhigh
  split_ifs with hcondition
  · rw [generalFactorialScalarRow_eq_of_rev high leftOne leftTwo hleft,
      generalFactorialScalarRow_eq_of_rev (degree - high) rightOne rightTwo hright,
      generalFactorialScalarRow_eq_of_rev high rightOne rightTwo hright,
      generalFactorialScalarRow_eq_of_rev (degree - high) leftOne leftTwo hleft]
  · rfl

theorem generalClosedPair_self
    {dimension : ℕ} (column : Fin dimension) :
    generalClosedPair column column = 0 := by
  ext degree
  rw [generalClosedPair_coeff_formula]
  apply Finset.sum_eq_zero
  intro high hhigh
  split_ifs <;> ring

/-- Canonical pair coordinate with reversed column heights `(gap,0)`. -/
noncomputable def universalBoundaryPair (gap : ℕ) : ℚ⟦X⟧ :=
  generalClosedPair (0 : Fin (gap + 1)) (Fin.last gap)

theorem universalBoundaryPair_revs (gap : ℕ) :
    (0 : Fin (gap + 1)).rev.val = gap ∧
      (Fin.last gap).rev.val = 0 := by
  simp [Fin.rev]

theorem generalClosedPair_coeff_eq_zero_of_lt_rev_add
    {dimension : ℕ} (degree : ℕ) (left right : Fin dimension)
    (hdegree : degree < left.rev.val + right.rev.val) :
    PowerSeries.coeff degree (generalClosedPair left right) = 0 := by
  rw [generalClosedPair_coeff_formula]
  apply Finset.sum_eq_zero
  intro high hhigh
  split_ifs with hcondition
  · have hle : high ≤ degree := by
      have := Finset.mem_range.mp hhigh
      omega
    have hfirst : generalFactorialScalarRow dimension high left *
        generalFactorialScalarRow dimension (degree - high) right = 0 := by
      by_cases hleft : high < left.rev.val
      · rw [generalFactorialScalarRow_eq_zero_of_lt_rev _ _ hleft,
          zero_mul]
      · have hright : degree - high < right.rev.val := by omega
        rw [generalFactorialScalarRow_eq_zero_of_lt_rev _ _ hright,
          mul_zero]
    have hsecond : generalFactorialScalarRow dimension high right *
        generalFactorialScalarRow dimension (degree - high) left = 0 := by
      by_cases hright : high < right.rev.val
      · rw [generalFactorialScalarRow_eq_zero_of_lt_rev _ _ hright,
          zero_mul]
      · have hleft : degree - high < left.rev.val := by omega
        rw [generalFactorialScalarRow_eq_zero_of_lt_rev _ _ hleft,
          mul_zero]
    rw [hfirst, hsecond, sub_self]
  · rfl

/-- The staircase factor removed from the universal boundary coordinate. -/
noncomputable def universalPairQ (gap : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    PowerSeries.coeff (degree + gap) (universalBoundaryPair gap)

@[simp] theorem universalPairQ_coeff (gap degree : ℕ) :
    PowerSeries.coeff degree (universalPairQ gap) =
      PowerSeries.coeff (degree + gap) (universalBoundaryPair gap) := by
  simp [universalPairQ]

theorem universalPairQ_coeff_boundary_sum (gap degree : ℕ) :
    PowerSeries.coeff degree (universalPairQ gap) =
      ∑ high ∈ Finset.Ico ((degree + gap) / 2 + 1)
          (min ((degree + gap) / 2 + 1 + gap) (degree + gap + 1)),
        generalPairBoundary gap (degree + gap) high := by
  rw [universalPairQ_coeff]
  unfold universalBoundaryPair
  have hrev : (0 : Fin (gap + 1)).rev.val = gap := by
    simp [Fin.rev]
  exact generalClosedPair_coeff_boundaries_min gap (degree + gap)
    (0 : Fin (gap + 1)) hrev

theorem universalBoundaryPair_eq_X_pow_mul_pairQ (gap : ℕ) :
    universalBoundaryPair gap = X ^ gap * universalPairQ gap := by
  ext degree
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hdegree : gap ≤ degree
  · rw [if_pos hdegree, universalPairQ_coeff]
    congr 2
    omega
  · rw [if_neg hdegree]
    apply generalClosedPair_coeff_eq_zero_of_lt_rev_add
    have hrevs := universalBoundaryPair_revs gap
    exact by simpa [universalBoundaryPair, hrevs.1, hrevs.2] using
      (show degree < gap by omega)

theorem generalClosedPair_eq_shifted_universal
    {rank gap : ℕ} (left right : Fin (rank + 1))
    (hgap : left.rev.val = right.rev.val + gap) :
    generalClosedPair left right =
      X ^ (2 * right.rev.val) * universalBoundaryPair gap := by
  have hgapRank : gap ≤ rank := by
    have hleftBound : left.rev.val ≤ rank := by
      simp [Fin.rev]
    omega
  let leftBase : Fin (rank + 1) := ⟨rank - gap, by omega⟩
  let rightBase : Fin (rank + 1) := Fin.last rank
  have hleftBase : leftBase.rev.val = gap := by
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
  apply congrArg (X ^ (2 * right.rev.val) * ·)
  apply generalClosedPair_eq_of_revs leftBase rightBase
    (0 : Fin (gap + 1)) (Fin.last gap)
  · rw [hleftBase]
    exact (universalBoundaryPair_revs gap).1.symm
  · rw [hrightBase]
    exact (universalBoundaryPair_revs gap).2.symm

/-- Every pair coordinate is a monomial times a universal series depending
only on the column gap. -/
theorem generalClosedPair_eq_X_rev_sum_mul_pairQ
    {rank gap : ℕ} (left right : Fin (rank + 1))
    (hgap : left.rev.val = right.rev.val + gap) :
    generalClosedPair left right =
      X ^ (left.rev.val + right.rev.val) * universalPairQ gap := by
  rw [generalClosedPair_eq_shifted_universal left right hgap,
    universalBoundaryPair_eq_X_pow_mul_pairQ]
  rw [← mul_assoc, ← pow_add]
  congr 2
  omega

theorem universalPairQ_one_eq_bessel :
    universalPairQ 1 = generalPairQOne := by
  apply PowerSeries.X_pow_mul_cancel (k := 1)
  rw [← universalBoundaryPair_eq_X_pow_mul_pairQ]
  unfold universalBoundaryPair
  have hrev : (0 : Fin 2).rev.val = 1 := by decide
  simpa [pow_one] using generalClosedPair_rev_one_eq_bessel 0 hrev

theorem universalPairQ_zero : universalPairQ 0 = 0 := by
  ext degree
  rw [universalPairQ_coeff]
  unfold universalBoundaryPair
  rw [show (0 : Fin 1) = Fin.last 0 by rfl, generalClosedPair_self]
  simp

end FibonacciRibbonKernel
