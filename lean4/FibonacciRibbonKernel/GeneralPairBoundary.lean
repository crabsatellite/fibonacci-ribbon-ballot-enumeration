import FibonacciRibbonKernel.GeneralClosedCoordinates

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def generalPairBoundary
    (shift degree high : ℕ) : ℚ :=
  reciprocalFactorialInt ((high : ℤ) - (shift : ℤ)) *
    reciprocalFactorialInt ((degree : ℤ) - (high : ℤ))

theorem generalPairBoundary_of_le
    (shift degree high : ℕ) (hshift : shift ≤ high)
    (hdegree : high ≤ degree) :
    generalPairBoundary shift degree high =
      1 / (((high - shift).factorial : ℚ) *
        ((degree - high).factorial : ℚ)) := by
  unfold generalPairBoundary
  rw [show (high : ℤ) - (shift : ℤ) = ((high - shift : ℕ) : ℤ) by
      omega,
    show (degree : ℤ) - (high : ℤ) = ((degree - high : ℕ) : ℤ) by
      omega]
  rw [reciprocalFactorialInt_ofNat, reciprocalFactorialInt_ofNat]
  ring

theorem generalPairBoundary_summand
    {rank : ℕ} (shift degree high : ℕ) (left : Fin (rank + 1))
    (hleft : left.rev.val = shift) (hhigh : high ≤ degree) :
    generalFactorialScalarRow (rank + 1) high left *
          generalFactorialScalarRow (rank + 1) (degree - high)
            (Fin.last rank) -
        generalFactorialScalarRow (rank + 1) high (Fin.last rank) *
          generalFactorialScalarRow (rank + 1) (degree - high) left =
      generalPairBoundary shift degree high -
        generalPairBoundary shift degree (high + shift) := by
  unfold generalFactorialScalarRow generalPairBoundary
  have hcast : ((degree - high : ℕ) : ℤ) =
      (degree : ℤ) - (high : ℤ) := by omega
  simp only [Fin.rev_last, Fin.val_zero, Nat.cast_zero, sub_zero]
  rw [hleft, hcast]
  have hshiftLeft : (((high + shift : ℕ) : ℤ) - (shift : ℤ)) =
      (high : ℤ) := by push_cast; ring
  have hshiftRight : (degree : ℤ) - ((high + shift : ℕ) : ℤ) =
      (degree : ℤ) - (high : ℤ) - (shift : ℤ) := by
    push_cast
    ring
  rw [hshiftLeft, hshiftRight]

theorem generalPairBoundary_eq_zero_of_degree_lt_high
    (shift degree high : ℕ) (hhigh : degree < high) :
    generalPairBoundary shift degree high = 0 := by
  unfold generalPairBoundary
  rw [reciprocalFactorialInt_nat_sub_eq_zero hhigh, mul_zero]

theorem generalClosedPair_coeff_boundary_sum
    {rank : ℕ} (shift degree : ℕ) (left : Fin (rank + 1))
    (hleft : left.rev.val = shift) :
    PowerSeries.coeff degree
        (generalClosedPair left (Fin.last rank)) =
      ∑ high ∈ Finset.Ico (degree / 2 + 1) (degree + 1),
        (generalPairBoundary shift degree high -
          generalPairBoundary shift degree (high + shift)) := by
  rw [generalClosedPair_coeff_formula]
  have hfilter :
      (Finset.range (degree + 1)).filter
          (fun high => degree - high < high) =
        Finset.Ico (degree / 2 + 1) (degree + 1) := by
    ext high
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hfilter]
  apply Finset.sum_congr rfl
  intro high hhigh
  apply generalPairBoundary_summand shift degree high left hleft
  have := (Finset.mem_Ico.mp hhigh).2
  omega

theorem sum_generalPairBoundary_shift_telescope
    (shift degree start : ℕ)
    (hstartShift : start + shift ≤ degree + 1) :
    (∑ high ∈ Finset.Ico start (degree + 1),
        (generalPairBoundary shift degree high -
          generalPairBoundary shift degree (high + shift))) =
      ∑ high ∈ Finset.Ico start (start + shift),
        generalPairBoundary shift degree high := by
  rw [Finset.sum_sub_distrib]
  have hshift := Finset.sum_Ico_add'
    (generalPairBoundary shift degree) start (degree + 1) shift
  rw [hshift]
  have hfirst := Finset.sum_Ico_consecutive
    (generalPairBoundary shift degree) (by omega : start ≤ start + shift)
      hstartShift
  have hsecond := Finset.sum_Ico_consecutive
    (generalPairBoundary shift degree) hstartShift
      (by omega : degree + 1 ≤ degree + 1 + shift)
  have htail :
      (∑ high ∈ Finset.Ico (degree + 1) (degree + 1 + shift),
        generalPairBoundary shift degree high) = 0 := by
    apply Finset.sum_eq_zero
    intro high hhigh
    apply generalPairBoundary_eq_zero_of_degree_lt_high
    have := (Finset.mem_Ico.mp hhigh).1
    omega
  rw [htail, add_zero] at hsecond
  rw [← hfirst, ← hsecond]
  ring

/-- Boundary telescope without a large-degree hypothesis.  The upper end is
clipped at `degree+1`, where every later reciprocal-factorial term vanishes. -/
theorem sum_generalPairBoundary_shift_telescope_min
    (shift degree start : ℕ) :
    (∑ high ∈ Finset.Ico start (degree + 1),
        (generalPairBoundary shift degree high -
          generalPairBoundary shift degree (high + shift))) =
      ∑ high ∈ Finset.Ico start (min (start + shift) (degree + 1)),
        generalPairBoundary shift degree high := by
  by_cases hshift : start + shift ≤ degree + 1
  · rw [min_eq_left hshift]
    exact sum_generalPairBoundary_shift_telescope shift degree start hshift
  · rw [min_eq_right (by omega : degree + 1 ≤ start + shift),
      Finset.sum_sub_distrib]
    have hzero :
        (∑ high ∈ Finset.Ico start (degree + 1),
          generalPairBoundary shift degree (high + shift)) = 0 := by
      apply Finset.sum_eq_zero
      intro high hhigh
      apply generalPairBoundary_eq_zero_of_degree_lt_high
      have hhighStart := (Finset.mem_Ico.mp hhigh).1
      omega
    rw [hzero, sub_zero]

theorem generalClosedPair_coeff_boundaries_min
    {rank : ℕ} (shift degree : ℕ) (left : Fin (rank + 1))
    (hleft : left.rev.val = shift) :
    PowerSeries.coeff degree
        (generalClosedPair left (Fin.last rank)) =
      ∑ high ∈ Finset.Ico (degree / 2 + 1)
          (min (degree / 2 + 1 + shift) (degree + 1)),
        generalPairBoundary shift degree high := by
  rw [generalClosedPair_coeff_boundary_sum shift degree left hleft]
  exact sum_generalPairBoundary_shift_telescope_min shift degree
    (degree / 2 + 1)

theorem generalClosedPair_coeff_first_boundaries
    {rank : ℕ} (shift degree : ℕ) (left : Fin (rank + 1))
    (hleft : left.rev.val = shift)
    (hlarge : degree / 2 + 1 + shift ≤ degree + 1) :
    PowerSeries.coeff degree
        (generalClosedPair left (Fin.last rank)) =
      ∑ high ∈ Finset.Ico (degree / 2 + 1)
          (degree / 2 + 1 + shift),
        generalPairBoundary shift degree high := by
  rw [generalClosedPair_coeff_boundary_sum shift degree left hleft]
  exact sum_generalPairBoundary_shift_telescope shift degree
    (degree / 2 + 1) hlarge

end FibonacciRibbonKernel
