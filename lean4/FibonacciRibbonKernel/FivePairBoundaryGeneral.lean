import FibonacciRibbonKernel.FivePairBesselOne

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def pairBoundary (shift degree high : ℕ) : ℚ :=
  reciprocalFactorialInt ((high : ℤ) - (shift : ℤ)) *
    reciprocalFactorialInt ((degree : ℤ) - (high : ℤ))

theorem pairBoundary_of_le
    (shift degree high : ℕ) (hshift : shift ≤ high)
    (hdegree : high ≤ degree) :
    pairBoundary shift degree high =
      1 / (((high - shift).factorial : ℚ) *
        ((degree - high).factorial : ℚ)) := by
  unfold pairBoundary
  rw [show (high : ℤ) - (shift : ℤ) = ((high - shift : ℕ) : ℤ) by
      omega,
    show (degree : ℤ) - (high : ℤ) = ((degree - high : ℕ) : ℤ) by
      omega]
  rw [show reciprocalFactorialInt ((high - shift : ℕ) : ℤ) =
      (((high - shift).factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat (high - shift),
    show reciprocalFactorialInt ((degree - high : ℕ) : ℤ) =
      (((degree - high).factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat (degree - high)]
  ring

theorem pairBoundary_summand
    (shift degree high : ℕ) (left : Fin 5)
    (hleft : left.rev.val = shift) (hhigh : high ≤ degree) :
    fiveFactorialScalarRow high left *
          fiveFactorialScalarRow (degree - high) 4 -
        fiveFactorialScalarRow high 4 *
          fiveFactorialScalarRow (degree - high) left =
      pairBoundary shift degree high -
        pairBoundary shift degree (high + shift) := by
  unfold fiveFactorialScalarRow pairBoundary
  have hcast : ((degree - high : ℕ) : ℤ) =
      (degree : ℤ) - (high : ℤ) := by omega
  change
    reciprocalFactorialInt ((high : ℤ) - (left.rev.val : ℤ)) *
          reciprocalFactorialInt ((degree - high : ℕ) : ℤ) -
        reciprocalFactorialInt (high : ℤ) *
          reciprocalFactorialInt
            (((degree - high : ℕ) : ℤ) - (left.rev.val : ℤ)) = _
  rw [hleft, hcast]
  have hshiftLeft : (((high + shift : ℕ) : ℤ) - (shift : ℤ)) =
      (high : ℤ) := by push_cast; ring
  have hshiftRight : (degree : ℤ) - ((high + shift : ℕ) : ℤ) =
      (degree : ℤ) - (high : ℤ) - (shift : ℤ) := by push_cast; ring
  rw [hshiftLeft, hshiftRight]

theorem pairBoundary_eq_zero_of_degree_lt_high
    (shift degree high : ℕ) (hhigh : degree < high) :
    pairBoundary shift degree high = 0 := by
  unfold pairBoundary
  rw [reciprocalFactorialInt_nat_sub_eq_zero hhigh, mul_zero]

theorem fiveClosedPair_coeff_boundary_sum
    (shift degree : ℕ) (left : Fin 5)
    (hleft : left.rev.val = shift) :
    PowerSeries.coeff degree (fiveClosedPair left 4) =
      ∑ high ∈ Finset.Ico (degree / 2 + 1) (degree + 1),
        (pairBoundary shift degree high -
          pairBoundary shift degree (high + shift)) := by
  rw [fiveClosedPair_coeff_formula]
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
  apply pairBoundary_summand shift degree high left hleft
  have := (Finset.mem_Ico.mp hhigh).2
  omega

theorem sum_pairBoundary_shift_telescope
    (shift degree start : ℕ)
    (hstartShift : start + shift ≤ degree + 1) :
    (∑ high ∈ Finset.Ico start (degree + 1),
        (pairBoundary shift degree high -
          pairBoundary shift degree (high + shift))) =
      ∑ high ∈ Finset.Ico start (start + shift),
        pairBoundary shift degree high := by
  rw [Finset.sum_sub_distrib]
  have hshift := Finset.sum_Ico_add'
    (pairBoundary shift degree) start (degree + 1) shift
  rw [hshift]
  have hfirst := Finset.sum_Ico_consecutive
    (pairBoundary shift degree) (by omega : start ≤ start + shift)
      hstartShift
  have hsecond := Finset.sum_Ico_consecutive
    (pairBoundary shift degree) hstartShift
      (by omega : degree + 1 ≤ degree + 1 + shift)
  have htail :
      (∑ high ∈ Finset.Ico (degree + 1) (degree + 1 + shift),
        pairBoundary shift degree high) = 0 := by
    apply Finset.sum_eq_zero
    intro high hhigh
    apply pairBoundary_eq_zero_of_degree_lt_high
    have := (Finset.mem_Ico.mp hhigh).1
    omega
  rw [htail, add_zero] at hsecond
  rw [← hfirst, ← hsecond]
  ring

theorem fiveClosedPair_coeff_first_boundaries
    (shift degree : ℕ) (left : Fin 5)
    (hleft : left.rev.val = shift)
    (hlarge : degree / 2 + 1 + shift ≤ degree + 1) :
    PowerSeries.coeff degree (fiveClosedPair left 4) =
      ∑ high ∈ Finset.Ico (degree / 2 + 1)
          (degree / 2 + 1 + shift),
        pairBoundary shift degree high := by
  rw [fiveClosedPair_coeff_boundary_sum shift degree left hleft]
  exact sum_pairBoundary_shift_telescope shift degree
    (degree / 2 + 1) hlarge

end FibonacciRibbonKernel
