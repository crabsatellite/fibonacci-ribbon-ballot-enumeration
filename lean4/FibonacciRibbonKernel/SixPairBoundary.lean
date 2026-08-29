import FibonacciRibbonKernel.SixClosedCoordinates
import FibonacciRibbonKernel.FivePairBoundaryGeneral

namespace FibonacciRibbonKernel

open PowerSeries

theorem sixPairBoundary_summand
    (shift degree high : ℕ) (left : Fin 6)
    (hleft : left.rev.val = shift) (hhigh : high ≤ degree) :
    sixFactorialScalarRow high left *
          sixFactorialScalarRow (degree - high) 5 -
        sixFactorialScalarRow high 5 *
          sixFactorialScalarRow (degree - high) left =
      pairBoundary shift degree high -
        pairBoundary shift degree (high + shift) := by
  unfold sixFactorialScalarRow pairBoundary
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

theorem sixClosedPair_coeff_boundary_sum
    (shift degree : ℕ) (left : Fin 6)
    (hleft : left.rev.val = shift) :
    PowerSeries.coeff degree (sixClosedPair left 5) =
      ∑ high ∈ Finset.Ico (degree / 2 + 1) (degree + 1),
        (pairBoundary shift degree high -
          pairBoundary shift degree (high + shift)) := by
  rw [sixClosedPair_coeff_formula]
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
  apply sixPairBoundary_summand shift degree high left hleft
  have := (Finset.mem_Ico.mp hhigh).2
  omega

theorem sixClosedPair_coeff_first_boundaries
    (shift degree : ℕ) (left : Fin 6)
    (hleft : left.rev.val = shift)
    (hlarge : degree / 2 + 1 + shift ≤ degree + 1) :
    PowerSeries.coeff degree (sixClosedPair left 5) =
      ∑ high ∈ Finset.Ico (degree / 2 + 1)
          (degree / 2 + 1 + shift),
        pairBoundary shift degree high := by
  rw [sixClosedPair_coeff_boundary_sum shift degree left hleft]
  exact sum_pairBoundary_shift_telescope shift degree
    (degree / 2 + 1) hlarge

end FibonacciRibbonKernel
