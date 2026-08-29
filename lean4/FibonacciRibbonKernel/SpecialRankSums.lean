import FibonacciRibbonKernel.EndpointEnumeration

namespace FibonacciRibbonKernel

noncomputable def heightFiveTableauCount (columns : ℕ) : ℕ :=
  unrestrictedCount 4 columns

noncomputable def heightSixTableauCount (columns : ℕ) : ℕ :=
  unrestrictedCount 5 columns

theorem heightFiveRibbonSum (columns : ℕ) :
    (ribbonCount 4 columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (heightFiveTableauCount (columns - 2 * edges) : ℤ) := by
  rw [ribbonCount_main_formula (rank := 4) (by omega)]
  unfold heightFiveTableauCount
  simp_rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  push_cast
  rfl

theorem heightSixRibbonSum (columns : ℕ) :
    (ribbonCount 5 columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (heightSixTableauCount (columns - 2 * edges) : ℤ) := by
  rw [ribbonCount_main_formula (rank := 5) (by omega)]
  unfold heightSixTableauCount
  simp_rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  push_cast
  rfl

end FibonacciRibbonKernel
