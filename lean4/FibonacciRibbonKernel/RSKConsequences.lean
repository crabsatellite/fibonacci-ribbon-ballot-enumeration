import FibonacciRibbonKernel.RSKBridge
import FibonacciRibbonKernel.NearStableDefect
import FibonacciRibbonKernel.StableInvolutions

namespace FibonacciRibbonKernel

open scoped Classical

theorem fullTableauSum_eq_involutionNumber (size : ℕ) :
    fullTableauSum size = involutionNumber size := by
  unfold fullTableauSum
  exact (involutionNumber_eq_sum_standardTableauNumbers size).symm

theorem tableauStableSignedNumber_eq_stableSignedNumber (size : ℕ) :
    tableauStableSignedNumber size = stableSignedNumber size := by
  unfold tableauStableSignedNumber stableSignedNumber
  apply Finset.sum_congr rfl
  intro edges hedges
  rw [fullTableauSum_eq_involutionNumber]

theorem tableauStableSignedNumber_eq_stableActualInvolutionNumber (size : ℕ) :
    tableauStableSignedNumber size = (stableActualInvolutionNumber size : ℤ) := by
  rw [tableauStableSignedNumber_eq_stableSignedNumber,
    ← stableActualInvolution_inclusion_exclusion]

/-- Complete RSK bridge and stable-range identification in `cor:stable`. -/
theorem ribbonCount_eq_stableActualInvolutionNumber
    (rank columns : ℕ) (hrank : 1 ≤ rank) (hstable : columns ≤ rank + 1) :
    ribbonCount rank columns = stableActualInvolutionNumber columns := by
  have hmain := ribbonCount_main_formula (rank := rank) hrank columns
  have hfull (edges : ℕ) :
      (∑ shape : BoundedPartition rank (columns - 2 * edges),
        (standardTableauNumber shape : ℤ)) =
        (fullTableauSum (columns - 2 * edges) : ℤ) := by
    have hheight : columns - 2 * edges ≤ rank + 1 := by omega
    have hcount := unrestrictedCount_eq_fullTableauSum_of_columns_le_height
      rank (columns - 2 * edges) hheight
    rw [unrestrictedCount_eq_sum_standardTableauNumbers] at hcount
    exact_mod_cast hcount
  simp_rw [hfull] at hmain
  have hstableTableau := tableauStableSignedNumber_eq_stableActualInvolutionNumber columns
  unfold tableauStableSignedNumber at hstableTableau
  have hcast : (ribbonCount rank columns : ℤ) =
      stableActualInvolutionNumber columns := hmain.trans hstableTableau
  exact_mod_cast hcast

/-- Complete endpoint of `eq:near-stable-defect` after consuming RSK. -/
theorem stableActualInvolutionNumber_sub_ribbonCount_tail
    (defect size : ℕ) (hsize : defect + 2 ≤ size) :
    (stableActualInvolutionNumber size : ℤ) -
        (ribbonCount (size - defect - 1) size : ℤ) =
      ∑ edges ∈ Finset.range ((defect + 1) / 2),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (tailTableauSum (defect - 2 * edges - 1)
            (size - 2 * edges) : ℤ) := by
  rw [← tableauStableSignedNumber_eq_stableActualInvolutionNumber]
  exact tableauStableSignedNumber_sub_ribbonCount defect size hsize

end FibonacciRibbonKernel
