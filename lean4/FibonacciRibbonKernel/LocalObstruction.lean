import FibonacciRibbonKernel.ParameterWords
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

/--
Original left-to-right Fibonaccian-string entry in zero-based block
`blockIndex`, expressed through a zero-based local parameter.
-/
def originalStringEntry (rank blockIndex : ℕ)
    (parameter : Fin (rank + 1)) : ℕ :=
  blockIndex * (rank + 1) + parameter.val + 1

/--
The original forbidden equality between consecutive left-to-right string
entries occurs exactly at the right-to-left parameter pair `(0,last)`.
-/
theorem original_adjacent_equality_iff_bad_parameters
    (rank leftIndex : ℕ)
    (rightParameter leftParameter : Fin (rank + 1)) :
    originalStringEntry rank (leftIndex + 1) rightParameter =
        originalStringEntry rank leftIndex leftParameter + 1 ↔
      rightParameter = 0 ∧ leftParameter = Fin.last rank := by
  constructor
  · intro heq
    have hright := rightParameter.isLt
    have hleft := leftParameter.isLt
    have hrightVal : rightParameter.val = 0 := by
      simp [originalStringEntry, Nat.add_mul] at heq
      omega
    have hleftVal : leftParameter.val = rank := by
      simp [originalStringEntry, Nat.add_mul] at heq
      omega
    constructor
    · apply Fin.ext
      simpa using hrightVal
    · apply Fin.ext
      simpa using hleftVal
  · rintro ⟨hright, hleft⟩
    subst rightParameter
    subst leftParameter
    simp [originalStringEntry, Nat.add_mul]
    omega

/-- The literal original Fibonaccian adjacency condition. -/
def OriginalAdjacencyAllowed (rank leftIndex : ℕ)
    (rightParameter leftParameter : Fin (rank + 1)) : Prop :=
  originalStringEntry rank (leftIndex + 1) rightParameter ≠
    originalStringEntry rank leftIndex leftParameter + 1

/-- The manuscript's right-to-left local parameter condition. -/
def LocalParameterAdjacencyAllowed (rank : ℕ)
    (rightParameter leftParameter : Fin (rank + 1)) : Prop :=
  (rightParameter, leftParameter) ≠ (0, Fin.last rank)

/--
Exact source-to-manuscript translation of the sole local obstruction, including
the reversal from left-to-right string order to right-to-left column order.
-/
theorem original_adjacency_allowed_iff_local_parameter_allowed
    (rank leftIndex : ℕ)
    (rightParameter leftParameter : Fin (rank + 1)) :
    OriginalAdjacencyAllowed rank leftIndex rightParameter leftParameter ↔
      LocalParameterAdjacencyAllowed rank rightParameter leftParameter := by
  have hiff := original_adjacent_equality_iff_bad_parameters
    rank leftIndex rightParameter leftParameter
  constructor
  · intro horiginal hpair
    apply horiginal
    apply hiff.mpr
    simpa only [Prod.mk.injEq] using hpair
  · intro hpair heq
    apply hpair
    have hbad := hiff.mp heq
    simpa only [Prod.mk.injEq] using hbad

end FibonacciRibbonKernel
