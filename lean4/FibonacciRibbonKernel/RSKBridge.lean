import FibonacciRibbonKernel.RSKRoundTrip
import FibonacciRibbonKernel.ActualInvolutions

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def diagonalRSKPair
    {size : ℕ} (tableau : StandardRowWordTableau size size) :
    RSKTableauPair size where
  insertion := tableau
  recording := tableau
  same_shape := rfl

@[simp] theorem diagonalRSKPair_swap
    {size : ℕ} (tableau : StandardRowWordTableau size size) :
    (diagonalRSKPair tableau).swap = diagonalRSKPair tableau := by
  apply RSKTableauPair.ext <;> rfl

theorem inverseRSKPermutation_diagonal_symm
    {size : ℕ} (tableau : StandardRowWordTableau size size) :
    (inverseRSKPermutation (diagonalRSKPair tableau)).symm =
      inverseRSKPermutation (diagonalRSKPair tableau) := by
  let permutation := inverseRSKPermutation (diagonalRSKPair tableau)
  have hforward : forwardRSK size permutation = diagonalRSKPair tableau :=
    forwardRSK_inverseRSKPermutation (diagonalRSKPair tableau)
  calc
    permutation.symm =
        inverseRSKPermutation (forwardRSK size permutation.symm) :=
      (inverseRSKPermutation_forwardRSK permutation.symm).symm
    _ = inverseRSKPermutation ((forwardRSK size permutation).swap) := by
      rw [forwardRSK_symm]
    _ = inverseRSKPermutation (diagonalRSKPair tableau) := by
      rw [hforward, diagonalRSKPair_swap]

theorem inverseRSKPermutation_diagonal_involutive
    {size : ℕ} (tableau : StandardRowWordTableau size size) :
    Function.Involutive (inverseRSKPermutation (diagonalRSKPair tableau)) := by
  let permutation := inverseRSKPermutation (diagonalRSKPair tableau)
  have hsymm := inverseRSKPermutation_diagonal_symm tableau
  intro value
  have hinverse := permutation.symm_apply_apply value
  rw [hsymm] at hinverse
  exact hinverse

noncomputable def involutionTableauEquiv (size : ℕ) :
    ActualInvolutionOn (Fin size) ≃ StandardRowWordTableau size size where
  toFun involution := (forwardRSK size involution.1).insertion
  invFun tableau :=
    ⟨inverseRSKPermutation (diagonalRSKPair tableau),
      inverseRSKPermutation_diagonal_involutive tableau⟩
  left_inv involution := by
    apply Subtype.ext
    have hdiagonal := forwardRSK_diagonal_of_involutive
      size involution.1 involution.2
    have hpair : forwardRSK size involution.1 =
        diagonalRSKPair (forwardRSK size involution.1).insertion := by
      apply RSKTableauPair.ext
      · rfl
      · exact hdiagonal.symm
    change inverseRSKPermutation
      (diagonalRSKPair (forwardRSK size involution.1).insertion) = involution.1
    rw [← hpair]
    exact inverseRSKPermutation_forwardRSK involution.1
  right_inv tableau := by
    change (forwardRSK size
      (inverseRSKPermutation (diagonalRSKPair tableau))).insertion = tableau
    have hpair := forwardRSK_inverseRSKPermutation (diagonalRSKPair tableau)
    exact congrArg RSKTableauPair.insertion hpair

def actualInvolutionFinEquiv (size : ℕ) :
    ActualInvolution size ≃ ActualInvolutionOn (Fin size) where
  toFun value := ⟨value.1, value.2⟩
  invFun value := ⟨value.1, value.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem involutionNumber_eq_sum_standardTableauNumbers (size : ℕ) :
    involutionNumber size =
      ∑ shape : BoundedPartition size size, standardTableauNumber shape := by
  calc
    involutionNumber size = Fintype.card (ActualInvolution size) :=
      (actualInvolutionNumber_eq_involutionNumber size).symm
    _ = Fintype.card (ActualInvolutionOn (Fin size)) :=
      Fintype.card_congr (actualInvolutionFinEquiv size)
    _ = Fintype.card (StandardRowWordTableau size size) :=
      Fintype.card_congr (involutionTableauEquiv size)
    _ = Fintype.card (StandardTableau size size) :=
      Fintype.card_congr (definingPathBallotRowWordEquiv (dominant_zero size) size).symm
    _ = ∑ shape : BoundedPartition size size, standardTableauNumber shape :=
      standardTableau_card_eq_sum_shape_numbers size size

end FibonacciRibbonKernel
