import FibonacciRibbonKernel.HookLength

namespace FibonacciRibbonKernel

/--
Canonical recursive code for involutions on `Fin size`: the largest label is
fixed, or is paired with one of the `size-1` smaller labels and the remaining
labels are relabelled increasingly.
-/
def InvolutionCode : ℕ → Type
  | 0 => PUnit
  | 1 => PUnit
  | size + 2 =>
      InvolutionCode (size + 1) ⊕ (Fin (size + 1) × InvolutionCode size)

noncomputable instance involutionCodeFintype (size : ℕ) :
    Fintype (InvolutionCode size) := by
  induction size using Nat.twoStepInduction with
  | zero => simp [InvolutionCode]; infer_instance
  | one => simp [InvolutionCode]; infer_instance
  | more size ih ihSucc =>
      simp only [InvolutionCode]
      letI := ih
      letI := ihSucc
      infer_instance

/-- Literal involution number `I_k`. -/
noncomputable def involutionNumber (size : ℕ) : ℕ :=
  Fintype.card (InvolutionCode size)

theorem involutionNumber_zero : involutionNumber 0 = 1 := by
  rfl

theorem involutionNumber_one : involutionNumber 1 = 1 := by
  rfl

/-- Telephone-number recurrence `I_{k+1}=I_k+k I_{k-1}`. -/
theorem involutionNumber_succ (size : ℕ) :
    involutionNumber (size + 1) =
      involutionNumber size + size * involutionNumber (size - 1) := by
  cases size with
  | zero => simp [involutionNumber_zero, involutionNumber_one]
  | succ size =>
      unfold involutionNumber
      change Fintype.card
          (InvolutionCode (size + 1) ⊕
            (Fin (size + 1) × InvolutionCode size)) = _
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      simp only [Nat.add_sub_cancel]

theorem involutionNumber_two : involutionNumber 2 = 2 := by
  rw [show 2 = 1 + 1 by omega, involutionNumber_succ]
  simp [involutionNumber_zero, involutionNumber_one]

end FibonacciRibbonKernel
