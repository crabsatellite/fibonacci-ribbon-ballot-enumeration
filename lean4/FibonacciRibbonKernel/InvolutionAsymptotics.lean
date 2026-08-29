import FibonacciRibbonKernel.InvolutionRatios

namespace FibonacciRibbonKernel

/-!
# Fixed-order involution ratios

This file promotes the two-step ratio proved in `InvolutionRatios` to every
fixed number of deleted transpositions.  Both the forward-shifted form and the
literal manuscript indexing are retained, so downstream moment calculations
consume the exact ratio they state.
-/

noncomputable def forwardFixedInvolutionRatio (rank size : ℕ) : ℝ :=
  ((size + 2 * rank : ℕ) : ℝ) ^ rank * involutionNumber size /
    involutionNumber (size + 2 * rank)

theorem forwardFixedInvolutionRatio_zero (size : ℕ) :
    forwardFixedInvolutionRatio 0 size = 1 := by
  unfold forwardFixedInvolutionRatio
  norm_num
  exact (involutionNumber_pos size).ne'

theorem forwardFixedInvolutionRatio_succ
    (rank size : ℕ) (hsize : 1 ≤ size) :
    forwardFixedInvolutionRatio (rank + 1) size =
      scaledTwoStepInvolutionRatio (size + 2 * (rank + 1)) *
        (((size + 2 * (rank + 1) : ℕ) : ℝ) /
          (((size + 2 * (rank + 1) : ℕ) : ℝ) - 2)) ^ rank *
        forwardFixedInvolutionRatio rank size := by
  have hindex : size + 2 * (rank + 1) - 2 = size + 2 * rank := by omega
  have hpositive : (0 : ℝ) < ((size + 2 * rank : ℕ) : ℝ) := by positivity
  have hcast :
      (((size + 2 * (rank + 1) : ℕ) : ℝ) - 2) =
        ((size + 2 * rank : ℕ) : ℝ) := by
    norm_num
    ring
  have hdenom : (((size + 2 * (rank + 1) : ℕ) : ℝ) - 2) ≠ 0 := by
    rw [hcast]
    exact ne_of_gt hpositive
  have hinvRank : (involutionNumber (size + 2 * rank) : ℝ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos (size + 2 * rank)).ne'
  have hinvSucc :
      (involutionNumber (size + 2 * (rank + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos (size + 2 * (rank + 1))).ne'
  unfold forwardFixedInvolutionRatio scaledTwoStepInvolutionRatio
  rw [hindex]
  rw [hcast]
  rw [div_pow]
  field_simp [pow_ne_zero rank hdenom]
  ring

theorem tendsto_forwardFixedInvolutionRatio_one (rank : ℕ) :
    Filter.Tendsto (forwardFixedInvolutionRatio rank)
      Filter.atTop (nhds 1) := by
  induction rank with
  | zero =>
      apply Filter.Tendsto.congr' _
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1))
      exact Filter.Eventually.of_forall fun size =>
        (forwardFixedInvolutionRatio_zero size).symm
  | succ rank ih =>
      let shift := 2 * (rank + 1)
      have htwo : Filter.Tendsto
          (fun size : ℕ => scaledTwoStepInvolutionRatio (size + shift))
          Filter.atTop (nhds 1) :=
        (Filter.tendsto_add_atTop_iff_nat shift).2
          tendsto_scaledTwoStepInvolutionRatio_one
      have hlinearBase : Filter.Tendsto
          (fun size : ℕ => (size : ℝ) / ((size : ℝ) - 2))
          Filter.atTop (nhds 1) := by
        simpa [sub_eq_add_neg] using
          (tendsto_natCast_div_add_atTop (-2 : ℝ))
      have hlinearShift : Filter.Tendsto
          (fun size : ℕ =>
            ((size + shift : ℕ) : ℝ) /
              (((size + shift : ℕ) : ℝ) - 2))
          Filter.atTop (nhds 1) :=
        (Filter.tendsto_add_atTop_iff_nat shift).2 hlinearBase
      have hpower : Filter.Tendsto
          (fun size : ℕ =>
            (((size + shift : ℕ) : ℝ) /
              (((size + shift : ℕ) : ℝ) - 2)) ^ rank)
          Filter.atTop (nhds 1) := by
        simpa using hlinearShift.pow rank
      have hproduct := htwo.mul (hpower.mul ih)
      have hproduct' : Filter.Tendsto
          (fun size : ℕ =>
            scaledTwoStepInvolutionRatio (size + shift) *
              ((((size + shift : ℕ) : ℝ) /
                (((size + shift : ℕ) : ℝ) - 2)) ^ rank *
                forwardFixedInvolutionRatio rank size))
          Filter.atTop (nhds 1) := by
        simpa using hproduct
      apply Filter.Tendsto.congr' _ hproduct'
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with size hsize
      simpa [shift, mul_assoc] using
        (forwardFixedInvolutionRatio_succ rank size hsize).symm

noncomputable def scaledFixedInvolutionRatio (rank size : ℕ) : ℝ :=
  (size : ℝ) ^ rank * involutionNumber (size - 2 * rank) /
    involutionNumber size

theorem scaledFixedInvolutionRatio_shift (rank size : ℕ) :
    scaledFixedInvolutionRatio rank (size + 2 * rank) =
      forwardFixedInvolutionRatio rank size := by
  unfold scaledFixedInvolutionRatio forwardFixedInvolutionRatio
  have hsub : size + 2 * rank - 2 * rank = size := by omega
  rw [hsub]

theorem tendsto_scaledFixedInvolutionRatio_one (rank : ℕ) :
    Filter.Tendsto (scaledFixedInvolutionRatio rank)
      Filter.atTop (nhds 1) := by
  apply (Filter.tendsto_add_atTop_iff_nat (2 * rank)).1
  have hforward := tendsto_forwardFixedInvolutionRatio_one rank
  apply Filter.Tendsto.congr' _ hforward
  exact Filter.Eventually.of_forall fun size =>
    (scaledFixedInvolutionRatio_shift rank size).symm

end FibonacciRibbonKernel
