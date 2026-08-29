import FibonacciRibbonKernel.InvolutionAsymptotics
import FibonacciRibbonKernel.StableInvolutions
import Mathlib.Analysis.SpecialFunctions.Choose

namespace FibonacciRibbonKernel

/-!
# Asymptotic factorial moments of adjacent cycles

The finite double count in `StableInvolutions` is combined here with the
kernel proof of every fixed involution ratio.  No asymptotic formula for
involution numbers is imported.
-/

noncomputable def matchingCoefficientRatio (selected size : ℕ) : ℝ :=
  (selected.factorial * Nat.choose (size - selected) selected : ℝ) /
    (size : ℝ) ^ selected

theorem matchingCoefficientRatio_shift (selected size : ℕ) :
    matchingCoefficientRatio selected (size + 2 * selected) =
      (selected.factorial * Nat.choose (size + selected) selected : ℝ) /
        ((size + 2 * selected : ℕ) : ℝ) ^ selected := by
  unfold matchingCoefficientRatio
  have hsub : size + 2 * selected - selected = size + selected := by omega
  rw [hsub]

theorem tendsto_matchingCoefficientRatio_one (selected : ℕ) :
    Filter.Tendsto (matchingCoefficientRatio selected)
      Filter.atTop (nhds 1) := by
  have hdenom : ∀ᶠ size : ℕ in Filter.atTop,
      (size : ℝ) ^ selected / selected.factorial ≠ 0 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with size hsize
    positivity
  have hchooseBase : Filter.Tendsto
      (fun size : ℕ =>
        (Nat.choose size selected : ℝ) /
          ((size : ℝ) ^ selected / selected.factorial))
      Filter.atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hdenom).1
      (isEquivalent_choose selected)
  have hchooseShift : Filter.Tendsto
      (fun size : ℕ =>
        (Nat.choose (size + selected) selected : ℝ) /
          (((size + selected : ℕ) : ℝ) ^ selected / selected.factorial))
      Filter.atTop (nhds 1) :=
    (Filter.tendsto_add_atTop_iff_nat selected).2 hchooseBase
  have hlinearBase : Filter.Tendsto
      (fun size : ℕ => (size : ℝ) / ((size : ℝ) + selected))
      Filter.atTop (nhds 1) := by
    simpa using tendsto_natCast_div_add_atTop (selected : ℝ)
  have hlinearShift : Filter.Tendsto
      (fun size : ℕ =>
        ((size + selected : ℕ) : ℝ) /
          (((size + selected : ℕ) : ℝ) + selected))
      Filter.atTop (nhds 1) :=
    (Filter.tendsto_add_atTop_iff_nat selected).2 hlinearBase
  have hpower : Filter.Tendsto
      (fun size : ℕ =>
        (((size + selected : ℕ) : ℝ) /
          (((size + selected : ℕ) : ℝ) + selected)) ^ selected)
      Filter.atTop (nhds 1) := by
    simpa using hlinearShift.pow selected
  have hproduct := hchooseShift.mul hpower
  have hproduct' : Filter.Tendsto
      (fun size : ℕ =>
        ((Nat.choose (size + selected) selected : ℝ) /
          (((size + selected : ℕ) : ℝ) ^ selected / selected.factorial)) *
        ((((size + selected : ℕ) : ℝ) /
          (((size + selected : ℕ) : ℝ) + selected)) ^ selected))
      Filter.atTop (nhds 1) := by
    simpa using hproduct
  have hshifted : Filter.Tendsto
      (fun size : ℕ => matchingCoefficientRatio selected (size + 2 * selected))
      Filter.atTop (nhds 1) := by
    apply Filter.Tendsto.congr' _ hproduct'
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with size hsize
    rw [matchingCoefficientRatio_shift]
    have hfactorial : (selected.factorial : ℝ) ≠ 0 := by positivity
    have hleft : ((size + selected : ℕ) : ℝ) ≠ 0 := by positivity
    have hright : ((size + 2 * selected : ℕ) : ℝ) ≠ 0 := by positivity
    have hsum :
        (((size + selected : ℕ) : ℝ) + selected) =
          ((size + 2 * selected : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hsum]
    rw [div_pow]
    field_simp [pow_ne_zero selected hleft, pow_ne_zero selected hright]
  exact (Filter.tendsto_add_atTop_iff_nat (2 * selected)).1 hshifted

noncomputable def adjacentCycleFactorialMomentReal
    (size selected : ℕ) : ℝ :=
  (∑ permutation : ActualInvolutionOn (Fin size),
      ((actualAdjacentLocations size permutation).card.descFactorial selected : ℝ)) /
    involutionNumber size

theorem adjacentCycleFactorialMomentReal_formula
    (size selected : ℕ) :
    adjacentCycleFactorialMomentReal size selected =
      (selected.factorial * Nat.choose (size - selected) selected : ℝ) *
        involutionNumber (size - 2 * selected) / involutionNumber size := by
  unfold adjacentCycleFactorialMomentReal
  have hsum := sum_descFactorial_adjacentCycleCount size selected
  have hsumR :
      (∑ permutation : ActualInvolutionOn (Fin size),
          ((actualAdjacentLocations size permutation).card.descFactorial selected : ℝ)) =
        (selected.factorial * Nat.choose (size - selected) selected *
          involutionNumber (size - 2 * selected) : ℕ) := by
    exact_mod_cast hsum
  rw [hsumR]
  push_cast
  ring

theorem adjacentCycleFactorialMomentReal_factorization
    (size selected : ℕ) (hsize : 1 ≤ size) :
    adjacentCycleFactorialMomentReal size selected =
      matchingCoefficientRatio selected size *
        scaledFixedInvolutionRatio selected size := by
  rw [adjacentCycleFactorialMomentReal_formula]
  unfold matchingCoefficientRatio scaledFixedInvolutionRatio
  have hsizeR : (size : ℝ) ≠ 0 := by positivity
  have hinvolution : (involutionNumber size : ℝ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos size).ne'
  field_simp [pow_ne_zero selected hsizeR]

theorem tendsto_adjacentCycleFactorialMomentReal_one (selected : ℕ) :
    Filter.Tendsto (fun size : ℕ =>
      adjacentCycleFactorialMomentReal size selected)
      Filter.atTop (nhds 1) := by
  have hproduct := (tendsto_matchingCoefficientRatio_one selected).mul
    (tendsto_scaledFixedInvolutionRatio_one selected)
  have hproduct' : Filter.Tendsto
      (fun size : ℕ => matchingCoefficientRatio selected size *
        scaledFixedInvolutionRatio selected size)
      Filter.atTop (nhds 1) := by
    simpa using hproduct
  apply Filter.Tendsto.congr' _ hproduct'
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with size hsize
  exact (adjacentCycleFactorialMomentReal_factorization size selected hsize).symm

end FibonacciRibbonKernel
