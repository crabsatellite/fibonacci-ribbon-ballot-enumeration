import FibonacciRibbonKernel.PoissonMoments
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Sum

namespace FibonacciRibbonKernel

open scoped Classical

/-! Finite Bonferroni bounds for the probability of no adjacent cycle. -/

def bonferroniPolynomial (cutoff value : ℕ) : ℤ :=
  ∑ selected ∈ Finset.range (cutoff + 1),
    (-1 : ℤ) ^ selected * Nat.choose value selected

theorem bonferroniPolynomial_eq
    (cutoff value : ℕ) :
    bonferroniPolynomial cutoff value =
      if value = 0 then 1
      else (-1 : ℤ) ^ cutoff * Nat.choose (value - 1) cutoff := by
  cases value with
  | zero =>
      unfold bonferroniPolynomial
      rw [Finset.sum_eq_single 0]
      · simp
      · intro selected hselected hne
        cases selected with
        | zero => contradiction
        | succ selected => simp
      · simp
  | succ previous =>
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      simpa [bonferroniPolynomial] using
        (Int.alternating_sum_range_choose_eq_choose
          (n := previous) (m := cutoff))

theorem bonferroni_odd_le_zeroIndicator
    (order value : ℕ) :
    bonferroniPolynomial (2 * order + 1) value ≤
      if value = 0 then 1 else 0 := by
  rw [bonferroniPolynomial_eq]
  by_cases hvalue : value = 0
  · simp [hvalue]
  · rw [if_neg hvalue, if_neg hvalue]
    have hsign : (-1 : ℤ) ^ (2 * order + 1) = -1 := by
      rw [pow_add]
      simp [pow_mul]
    rw [hsign]
    exact neg_nonpos.mpr (Int.natCast_nonneg _)

theorem zeroIndicator_le_bonferroni_even
    (order value : ℕ) :
    (if value = 0 then 1 else 0 : ℤ) ≤
      bonferroniPolynomial (2 * order) value := by
  rw [bonferroniPolynomial_eq]
  by_cases hvalue : value = 0
  · simp [hvalue]
  · rw [if_neg hvalue, if_neg hvalue]
    have hsign : (-1 : ℤ) ^ (2 * order) = 1 := by
      simp [pow_mul]
    rw [hsign]
    positivity

noncomputable def adjacentCycleChooseMomentReal
    (size selected : ℕ) : ℝ :=
  (∑ permutation : ActualInvolutionOn (Fin size),
      (Nat.choose (actualAdjacentLocations size permutation).card selected : ℝ)) /
    involutionNumber size

theorem adjacentCycleChooseMomentReal_eq
    (size selected : ℕ) :
    adjacentCycleChooseMomentReal size selected =
      adjacentCycleFactorialMomentReal size selected / selected.factorial := by
  unfold adjacentCycleChooseMomentReal adjacentCycleFactorialMomentReal
  have hfactorial : (selected.factorial : ℝ) ≠ 0 := by positivity
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← Finset.mul_sum]
  field_simp

theorem tendsto_adjacentCycleChooseMomentReal
    (selected : ℕ) :
    Filter.Tendsto (fun size : ℕ => adjacentCycleChooseMomentReal size selected)
      Filter.atTop (nhds ((selected.factorial : ℝ)⁻¹)) := by
  have h := (tendsto_adjacentCycleFactorialMomentReal_one selected).div_const
    (selected.factorial : ℝ)
  have h' : Filter.Tendsto
      (fun size : ℕ => adjacentCycleFactorialMomentReal size selected /
        (selected.factorial : ℝ))
      Filter.atTop (nhds ((selected.factorial : ℝ)⁻¹)) := by
    simpa [one_div] using h
  apply Filter.Tendsto.congr' _ h'
  exact Filter.Eventually.of_forall fun size => by
    exact (adjacentCycleChooseMomentReal_eq size selected).symm
  
noncomputable def bonferroniMomentSum (size cutoff : ℕ) : ℝ :=
  ∑ selected ∈ Finset.range (cutoff + 1),
    (-1 : ℝ) ^ selected * adjacentCycleChooseMomentReal size selected

noncomputable def bonferroniLimitSum (cutoff : ℕ) : ℝ :=
  ∑ selected ∈ Finset.range (cutoff + 1),
    (-1 : ℝ) ^ selected / selected.factorial

theorem tendsto_bonferroniMomentSum (cutoff : ℕ) :
    Filter.Tendsto (fun size : ℕ => bonferroniMomentSum size cutoff)
      Filter.atTop (nhds (bonferroniLimitSum cutoff)) := by
  unfold bonferroniMomentSum bonferroniLimitSum
  apply tendsto_finsetSum
  intro selected hselected
  have h := (tendsto_adjacentCycleChooseMomentReal selected).const_mul
    ((-1 : ℝ) ^ selected)
  simpa [div_eq_mul_inv] using h

theorem bonferroniMomentSum_eq_average
    (size cutoff : ℕ) :
    bonferroniMomentSum size cutoff =
      (∑ permutation : ActualInvolutionOn (Fin size),
        (bonferroniPolynomial cutoff
          (actualAdjacentLocations size permutation).card : ℝ)) /
        involutionNumber size := by
  unfold bonferroniMomentSum adjacentCycleChooseMomentReal bonferroniPolynomial
  simp_rw [mul_div_assoc']
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro permutation hpermutation
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro selected hselected
  push_cast
  norm_num

noncomputable def zeroAdjacentCycleProbability (size : ℕ) : ℝ :=
  (stableActualInvolutionNumber size : ℝ) / involutionNumber size

theorem zeroAdjacentCycleProbability_eq_average (size : ℕ) :
    zeroAdjacentCycleProbability size =
      (∑ permutation : ActualInvolutionOn (Fin size),
        if (actualAdjacentLocations size permutation).card = 0 then (1 : ℝ) else 0) /
        involutionNumber size := by
  unfold zeroAdjacentCycleProbability stableActualInvolutionNumber
  have hsum := Finset.sum_boole
    (fun permutation : ActualInvolutionOn (Fin size) =>
      (actualAdjacentLocations size permutation).card = 0)
    (Finset.univ : Finset (ActualInvolutionOn (Fin size))) (R := ℝ)
  rw [show stableActualInvolutionFinset size =
      Finset.univ.filter (fun permutation : ActualInvolutionOn (Fin size) =>
        (actualAdjacentLocations size permutation).card = 0) by
    unfold stableActualInvolutionFinset
    ext permutation
    simp]
  rw [← hsum]

theorem bonferroni_lower_bound
    (size order : ℕ) :
    bonferroniMomentSum size (2 * order + 1) ≤
      zeroAdjacentCycleProbability size := by
  rw [bonferroniMomentSum_eq_average,
    zeroAdjacentCycleProbability_eq_average]
  have hdenom : (0 : ℝ) ≤ involutionNumber size := by positivity
  apply div_le_div_of_nonneg_right _ hdenom
  apply Finset.sum_le_sum
  intro permutation hpermutation
  exact_mod_cast bonferroni_odd_le_zeroIndicator order
    (actualAdjacentLocations size permutation).card

theorem bonferroni_upper_bound
    (size order : ℕ) :
    zeroAdjacentCycleProbability size ≤
      bonferroniMomentSum size (2 * order) := by
  rw [bonferroniMomentSum_eq_average,
    zeroAdjacentCycleProbability_eq_average]
  have hdenom : (0 : ℝ) ≤ involutionNumber size := by positivity
  apply div_le_div_of_nonneg_right _ hdenom
  apply Finset.sum_le_sum
  intro permutation hpermutation
  exact_mod_cast zeroIndicator_le_bonferroni_even order
    (actualAdjacentLocations size permutation).card

theorem tendsto_bonferroniLimitSum_exp_neg_one :
    Filter.Tendsto bonferroniLimitSum Filter.atTop
      (nhds (Real.exp (-1))) := by
  have hseries :=
    (NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)).tendsto_sum_nat
  have hshift := (Filter.tendsto_add_atTop_iff_nat 1).2 hseries
  change Filter.Tendsto
    (fun cutoff : ℕ => ∑ selected ∈ Finset.range (cutoff + 1),
      (-1 : ℝ) ^ selected / selected.factorial)
    Filter.atTop (nhds (Real.exp (-1)))
  simpa [Real.exp_eq_exp_ℝ] using hshift

/-- The exact no-adjacent-cycle probability tends to `e⁻¹`.  The proof is a
finite Bonferroni squeeze; it does not interchange a growing finite sum with a
limit. -/
theorem tendsto_zeroAdjacentCycleProbability_exp_neg_one :
    Filter.Tendsto zeroAdjacentCycleProbability Filter.atTop
      (nhds (Real.exp (-1))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨limitIndex, hlimitIndex⟩ :=
    (Metric.tendsto_atTop.mp tendsto_bonferroniLimitSum_exp_neg_one)
      (ε / 3) hthird
  let order := limitIndex
  have hlowerLimit :
      dist (bonferroniLimitSum (2 * order + 1)) (Real.exp (-1)) < ε / 3 :=
    hlimitIndex (2 * order + 1) (by omega)
  have hupperLimit :
      dist (bonferroniLimitSum (2 * order)) (Real.exp (-1)) < ε / 3 :=
    hlimitIndex (2 * order) (by omega)
  obtain ⟨lowerIndex, hlowerIndex⟩ :=
    (Metric.tendsto_atTop.mp
      (tendsto_bonferroniMomentSum (2 * order + 1)))
      (ε / 3) hthird
  obtain ⟨upperIndex, hupperIndex⟩ :=
    (Metric.tendsto_atTop.mp
      (tendsto_bonferroniMomentSum (2 * order)))
      (ε / 3) hthird
  refine ⟨max lowerIndex upperIndex, ?_⟩
  intro size hsize
  have hlowerApprox := hlowerIndex size (le_trans (le_max_left _ _) hsize)
  have hupperApprox := hupperIndex size (le_trans (le_max_right _ _) hsize)
  have hlowerBound := bonferroni_lower_bound size order
  have hupperBound := bonferroni_upper_bound size order
  rw [Real.dist_eq] at hlowerLimit hupperLimit hlowerApprox hupperApprox ⊢
  have hlowerLimitBounds := abs_lt.mp hlowerLimit
  have hupperLimitBounds := abs_lt.mp hupperLimit
  have hlowerApproxBounds := abs_lt.mp hlowerApprox
  have hupperApproxBounds := abs_lt.mp hupperApprox
  apply abs_lt.mpr
  constructor <;> linarith

theorem tendsto_zeroAdjacentCycleProbability_e_inv :
    Filter.Tendsto zeroAdjacentCycleProbability Filter.atTop
      (nhds ((Real.exp 1)⁻¹)) := by
  simpa [Real.exp_neg] using
    tendsto_zeroAdjacentCycleProbability_exp_neg_one

end FibonacciRibbonKernel
