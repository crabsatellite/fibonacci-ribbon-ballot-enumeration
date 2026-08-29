import FibonacciRibbonKernel.HeightFourBessel

namespace FibonacciRibbonKernel

/-- The literal Catalan product occurring in the manuscript's four-letter case. -/
noncomputable def heightFourCatalanCount (index : ℕ) : ℕ :=
  if Even index then
    catalan (index / 2) * catalan (index / 2 + 1)
  else
    catalan ((index + 1) / 2) ^ 2

@[simp] theorem heightFourCatalanCount_two_mul (rank : ℕ) :
    heightFourCatalanCount (2 * rank) =
      catalan rank * catalan (rank + 1) := by
  have heven : Even (2 * rank) := ⟨rank, by omega⟩
  rw [heightFourCatalanCount, if_pos heven]
  congr 2 <;> omega

@[simp] theorem heightFourCatalanCount_two_mul_add_one (rank : ℕ) :
    heightFourCatalanCount (2 * rank + 1) = catalan (rank + 1) ^ 2 := by
  rw [heightFourCatalanCount,
    if_neg (Nat.not_even_two_mul_add_one rank)]
  congr 2
  omega

/-- The exact first-order Catalan ratio, stated over `ℚ` so that it can be
consumed directly by the factorial differential recurrence. -/
theorem catalan_successor_ratio (rank : ℕ) :
    (rank + 2 : ℚ) * (catalan (rank + 1) : ℚ) =
      2 * (2 * rank + 1 : ℚ) * (catalan rank : ℚ) := by
  have hcentral := Nat.succ_mul_centralBinom_succ rank
  have hcurrent := succ_mul_catalan_eq_centralBinom rank
  have hnext := succ_mul_catalan_eq_centralBinom (rank + 1)
  have hcentralQ :
      (rank + 1 : ℚ) * (Nat.centralBinom (rank + 1) : ℚ) =
        2 * (2 * rank + 1 : ℚ) * (Nat.centralBinom rank : ℚ) := by
    exact_mod_cast hcentral
  have hcurrentQ :
      (rank + 1 : ℚ) * (catalan rank : ℚ) =
        (Nat.centralBinom rank : ℚ) := by
    exact_mod_cast hcurrent
  have hnextQ :
      (rank + 2 : ℚ) * (catalan (rank + 1) : ℚ) =
        (Nat.centralBinom (rank + 1) : ℚ) := by
    norm_num [Nat.add_assoc] at hnext ⊢
    exact_mod_cast hnext
  have hproduct :
      (rank + 1 : ℚ) *
          ((rank + 2 : ℚ) * (catalan (rank + 1) : ℚ) -
            2 * (2 * rank + 1 : ℚ) * (catalan rank : ℚ)) = 0 := by
    linear_combination
      (rank + 1 : ℚ) * hnextQ + hcentralQ -
        2 * (2 * rank + 1 : ℚ) * hcurrentQ
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left (by positivity))

theorem heightFourCatalanCount_even_recurrence
    (rank : ℕ) (hrank : 1 ≤ rank) :
    (2 * rank + 3 : ℚ) * (2 * rank + 4 : ℚ) *
          heightFourCatalanCount (2 * rank) -
        (8 * (2 * rank) + 12 : ℚ) *
          heightFourCatalanCount (2 * rank - 1) -
        16 * (2 * rank : ℚ) * (2 * rank - 1 : ℚ) *
          heightFourCatalanCount (2 * rank - 2) = 0 := by
  have hindexOne : 2 * rank - 1 = 2 * (rank - 1) + 1 := by omega
  have hindexTwo : 2 * rank - 2 = 2 * (rank - 1) := by omega
  rw [hindexOne, hindexTwo, heightFourCatalanCount_two_mul,
    heightFourCatalanCount_two_mul_add_one,
    heightFourCatalanCount_two_mul]
  have hnext := catalan_successor_ratio rank
  have hprevious := catalan_successor_ratio (rank - 1)
  rw [Nat.sub_add_cancel hrank] at hprevious
  rw [Nat.sub_add_cancel hrank]
  norm_num [Nat.cast_sub hrank] at hprevious
  push_cast at hnext hprevious ⊢
  linear_combination
    2 * (2 * (rank : ℚ) + 3) * (catalan rank : ℚ) * hnext +
      16 * (rank : ℚ) * (catalan rank : ℚ) * hprevious

theorem heightFourCatalanCount_odd_recurrence
    (rank : ℕ) (hrank : 1 ≤ rank) :
    (2 * rank + 4 : ℚ) * (2 * rank + 5 : ℚ) *
          heightFourCatalanCount (2 * rank + 1) -
        (8 * (2 * rank + 1) + 12 : ℚ) *
          heightFourCatalanCount (2 * rank + 1 - 1) -
        16 * (2 * rank + 1 : ℚ) * (2 * rank + 1 - 1 : ℚ) *
          heightFourCatalanCount (2 * rank + 1 - 2) = 0 := by
  have hindexOne : 2 * rank + 1 - 1 = 2 * rank := by omega
  have hindexTwo : 2 * rank + 1 - 2 = 2 * (rank - 1) + 1 := by omega
  rw [hindexOne, hindexTwo, heightFourCatalanCount_two_mul_add_one,
    heightFourCatalanCount_two_mul,
    heightFourCatalanCount_two_mul_add_one]
  have hnext := catalan_successor_ratio rank
  rw [Nat.sub_add_cancel hrank]
  push_cast at hnext ⊢
  linear_combination
    (2 * (2 * (rank : ℚ) + 5) * (catalan (rank + 1) : ℚ) +
      16 * (rank : ℚ) * (catalan rank : ℚ)) * hnext

theorem heightFourCatalanCount_recurrence
    (index : ℕ) (hindex : 2 ≤ index) :
    (index + 3 : ℚ) * (index + 4 : ℚ) * heightFourCatalanCount index -
        (8 * index + 12 : ℚ) * heightFourCatalanCount (index - 1) -
        16 * (index : ℚ) * (index - 1 : ℚ) *
          heightFourCatalanCount (index - 2) = 0 := by
  obtain ⟨rank, rfl | rfl⟩ := Nat.even_or_odd' index
  · push_cast
    exact heightFourCatalanCount_even_recurrence rank (by omega)
  · have hrec := heightFourCatalanCount_odd_recurrence rank (by omega)
    have hsub : 2 * rank + 1 - 2 = 2 * rank - 1 := by omega
    rw [Nat.add_sub_cancel, hsub] at hrec
    push_cast at hrec ⊢
    convert hrec using 1
    all_goals ring

theorem heightFourTableauCount_initial :
    heightFourTableauCount 0 = 1 ∧ heightFourTableauCount 1 = 1 := by
  unfold heightFourTableauCount
  constructor
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 4 0 (by omega),
      involutionNumber_zero]
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 4 1 (by omega),
      involutionNumber_one]

theorem heightFourCatalanCount_initial :
    heightFourCatalanCount 0 = 1 ∧ heightFourCatalanCount 1 = 1 := by
  simp [heightFourCatalanCount]

/-- Kernel proof of the classical bounded-height Catalan product formula. -/
theorem heightFourTableauCount_eq_catalan (index : ℕ) :
    heightFourTableauCount index = heightFourCatalanCount index := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
      by_cases hzero : index = 0
      · subst index
        exact heightFourTableauCount_initial.1.trans
          heightFourCatalanCount_initial.1.symm
      by_cases hone : index = 1
      · subst index
        exact heightFourTableauCount_initial.2.trans
          heightFourCatalanCount_initial.2.symm
      have hindex : 2 ≤ index := by omega
      have hactual := heightFourTableauCount_recurrence index hindex
      have hcatalan := heightFourCatalanCount_recurrence index hindex
      rw [ih (index - 1) (by omega), ih (index - 2) (by omega)] at hactual
      have hproduct :
          ((index + 3 : ℚ) * (index + 4 : ℚ)) *
              ((heightFourTableauCount index : ℚ) -
                (heightFourCatalanCount index : ℚ)) = 0 := by
        linear_combination hactual - hcatalan
      have hcast : (heightFourTableauCount index : ℚ) =
          (heightFourCatalanCount index : ℚ) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left (by positivity))
      exact_mod_cast hcast

theorem heightFourTableauCount_even_catalan (rank : ℕ) :
    heightFourTableauCount (2 * rank) =
      catalan rank * catalan (rank + 1) := by
  rw [heightFourTableauCount_eq_catalan,
    heightFourCatalanCount_two_mul]

theorem heightFourTableauCount_odd_catalan (rank : ℕ) :
    heightFourTableauCount (2 * rank + 1) = catalan (rank + 1) ^ 2 := by
  rw [heightFourTableauCount_eq_catalan,
    heightFourCatalanCount_two_mul_add_one]

theorem boundedPartition_three_sum_eq_heightFourCatalanCount (size : ℕ) :
    (∑ shape : BoundedPartition 3 size,
        (standardTableauNumber shape : ℤ)) =
      (heightFourCatalanCount size : ℤ) := by
  rw [← Nat.cast_sum,
    ← unrestrictedCount_eq_sum_standardTableauNumbers]
  change (heightFourTableauCount size : ℤ) =
    (heightFourCatalanCount size : ℤ)
  exact_mod_cast heightFourTableauCount_eq_catalan size

/-- Exact specialization of the main convolution to the four-letter Catalan
product sequence (`eq:n-four-sum`). -/
theorem ribbonCount_rankThree_catalan_sum (columns : ℕ) :
    (ribbonCount 3 columns : ℤ) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (heightFourCatalanCount (columns - 2 * edges) : ℤ) := by
  rw [ribbonCount_main_formula (rank := 3) (by omega)]
  apply Finset.sum_congr rfl
  intro edges hedges
  rw [boundedPartition_three_sum_eq_heightFourCatalanCount]

end FibonacciRibbonKernel
