import FibonacciRibbonKernel.PoissonZero

namespace FibonacciRibbonKernel

open scoped Classical

/-!
# Pointwise Poisson convergence

For a nonnegative integer-valued random variable, convergence of every finite
distribution function is the literal discrete form of convergence in
distribution.  We prove it here from shifted Bonferroni polynomials, rather
than declaring factorial-moment convergence to be distributional convergence.
-/

def pointBonferroniPolynomial
    (value cutoff count : ℕ) : ℤ :=
  ∑ extra ∈ Finset.range (cutoff + 1),
    (-1 : ℤ) ^ extra * Nat.choose (value + extra) value *
      Nat.choose count (value + extra)

theorem pointBonferroniPolynomial_eq_mul
    (value cutoff count : ℕ) (_hvalue : value ≤ count) :
    pointBonferroniPolynomial value cutoff count =
      Nat.choose count value * bonferroniPolynomial cutoff (count - value) := by
  unfold pointBonferroniPolynomial bonferroniPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro extra hextra
  have hchoose := Nat.choose_mul (n := count) (k := value + extra)
    (s := value) (by omega)
  have hsub : value + extra - value = extra := by omega
  rw [hsub] at hchoose
  have hchooseZ :
      (Nat.choose count (value + extra) : ℤ) *
          Nat.choose (value + extra) value =
        Nat.choose count value * Nat.choose (count - value) extra := by
    exact_mod_cast hchoose
  linear_combination ((-1 : ℤ) ^ extra) * hchooseZ

theorem pointBonferroniPolynomial_eq_zero_of_lt
    (value cutoff count : ℕ) (hcount : count < value) :
    pointBonferroniPolynomial value cutoff count = 0 := by
  unfold pointBonferroniPolynomial
  apply Finset.sum_eq_zero
  intro extra hextra
  rw [Nat.choose_eq_zero_of_lt (lt_of_lt_of_le hcount (Nat.le_add_right _ _))]
  simp

theorem pointBonferroni_odd_le_indicator
    (value order count : ℕ) :
    pointBonferroniPolynomial value (2 * order + 1) count ≤
      if count = value then 1 else 0 := by
  by_cases hcount : count < value
  · rw [pointBonferroniPolynomial_eq_zero_of_lt value _ count hcount]
    simp [Nat.ne_of_lt hcount]
  · have hvalue : value ≤ count := Nat.le_of_not_gt hcount
    rw [pointBonferroniPolynomial_eq_mul value _ count hvalue]
    have hbound := bonferroni_odd_le_zeroIndicator order (count - value)
    have hchoose : (0 : ℤ) ≤ Nat.choose count value := Int.natCast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hbound hchoose
    by_cases heq : count = value
    · subst count
      simpa using hmul
    · have hsub : count - value ≠ 0 :=
        (Nat.sub_pos_of_lt (lt_of_le_of_ne hvalue (Ne.symm heq))).ne'
      simp [heq, hsub] at hmul ⊢
      exact hmul

theorem indicator_le_pointBonferroni_even
    (value order count : ℕ) :
    (if count = value then 1 else 0 : ℤ) ≤
      pointBonferroniPolynomial value (2 * order) count := by
  by_cases hcount : count < value
  · rw [pointBonferroniPolynomial_eq_zero_of_lt value _ count hcount]
    simp [Nat.ne_of_lt hcount]
  · have hvalue : value ≤ count := Nat.le_of_not_gt hcount
    rw [pointBonferroniPolynomial_eq_mul value _ count hvalue]
    have hbound := zeroIndicator_le_bonferroni_even order (count - value)
    have hchoose : (0 : ℤ) ≤ Nat.choose count value := Int.natCast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hbound hchoose
    by_cases heq : count = value
    · subst count
      simpa using hmul
    · have hsub : count - value ≠ 0 :=
        (Nat.sub_pos_of_lt (lt_of_le_of_ne hvalue (Ne.symm heq))).ne'
      simp [heq, hsub] at hmul ⊢
      exact hmul

noncomputable def pointBonferroniMomentSum
    (size value cutoff : ℕ) : ℝ :=
  ∑ extra ∈ Finset.range (cutoff + 1),
    (-1 : ℝ) ^ extra * Nat.choose (value + extra) value *
      adjacentCycleChooseMomentReal size (value + extra)

noncomputable def pointBonferroniLimitSum
    (value cutoff : ℕ) : ℝ :=
  ∑ extra ∈ Finset.range (cutoff + 1),
    (-1 : ℝ) ^ extra /
      ((value.factorial : ℝ) * extra.factorial)

theorem choose_add_mul_inv_factorial
    (value extra : ℕ) :
    (Nat.choose (value + extra) value : ℝ) *
        ((value + extra).factorial : ℝ)⁻¹ =
      ((value.factorial : ℝ) * extra.factorial)⁻¹ := by
  have hfactorial := Nat.choose_mul_factorial_mul_factorial
    (n := value + extra) (k := value) (Nat.le_add_right value extra)
  have hsub : value + extra - value = extra := by omega
  rw [hsub] at hfactorial
  have hchoose : (Nat.choose (value + extra) value : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right value extra)).ne'
  have hvalue : (value.factorial : ℝ) ≠ 0 := by positivity
  have hextra : (extra.factorial : ℝ) ≠ 0 := by positivity
  have hadd : ((value + extra).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  exact_mod_cast hfactorial

theorem tendsto_pointBonferroniMomentSum
    (value cutoff : ℕ) :
    Filter.Tendsto (fun size : ℕ =>
      pointBonferroniMomentSum size value cutoff)
      Filter.atTop (nhds (pointBonferroniLimitSum value cutoff)) := by
  unfold pointBonferroniMomentSum pointBonferroniLimitSum
  apply tendsto_finsetSum
  intro extra hextra
  have h := (tendsto_adjacentCycleChooseMomentReal (value + extra)).const_mul
    (((-1 : ℝ) ^ extra) * Nat.choose (value + extra) value)
  have hlimit := choose_add_mul_inv_factorial value extra
  convert h using 1
  congr 1
  rw [div_eq_mul_inv, ← hlimit]
  ring

theorem pointBonferroniMomentSum_eq_average
    (size value cutoff : ℕ) :
    pointBonferroniMomentSum size value cutoff =
      (∑ permutation : ActualInvolutionOn (Fin size),
        (pointBonferroniPolynomial value cutoff
          (actualAdjacentLocations size permutation).card : ℝ)) /
        involutionNumber size := by
  unfold pointBonferroniMomentSum adjacentCycleChooseMomentReal
  unfold pointBonferroniPolynomial
  simp_rw [mul_div_assoc']
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro permutation hpermutation
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro extra hextra
  push_cast
  norm_num

noncomputable def adjacentCyclePointProbability
    (size value : ℕ) : ℝ :=
  ((Finset.univ.filter fun permutation : ActualInvolutionOn (Fin size) =>
      (actualAdjacentLocations size permutation).card = value).card : ℝ) /
    involutionNumber size

theorem adjacentCyclePointProbability_eq_average
    (size value : ℕ) :
    adjacentCyclePointProbability size value =
      (∑ permutation : ActualInvolutionOn (Fin size),
        if (actualAdjacentLocations size permutation).card = value then (1 : ℝ) else 0) /
        involutionNumber size := by
  unfold adjacentCyclePointProbability
  have hsum := Finset.sum_boole
    (fun permutation : ActualInvolutionOn (Fin size) =>
      (actualAdjacentLocations size permutation).card = value)
    (Finset.univ : Finset (ActualInvolutionOn (Fin size))) (R := ℝ)
  rw [← hsum]

theorem pointBonferroni_lower_bound
    (size value order : ℕ) :
    pointBonferroniMomentSum size value (2 * order + 1) ≤
      adjacentCyclePointProbability size value := by
  rw [pointBonferroniMomentSum_eq_average,
    adjacentCyclePointProbability_eq_average]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro permutation hpermutation
  exact_mod_cast pointBonferroni_odd_le_indicator value order
    (actualAdjacentLocations size permutation).card

theorem pointBonferroni_upper_bound
    (size value order : ℕ) :
    adjacentCyclePointProbability size value ≤
      pointBonferroniMomentSum size value (2 * order) := by
  rw [pointBonferroniMomentSum_eq_average,
    adjacentCyclePointProbability_eq_average]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro permutation hpermutation
  exact_mod_cast indicator_le_pointBonferroni_even value order
    (actualAdjacentLocations size permutation).card

theorem tendsto_pointBonferroniLimitSum
    (value : ℕ) :
    Filter.Tendsto (pointBonferroniLimitSum value) Filter.atTop
      (nhds (Real.exp (-1) / value.factorial)) := by
  have hseries :=
    (NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)).tendsto_sum_nat
  have hscaled := hseries.const_mul ((value.factorial : ℝ)⁻¹)
  have hshift := (Filter.tendsto_add_atTop_iff_nat 1).2 hscaled
  change Filter.Tendsto
    (fun cutoff : ℕ => ∑ extra ∈ Finset.range (cutoff + 1),
      (-1 : ℝ) ^ extra /
        ((value.factorial : ℝ) * extra.factorial))
    Filter.atTop (nhds (Real.exp (-1) / value.factorial))
  convert hshift using 1 <;> simp [Real.exp_eq_exp_ℝ, div_eq_mul_inv]
  · funext cutoff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro extra hextra
    field_simp
  · ring

theorem tendsto_adjacentCyclePointProbability
    (value : ℕ) :
    Filter.Tendsto (fun size : ℕ =>
      adjacentCyclePointProbability size value)
      Filter.atTop (nhds (Real.exp (-1) / value.factorial)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨limitIndex, hlimitIndex⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_pointBonferroniLimitSum value))
      (ε / 3) hthird
  let order := limitIndex
  have hlowerLimit := hlimitIndex (2 * order + 1) (by omega)
  have hupperLimit := hlimitIndex (2 * order) (by omega)
  obtain ⟨lowerIndex, hlowerIndex⟩ :=
    (Metric.tendsto_atTop.mp
      (tendsto_pointBonferroniMomentSum value (2 * order + 1)))
      (ε / 3) hthird
  obtain ⟨upperIndex, hupperIndex⟩ :=
    (Metric.tendsto_atTop.mp
      (tendsto_pointBonferroniMomentSum value (2 * order)))
      (ε / 3) hthird
  refine ⟨max lowerIndex upperIndex, ?_⟩
  intro size hsize
  have hlowerApprox := hlowerIndex size (le_trans (le_max_left _ _) hsize)
  have hupperApprox := hupperIndex size (le_trans (le_max_right _ _) hsize)
  have hlowerBound := pointBonferroni_lower_bound size value order
  have hupperBound := pointBonferroni_upper_bound size value order
  rw [Real.dist_eq] at hlowerLimit hupperLimit hlowerApprox hupperApprox ⊢
  have hlowerLimitBounds := abs_lt.mp hlowerLimit
  have hupperLimitBounds := abs_lt.mp hupperLimit
  have hlowerApproxBounds := abs_lt.mp hlowerApprox
  have hupperApproxBounds := abs_lt.mp hupperApprox
  apply abs_lt.mpr
  constructor <;> linarith

noncomputable def adjacentCycleCDF (size maximum : ℕ) : ℝ :=
  ∑ value ∈ Finset.range (maximum + 1),
    adjacentCyclePointProbability size value

noncomputable def poissonOneCDF (maximum : ℕ) : ℝ :=
  ∑ value ∈ Finset.range (maximum + 1),
    Real.exp (-1) / value.factorial

theorem tendsto_adjacentCycleCDF_poissonOne (maximum : ℕ) :
    Filter.Tendsto (fun size : ℕ => adjacentCycleCDF size maximum)
      Filter.atTop (nhds (poissonOneCDF maximum)) := by
  unfold adjacentCycleCDF poissonOneCDF
  apply tendsto_finsetSum
  intro value hvalue
  exact tendsto_adjacentCyclePointProbability value

/-- Exact discrete-CDF formulation of `X_k →ᵈ Poisson(1)`. -/
def PoissonOneDistributionalLimit : Prop :=
  ∀ maximum : ℕ,
    Filter.Tendsto (fun size : ℕ => adjacentCycleCDF size maximum)
      Filter.atTop (nhds (poissonOneCDF maximum))

theorem poissonOneDistributionalLimit : PoissonOneDistributionalLimit :=
  tendsto_adjacentCycleCDF_poissonOne

end FibonacciRibbonKernel
