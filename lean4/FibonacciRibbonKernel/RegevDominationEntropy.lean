import FibonacciRibbonKernel.RegevLocalLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace FibonacciRibbonKernel

open Filter Asymptotics

theorem entropyRemainder_lower_of_nonneg
    {value : ℝ} (hvalue : 0 ≤ value) :
    value ^ 2 / (value + 2) ≤ entropyRemainder value := by
  have hlog := Real.le_log_one_add_of_nonneg hvalue
  have hone : 0 ≤ 1 + value := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hone
  unfold entropyRemainder
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  have hdenominator : 0 < value + 2 := by linarith
  apply (div_le_iff₀ hdenominator).2
  field_simp at hmul
  nlinarith

noncomputable def negativeEntropyGap (value : ℝ) : ℝ :=
  entropyRemainder value - value ^ 2 / 2

theorem hasDerivAt_negativeEntropyGap
    (value : ℝ) (hvalue : -1 < value) :
    HasDerivAt negativeEntropyGap
      (Real.log (1 + value) - value) value := by
  have hentropy := hasDerivAt_entropyRemainder value (by linarith)
  have hsquare : HasDerivAt (fun current : ℝ => current ^ 2 / 2)
      value value := by
    convert! (hasDerivAt_pow 2 value).div_const 2 using 1
    ring
  unfold negativeEntropyGap
  convert! hentropy.sub hsquare using 1

theorem entropyRemainder_lower_of_mem_neg_one_zero
    {value : ℝ} (hlower : -1 ≤ value) (hupper : value ≤ 0) :
    value ^ 2 / 2 ≤ entropyRemainder value := by
  by_cases hendpoint : value = -1
  · subst value
    norm_num [entropyRemainder]
  · have hlowerStrict : -1 < value := lt_of_le_of_ne hlower
      (Ne.symm hendpoint)
    have hcontinuous : ContinuousOn negativeEntropyGap
        (Set.Icc value 0) := by
      intro current hcurrent
      exact (hasDerivAt_negativeEntropyGap current
        (lt_of_lt_of_le hlowerStrict hcurrent.1)).continuousAt.continuousWithinAt
    have hdifferentiable : DifferentiableOn ℝ negativeEntropyGap
        (Set.Ioo value 0) := by
      intro current hcurrent
      exact (hasDerivAt_negativeEntropyGap current
        (hlowerStrict.trans hcurrent.1)).differentiableAt.differentiableWithinAt
    have hderivative : ∀ current ∈ Set.Ioo value 0,
        deriv negativeEntropyGap current ≤ 0 := by
      intro current hcurrent
      rw [(hasDerivAt_negativeEntropyGap current
        (hlowerStrict.trans hcurrent.1)).deriv]
      have hcurrentLower : -1 < current := hlowerStrict.trans hcurrent.1
      have hlog := Real.log_le_sub_one_of_pos
        (by linarith : 0 < 1 + current)
      linarith
    have hanti := antitoneOn_of_deriv_nonpos
      (convex_Icc value 0) hcontinuous
      (by simpa [interior_Icc] using hdifferentiable)
      (by simpa [interior_Icc] using hderivative)
    have hcompare := hanti (Set.left_mem_Icc.mpr hupper)
      (Set.right_mem_Icc.mpr hupper) hupper
    unfold negativeEntropyGap at hcompare
    unfold entropyRemainder at hcompare
    simp only [Pi.mul_apply, Pi.sub_apply, id_eq] at hcompare
    norm_num at hcompare
    exact hcompare

theorem entropyRemainder_global_lower
    {value : ℝ} (hlower : -1 ≤ value) :
    value ^ 2 / (2 * (|value| + 2)) ≤ entropyRemainder value := by
  by_cases hnonneg : 0 ≤ value
  · have hbase := entropyRemainder_lower_of_nonneg hnonneg
    rw [abs_of_nonneg hnonneg]
    have hdenominator : 0 < value + 2 := by linarith
    have hdenominatorTwo : 0 < 2 * (value + 2) := by positivity
    apply hbase.trans'
    apply (div_le_div_iff₀ hdenominatorTwo hdenominator).2
    nlinarith [sq_nonneg value]
  · have hnonpos : value ≤ 0 := le_of_not_ge hnonneg
    have hbase := entropyRemainder_lower_of_mem_neg_one_zero hlower hnonpos
    rw [abs_of_nonpos hnonpos]
    have hdenominator : 0 < 2 * (-value + 2) := by nlinarith
    apply hbase.trans'
    apply (div_le_div_iff₀ hdenominator (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [sq_nonneg value]

noncomputable def regevEntropyDenominator (rank : ℕ) : ℝ :=
  2 * (((rank + 1 : ℕ) : ℝ) * (staircaseWeight rank + 1 : ℕ) + 2)

theorem regevShiftedDeviation_lower
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    -1 ≤ regevShiftedDeviation shape row := by
  unfold regevShiftedDeviation
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hnonneg : 0 ≤
      (shape.toStrictShiftedTuple.values row : ℝ) /
        regevCenter rank size := by positivity
  linarith

theorem abs_regevShiftedDeviation_le
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    |regevShiftedDeviation shape row| ≤
      ((rank + 1 : ℕ) : ℝ) * (staircaseWeight rank + 1 : ℕ) := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hvalueNat := shape.toStrictShiftedTuple.value_le_sum row
  have hvalue : (shape.toStrictShiftedTuple.values row : ℝ) ≤
      (size + staircaseWeight rank : ℕ) := by exact_mod_cast hvalueNat
  have hlower := regevShiftedDeviation_lower shape hsize row
  have hupper : regevShiftedDeviation shape row ≤
      ((rank + 1 : ℕ) : ℝ) * (staircaseWeight rank + 1 : ℕ) := by
    unfold regevShiftedDeviation regevCenter
    have hsizeReal : (1 : ℝ) ≤ size := by exact_mod_cast hsize
    apply (sub_le_iff_le_add).2
    have hdimensionPos : (0 : ℝ) < rank + 1 := by positivity
    have hcenterPos' : (0 : ℝ) < (size : ℝ) / (rank + 1 : ℝ) := by positivity
    apply (div_le_iff₀ hcenterPos').2
    rw [show ((((rank + 1 : ℕ) : ℝ) *
          (staircaseWeight rank + 1 : ℕ) + 1) *
          ((size : ℝ) / (rank + 1 : ℝ))) =
        (size : ℝ) * (((rank + 1 : ℕ) : ℝ) *
          (staircaseWeight rank + 1 : ℕ) + 1) /
          (rank + 1 : ℝ) by ring]
    apply (le_div_iff₀ hdimensionPos).2
    push_cast at hvalue ⊢
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ rank by positivity)
      (show (0 : ℝ) ≤ staircaseWeight rank by positivity)]
  rw [abs_le]
  constructor
  · have hconstant : (1 : ℝ) ≤
        ((rank + 1 : ℕ) : ℝ) * (staircaseWeight rank + 1 : ℕ) := by
      have hd : (1 : ℝ) ≤ ((rank + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le rank)
      have hs : (1 : ℝ) ≤ ((staircaseWeight rank + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le (staircaseWeight rank))
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((rank + 1 : ℕ) : ℝ) *
            (staircaseWeight rank + 1 : ℕ) :=
          mul_le_mul hd hs (by norm_num)
            (le_trans (by norm_num) hd)
    linarith
  · exact hupper

theorem regev_entropy_uniform_quadratic_lower
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    regevShiftedDeviation shape row ^ 2 /
        regevEntropyDenominator rank ≤
      entropyRemainder (regevShiftedDeviation shape row) := by
  have hlower := entropyRemainder_global_lower
    (regevShiftedDeviation_lower shape hsize row)
  have habs := abs_regevShiftedDeviation_le shape hsize row
  unfold regevEntropyDenominator
  have hsmallDenominator : 0 <
      2 * (|regevShiftedDeviation shape row| + 2) := by positivity
  have hlargeDenominator : 0 <
      2 * (((rank + 1 : ℕ) : ℝ) *
        (staircaseWeight rank + 1 : ℕ) + 2) := by positivity
  apply hlower.trans'
  apply (div_le_div_iff₀ hlargeDenominator hsmallDenominator).2
  nlinarith [sq_nonneg (regevShiftedDeviation shape row)]

theorem regev_scaled_entropy_gaussian_lower
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    (regevCenteredRow shape row ^ 2 / 2 -
          (row.rev.val : ℝ) ^ 2 * (rank + 1 : ℕ)) /
        regevEntropyDenominator rank ≤
      regevCenter rank size *
        entropyRemainder (regevShiftedDeviation shape row) := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hdenominatorPos : 0 < regevEntropyDenominator rank := by
    unfold regevEntropyDenominator
    positivity
  have hbase := mul_le_mul_of_nonneg_left
    (regev_entropy_uniform_quadratic_lower shape hsize row)
    hcenterPos.le
  have hscaled :
      (regevCenter rank size * regevShiftedDeviation shape row ^ 2) /
          regevEntropyDenominator rank ≤
        regevCenter rank size *
          entropyRemainder (regevShiftedDeviation shape row) := by
    simpa only [div_eq_mul_inv, mul_assoc] using hbase
  rw [regevCenter_mul_deviation_sq shape hsize row] at hscaled
  apply hscaled.trans'
  apply (div_le_div_iff₀ hdenominatorPos hdenominatorPos).2
  have hsqrtSq : Real.sqrt (regevCenter rank size) ^ 2 =
      regevCenter rank size := Real.sq_sqrt hcenterPos.le
  have hcenterLower : 1 / ((rank + 1 : ℕ) : ℝ) ≤
      regevCenter rank size := by
    unfold regevCenter
    push_cast
    have hdimensionPos : (0 : ℝ) < (rank : ℝ) + 1 := by positivity
    apply (div_le_div_iff_of_pos_right hdimensionPos).2
    exact_mod_cast hsize
  have hinverseUpper : (regevCenter rank size)⁻¹ ≤
      ((rank + 1 : ℕ) : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hcenterPos]
    have hdimensionPos : (0 : ℝ) < ((rank + 1 : ℕ) : ℝ) := by positivity
    have hmul : (1 : ℝ) ≤ regevCenter rank size *
        ((rank + 1 : ℕ) : ℝ) :=
      (div_le_iff₀ hdimensionPos).mp hcenterLower
    simpa [mul_comm] using hmul
  have hcorrectionSq :
      ((row.rev.val : ℝ) / Real.sqrt (regevCenter rank size)) ^ 2 ≤
        (row.rev.val : ℝ) ^ 2 * ((rank + 1 : ℕ) : ℝ) := by
    rw [div_pow, hsqrtSq]
    change (row.rev.val : ℝ) ^ 2 * (regevCenter rank size)⁻¹ ≤ _
    exact mul_le_mul_of_nonneg_left hinverseUpper (sq_nonneg _)
  nlinarith [sq_nonneg (regevCenteredRow shape row +
    2 * ((row.rev.val : ℝ) / Real.sqrt (regevCenter rank size)))]

noncomputable def regevEntropyOffset (rank : ℕ) : ℝ :=
  ∑ row : Fin (rank + 1),
    (row.rev.val : ℝ) ^ 2 * ((rank + 1 : ℕ) : ℝ)

theorem regevShiftedEntropySum_gaussian_lower
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    ((∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 / 2) -
        regevEntropyOffset rank) /
          regevEntropyDenominator rank ≤
      regevShiftedEntropySum shape := by
  unfold regevShiftedEntropySum regevEntropyOffset
  rw [sub_div, Finset.sum_div, Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro row hrow
  simpa [sub_div] using
    regev_scaled_entropy_gaussian_lower shape hsize row

theorem exp_neg_regevShiftedEntropySum_upper
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    Real.exp (-regevShiftedEntropySum shape) ≤
      Real.exp (regevEntropyOffset rank /
          regevEntropyDenominator rank) *
        Real.exp (-(∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 /
            (2 * regevEntropyDenominator rank))) := by
  have hlower := regevShiftedEntropySum_gaussian_lower shape hsize
  have hneg : -regevShiftedEntropySum shape ≤
      -(((∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 / 2) -
        regevEntropyOffset rank) /
          regevEntropyDenominator rank) := neg_le_neg hlower
  have hexp := Real.exp_le_exp.mpr hneg
  apply hexp.trans_eq
  rw [← Real.exp_add]
  congr 1
  have hsum :
      (∑ row : Fin (rank + 1),
        regevCenteredRow shape row ^ 2 /
          (2 * regevEntropyDenominator rank)) =
        (∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 / 2) /
            regevEntropyDenominator rank := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro row hrow
    ring
  rw [hsum]
  ring

end FibonacciRibbonKernel
