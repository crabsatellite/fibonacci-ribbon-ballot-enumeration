import FibonacciRibbonKernel.RegevDominationEntropy
import FibonacciRibbonKernel.RegevLocalLimit
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace FibonacciRibbonKernel

open Filter Asymptotics
open scoped Classical

theorem sqrt_succ_mul_stirling_le_factorial (value : ℕ) :
    Real.sqrt (value + 1 : ℕ) *
        (((value : ℝ) / Real.exp 1) ^ value) ≤
      (value.factorial : ℝ) := by
  cases value with
  | zero => norm_num
  | succ value =>
      have hsquare : ((value + 1 : ℕ) : ℝ) + 1 ≤
          2 * (value + 1 : ℕ) * Real.pi := by
        have hpi := Real.pi_gt_three
        push_cast
        nlinarith
      have hsqrt : Real.sqrt ((value + 1 : ℕ) + 1) ≤
          Real.sqrt (2 * (value + 1 : ℕ) * Real.pi) :=
        Real.sqrt_le_sqrt hsquare
      have hpower : 0 ≤
          (((value + 1 : ℕ) : ℝ) / Real.exp 1) ^ (value + 1) := by
        positivity
      have hstirling :
          Real.sqrt (2 * (value + 1 : ℕ) * Real.pi) *
              (((value + 1 : ℕ) : ℝ) / Real.exp 1) ^ (value + 1) ≤
            ((value + 1).factorial : ℝ) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          (Stirling.le_factorial_stirling (value + 1))
      simpa only [Nat.cast_add, Nat.cast_one] using
        (mul_le_mul_of_nonneg_right hsqrt hpower).trans hstirling

noncomputable def shiftedAdjustedSqrtProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1),
    Real.sqrt (shape.toStrictShiftedTuple.values row + 1 : ℕ)

theorem shiftedAdjustedSqrt_mul_power_le_factorialProduct
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (index : ℕ) :
    shiftedAdjustedSqrtProduct (shapes index) *
        shiftedStirlingPowerProduct (shapes index) ≤
      shiftedFactorialProduct sizes shapes index := by
  unfold shiftedAdjustedSqrtProduct shiftedStirlingPowerProduct
  unfold shiftedFactorialProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro row hrow
    positivity
  · intro row hrow
    exact sqrt_succ_mul_stirling_le_factorial _

noncomputable def regevAdjustedSqrtRatioProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1),
    Real.sqrt (((shape.toStrictShiftedTuple.values row + 1 : ℕ) : ℝ) /
      regevCenter rank size)

theorem shiftedAdjustedSqrtProduct_factor
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    shiftedAdjustedSqrtProduct shape =
      Real.sqrt (regevCenter rank size) ^ (rank + 1) *
        regevAdjustedSqrtRatioProduct shape := by
  unfold shiftedAdjustedSqrtProduct regevAdjustedSqrtRatioProduct
  calc
    (∏ row : Fin (rank + 1),
      Real.sqrt (shape.toStrictShiftedTuple.values row + 1 : ℕ)) =
      ∏ row : Fin (rank + 1),
        (Real.sqrt (regevCenter rank size) *
          Real.sqrt (((shape.toStrictShiftedTuple.values row + 1 : ℕ) : ℝ) /
            regevCenter rank size)) := by
      apply Finset.prod_congr rfl
      intro row hrow
      have hcenterNonneg : 0 ≤ regevCenter rank size := by
        unfold regevCenter
        positivity
      rw [← Real.sqrt_mul hcenterNonneg]
      congr 1
      have hcenterNe : regevCenter rank size ≠ 0 := by
        unfold regevCenter
        positivity
      field_simp
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      simp

theorem shiftedValueReal_eq_centered
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    (shape.toStrictShiftedTuple.values row : ℝ) =
      regevCenter rank size +
        regevCenteredRow shape row * Real.sqrt (regevCenter rank size) +
        row.rev.val := by
  have hreconstruct := regevCenteredRow_reconstruct shape hsize row
  rw [BoundedPartition.toStrictShiftedTuple_values]
  unfold regevCenter at *
  push_cast
  linarith

theorem center_le_polynomial_mul_shifted_succ
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    regevCenter rank size ≤
      4 * (1 + |regevCenteredRow shape row| + (row.rev.val : ℝ)) ^ 2 *
        ((shape.toStrictShiftedTuple.values row : ℝ) + 1) := by
  let center := regevCenter rank size
  let root := Real.sqrt center
  let centered := regevCenteredRow shape row
  let offset := (row.rev.val : ℝ)
  let envelope := 1 + |centered| + offset
  have hcenterPos : 0 < center := by
    dsimp only [center]
    unfold regevCenter
    positivity
  have hrootNonneg : 0 ≤ root := Real.sqrt_nonneg _
  have hrootSq : root ^ 2 = center := Real.sq_sqrt hcenterPos.le
  have hoffsetNonneg : 0 ≤ offset := by positivity
  have henvelopeOne : 1 ≤ envelope := by
    dsimp only [envelope]
    nlinarith [abs_nonneg centered, hoffsetNonneg]
  have hvalue : (shape.toStrictShiftedTuple.values row : ℝ) =
      center + centered * root + offset := by
    exact shiftedValueReal_eq_centered shape hsize row
  change center ≤ 4 * envelope ^ 2 *
    ((shape.toStrictShiftedTuple.values row : ℝ) + 1)
  by_cases hsmall : root ≤ 2 * envelope
  · have hsucc : (1 : ℝ) ≤
        (shape.toStrictShiftedTuple.values row : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ
        (Nat.zero_le (shape.toStrictShiftedTuple.values row))
    rw [← hrootSq]
    nlinarith [sq_nonneg (2 * envelope - root)]
  · have hlarge : 2 * envelope < root := lt_of_not_ge hsmall
    have hcenteredAbs : |centered| < root / 2 := by
      dsimp only [envelope] at hlarge
      nlinarith
    have hcenteredLower : -root / 2 < centered := by
      have := neg_abs_le centered
      nlinarith
    have hvalueLower : root ^ 2 / 2 ≤
        (shape.toStrictShiftedTuple.values row : ℝ) + 1 := by
      rw [hvalue, hrootSq]
      nlinarith
    rw [← hrootSq]
    have hfirst : root ^ 2 ≤
        2 * ((shape.toStrictShiftedTuple.values row : ℝ) + 1) := by
      nlinarith
    have hcoefficient : (2 : ℝ) ≤ 4 * envelope ^ 2 := by
      nlinarith [sq_nonneg envelope]
    have hvalueNonneg : 0 ≤
        (shape.toStrictShiftedTuple.values row : ℝ) + 1 := by positivity
    exact hfirst.trans
      (mul_le_mul_of_nonneg_right hcoefficient hvalueNonneg)

theorem adjusted_sqrt_inverse_bound
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    Real.sqrt (regevCenter rank size) /
        Real.sqrt ((shape.toStrictShiftedTuple.values row : ℝ) + 1) ≤
      2 * (1 + |regevCenteredRow shape row| + (row.rev.val : ℝ)) := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hshiftedPos : 0 <
      (shape.toStrictShiftedTuple.values row : ℝ) + 1 := by positivity
  have henvelopeNonneg : 0 ≤
      2 * (1 + |regevCenteredRow shape row| + (row.rev.val : ℝ)) := by
    positivity
  have hsquare := center_le_polynomial_mul_shifted_succ shape hsize row
  have hsqrt := Real.sqrt_le_sqrt hsquare
  have hrewrite : Real.sqrt
      (4 * (1 + |regevCenteredRow shape row| + (row.rev.val : ℝ)) ^ 2 *
        ((shape.toStrictShiftedTuple.values row : ℝ) + 1)) =
      2 * (1 + |regevCenteredRow shape row| + (row.rev.val : ℝ)) *
        Real.sqrt ((shape.toStrictShiftedTuple.values row : ℝ) + 1) := by
    rw [show 4 * (1 + |regevCenteredRow shape row| + (row.rev.val : ℝ)) ^ 2 *
        ((shape.toStrictShiftedTuple.values row : ℝ) + 1) =
      (2 * (1 + |regevCenteredRow shape row| + (row.rev.val : ℝ))) ^ 2 *
        ((shape.toStrictShiftedTuple.values row : ℝ) + 1) by ring]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq henvelopeNonneg]
  rw [hrewrite] at hsqrt
  exact (div_le_iff₀ (Real.sqrt_pos.2 hshiftedPos)).2 hsqrt

noncomputable def regevRowEnvelopeProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1),
    2 * (1 + |regevCenteredRow shape row| + (row.rev.val : ℝ))

theorem sqrtCenter_pow_div_adjustedSqrtProduct_le
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    Real.sqrt (regevCenter rank size) ^ (rank + 1) /
        shiftedAdjustedSqrtProduct shape ≤
      regevRowEnvelopeProduct shape := by
  unfold shiftedAdjustedSqrtProduct regevRowEnvelopeProduct
  have hrewrite :
      Real.sqrt (regevCenter rank size) ^ (rank + 1) /
          (∏ row : Fin (rank + 1),
            Real.sqrt (shape.toStrictShiftedTuple.values row + 1 : ℕ)) =
        ∏ row : Fin (rank + 1),
          (Real.sqrt (regevCenter rank size) /
            Real.sqrt ((shape.toStrictShiftedTuple.values row : ℝ) + 1)) := by
    rw [show Real.sqrt (regevCenter rank size) ^ (rank + 1) =
        ∏ _row : Fin (rank + 1),
          Real.sqrt (regevCenter rank size) by simp]
    push_cast
    rw [Finset.prod_div_distrib]
  rw [hrewrite]
  apply Finset.prod_le_prod
  · intro row hrow
    positivity
  · intro row hrow
    exact adjusted_sqrt_inverse_bound shape hsize row

noncomputable def regevPairEnvelopeProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
    (|regevCenteredRow shape row| + |regevCenteredRow shape next| +
      (rank : ℝ) * (rank + 1 : ℕ))

theorem pair_correction_le_rank_dimension
    {rank size : ℕ} (_shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row next : Fin (rank + 1)) (hnext : row < next) :
    ((next.val : ℝ) - row.val) /
        Real.sqrt (regevCenter rank size) ≤
      (rank : ℝ) * (rank + 1 : ℕ) := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hsqrtPos : 0 < Real.sqrt (regevCenter rank size) := by positivity
  have hdimensionPos : (0 : ℝ) < rank + 1 := by positivity
  have hcenterLower : 1 / ((rank + 1 : ℕ) : ℝ) ≤
      regevCenter rank size := by
    unfold regevCenter
    push_cast
    apply (div_le_div_iff_of_pos_right (by positivity :
      (0 : ℝ) < (rank : ℝ) + 1)).2
    exact_mod_cast hsize
  have hrootDimension : 1 ≤
      Real.sqrt (regevCenter rank size) * ((rank + 1 : ℕ) : ℝ) := by
    have hsquare : (1 : ℝ) ≤
        (Real.sqrt (regevCenter rank size) *
          ((rank + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hcenterPos.le]
      have hdimensionNonneg : (0 : ℝ) ≤ rank + 1 := by positivity
      have hmul : (1 : ℝ) ≤ regevCenter rank size *
          ((rank + 1 : ℕ) : ℝ) :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < ((rank + 1 : ℕ) : ℝ))).mp
          hcenterLower
      have hdimensionOne : (1 : ℝ) ≤ ((rank + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le rank)
      nlinarith [mul_le_mul_of_nonneg_left hdimensionOne
        (mul_nonneg hcenterPos.le hdimensionNonneg)]
    have hnonneg : 0 ≤ Real.sqrt (regevCenter rank size) *
        ((rank + 1 : ℕ) : ℝ) := by positivity
    nlinarith [sq_nonneg (Real.sqrt (regevCenter rank size) *
      ((rank + 1 : ℕ) : ℝ) - 1)]
  have hdifference : ((next.val : ℝ) - row.val) ≤ rank := by
    have hrowNext : row.val ≤ next.val := Nat.le_of_lt hnext
    have hdiffNat : next.val - row.val ≤ rank := by omega
    rw [← Nat.cast_sub hrowNext]
    exact_mod_cast hdiffNat
  apply (div_le_iff₀ hsqrtPos).2
  have hrankNonneg : (0 : ℝ) ≤ rank := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hrootDimension hrankNonneg]

theorem abs_regevCorrectedPair_le_envelope
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row next : Fin (rank + 1)) (hnext : row < next) :
    |regevCorrectedPair shape row next| ≤
      |regevCenteredRow shape row| + |regevCenteredRow shape next| +
        (rank : ℝ) * (rank + 1 : ℕ) := by
  unfold regevCorrectedPair
  have hcorrectionNonneg : 0 ≤ ((next.val : ℝ) - row.val) /
      Real.sqrt (regevCenter rank size) := by
    apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt hnext)
    · exact Real.sqrt_nonneg _
  calc
    |regevCenteredRow shape row - regevCenteredRow shape next +
        ((next.val : ℝ) - row.val) /
          Real.sqrt (regevCenter rank size)| ≤
      |regevCenteredRow shape row| + |regevCenteredRow shape next| +
        ((next.val : ℝ) - row.val) /
          Real.sqrt (regevCenter rank size) := by
      calc
        |_ + _| ≤ |regevCenteredRow shape row -
            regevCenteredRow shape next| +
            |((next.val : ℝ) - row.val) /
            Real.sqrt (regevCenter rank size)| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_of_nonneg hcorrectionNonneg]
          have habsSub : |regevCenteredRow shape row -
              regevCenteredRow shape next| ≤
            |regevCenteredRow shape row| +
              |regevCenteredRow shape next| := by
            simpa [sub_eq_add_neg] using abs_add_le
              (regevCenteredRow shape row)
              (-regevCenteredRow shape next)
          simpa [add_assoc, add_comm, add_left_comm] using
            add_le_add_right habsSub
              (((next.val : ℝ) - row.val) /
                Real.sqrt (regevCenter rank size))
    _ ≤ _ := by
      simpa [add_assoc] using add_le_add_left
        (pair_correction_le_rank_dimension shape hsize row next hnext)
        (|regevCenteredRow shape row| + |regevCenteredRow shape next|)

theorem abs_correctedPairProduct_le_envelope
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    |∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
        regevCorrectedPair shape row next| ≤
      regevPairEnvelopeProduct shape := by
  rw [Finset.abs_prod]
  unfold regevPairEnvelopeProduct
  apply Finset.prod_le_prod
  · intro row hrow
    positivity
  · intro row hrow
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod
    · intro next hnext
      positivity
    · intro next hnext
      exact abs_regevCorrectedPair_le_envelope shape hsize row next
        (Finset.mem_Ioi.mp hnext)

theorem matsumotoPairProduct_normalized_eq_corrected
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    matsumotoPairProduct shape /
        (regevCenter rank size ^ fixedRankExponent (rank + 1)) =
      ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
        regevCorrectedPair shape row next := by
  unfold matsumotoPairProduct
  rw [matsumoto_pair_product_centered shape hsize,
    pairScale_power_eq_fixedRankExponent rank size hsize]
  have hpower : regevCenter rank size ^
      fixedRankExponent (rank + 1) ≠ 0 := by
    apply (Real.rpow_pos_of_pos _ _).ne'
    unfold regevCenter
    positivity
  change (regevCenter rank size ^ fixedRankExponent (rank + 1) *
      (∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
        regevCorrectedPair shape row next)) /
      regevCenter rank size ^ fixedRankExponent (rank + 1) = _
  rw [mul_div_cancel_left₀ _ hpower]

noncomputable def regevAdjustedFactorialUpper
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  (Real.exp (staircaseWeight rank : ℝ) /
      regevShiftedPowerProduct shape) /
    regevAdjustedSqrtRatioProduct shape

theorem regevFactorialNormalized_le_adjustedUpper
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    regevFactorialNormalized (fun _ => size) (fun _ => shape) 0 ≤
      regevAdjustedFactorialUpper shape := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hsqrtAdjustedPos : 0 < shiftedAdjustedSqrtProduct shape := by
    unfold shiftedAdjustedSqrtProduct
    positivity
  have hpowerPos : 0 < shiftedStirlingPowerProduct shape := by
    unfold shiftedStirlingPowerProduct
    apply Finset.prod_pos
    intro row hrow
    by_cases hzero : shape.toStrictShiftedTuple.values row = 0
    · simp [hzero]
    · positivity
  have hfactorialPos : 0 < shiftedFactorialProduct
      (fun _ => size) (fun _ => shape) 0 := by
    unfold shiftedFactorialProduct
    positivity
  have hdenominatorLower :=
    shiftedAdjustedSqrt_mul_power_le_factorialProduct
      (fun _ => size) (fun _ => shape) 0
  have hnumeratorNonneg : 0 ≤
      regevCenter rank size ^ (size + staircaseWeight rank) *
        Real.sqrt (regevCenter rank size) ^ (rank + 1) *
        Real.exp (-(size : ℝ)) := by positivity
  have hdivision :
      (regevCenter rank size ^ (size + staircaseWeight rank) *
          Real.sqrt (regevCenter rank size) ^ (rank + 1) *
          Real.exp (-(size : ℝ))) /
          shiftedFactorialProduct (fun _ => size) (fun _ => shape) 0 ≤
        (regevCenter rank size ^ (size + staircaseWeight rank) *
          Real.sqrt (regevCenter rank size) ^ (rank + 1) *
          Real.exp (-(size : ℝ))) /
          (shiftedAdjustedSqrtProduct shape *
            shiftedStirlingPowerProduct shape) := by
    exact div_le_div_of_nonneg_left hnumeratorNonneg
      (mul_pos hsqrtAdjustedPos hpowerPos) hdenominatorLower
  apply hdivision.trans_eq
  unfold regevAdjustedFactorialUpper
  rw [shiftedAdjustedSqrtProduct_factor shape hsize,
    shiftedStirlingPowerProduct_factor shape hsize]
  have hcenterPower : regevCenter rank size ^
      (size + staircaseWeight rank) ≠ 0 := pow_ne_zero _ hcenterPos.ne'
  have hsqrtPower : Real.sqrt (regevCenter rank size) ^
      (rank + 1) ≠ 0 := pow_ne_zero _ (by positivity)
  have hpowerProduct : regevShiftedPowerProduct shape ≠ 0 := by
    unfold regevShiftedPowerProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro row hrow
    by_cases hzero : shape.toStrictShiftedTuple.values row = 0
    · simp [hzero]
    · exact (Real.rpow_pos_of_pos (by
        unfold regevCenter
        positivity) _).ne'
  have hadjustedRatio : regevAdjustedSqrtRatioProduct shape ≠ 0 := by
    unfold regevAdjustedSqrtRatioProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro row hrow
    apply Real.sqrt_ne_zero'.mpr
    unfold regevCenter
    positivity
  field_simp
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem regevAdjustedFactorialUpper_gaussian_bound
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    regevAdjustedFactorialUpper shape ≤
      Real.exp (regevEntropyOffset rank /
          regevEntropyDenominator rank) *
        regevRowEnvelopeProduct shape *
        Real.exp (-(∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 /
            (2 * regevEntropyDenominator rank))) := by
  have hpowerEq := exp_staircase_div_shiftedPowerProduct shape hsize
  have hexpBound := exp_neg_regevShiftedEntropySum_upper shape hsize
  have hsqrtBound := sqrtCenter_pow_div_adjustedSqrtProduct_le shape hsize
  unfold regevAdjustedFactorialUpper
  rw [hpowerEq]
  have hadjustedFactor :
      (regevAdjustedSqrtRatioProduct shape)⁻¹ =
        Real.sqrt (regevCenter rank size) ^ (rank + 1) /
          shiftedAdjustedSqrtProduct shape := by
    rw [shiftedAdjustedSqrtProduct_factor shape hsize]
    have hsqrtPower : Real.sqrt (regevCenter rank size) ^
        (rank + 1) ≠ 0 := pow_ne_zero _ (by
      unfold regevCenter
      positivity)
    field_simp
  rw [div_eq_mul_inv, hadjustedFactor]
  have hnonnegExp : 0 ≤ Real.exp (-regevShiftedEntropySum shape) := by positivity
  have hsqrtNonneg : 0 ≤
      Real.sqrt (regevCenter rank size) ^ (rank + 1) /
        shiftedAdjustedSqrtProduct shape := by
    apply div_nonneg
    · positivity
    · unfold shiftedAdjustedSqrtProduct
      positivity
  have hupperNonneg : 0 ≤
      Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        Real.exp (-(∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 /
            (2 * regevEntropyDenominator rank))) := by positivity
  exact (mul_le_mul hexpBound hsqrtBound hsqrtNonneg hupperNonneg).trans_eq
    (by ring)

theorem regevFactorialNormalized_nonneg
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    0 ≤ regevFactorialNormalized (fun _ => size) (fun _ => shape) 0 := by
  unfold regevFactorialNormalized
  apply div_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg (by
          unfold regevCenter
          positivity) _
      · exact pow_nonneg (Real.sqrt_nonneg _) _
    · exact (Real.exp_pos _).le
  · unfold shiftedFactorialProduct
    apply Finset.prod_nonneg
    intro row hrow
    positivity

theorem abs_matsumotoLocalNormalizedTableau_gaussian_bound
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    |matsumotoLocalNormalizedTableau shape| ≤
      Real.exp (regevEntropyOffset rank /
          regevEntropyDenominator rank) *
        regevRowEnvelopeProduct shape *
        regevPairEnvelopeProduct shape *
        Real.exp (-(∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 /
            (2 * regevEntropyDenominator rank))) := by
  rw [matsumotoLocalNormalizedTableau_factor shape hsize]
  rw [abs_mul, abs_of_nonneg (regevFactorialNormalized_nonneg shape)]
  rw [matsumotoPairProduct_normalized_eq_corrected shape hsize]
  have hfactorial :=
    (regevFactorialNormalized_le_adjustedUpper shape hsize).trans
      (regevAdjustedFactorialUpper_gaussian_bound shape hsize)
  have hpairs := abs_correctedPairProduct_le_envelope shape hsize
  have hfactorialNonneg : 0 ≤
      regevFactorialNormalized (fun _ => size) (fun _ => shape) 0 :=
    regevFactorialNormalized_nonneg shape
  have hpairsNonneg : 0 ≤ regevPairEnvelopeProduct shape := by
    unfold regevPairEnvelopeProduct
    positivity
  have hupperNonneg : 0 ≤
      Real.exp (regevEntropyOffset rank /
          regevEntropyDenominator rank) *
        regevRowEnvelopeProduct shape *
        Real.exp (-(∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 /
            (2 * regevEntropyDenominator rank))) := by
    unfold regevRowEnvelopeProduct
    positivity
  exact (mul_le_mul hfactorial hpairs (abs_nonneg _)
    hupperNonneg).trans_eq (by ring)

end FibonacciRibbonKernel
