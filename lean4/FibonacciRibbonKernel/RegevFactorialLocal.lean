import FibonacciRibbonKernel.RegevEntropy
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace FibonacciRibbonKernel

open Filter Asymptotics
open scoped Classical

noncomputable def regevCenter (rank size : ℕ) : ℝ :=
  (size : ℝ) / (rank + 1 : ℝ)

noncomputable def regevShiftedDeviation
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (row : Fin (rank + 1)) : ℝ :=
  (shape.toStrictShiftedTuple.values row : ℝ) / regevCenter rank size - 1

theorem regevShiftedDeviation_eq_centered
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    regevShiftedDeviation shape row =
      regevCenteredRow shape row /
          Real.sqrt (regevCenter rank size) +
        (row.rev.val : ℝ) / regevCenter rank size := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hsqrtNe : Real.sqrt (regevCenter rank size) ≠ 0 := by positivity
  have hreconstruct := regevCenteredRow_reconstruct shape hsize row
  unfold regevShiftedDeviation
  rw [BoundedPartition.toStrictShiftedTuple_values]
  unfold regevCenter at *
  push_cast
  rw [hreconstruct]
  field_simp
  ring_nf
  have hsquare :
      Real.sqrt ((size : ℝ) * (1 + (rank : ℝ))⁻¹) ^ 2 =
        (size : ℝ) * (1 + (rank : ℝ))⁻¹ := by
    exact Real.sq_sqrt (by positivity)
  rw [hsquare]
  field_simp
  ring

theorem regevCenter_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (hsizes : Tendsto sizes atTop atTop) :
    Tendsto (fun index => regevCenter rank (sizes index)) atTop atTop := by
  unfold regevCenter
  exact Tendsto.atTop_div_const (by positivity)
    (tendsto_natCast_atTop_atTop.comp hsizes)

theorem regevShiftedDeviation_tendsto_zero
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row)))
    (row : Fin (rank + 1)) :
    Tendsto (fun index => regevShiftedDeviation (shapes index) row)
      atTop (nhds 0) := by
  have hcenter := regevCenter_tendsto (rank := rank) sizes hsizes
  have hsqrt := Real.tendsto_sqrt_atTop.comp hcenter
  have hinvSqrt := tendsto_inv_atTop_zero.comp hsqrt
  have hinvCenter := tendsto_inv_atTop_zero.comp hcenter
  have hfirst : Tendsto
      (fun index => regevCenteredRow (shapes index) row /
        Real.sqrt (regevCenter rank (sizes index)))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hcentered row).mul hinvSqrt
  have hsecond : Tendsto
      (fun index => (row.rev.val : ℝ) / regevCenter rank (sizes index))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinvCenter.const_mul (row.rev.val : ℝ)
  have hsum : Tendsto
      (fun index => regevCenteredRow (shapes index) row /
          Real.sqrt (regevCenter rank (sizes index)) +
        (row.rev.val : ℝ) / regevCenter rank (sizes index))
      atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  apply hsum.congr'
  have heventSize : ∀ᶠ index in atTop, 1 ≤ sizes index :=
    hsizes.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [heventSize] with index hsize
  rw [regevShiftedDeviation_eq_centered (shapes index) hsize]

theorem regevCenter_mul_deviation_sq
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    regevCenter rank size * regevShiftedDeviation shape row ^ 2 =
      (regevCenteredRow shape row +
        (row.rev.val : ℝ) / Real.sqrt (regevCenter rank size)) ^ 2 := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hsqrtNe : Real.sqrt (regevCenter rank size) ≠ 0 := by positivity
  rw [regevShiftedDeviation_eq_centered shape hsize]
  field_simp
  let center := regevCenter rank size
  let root := Real.sqrt center
  have hcenterEq : center = root ^ 2 := by
    exact (Real.sq_sqrt hcenterPos.le).symm
  change (center * regevCenteredRow shape row +
      root * (row.rev.val : ℝ)) ^ 2 =
    center * (regevCenteredRow shape row * root +
      (row.rev.val : ℝ)) ^ 2
  rw [hcenterEq]
  ring

theorem regevCenter_mul_deviation_sq_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row)))
    (row : Fin (rank + 1)) :
    Tendsto
      (fun index => regevCenter rank (sizes index) *
        regevShiftedDeviation (shapes index) row ^ 2)
      atTop (nhds (limitRows row ^ 2)) := by
  have hcenter := regevCenter_tendsto (rank := rank) sizes hsizes
  have hsqrt := Real.tendsto_sqrt_atTop.comp hcenter
  have hcorrection : Tendsto
      (fun index => (row.rev.val : ℝ) /
        Real.sqrt (regevCenter rank (sizes index)))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hsqrt).const_mul (row.rev.val : ℝ)
  have hright := ((hcentered row).add hcorrection).pow 2
  have hright' : Tendsto
      (fun index => (regevCenteredRow (shapes index) row +
        (row.rev.val : ℝ) /
          Real.sqrt (regevCenter rank (sizes index))) ^ 2)
      atTop (nhds (limitRows row ^ 2)) := by
    simpa using hright
  apply hright'.congr'
  have heventSize : ∀ᶠ index in atTop, 1 ≤ sizes index :=
    hsizes.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [heventSize] with index hsize
  exact (regevCenter_mul_deviation_sq (shapes index) hsize row).symm

theorem regev_scaled_entropy_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row)))
    (row : Fin (rank + 1)) :
    Tendsto
      (fun index => regevCenter rank (sizes index) *
        entropyRemainder (regevShiftedDeviation (shapes index) row))
      atTop (nhds (limitRows row ^ 2 / 2)) :=
  tendsto_scaled_entropyRemainder
    (regevShiftedDeviation_tendsto_zero
      sizes shapes limitRows hsizes hcentered row)
    (regevCenter_mul_deviation_sq_tendsto
      sizes shapes limitRows hsizes hcentered row)

noncomputable def regevShiftedEntropySum
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∑ row : Fin (rank + 1),
    regevCenter rank size *
      entropyRemainder (regevShiftedDeviation shape row)

theorem regevShiftedEntropySum_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row))) :
    Tendsto
      (fun index => regevShiftedEntropySum (shapes index))
      atTop (nhds (∑ row : Fin (rank + 1), limitRows row ^ 2 / 2)) := by
  unfold regevShiftedEntropySum
  apply tendsto_finsetSum Finset.univ
  intro row hrow
  exact regev_scaled_entropy_tendsto
    sizes shapes limitRows hsizes hcentered row

theorem sum_regevCenter_mul_shiftedDeviation
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    (∑ row : Fin (rank + 1),
        regevCenter rank size * regevShiftedDeviation shape row) =
      (staircaseWeight rank : ℝ) := by
  have hcenterNe : regevCenter rank size ≠ 0 := by
    unfold regevCenter
    positivity
  unfold regevShiftedDeviation
  simp_rw [mul_sub, mul_div_cancel₀ _ hcenterNe]
  rw [Finset.sum_sub_distrib]
  have hvalues :
      (∑ row : Fin (rank + 1),
        (shape.toStrictShiftedTuple.values row : ℝ)) =
      (size + staircaseWeight rank : ℕ) := by
    exact_mod_cast shape.toStrictShiftedTuple.sum_eq
  rw [hvalues]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  unfold regevCenter
  have hdimensionNe : (rank + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

noncomputable def regevShiftedLogSum
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∑ row : Fin (rank + 1),
    (shape.toStrictShiftedTuple.values row : ℝ) *
      Real.log ((shape.toStrictShiftedTuple.values row : ℝ) /
        regevCenter rank size)

theorem regevShiftedLogSum_eq_staircase_add_entropy
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    regevShiftedLogSum shape =
      (staircaseWeight rank : ℝ) + regevShiftedEntropySum shape := by
  have hcenterNe : regevCenter rank size ≠ 0 := by
    unfold regevCenter
    positivity
  unfold regevShiftedLogSum regevShiftedEntropySum
  rw [← sum_regevCenter_mul_shiftedDeviation shape hsize]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row hrow
  have hratio :
      (shape.toStrictShiftedTuple.values row : ℝ) /
          regevCenter rank size =
        1 + regevShiftedDeviation shape row := by
    unfold regevShiftedDeviation
    ring
  rw [hratio]
  unfold entropyRemainder
  change (shape.toStrictShiftedTuple.values row : ℝ) *
      Real.log (1 + regevShiftedDeviation shape row) = _
  have hvalue : (shape.toStrictShiftedTuple.values row : ℝ) =
      regevCenter rank size *
        (1 + regevShiftedDeviation shape row) := by
    rw [← hratio]
    field_simp
  rw [hvalue]
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

noncomputable def regevShiftedPowerProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1),
    ((shape.toStrictShiftedTuple.values row : ℝ) /
      regevCenter rank size) ^
        (shape.toStrictShiftedTuple.values row : ℝ)

theorem shifted_ratio_rpow_eq_exp
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    ((shape.toStrictShiftedTuple.values row : ℝ) /
        regevCenter rank size) ^
          (shape.toStrictShiftedTuple.values row : ℝ) =
      Real.exp ((shape.toStrictShiftedTuple.values row : ℝ) *
        Real.log ((shape.toStrictShiftedTuple.values row : ℝ) /
          regevCenter rank size)) := by
  by_cases hzero : shape.toStrictShiftedTuple.values row = 0
  · simp [hzero]
  · have hpositive :
        0 < (shape.toStrictShiftedTuple.values row : ℝ) /
          regevCenter rank size := by
      unfold regevCenter
      positivity
    rw [Real.rpow_def_of_pos hpositive]
    congr 1
    ring

theorem regevShiftedPowerProduct_eq_exp_logSum
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    regevShiftedPowerProduct shape =
      Real.exp (regevShiftedLogSum shape) := by
  unfold regevShiftedPowerProduct regevShiftedLogSum
  simp_rw [shifted_ratio_rpow_eq_exp shape hsize]
  rw [← Real.exp_sum]

theorem regevShiftedPowerProduct_eq_exp_staircase_entropy
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    regevShiftedPowerProduct shape =
      Real.exp ((staircaseWeight rank : ℝ) +
        regevShiftedEntropySum shape) := by
  rw [regevShiftedPowerProduct_eq_exp_logSum shape hsize,
    regevShiftedLogSum_eq_staircase_add_entropy shape hsize]

theorem exp_staircase_div_shiftedPowerProduct
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    Real.exp (staircaseWeight rank : ℝ) /
        regevShiftedPowerProduct shape =
      Real.exp (-regevShiftedEntropySum shape) := by
  rw [regevShiftedPowerProduct_eq_exp_staircase_entropy shape hsize]
  rw [← Real.exp_sub]
  congr 1
  ring

theorem exp_staircase_div_shiftedPowerProduct_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row))) :
    Tendsto
      (fun index => Real.exp (staircaseWeight rank : ℝ) /
        regevShiftedPowerProduct (shapes index))
      atTop
      (nhds (Real.exp (-(∑ row : Fin (rank + 1),
        limitRows row ^ 2 / 2)))) := by
  have hentropy := regevShiftedEntropySum_tendsto
    sizes shapes limitRows hsizes hcentered
  have hexp : Tendsto
      (fun index => Real.exp (-regevShiftedEntropySum (shapes index)))
      atTop
      (nhds (Real.exp (-(∑ row : Fin (rank + 1),
        limitRows row ^ 2 / 2)))) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp hentropy.neg
  apply hexp.congr'
  have heventSize : ∀ᶠ index in atTop, 1 ≤ sizes index :=
    hsizes.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [heventSize] with index hsize
  exact (exp_staircase_div_shiftedPowerProduct
    (shapes index) hsize).symm

end FibonacciRibbonKernel
