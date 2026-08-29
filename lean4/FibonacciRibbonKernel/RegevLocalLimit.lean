import FibonacciRibbonKernel.RegevStirlingLocal

namespace FibonacciRibbonKernel

open Filter Asymptotics
open scoped Classical

theorem standardTableau_div_factorial_eq_pair_div_shiftedFactorials
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    (standardTableauNumber shape : ℝ) / (size.factorial : ℝ) =
      matsumotoPairProduct shape /
        (∏ row : Fin (rank + 1),
          ((shape.toStrictShiftedTuple.values row).factorial : ℝ)) := by
  have hq := standardTableauNumber_eq_matsumoto_row_product shape
  have hr : (standardTableauNumber shape : ℝ) =
      (size.factorial : ℝ) *
        ((∏ row : Fin (rank + 1),
            (((shape.1 row).val + row.rev.val).factorial : ℝ)⁻¹) *
          matsumotoPairProduct shape) := by
    have hr0 := congrArg (Rat.castHom ℝ) hq
    simpa [matsumotoPairProduct] using hr0
  rw [hr]
  have hfactorial : (size.factorial : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hfactorial]
  unfold matsumotoPairProduct
  have hinverse :
      (∏ row : Fin (rank + 1),
          (((shape.1 row).val + row.rev.val).factorial : ℝ)⁻¹) =
        (∏ row : Fin (rank + 1),
          ((shape.toStrictShiftedTuple.values row).factorial : ℝ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro row hrow
    rw [BoundedPartition.toStrictShiftedTuple_values]
  rw [hinverse]
  ring

noncomputable def matsumotoLocalExponent (dimension : ℕ) : ℝ :=
  ((dimension : ℝ) ^ 2 + dimension) / 4

theorem matsumoto_center_power_factor
    (rank size : ℕ) (hsize : 1 ≤ size) :
    regevCenter rank size ^
        ((size : ℝ) + matsumotoLocalExponent (rank + 1)) =
      (regevCenter rank size ^ (size + staircaseWeight rank) *
        Real.sqrt (regevCenter rank size) ^ (rank + 1)) /
          (regevCenter rank size ^ fixedRankExponent (rank + 1)) := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hbaseNonneg : 0 ≤ regevCenter rank size := hcenterPos.le
  have hstaircaseNat : 2 * staircaseWeight rank = (rank + 1) * rank := by
    unfold staircaseWeight
    rw [show (∑ row : Fin (rank + 1), row.rev.val) =
        ∑ row : Fin (rank + 1), row.val by
      exact Equiv.sum_comp Fin.revPerm
        (fun row : Fin (rank + 1) => row.val)]
    have hfin : (∑ row : Fin (rank + 1), row.val) =
        ∑ value ∈ Finset.range (rank + 1), value := by
      simpa using (Fin.sum_univ_eq_sum_range (n := rank + 1)
        (fun value : ℕ => value))
    rw [hfin]
    have hsum := Finset.sum_range_id_mul_two (rank + 1)
    calc
      2 * (∑ value ∈ Finset.range (rank + 1), value) =
          (∑ value ∈ Finset.range (rank + 1), value) * 2 := by omega
      _ = (rank + 1) * ((rank + 1) - 1) := hsum
      _ = (rank + 1) * rank := by rw [Nat.add_sub_cancel]
  have hstaircaseReal :
      2 * (staircaseWeight rank : ℝ) =
        ((rank + 1) : ℝ) * rank := by
    exact_mod_cast hstaircaseNat
  have hsqrtPower :
      Real.sqrt (regevCenter rank size) ^ (rank + 1) =
        regevCenter rank size ^ (((rank + 1 : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hbaseNonneg]
    congr 1
    ring
  rw [hsqrtPower]
  simp_rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hcenterPos, ← Real.rpow_sub hcenterPos]
  congr 1
  unfold matsumotoLocalExponent fixedRankExponent
  have hcastSub : (((rank + 1) - 1 : ℕ) : ℝ) = rank := by norm_num
  rw [hcastSub]
  push_cast
  nlinarith

noncomputable def matsumotoLocalNormalizedTableau
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  regevCenter rank size ^
      ((size : ℝ) + matsumotoLocalExponent (rank + 1)) *
    (standardTableauNumber shape : ℝ) /
      ((size.factorial : ℝ) * Real.exp size)

theorem matsumotoLocalNormalizedTableau_factor
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    matsumotoLocalNormalizedTableau shape =
      regevFactorialNormalized (fun _ => size) (fun _ => shape) 0 *
        (matsumotoPairProduct shape /
          (regevCenter rank size ^ fixedRankExponent (rank + 1))) := by
  unfold matsumotoLocalNormalizedTableau regevFactorialNormalized
  simp only
  have hfactorial : (size.factorial : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp (size : ℝ) ≠ 0 := Real.exp_ne_zero _
  have hrewrite :
      regevCenter rank size ^
            ((size : ℝ) + matsumotoLocalExponent (rank + 1)) *
          (standardTableauNumber shape : ℝ) /
          ((size.factorial : ℝ) * Real.exp size) =
        regevCenter rank size ^
            ((size : ℝ) + matsumotoLocalExponent (rank + 1)) *
          ((standardTableauNumber shape : ℝ) / size.factorial) *
          Real.exp (-(size : ℝ)) := by
    rw [Real.exp_neg]
    field_simp
  rw [hrewrite,
    standardTableau_div_factorial_eq_pair_div_shiftedFactorials,
    matsumoto_center_power_factor rank size hsize]
  unfold shiftedFactorialProduct
  have hfactorialProduct :
      (∏ row : Fin (rank + 1),
        ((shape.toStrictShiftedTuple.values row).factorial : ℝ)) ≠ 0 := by
    positivity
  have hcenterPower : regevCenter rank size ^
      fixedRankExponent (rank + 1) ≠ 0 := by
    apply (Real.rpow_pos_of_pos _ _).ne'
    unfold regevCenter
    positivity
  field_simp

theorem matsumotoLocalNormalizedTableau_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row))) :
    Tendsto (fun index => matsumotoLocalNormalizedTableau (shapes index))
      atTop
      (nhds (((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
          Real.exp (-(∑ row : Fin (rank + 1),
            limitRows row ^ 2 / 2))) *
        (∏ row : Fin (rank + 1),
          ∏ next ∈ Finset.Ioi row,
            (limitRows row - limitRows next)))) := by
  have hfactorial := regevFactorialNormalized_tendsto
    sizes shapes limitRows hsizes hcentered
  have hpairs := matsumoto_pair_normalized_tendsto
    sizes shapes limitRows hsizes hcentered
  have hproduct := hfactorial.mul hpairs
  apply hproduct.congr'
  have heventSize : ∀ᶠ index in atTop, 1 ≤ sizes index :=
    hsizes.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [heventSize] with index hsize
  exact (matsumotoLocalNormalizedTableau_factor
    (shapes index) hsize).symm

end FibonacciRibbonKernel
