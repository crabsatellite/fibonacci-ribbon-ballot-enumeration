import FibonacciRibbonKernel.RegevFactorialLocal

namespace FibonacciRibbonKernel

open Filter Asymptotics
open scoped Classical

theorem shiftedValue_eq_center_mul_deviation
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    (shape.toStrictShiftedTuple.values row : ℝ) =
      regevCenter rank size *
        (1 + regevShiftedDeviation shape row) := by
  unfold regevShiftedDeviation
  have hcenterNe : regevCenter rank size ≠ 0 := by
    unfold regevCenter
    positivity
  field_simp
  ring

theorem shiftedValue_tendsto_atTop
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row)))
    (row : Fin (rank + 1)) :
    Tendsto (fun index => shapes index |>.toStrictShiftedTuple.values row)
      atTop atTop := by
  have hdelta := regevShiftedDeviation_tendsto_zero
    sizes shapes limitRows hsizes hcentered row
  have heventDelta : ∀ᶠ index in atTop,
      -(1 / 2 : ℝ) < regevShiftedDeviation (shapes index) row :=
    hdelta.eventually (Ioi_mem_nhds
      (by norm_num : -(1 / 2 : ℝ) < 0))
  have heventSize : ∀ᶠ index in atTop, 1 ≤ sizes index :=
    hsizes.eventually (Filter.eventually_ge_atTop 1)
  have hcenter := regevCenter_tendsto (rank := rank) sizes hsizes
  have hhalfCenter : Tendsto
      (fun index => regevCenter rank (sizes index) / 2)
      atTop atTop := Tendsto.atTop_div_const (by norm_num) hcenter
  have hreal : Tendsto
      (fun index => (shapes index |>.toStrictShiftedTuple.values row : ℝ))
      atTop atTop := by
    have heventLower : ∀ᶠ index in atTop,
        regevCenter rank (sizes index) / 2 ≤
          (shapes index |>.toStrictShiftedTuple.values row : ℝ) := by
      filter_upwards [heventDelta, heventSize] with index hdeltaIndex hsize
      rw [shiftedValue_eq_center_mul_deviation
        (shapes index) hsize row]
      have hcenterNonneg : 0 ≤ regevCenter rank (sizes index) := by
        unfold regevCenter
        positivity
      nlinarith
    exact tendsto_atTop_mono' atTop heventLower hhalfCenter
  exact tendsto_natCast_atTop_iff.mp hreal

noncomputable def shiftedFactorialProduct
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (index : ℕ) : ℝ :=
  ∏ row : Fin (rank + 1),
    ((shapes index).toStrictShiftedTuple.values row).factorial

noncomputable def shiftedStirlingProduct
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (index : ℕ) : ℝ :=
  ∏ row : Fin (rank + 1),
    Real.sqrt (2 *
      (shapes index).toStrictShiftedTuple.values row * Real.pi) *
      (((shapes index).toStrictShiftedTuple.values row : ℝ) /
        Real.exp 1) ^
          (shapes index).toStrictShiftedTuple.values row

theorem shiftedFactorialProduct_isEquivalent_stirling
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row))) :
    shiftedFactorialProduct sizes shapes ~[atTop]
      shiftedStirlingProduct sizes shapes := by
  unfold shiftedFactorialProduct shiftedStirlingProduct
  apply IsEquivalent.finsetProd
  intro row hrow
  exact (Stirling.factorial_isEquivalent_stirling).comp_tendsto
    (shiftedValue_tendsto_atTop
      sizes shapes limitRows hsizes hcentered row)

noncomputable def regevSqrtRatioProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1),
    Real.sqrt ((shape.toStrictShiftedTuple.values row : ℝ) /
      regevCenter rank size)

theorem regevSqrtRatioProduct_tendsto_one
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row))) :
    Tendsto (fun index => regevSqrtRatioProduct (shapes index))
      atTop (nhds 1) := by
  unfold regevSqrtRatioProduct
  have hproduct : Tendsto
      (fun index => ∏ row : Fin (rank + 1),
        Real.sqrt (1 + regevShiftedDeviation (shapes index) row))
      atTop (nhds (∏ _row : Fin (rank + 1), (1 : ℝ))) := by
    apply tendsto_finsetProd Finset.univ
    intro row hrow
    have hdelta := regevShiftedDeviation_tendsto_zero
      sizes shapes limitRows hsizes hcentered row
    have hadd : Tendsto
        (fun index => 1 + regevShiftedDeviation (shapes index) row)
        atTop (nhds 1) := by simpa using tendsto_const_nhds.add hdelta
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hadd using 1
    · funext index
      rfl
    · rw [Real.sqrt_one]
  have hproduct' : Tendsto
      (fun index => ∏ row : Fin (rank + 1),
        Real.sqrt (1 + regevShiftedDeviation (shapes index) row))
      atTop (nhds 1) := by simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [] with index
  apply Finset.prod_congr rfl
  intro row hrow
  unfold regevShiftedDeviation
  ring_nf

noncomputable def shiftedStirlingSqrtProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1),
    Real.sqrt (2 *
      shape.toStrictShiftedTuple.values row * Real.pi)

theorem shiftedStirlingSqrtProduct_factor
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    shiftedStirlingSqrtProduct shape =
      Real.sqrt (2 * Real.pi * regevCenter rank size) ^ (rank + 1) *
        regevSqrtRatioProduct shape := by
  unfold shiftedStirlingSqrtProduct regevSqrtRatioProduct
  calc
    (∏ row : Fin (rank + 1),
        Real.sqrt (2 *
          shape.toStrictShiftedTuple.values row * Real.pi)) =
      ∏ row : Fin (rank + 1),
        (Real.sqrt (2 * Real.pi * regevCenter rank size) *
          Real.sqrt ((shape.toStrictShiftedTuple.values row : ℝ) /
            regevCenter rank size)) := by
      apply Finset.prod_congr rfl
      intro row hrow
      have hcenterPos : 0 < regevCenter rank size := by
        unfold regevCenter
        positivity
      have hratioNonneg :
          0 ≤ (shape.toStrictShiftedTuple.values row : ℝ) /
            regevCenter rank size := by positivity
      rw [← Real.sqrt_mul (by positivity :
        0 ≤ 2 * Real.pi * regevCenter rank size)]
      congr 1
      field_simp
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      simp

noncomputable def shiftedStirlingPowerProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1),
    (((shape.toStrictShiftedTuple.values row : ℝ) / Real.exp 1) ^
      shape.toStrictShiftedTuple.values row)

theorem shiftedStirlingProduct_eq_sqrt_mul_power
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (index : ℕ) :
    shiftedStirlingProduct sizes shapes index =
      shiftedStirlingSqrtProduct (shapes index) *
        shiftedStirlingPowerProduct (shapes index) := by
  unfold shiftedStirlingProduct shiftedStirlingSqrtProduct
  unfold shiftedStirlingPowerProduct
  rw [Finset.prod_mul_distrib]

theorem shiftedStirlingPowerProduct_factor
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    shiftedStirlingPowerProduct shape =
      regevCenter rank size ^ (size + staircaseWeight rank) *
        Real.exp (-(size + staircaseWeight rank : ℕ)) *
        regevShiftedPowerProduct shape := by
  have hcenterNe : regevCenter rank size ≠ 0 := by
    unfold regevCenter
    positivity
  unfold shiftedStirlingPowerProduct regevShiftedPowerProduct
  calc
    (∏ row : Fin (rank + 1),
        ((shape.toStrictShiftedTuple.values row : ℝ) / Real.exp 1) ^
          shape.toStrictShiftedTuple.values row) =
      ∏ row : Fin (rank + 1),
        (regevCenter rank size ^ shape.toStrictShiftedTuple.values row *
          (((shape.toStrictShiftedTuple.values row : ℝ) /
            regevCenter rank size) ^
              shape.toStrictShiftedTuple.values row) *
          ((Real.exp 1)⁻¹ ^
            shape.toStrictShiftedTuple.values row)) := by
      apply Finset.prod_congr rfl
      intro row hrow
      rw [← mul_pow, ← mul_pow]
      congr 1
      field_simp
    _ = (∏ row : Fin (rank + 1),
          regevCenter rank size ^ shape.toStrictShiftedTuple.values row) *
        (∏ row : Fin (rank + 1),
          ((shape.toStrictShiftedTuple.values row : ℝ) /
            regevCenter rank size) ^
              shape.toStrictShiftedTuple.values row) *
        ∏ row : Fin (rank + 1),
          (Real.exp 1)⁻¹ ^ shape.toStrictShiftedTuple.values row := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = _ := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        shape.toStrictShiftedTuple.sum_eq]
      simp_rw [← Real.rpow_natCast]
      rw [← Real.exp_neg]
      rw [← Real.exp_mul]
      rw [show (-1 : ℝ) * (size + staircaseWeight rank : ℕ) =
          -(size + staircaseWeight rank : ℕ) by ring]
      ring

noncomputable def regevStirlingNormalized
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  (regevCenter rank size ^ (size + staircaseWeight rank) *
      Real.sqrt (regevCenter rank size) ^ (rank + 1) *
      Real.exp (-(size : ℝ))) /
    (shiftedStirlingSqrtProduct shape * shiftedStirlingPowerProduct shape)

theorem sqrt_center_div_sqrt_two_pi_center
    (rank size : ℕ) (hsize : 1 ≤ size) :
    Real.sqrt (regevCenter rank size) /
        Real.sqrt (2 * Real.pi * regevCenter rank size) =
      1 / Real.sqrt (2 * Real.pi) := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  rw [show 2 * Real.pi * regevCenter rank size =
      (2 * Real.pi) * regevCenter rank size by ring]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hsqrtCenter : Real.sqrt (regevCenter rank size) ≠ 0 := by positivity
  have hsqrtTwoPi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

theorem regevStirlingNormalized_factor
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size)
    (hpositive : ∀ row, 1 ≤ shape.toStrictShiftedTuple.values row) :
    regevStirlingNormalized shape =
      (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
        (Real.exp (staircaseWeight rank : ℝ) /
          regevShiftedPowerProduct shape) /
        regevSqrtRatioProduct shape := by
  have hcenterPos : 0 < regevCenter rank size := by
    unfold regevCenter
    positivity
  have hsqrtCenter : Real.sqrt (regevCenter rank size) ≠ 0 := by positivity
  have hpowerProduct : regevShiftedPowerProduct shape ≠ 0 := by
    unfold regevShiftedPowerProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro row hrow
    apply (Real.rpow_pos_of_pos _ _).ne'
    unfold regevCenter
    exact div_pos (by exact_mod_cast hpositive row) (by positivity)
  have hsqrtRatio : regevSqrtRatioProduct shape ≠ 0 := by
    unfold regevSqrtRatioProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro row hrow
    apply Real.sqrt_ne_zero'.mpr
    unfold regevCenter
    exact div_pos (by exact_mod_cast hpositive row) (by positivity)
  unfold regevStirlingNormalized
  rw [shiftedStirlingSqrtProduct_factor shape hsize,
    shiftedStirlingPowerProduct_factor shape hsize]
  have hsqrtTwoPi : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hsqrtTwoPiCenter :
      Real.sqrt (2 * Real.pi * regevCenter rank size) ≠ 0 := by positivity
  have hsqrtPowers :
      Real.sqrt (regevCenter rank size) ^ (rank + 1) =
        (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
          Real.sqrt (2 * Real.pi * regevCenter rank size) ^ (rank + 1) := by
    have hratio := congrArg (fun value : ℝ => value ^ (rank + 1))
      (sqrt_center_div_sqrt_two_pi_center rank size hsize)
    calc
      Real.sqrt (regevCenter rank size) ^ (rank + 1) =
          (Real.sqrt (regevCenter rank size) ^ (rank + 1) /
            Real.sqrt (2 * Real.pi * regevCenter rank size) ^ (rank + 1)) *
              Real.sqrt (2 * Real.pi * regevCenter rank size) ^ (rank + 1) := by
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hsqrtTwoPiCenter)]
      _ = (Real.sqrt (regevCenter rank size) /
            Real.sqrt (2 * Real.pi * regevCenter rank size)) ^ (rank + 1) *
              Real.sqrt (2 * Real.pi * regevCenter rank size) ^ (rank + 1) := by
        rw [div_pow]
      _ = _ := by rw [hratio]
  rw [hsqrtPowers]
  have hcenterPower : regevCenter rank size ^
      (size + staircaseWeight rank) ≠ 0 :=
    pow_ne_zero _ hcenterPos.ne'
  have hexp : Real.exp (-(size + staircaseWeight rank : ℕ)) ≠ 0 := by
    positivity
  field_simp
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem regevStirlingNormalized_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row))) :
    Tendsto (fun index => regevStirlingNormalized (shapes index))
      atTop
      (nhds ((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
        Real.exp (-(∑ row : Fin (rank + 1),
          limitRows row ^ 2 / 2)))) := by
  have hgaussian := exp_staircase_div_shiftedPowerProduct_tendsto
    sizes shapes limitRows hsizes hcentered
  have hsqrtRatio := regevSqrtRatioProduct_tendsto_one
    sizes shapes limitRows hsizes hcentered
  have hlimit := (hgaussian.div hsqrtRatio (by norm_num)).const_mul
    ((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1))
  have hlimit' : Tendsto
      (fun index => (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
        ((Real.exp (staircaseWeight rank : ℝ) /
          regevShiftedPowerProduct (shapes index)) /
            regevSqrtRatioProduct (shapes index)))
      atTop
      (nhds ((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
        Real.exp (-(∑ row : Fin (rank + 1),
          limitRows row ^ 2 / 2)))) := by
    simpa using hlimit
  apply hlimit'.congr'
  have heventSize : ∀ᶠ index in atTop, 1 ≤ sizes index :=
    hsizes.eventually (Filter.eventually_ge_atTop 1)
  have heventPositive : ∀ᶠ index in atTop,
      ∀ row : Fin (rank + 1),
        1 ≤ (shapes index).toStrictShiftedTuple.values row := by
    rw [Filter.eventually_all]
    intro row
    exact (shiftedValue_tendsto_atTop
      sizes shapes limitRows hsizes hcentered row).eventually
        (Filter.eventually_ge_atTop 1)
  filter_upwards [heventSize, heventPositive] with index hsize hpositive
  simpa [div_eq_mul_inv, mul_assoc] using
    (regevStirlingNormalized_factor
      (shapes index) hsize hpositive).symm

noncomputable def regevFactorialNormalized
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (index : ℕ) : ℝ :=
  (regevCenter rank (sizes index) ^
        (sizes index + staircaseWeight rank) *
      Real.sqrt (regevCenter rank (sizes index)) ^ (rank + 1) *
      Real.exp (-(sizes index : ℝ))) /
    shiftedFactorialProduct sizes shapes index

theorem regevFactorialNormalized_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hcentered : ∀ row,
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (limitRows row))) :
    Tendsto (regevFactorialNormalized sizes shapes)
      atTop
      (nhds ((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
        Real.exp (-(∑ row : Fin (rank + 1),
          limitRows row ^ 2 / 2)))) := by
  have hequiv := shiftedFactorialProduct_isEquivalent_stirling
    sizes shapes limitRows hsizes hcentered
  have hfactorialNe : ∀ᶠ index in atTop,
      shiftedFactorialProduct sizes shapes index ≠ 0 := by
    exact Filter.Eventually.of_forall fun index => by
      unfold shiftedFactorialProduct
      positivity
  have hratio : Tendsto
      (fun index => shiftedStirlingProduct sizes shapes index /
        shiftedFactorialProduct sizes shapes index)
      atTop (nhds 1) :=
    ((isEquivalent_iff_tendsto_one hfactorialNe).mp hequiv.symm)
  have hstirling := regevStirlingNormalized_tendsto
    sizes shapes limitRows hsizes hcentered
  have hproduct := hstirling.mul hratio
  have hproduct' : Tendsto
      (fun index => regevStirlingNormalized (shapes index) *
        (shiftedStirlingProduct sizes shapes index /
          shiftedFactorialProduct sizes shapes index))
      atTop
      (nhds ((1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
        Real.exp (-(∑ row : Fin (rank + 1),
          limitRows row ^ 2 / 2)))) := by
    simpa using hproduct
  apply hproduct'.congr'
  have heventSize : ∀ᶠ index in atTop, 1 ≤ sizes index :=
    hsizes.eventually (Filter.eventually_ge_atTop 1)
  have heventPositive : ∀ᶠ index in atTop,
      ∀ row : Fin (rank + 1),
        1 ≤ (shapes index).toStrictShiftedTuple.values row := by
    rw [Filter.eventually_all]
    intro row
    exact (shiftedValue_tendsto_atTop
      sizes shapes limitRows hsizes hcentered row).eventually
        (Filter.eventually_ge_atTop 1)
  filter_upwards [heventSize, heventPositive] with index hsize hpositive
  unfold regevFactorialNormalized regevStirlingNormalized
  rw [shiftedStirlingProduct_eq_sqrt_mul_power]
  have hstirlingNe :
      shiftedStirlingSqrtProduct (shapes index) *
        shiftedStirlingPowerProduct (shapes index) ≠ 0 := by
    rw [shiftedStirlingSqrtProduct_factor (shapes index) hsize,
      shiftedStirlingPowerProduct_factor (shapes index) hsize]
    have hpowerProduct : regevShiftedPowerProduct (shapes index) ≠ 0 := by
      unfold regevShiftedPowerProduct
      apply Finset.prod_ne_zero_iff.mpr
      intro row hrow
      apply (Real.rpow_pos_of_pos _ _).ne'
      unfold regevCenter
      exact div_pos (by exact_mod_cast hpositive row) (by positivity)
    have hsqrtRatio : regevSqrtRatioProduct (shapes index) ≠ 0 := by
      unfold regevSqrtRatioProduct
      apply Finset.prod_ne_zero_iff.mpr
      intro row hrow
      apply Real.sqrt_ne_zero'.mpr
      unfold regevCenter
      exact div_pos (by exact_mod_cast hpositive row) (by positivity)
    have hcenterNe : regevCenter rank (sizes index) ≠ 0 := by
      unfold regevCenter
      positivity
    have hsqrtBig :
        Real.sqrt (2 * Real.pi * regevCenter rank (sizes index)) ≠ 0 := by
      apply Real.sqrt_ne_zero'.mpr
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (by
        unfold regevCenter
        positivity)
    apply mul_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ hsqrtBig) hsqrtRatio
    · exact mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ hcenterNe) (Real.exp_ne_zero _))
        hpowerProduct
  have hparts := mul_ne_zero_iff.mp hstirlingNe
  have hfactorialPoint : shiftedFactorialProduct sizes shapes index ≠ 0 := by
    unfold shiftedFactorialProduct
    positivity
  field_simp [hparts.1, hparts.2, hfactorialPoint]

end FibonacciRibbonKernel
