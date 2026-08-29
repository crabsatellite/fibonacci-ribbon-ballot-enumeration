import FibonacciRibbonKernel.PowerExponentialEnvelope

namespace FibonacciRibbonKernel

open Filter Asymptotics

/-!
# Uniform geometric bound for all coefficient shifts

The pointwise shift limit is strengthened here to one bound uniform in both
the coefficient index and the shift.  A polynomial factor in the shift is
first exposed algebraically and then absorbed by any geometric radius strictly
larger than the dominant inverse growth.
-/

theorem index_div_regularized_sub_le_shift_succ
    (index shift : ℕ) (hshift : shift ≤ index) :
    (index : ℝ) / regularizedIndex (index - shift) ≤ shift + 1 := by
  have hregularizedPos : (0 : ℝ) < regularizedIndex (index - shift) := by
    unfold regularizedIndex
    positivity
  rw [div_le_iff₀ hregularizedPos]
  by_cases hzero : index - shift = 0
  · have hindexEq : index = shift := by omega
    rw [hindexEq]
    simp [regularizedIndex]
  · have hone : 1 ≤ index - shift := Nat.one_le_iff_ne_zero.mpr hzero
    have hregularized : regularizedIndex (index - shift) = index - shift := by
      unfold regularizedIndex
      omega
    rw [hregularized]
    have heq : index = (index - shift) + shift := by omega
    exact_mod_cast (show index ≤ (shift + 1) * (index - shift) by
      nlinarith [show 1 ≤ index - shift by omega, heq])

theorem envelope_div_powerExponentialTerm_abs
    {constant growth exponent : ℝ}
    (hconstant : constant ≠ 0) (hgrowth : 0 < growth)
    (index shift : ℕ) (hshift : shift ≤ index) (hindex : index ≠ 0) :
    powerExponentialEnvelope growth exponent (index - shift) /
        |powerExponentialTerm constant growth exponent index| =
      |constant|⁻¹ * (growth⁻¹) ^ shift *
        ((index : ℝ) / regularizedIndex (index - shift)) ^ exponent := by
  have hconstantAbs : |constant| ≠ 0 := abs_ne_zero.mpr hconstant
  have hgrowthNe : growth ≠ 0 := hgrowth.ne'
  have hindexPos : (0 : ℝ) < index := by positivity
  have hregularizedPos : (0 : ℝ) < regularizedIndex (index - shift) := by
    unfold regularizedIndex
    positivity
  have hgrowthPow : growth ^ index =
      growth ^ (index - shift) * growth ^ shift := by
    nth_rw 1 [show index = (index - shift) + shift by omega]
    rw [pow_add]
  have hrpowRatio :
      (regularizedIndex (index - shift) : ℝ) ^ (-exponent) /
          (index : ℝ) ^ (-exponent) =
        ((index : ℝ) / regularizedIndex (index - shift)) ^ exponent := by
    rw [Real.rpow_neg hregularizedPos.le,
      Real.rpow_neg hindexPos.le,
      Real.div_rpow hindexPos.le hregularizedPos.le]
    field_simp
  unfold powerExponentialEnvelope powerExponentialTerm
  rw [abs_mul, abs_mul, abs_of_pos (pow_pos hgrowth _),
    abs_of_pos (Real.rpow_pos_of_pos hindexPos _), hgrowthPow]
  have hgrowthSubNe : growth ^ (index - shift) ≠ 0 :=
    pow_ne_zero _ hgrowthNe
  have hgrowthShiftNe : growth ^ shift ≠ 0 := pow_ne_zero _ hgrowthNe
  have hregularizedRpowNe :
      (regularizedIndex (index - shift) : ℝ) ^ (-exponent) ≠ 0 :=
    (Real.rpow_pos_of_pos hregularizedPos _).ne'
  have hindexRpowNe : (index : ℝ) ^ (-exponent) ≠ 0 :=
    (Real.rpow_pos_of_pos hindexPos _).ne'
  calc
    growth ^ (index - shift) *
          (regularizedIndex (index - shift) : ℝ) ^ (-exponent) /
        (|constant| *
          (growth ^ (index - shift) * growth ^ shift) *
          (index : ℝ) ^ (-exponent)) =
      |constant|⁻¹ * (growth ^ shift)⁻¹ *
        ((regularizedIndex (index - shift) : ℝ) ^ (-exponent) /
          (index : ℝ) ^ (-exponent)) := by
            field_simp [hconstantAbs, hgrowthSubNe, hgrowthShiftNe,
              hregularizedRpowNe, hindexRpowNe]
    _ = |constant|⁻¹ * (growth⁻¹) ^ shift *
        ((index : ℝ) / regularizedIndex (index - shift)) ^ exponent := by
          rw [hrpowRatio, inv_pow]

theorem shiftedCoefficientRatio_le_polynomial_geometric
    {source : ℕ → ℝ} {constant growth exponent sourceBound : ℝ}
    (hsourceBound : ∀ index : ℕ,
      |source index| ≤ sourceBound *
        powerExponentialEnvelope growth exponent index)
    (hsourceBoundNonneg : 0 ≤ sourceBound)
    (hconstant : constant ≠ 0) (hgrowth : 0 < growth)
    (hexponent : 0 < exponent)
    (index shift : ℕ) :
    ‖shiftedCoefficientRatio source
        (powerExponentialTerm constant growth exponent) shift index‖ ≤
      (sourceBound / |constant|) * (growth⁻¹) ^ shift *
        ((shift + 1 : ℕ) : ℝ) ^ exponent := by
  unfold shiftedCoefficientRatio
  split_ifs with hshift
  · by_cases hindex : index = 0
    · subst index
      have hshiftZero : shift = 0 := by omega
      subst shift
      simp [powerExponentialTerm, hexponent.ne']
      exact div_nonneg hsourceBoundNonneg (abs_nonneg _)
    · have hcomparisonAbsPos :
          0 < |powerExponentialTerm constant growth exponent index| := by
        rw [abs_pos]
        unfold powerExponentialTerm
        exact mul_ne_zero (mul_ne_zero hconstant (pow_ne_zero _ hgrowth.ne'))
          (Real.rpow_pos_of_pos (by positivity) _).ne'
      have hdivide := div_le_div_of_nonneg_right
        (hsourceBound (index - shift)) hcomparisonAbsPos.le
      have hnormRatio :
          ‖source (index - shift) /
              powerExponentialTerm constant growth exponent index‖ =
            |source (index - shift)| /
              |powerExponentialTerm constant growth exponent index| := by
        rw [Real.norm_eq_abs, abs_div]
      rw [hnormRatio]
      calc
        |source (index - shift)| /
            |powerExponentialTerm constant growth exponent index| ≤
          (sourceBound * powerExponentialEnvelope growth exponent
            (index - shift)) /
              |powerExponentialTerm constant growth exponent index| := hdivide
        _ = sourceBound *
            (|constant|⁻¹ * (growth⁻¹) ^ shift *
              ((index : ℝ) / regularizedIndex (index - shift)) ^ exponent) := by
              rw [mul_div_assoc,
                envelope_div_powerExponentialTerm_abs hconstant hgrowth
                  index shift hshift hindex]
        _ ≤ sourceBound *
            (|constant|⁻¹ * (growth⁻¹) ^ shift *
              ((shift + 1 : ℕ) : ℝ) ^ exponent) := by
              apply mul_le_mul_of_nonneg_left _
                hsourceBoundNonneg
              apply mul_le_mul_of_nonneg_left
              · apply Real.rpow_le_rpow (by positivity) _ hexponent.le
                simpa only [Nat.cast_add, Nat.cast_one] using
                  index_div_regularized_sub_le_shift_succ index shift hshift
              · positivity
        _ = (sourceBound / |constant|) * (growth⁻¹) ^ shift *
            ((shift + 1 : ℕ) : ℝ) ^ exponent := by
              rw [div_eq_mul_inv]
              ring
  · simp
    have hright : 0 ≤ (sourceBound / |constant|) *
        (growth⁻¹) ^ shift * ((shift + 1 : ℕ) : ℝ) ^ exponent := by
      positivity
    simpa only [inv_pow, Nat.cast_add, Nat.cast_one] using hright

theorem exists_shiftedCoefficientRatio_geometric_bound
    {source : ℕ → ℝ} {constant growth exponent radius : ℝ}
    (hsource : source ~[atTop]
      powerExponentialTerm constant growth exponent)
    (hconstant : constant ≠ 0) (hgrowth : 1 < growth)
    (hexponent : 0 < exponent)
    (hradius : growth⁻¹ < radius) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ index shift : ℕ,
      ‖shiftedCoefficientRatio source
          (powerExponentialTerm constant growth exponent) shift index‖ ≤
        bound * radius ^ shift := by
  have hgrowthPos : 0 < growth := one_pos.trans hgrowth
  obtain ⟨sourceBound, hsourceBoundPos, hsourceBound⟩ :=
    exists_global_powerExponentialEnvelope hsource hgrowthPos
  have hinversePos : 0 < growth⁻¹ := inv_pos.mpr hgrowthPos
  obtain ⟨geometricBound, hgeometricBoundPos, hgeometricBound⟩ :=
    exists_polynomial_geometric_comparison exponent hinversePos hradius
  let bound := (sourceBound / |constant|) * geometricBound
  have hconstantAbsPos : 0 < |constant| := abs_pos.mpr hconstant
  have hboundPos : 0 < bound := by
    dsimp only [bound]
    exact mul_pos (div_pos hsourceBoundPos hconstantAbsPos)
      hgeometricBoundPos
  refine ⟨bound, hboundPos, fun index shift => ?_⟩
  have hbase := shiftedCoefficientRatio_le_polynomial_geometric
    hsourceBound hsourceBoundPos.le hconstant hgrowthPos hexponent index shift
  have hgeom := hgeometricBound shift
  calc
    ‖shiftedCoefficientRatio source
        (powerExponentialTerm constant growth exponent) shift index‖ ≤
      (sourceBound / |constant|) * (growth⁻¹) ^ shift *
        ((shift + 1 : ℕ) : ℝ) ^ exponent := hbase
    _ = (sourceBound / |constant|) *
        (((shift + 1 : ℕ) : ℝ) ^ exponent * (growth⁻¹) ^ shift) := by ring
    _ ≤ (sourceBound / |constant|) *
        (geometricBound * radius ^ shift) := by
          exact mul_le_mul_of_nonneg_left hgeom
            (div_nonneg hsourceBoundPos.le (abs_nonneg _))
    _ = bound * radius ^ shift := by
      dsimp only [bound]
      ring

end FibonacciRibbonKernel
