import FibonacciRibbonKernel.WeightedShiftedConvolution
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace FibonacciRibbonKernel

open Filter Asymptotics

/-!
# Fixed shifts of power--exponential leading terms

This file proves the pointwise input for Tannery transfer: a fixed coefficient
shift of `C alpha^n n^{-beta}` has normalized limit `alpha^{-shift}`.
-/

noncomputable def powerExponentialTerm
    (constant growth exponent : ℝ) (index : ℕ) : ℝ :=
  constant * growth ^ index * (index : ℝ) ^ (-exponent)

theorem natSubCast_div_cast_tendsto_one (shift : ℕ) :
    Tendsto (fun index : ℕ =>
      ((index - shift : ℕ) : ℝ) / (index : ℝ))
      atTop (nhds 1) := by
  rw [← tendsto_add_atTop_iff_nat shift]
  have hlimit := tendsto_natCast_div_add_atTop (shift : ℝ)
  convert hlimit using 1
  funext index
  rw [Nat.add_sub_cancel]
  push_cast
  rfl

theorem natSubCast_div_cast_rpow_tendsto_one
    (shift : ℕ) (exponent : ℝ) :
    Tendsto (fun index : ℕ =>
      (((index - shift : ℕ) : ℝ) / (index : ℝ)) ^ (-exponent))
      atTop (nhds 1) := by
  have hcontinuous : ContinuousAt
      (fun value : ℝ => value ^ (-exponent)) 1 :=
    Real.continuousAt_rpow_const 1 (-exponent) (Or.inl one_ne_zero)
  have hlimit := hcontinuous.tendsto.comp
    (natSubCast_div_cast_tendsto_one shift)
  norm_num at hlimit
  exact hlimit

theorem powerExponentialTerm_shift_ratio_eventually_eq
    {constant growth : ℝ} (exponent : ℝ)
    (hconstant : constant ≠ 0) (hgrowth : 0 < growth)
    (shift : ℕ) :
    ∀ᶠ index : ℕ in atTop,
      powerExponentialTerm constant growth exponent (index - shift) /
          powerExponentialTerm constant growth exponent index =
        (growth⁻¹) ^ shift *
          (((index - shift : ℕ) : ℝ) / (index : ℝ)) ^ (-exponent) := by
  filter_upwards [eventually_ge_atTop (shift + 1)] with index hindex
  have hshift : shift ≤ index := by omega
  have hindexNatNe : index ≠ 0 := by omega
  have hindexNe : (index : ℝ) ≠ 0 := by exact_mod_cast hindexNatNe
  have hsubNatNe : index - shift ≠ 0 := by omega
  have hsubNe : ((index - shift : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hsubNatNe
  have hgrowthNe : growth ≠ 0 := hgrowth.ne'
  have hgrowthPow : growth ^ index =
      growth ^ (index - shift) * growth ^ shift := by
    nth_rw 1 [show index = (index - shift) + shift by omega]
    rw [pow_add]
  have hrpowDiv :
      (((index - shift : ℕ) : ℝ) / (index : ℝ)) ^ (-exponent) =
        ((index - shift : ℕ) : ℝ) ^ (-exponent) /
          (index : ℝ) ^ (-exponent) :=
    Real.div_rpow (by positivity) (by positivity) _
  unfold powerExponentialTerm
  rw [hrpowDiv, hgrowthPow]
  field_simp [hconstant, hgrowthNe, hindexNe, hsubNe]
  rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero shift hgrowthNe)]

theorem powerExponentialTerm_shift_ratio_tendsto
    {constant growth : ℝ} (exponent : ℝ)
    (hconstant : constant ≠ 0) (hgrowth : 0 < growth)
    (shift : ℕ) :
    Tendsto (fun index : ℕ =>
      powerExponentialTerm constant growth exponent (index - shift) /
        powerExponentialTerm constant growth exponent index)
      atTop (nhds ((growth⁻¹) ^ shift)) := by
  have hlimit :=
    (natSubCast_div_cast_rpow_tendsto_one shift exponent).const_mul
      ((growth⁻¹) ^ shift)
  have heq := powerExponentialTerm_shift_ratio_eventually_eq exponent
    hconstant hgrowth shift
  have heqSymm :
      (fun index : ℕ => (growth⁻¹) ^ shift *
          (((index - shift : ℕ) : ℝ) / (index : ℝ)) ^ (-exponent)) =ᶠ[atTop]
        (fun index : ℕ =>
          powerExponentialTerm constant growth exponent (index - shift) /
            powerExponentialTerm constant growth exponent index) := by
    filter_upwards [heq] with index hindex
    exact hindex.symm
  simpa using hlimit.congr' heqSymm

theorem shiftedCoefficientRatio_tendsto_of_isEquivalent
    {source : ℕ → ℝ} {constant growth exponent : ℝ}
    (hsource : source ~[atTop]
      powerExponentialTerm constant growth exponent)
    (hconstant : constant ≠ 0) (hgrowth : 0 < growth)
    (shift : ℕ) :
    Tendsto
      (shiftedCoefficientRatio source
        (powerExponentialTerm constant growth exponent) shift)
      atTop (nhds ((growth⁻¹) ^ shift)) := by
  have hcomparisonNe : ∀ᶠ index : ℕ in atTop,
      powerExponentialTerm constant growth exponent index ≠ 0 := by
    filter_upwards [eventually_ne_atTop 0] with index hindex
    unfold powerExponentialTerm
    exact mul_ne_zero (mul_ne_zero hconstant (pow_ne_zero _ hgrowth.ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hsourceRatio :=
    (isEquivalent_iff_tendsto_one hcomparisonNe).mp hsource
  have hsourceShift := hsourceRatio.comp
    (tendsto_sub_atTop_nat shift)
  have hcomparisonShift := powerExponentialTerm_shift_ratio_tendsto
    exponent hconstant hgrowth shift
  have hproduct := hsourceShift.mul hcomparisonShift
  norm_num at hproduct
  have hcomparisonSubNe : ∀ᶠ index : ℕ in atTop,
      powerExponentialTerm constant growth exponent (index - shift) ≠ 0 :=
    (tendsto_sub_atTop_nat shift).eventually hcomparisonNe
  rw [inv_pow]
  apply hproduct.congr'
  filter_upwards [eventually_ge_atTop shift, hcomparisonNe,
    hcomparisonSubNe] with index hindex hne hsubNe
  unfold shiftedCoefficientRatio
  rw [if_pos hindex]
  field_simp [hne, hsubNe]

end FibonacciRibbonKernel
