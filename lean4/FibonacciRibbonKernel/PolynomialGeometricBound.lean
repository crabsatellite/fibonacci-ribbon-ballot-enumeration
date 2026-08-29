import FibonacciRibbonKernel.PowerExponentialShift
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Group.Bounded

namespace FibonacciRibbonKernel

open Filter

/-!
# Uniform absorption of polynomial factors by a larger geometric radius

This is the uniform domination needed by the Tannery step.  Any fixed real
power of `n+1`, multiplied by `c^n` with `0<c<1`, is globally bounded.
-/

theorem tendsto_succ_rpow_mul_const_pow_zero
    (exponent : ℝ) {ratio : ℝ} (hratioPos : 0 < ratio)
    (hratioLt : ratio < 1) :
    Tendsto (fun index : ℕ =>
      ((index + 1 : ℕ) : ℝ) ^ exponent * ratio ^ index)
      atTop (nhds 0) := by
  let decay := -Real.log ratio
  have hlogNeg : Real.log ratio < 0 :=
    Real.log_neg hratioPos hratioLt
  have hdecay : 0 < decay := by
    dsimp only [decay]
    linarith
  have hreal := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    exponent decay hdecay
  have hnatTop : Tendsto (fun index : ℕ => ((index : ℝ) + 1))
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hcomposed := hreal.comp hnatTop
  have hconst : Tendsto (fun _index : ℕ => Real.exp decay)
      atTop (nhds (Real.exp decay)) := tendsto_const_nhds
  have hscaled := hconst.mul hcomposed
  norm_num at hscaled
  apply hscaled.congr'
  filter_upwards with index
  have hexpIdentity :
      Real.exp decay * Real.exp (-(decay * ((index : ℝ) + 1))) =
        ratio ^ index := by
    rw [← Real.exp_add]
    have harg : decay + -(decay * ((index : ℝ) + 1)) =
        (index : ℝ) * Real.log ratio := by
      dsimp only [decay]
      ring
    rw [harg, Real.exp_nat_mul, Real.exp_log hratioPos]
  push_cast
  calc
    Real.exp decay *
        (((index : ℝ) + 1) ^ exponent *
          Real.exp (-(decay * ((index : ℝ) + 1)))) =
      ((index : ℝ) + 1) ^ exponent *
        (Real.exp decay * Real.exp (-(decay * ((index : ℝ) + 1)))) := by ring
    _ = ((index : ℝ) + 1) ^ exponent * ratio ^ index := by
      rw [hexpIdentity]

theorem exists_global_succ_rpow_mul_const_pow_bound
    (exponent : ℝ) {ratio : ℝ} (hratioPos : 0 < ratio)
    (hratioLt : ratio < 1) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ index : ℕ,
      ((index + 1 : ℕ) : ℝ) ^ exponent * ratio ^ index ≤ bound := by
  have hlimit := tendsto_succ_rpow_mul_const_pow_zero
    exponent hratioPos hratioLt
  have hbounded := Metric.isBounded_range_of_tendsto
    (fun index : ℕ => ((index + 1 : ℕ) : ℝ) ^ exponent * ratio ^ index)
    hlimit
  obtain ⟨bound, hboundPos, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨bound, hboundPos, fun index => ?_⟩
  have hmem :
      ((index + 1 : ℕ) : ℝ) ^ exponent * ratio ^ index ∈
        Set.range (fun index : ℕ =>
          ((index + 1 : ℕ) : ℝ) ^ exponent * ratio ^ index) :=
    ⟨index, rfl⟩
  have hnorm := hbound _ hmem
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (pow_nonneg hratioPos.le _))] at hnorm
  exact hnorm

theorem exists_polynomial_geometric_comparison
    (exponent : ℝ) {small large : ℝ}
    (hsmall : 0 < small) (hlarge : small < large) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ index : ℕ,
      ((index + 1 : ℕ) : ℝ) ^ exponent * small ^ index ≤
        bound * large ^ index := by
  have hlargePos : 0 < large := hsmall.trans hlarge
  have hratioPos : 0 < small / large := div_pos hsmall hlargePos
  have hratioLt : small / large < 1 := (div_lt_one hlargePos).2 hlarge
  obtain ⟨bound, hboundPos, hbound⟩ :=
    exists_global_succ_rpow_mul_const_pow_bound
      exponent hratioPos hratioLt
  refine ⟨bound, hboundPos, fun index => ?_⟩
  have hlargePowPos : 0 < large ^ index := pow_pos hlargePos _
  have h := mul_le_mul_of_nonneg_right (hbound index) hlargePowPos.le
  have hratioPow : (small / large) ^ index * large ^ index =
      small ^ index := by
    rw [div_pow]
    field_simp [pow_ne_zero index hlargePos.ne']
  rw [mul_assoc, hratioPow] at h
  simpa [mul_assoc] using h

end FibonacciRibbonKernel
