import FibonacciRibbonKernel.ShiftedRatioEnvelope

namespace FibonacciRibbonKernel

open Filter Asymptotics

/-!
# Complete analytic-multiplier convolution transfer

Combining the fixed-shift limit, the global shift envelope, and Tannery's
theorem yields a reusable coefficient-transfer theorem.  All hypotheses are
literal coefficient statements; no analytic-transfer theorem is assumed.
-/

theorem weightedShiftedConvolutionRatio_tendsto_multiplier
    {carrier : Type*} (weight : carrier → ℝ) (shift : carrier → ℕ)
    {source : ℕ → ℝ} {constant growth exponent radius multiplierValue : ℝ}
    (hsource : source ~[atTop]
      powerExponentialTerm constant growth exponent)
    (hconstant : constant ≠ 0) (hgrowth : 1 < growth)
    (hexponent : 0 < exponent) (hradius : growth⁻¹ < radius)
    (hweighted : HasSum
      (fun point : carrier => weight point * (growth⁻¹) ^ shift point)
      multiplierValue)
    (habsolute : Summable
      (fun point : carrier => |weight point| * radius ^ shift point)) :
    Tendsto
      (weightedShiftedConvolutionRatio weight shift source
        (powerExponentialTerm constant growth exponent))
      atTop (nhds multiplierValue) := by
  obtain ⟨ratioBound, hratioBoundPos, hratioBound⟩ :=
    exists_shiftedCoefficientRatio_geometric_bound hsource hconstant
      hgrowth hexponent hradius
  have hpoint : ∀ point : carrier,
      Tendsto
        (shiftedCoefficientRatio source
          (powerExponentialTerm constant growth exponent) (shift point))
        atTop (nhds ((growth⁻¹) ^ shift point)) := by
    intro point
    exact shiftedCoefficientRatio_tendsto_of_isEquivalent
      hsource hconstant (one_pos.trans hgrowth) (shift point)
  have hboundSummable : Summable (fun point : carrier =>
      |weight point| * (ratioBound * radius ^ shift point)) := by
    have hscaled := habsolute.mul_right ratioBound
    apply hscaled.congr
    intro point
    ring
  have hbound : ∀ᶠ index : ℕ in atTop, ∀ point : carrier,
      ‖shiftedCoefficientRatio source
          (powerExponentialTerm constant growth exponent) (shift point) index‖ ≤
        ratioBound * radius ^ shift point := by
    exact Filter.Eventually.of_forall fun index point =>
      hratioBound index (shift point)
  have hlimit := tendsto_weightedShiftedConvolutionRatio
    weight shift source (powerExponentialTerm constant growth exponent)
    (fun point => (growth⁻¹) ^ shift point)
    (fun point => ratioBound * radius ^ shift point)
    hpoint hboundSummable hbound
  rw [hweighted.tsum_eq] at hlimit
  exact hlimit

noncomputable def scaledWeightedShiftedConvolution
    {carrier : Type*} (weight : carrier → ℝ) (shift : carrier → ℕ)
    (source comparison : ℕ → ℝ) (index : ℕ) : ℝ :=
  comparison index *
    weightedShiftedConvolutionRatio weight shift source comparison index

theorem scaledWeightedShiftedConvolution_isEquivalent
    {carrier : Type*} (weight : carrier → ℝ) (shift : carrier → ℕ)
    {source : ℕ → ℝ} {constant growth exponent radius multiplierValue : ℝ}
    (hsource : source ~[atTop]
      powerExponentialTerm constant growth exponent)
    (hconstant : constant ≠ 0) (hgrowth : 1 < growth)
    (hexponent : 0 < exponent) (hradius : growth⁻¹ < radius)
    (hweighted : HasSum
      (fun point : carrier => weight point * (growth⁻¹) ^ shift point)
      multiplierValue)
    (habsolute : Summable
      (fun point : carrier => |weight point| * radius ^ shift point))
    (hmultiplier : multiplierValue ≠ 0) :
    scaledWeightedShiftedConvolution weight shift source
        (powerExponentialTerm constant growth exponent) ~[atTop]
      (fun index => multiplierValue *
        powerExponentialTerm constant growth exponent index) := by
  have hratio := weightedShiftedConvolutionRatio_tendsto_multiplier
    weight shift hsource hconstant hgrowth hexponent hradius
    hweighted habsolute
  have hratioDiv := hratio.div_const multiplierValue
  norm_num [hmultiplier] at hratioDiv
  have hcomparisonNe : ∀ᶠ index : ℕ in atTop,
      powerExponentialTerm constant growth exponent index ≠ 0 := by
    filter_upwards [eventually_ne_atTop 0] with index hindex
    unfold powerExponentialTerm
    exact mul_ne_zero (mul_ne_zero hconstant
      (pow_ne_zero _ (one_pos.trans hgrowth).ne'))
      (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hdenominatorNe : ∀ᶠ index : ℕ in atTop,
      multiplierValue * powerExponentialTerm constant growth exponent index ≠ 0 := by
    filter_upwards [hcomparisonNe] with index hindex
    exact mul_ne_zero hmultiplier hindex
  rw [isEquivalent_iff_tendsto_one hdenominatorNe]
  apply hratioDiv.congr'
  filter_upwards [hcomparisonNe] with index hindex
  change weightedShiftedConvolutionRatio weight shift source
      (powerExponentialTerm constant growth exponent) index / multiplierValue =
    (powerExponentialTerm constant growth exponent index *
      weightedShiftedConvolutionRatio weight shift source
        (powerExponentialTerm constant growth exponent) index) /
      (multiplierValue * powerExponentialTerm constant growth exponent index)
  field_simp [hindex, hmultiplier]

end FibonacciRibbonKernel
