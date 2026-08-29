import FibonacciRibbonKernel.FibonacciCosineScalePointwise

namespace FibonacciRibbonKernel

open Filter

theorem tendsto_variable_pow_zero
    {sequence : ℕ → ℝ} {limit : ℝ}
    (hsequence : Tendsto sequence atTop (nhds limit))
    (hlimitNonneg : 0 ≤ limit) (hlimitLt : limit < 1)
    (hsequenceNonneg : ∀ᶠ index : ℕ in atTop, 0 ≤ sequence index) :
    Tendsto (fun index : ℕ => sequence index ^ (index + 1))
      atTop (nhds 0) := by
  let bound : ℝ := (limit + 1) / 2
  have hlimitBound : limit < bound := by
    dsimp only [bound]
    linarith
  have hboundNonneg : 0 ≤ bound := by
    dsimp only [bound]
    linarith
  have hboundLt : bound < 1 := by
    dsimp only [bound]
    linarith
  have hsequenceBound : ∀ᶠ index : ℕ in atTop,
      sequence index < bound :=
    (tendsto_order.1 hsequence).2 bound hlimitBound
  have hboundPow : Tendsto (fun index : ℕ => bound ^ (index + 1))
      atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hboundNonneg hboundLt).comp
      (tendsto_add_atTop_nat 1)
  have hpowNonneg : ∀ᶠ index : ℕ in atTop,
      0 ≤ sequence index ^ (index + 1) :=
    hsequenceNonneg.mono fun index hnonneg => pow_nonneg hnonneg _
  apply squeeze_zero' hpowNonneg
  · filter_upwards [hsequenceNonneg, hsequenceBound] with index hnonneg hbound
    exact pow_le_pow_left₀ hnonneg hbound.le (index + 1)
  · exact hboundPow

end FibonacciRibbonKernel
