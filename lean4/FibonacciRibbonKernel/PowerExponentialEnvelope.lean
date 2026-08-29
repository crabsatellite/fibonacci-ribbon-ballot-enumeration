import FibonacciRibbonKernel.PolynomialGeometricBound

namespace FibonacciRibbonKernel

open Filter Asymptotics

/-!
# A global envelope from asymptotic equivalence

Asymptotic equivalence supplies a large-index bound.  This file absorbs the
finite prefix into one explicit finite sum and obtains a bound valid at every
index.  The regularized index `max 1 n` avoids inserting a false nonzero value
at `n=0` into the manuscript leading term.
-/

def regularizedIndex (index : ℕ) : ℕ := max 1 index

noncomputable def powerExponentialEnvelope
    (growth exponent : ℝ) (index : ℕ) : ℝ :=
  growth ^ index * (regularizedIndex index : ℝ) ^ (-exponent)

theorem powerExponentialEnvelope_pos
    {growth : ℝ} (hgrowth : 0 < growth) (exponent : ℝ) (index : ℕ) :
    0 < powerExponentialEnvelope growth exponent index := by
  unfold powerExponentialEnvelope regularizedIndex
  exact mul_pos (pow_pos hgrowth _) (Real.rpow_pos_of_pos (by positivity) _)

theorem exists_global_powerExponentialEnvelope
    {source : ℕ → ℝ} {constant growth exponent : ℝ}
    (hsource : source ~[atTop]
      powerExponentialTerm constant growth exponent)
    (hgrowth : 0 < growth) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ index : ℕ,
      |source index| ≤ bound *
        powerExponentialEnvelope growth exponent index := by
  rcases hsource.isBigO.exists_pos with ⟨asymptoticBound,
    hasymptoticBoundPos, hasymptotic⟩
  have hasymptoticEventually := hasymptotic.bound
  obtain ⟨threshold₀, hthreshold₀⟩ :=
    eventually_atTop.1 hasymptoticEventually
  let threshold := max threshold₀ 1
  let prefixBound : ℝ :=
    ∑ index ∈ Finset.range threshold,
      |source index| / powerExponentialEnvelope growth exponent index
  let bound := asymptoticBound * |constant| + prefixBound + 1
  have hprefixNonneg : 0 ≤ prefixBound := by
    dsimp only [prefixBound]
    apply Finset.sum_nonneg
    intro index _
    exact div_nonneg (abs_nonneg _)
      (powerExponentialEnvelope_pos hgrowth exponent index).le
  have hboundPos : 0 < bound := by
    dsimp only [bound]
    have hleft : 0 ≤ asymptoticBound * |constant| := by positivity
    linarith
  refine ⟨bound, hboundPos, fun index => ?_⟩
  by_cases hlarge : threshold ≤ index
  · have hthreshold₀Index : threshold₀ ≤ index :=
      (le_max_left _ _).trans hlarge
    have honeIndex : 1 ≤ index := (le_max_right _ _).trans hlarge
    have hasymptoticIndex := hthreshold₀ index hthreshold₀Index
    have hindexPos : (0 : ℝ) < index := by positivity
    have hgrowthPowPos : 0 < growth ^ index := pow_pos hgrowth _
    have hrpowPos : 0 < (index : ℝ) ^ (-exponent) :=
      Real.rpow_pos_of_pos hindexPos _
    have hnormComparison :
        ‖powerExponentialTerm constant growth exponent index‖ =
          |constant| * powerExponentialEnvelope growth exponent index := by
      unfold powerExponentialTerm powerExponentialEnvelope regularizedIndex
      rw [max_eq_right honeIndex]
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos hgrowthPowPos, abs_of_pos hrpowPos]
      ring
    rw [Real.norm_eq_abs, hnormComparison] at hasymptoticIndex
    calc
      |source index| ≤ asymptoticBound *
          (|constant| * powerExponentialEnvelope growth exponent index) :=
        hasymptoticIndex
      _ = (asymptoticBound * |constant|) *
          powerExponentialEnvelope growth exponent index := by ring
      _ ≤ bound * powerExponentialEnvelope growth exponent index := by
        apply mul_le_mul_of_nonneg_right _
          (powerExponentialEnvelope_pos hgrowth exponent index).le
        dsimp only [bound]
        linarith
  · have hsmall : index < threshold := by omega
    have henvelopePos := powerExponentialEnvelope_pos hgrowth exponent index
    have htermNonneg : ∀ value ∈ Finset.range threshold,
        0 ≤ |source value| /
          powerExponentialEnvelope growth exponent value := by
      intro value _
      exact div_nonneg (abs_nonneg _) (powerExponentialEnvelope_pos
        hgrowth exponent value).le
    have hsingle :
        |source index| / powerExponentialEnvelope growth exponent index ≤
          prefixBound := by
      dsimp only [prefixBound]
      exact Finset.single_le_sum htermNonneg (Finset.mem_range.mpr hsmall)
    have hprefixBound : prefixBound ≤ bound := by
      dsimp only [bound]
      have hleft : 0 ≤ asymptoticBound * |constant| := by positivity
      linarith
    have hratio :
        |source index| / powerExponentialEnvelope growth exponent index ≤
          bound := hsingle.trans hprefixBound
    exact (div_le_iff₀ henvelopePos).mp hratio

end FibonacciRibbonKernel
