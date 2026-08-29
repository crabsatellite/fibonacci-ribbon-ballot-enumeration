import FibonacciRibbonKernel.RibbonModelConvolutionTransfer

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators

/-!
# Exact coefficient carrier for the ribbon multiplier

The analytic multiplier is converted back to literal power-series
coefficients.  The resulting finite pair sum uses the exact degree shift
`i+2j` and is the same carrier consumed by the Tannery transfer.
-/

noncomputable def ribbonFinitePairConvolution
    (source : ℕ → ℝ) (parameter rho : ℝ) (index : ℕ) : ℝ :=
  ∑ first ∈ Finset.range (index + 1),
    ∑ second ∈ Finset.range (index + 1),
      if ribbonMultiplierPairShift (first, second) ≤ index then
        ribbonMultiplierPairCoefficient parameter rho (first, second) *
          source (index - ribbonMultiplierPairShift (first, second))
      else 0

theorem coeff_mul_subst_X_sq
    (source denominator : ℝ⟦X⟧) (index : ℕ) :
    PowerSeries.coeff index
        (source * PowerSeries.subst (PowerSeries.X ^ 2) denominator) =
      ∑ halfDegree ∈ Finset.range (index + 1),
        if 2 * halfDegree ≤ index then
          PowerSeries.coeff (index - 2 * halfDegree) source *
            PowerSeries.coeff halfDegree denominator
        else 0 := by
  calc
    PowerSeries.coeff index
        (source * PowerSeries.subst (PowerSeries.X ^ 2) denominator) =
      ∑ degree ∈ Finset.range (index + 1),
        PowerSeries.coeff degree
            (PowerSeries.subst (PowerSeries.X ^ 2) denominator) *
          PowerSeries.coeff (index - degree) source := by
            rw [mul_comm, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = ∑ degree ∈ Finset.range (index + 1),
        if 2 ∣ degree then
          PowerSeries.coeff (degree / 2) denominator *
            PowerSeries.coeff (index - degree) source
        else 0 := by
          apply Finset.sum_congr rfl
          intro degree hdegree
          rw [PowerSeries.coeff_subst_X_pow (by omega)]
          split_ifs <;> simp
    _ = ∑ degree ∈ (Finset.range (index + 1)).filter (fun degree => 2 ∣ degree),
        PowerSeries.coeff (degree / 2) denominator *
          PowerSeries.coeff (index - degree) source := by
          rw [Finset.sum_filter]
    _ = ∑ halfDegree ∈
        (Finset.range (index + 1)).filter (fun halfDegree => 2 * halfDegree ≤ index),
        PowerSeries.coeff halfDegree denominator *
          PowerSeries.coeff (index - 2 * halfDegree) source := by
          apply Finset.sum_bij (fun degree _ => degree / 2)
          · intro degree hdegree
            simp only [Finset.mem_filter, Finset.mem_range] at hdegree ⊢
            obtain ⟨halfDegree, hhalfDegree⟩ := hdegree.2
            constructor <;> omega
          · intro left hleft right hright heq
            simp only [Finset.mem_filter, Finset.mem_range] at hleft hright
            obtain ⟨leftHalf, hleftHalf⟩ := hleft.2
            obtain ⟨rightHalf, hrightHalf⟩ := hright.2
            omega
          · intro halfDegree hhalfDegree
            simp only [Finset.mem_filter, Finset.mem_range] at hhalfDegree
            let degree := 2 * halfDegree
            have hdegree : degree ∈
                (Finset.range (index + 1)).filter (fun degree => 2 ∣ degree) := by
              simp only [Finset.mem_filter, Finset.mem_range, degree]
              constructor
              · omega
              · exact ⟨halfDegree, by omega⟩
            refine ⟨degree, hdegree, ?_⟩
            dsimp only [degree]
            omega
          · intro degree hdegree
            simp only [Finset.mem_filter, Finset.mem_range] at hdegree
            obtain ⟨halfDegree, hhalfDegree⟩ := hdegree.2
            rw [show degree / 2 = halfDegree by omega,
              show 2 * halfDegree = degree by omega]
    _ = ∑ halfDegree ∈ Finset.range (index + 1),
        if 2 * halfDegree ≤ index then
          PowerSeries.coeff (index - 2 * halfDegree) source *
            PowerSeries.coeff halfDegree denominator
        else 0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro halfDegree hhalfDegree
          split_ifs <;> ring

theorem coeff_mul_ribbonSingularAnalyticMultiplier
    (source : ℝ⟦X⟧) (parameter rho : ℝ) (index : ℕ) :
    PowerSeries.coeff index
        (source *
          (rescaledBinomialSeries parameter rho *
            PowerSeries.subst (PowerSeries.X ^ 2)
              (PowerSeries.binomialSeries ℝ (-(parameter + 1))))) =
      ribbonFinitePairConvolution
        (fun degree => PowerSeries.coeff degree source)
        parameter rho index := by
  rw [← mul_assoc]
  rw [coeff_mul_subst_X_sq]
  unfold ribbonFinitePairConvolution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro second hsecond
  by_cases hsecondBound : 2 * second ≤ index
  · rw [if_pos hsecondBound]
    rw [show source * rescaledBinomialSeries parameter rho =
        rescaledBinomialSeries parameter rho * source by ring]
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [PowerSeries.binomialSeries_coeff]
    simp only [smul_eq_mul, mul_one]
    rw [Finset.sum_mul]
    calc
      ∑ first ∈ Finset.range (index - 2 * second + 1),
          PowerSeries.coeff first (rescaledBinomialSeries parameter rho) *
              PowerSeries.coeff (index - 2 * second - first) source *
            Ring.choose (-(parameter + 1)) second =
        ∑ first ∈ Finset.range (index - 2 * second + 1),
          ribbonMultiplierPairCoefficient parameter rho (first, second) *
            PowerSeries.coeff
              (index - ribbonMultiplierPairShift (first, second)) source := by
                apply Finset.sum_congr rfl
                intro first hfirst
                simp only [Finset.mem_range] at hfirst
                unfold ribbonMultiplierPairCoefficient ribbonMultiplierPairShift
                rw [show index - (first + 2 * second) =
                    index - 2 * second - first by omega]
                ring
      _ = ∑ first ∈ (Finset.range (index + 1)).filter
            (fun first => ribbonMultiplierPairShift (first, second) ≤ index),
          ribbonMultiplierPairCoefficient parameter rho (first, second) *
            PowerSeries.coeff
              (index - ribbonMultiplierPairShift (first, second)) source := by
                congr 1
                ext first
                simp only [Finset.mem_filter, Finset.mem_range]
                unfold ribbonMultiplierPairShift
                omega
      _ = ∑ first ∈ Finset.range (index + 1),
          if ribbonMultiplierPairShift (first, second) ≤ index then
            ribbonMultiplierPairCoefficient parameter rho (first, second) *
              PowerSeries.coeff
                (index - ribbonMultiplierPairShift (first, second)) source
          else 0 := by
            rw [Finset.sum_filter]
  · rw [if_neg hsecondBound]
    symm
    apply Finset.sum_eq_zero
    intro first hfirst
    rw [if_neg]
    unfold ribbonMultiplierPairShift
    omega

theorem coeff_model_mul_ribbonMultiplier
    (source : ℝ⟦X⟧) (parameter : ℝ)
    (alphabetSize index : ℕ) :
    PowerSeries.coeff index
        (source * ribbonSingularAnalyticMultiplier parameter alphabetSize) =
      ribbonFinitePairConvolution
        (fun degree => PowerSeries.coeff degree source)
        parameter (fixedRankPreimage alphabetSize) index := by
  rw [ribbonSingularAnalyticMultiplier_explicit]
  exact coeff_mul_ribbonSingularAnalyticMultiplier source parameter
    (fixedRankPreimage alphabetSize) index

theorem scaledRibbonPairConvolution_eq_finite
    (source comparison : ℕ → ℝ) (parameter rho : ℝ)
    (index : ℕ) (hcomparison : comparison index ≠ 0) :
    scaledWeightedShiftedConvolution
        (ribbonMultiplierPairCoefficient parameter rho)
        ribbonMultiplierPairShift source comparison index =
      ribbonFinitePairConvolution source parameter rho index := by
  let rectangle : Finset (ℕ × ℕ) :=
    (Finset.range (index + 1)).product (Finset.range (index + 1))
  have hfinite :
      weightedShiftedConvolutionRatio
          (ribbonMultiplierPairCoefficient parameter rho)
          ribbonMultiplierPairShift source comparison index =
        ∑ pair ∈ rectangle,
          ribbonMultiplierPairCoefficient parameter rho pair *
            shiftedCoefficientRatio source comparison
              (ribbonMultiplierPairShift pair) index := by
    unfold weightedShiftedConvolutionRatio
    rw [tsum_eq_sum (s := rectangle)]
    intro pair hpair
    have hshift : ¬ribbonMultiplierPairShift pair ≤ index := by
      intro hshift
      apply hpair
      unfold rectangle
      apply Finset.mem_product.mpr
      unfold ribbonMultiplierPairShift at hshift
      constructor <;> rw [Finset.mem_range] <;> omega
    unfold shiftedCoefficientRatio
    rw [if_neg hshift, mul_zero]
  unfold scaledWeightedShiftedConvolution
  rw [hfinite, Finset.mul_sum]
  unfold rectangle ribbonFinitePairConvolution
  change (∑ pair ∈
      (Finset.range (index + 1) ×ˢ Finset.range (index + 1)),
        comparison index *
          (ribbonMultiplierPairCoefficient parameter rho pair *
            shiftedCoefficientRatio source comparison
              (ribbonMultiplierPairShift pair) index)) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro first hfirst
  apply Finset.sum_congr rfl
  intro second hsecond
  unfold shiftedCoefficientRatio
  by_cases hshift : ribbonMultiplierPairShift (first, second) ≤ index
  · rw [if_pos hshift, if_pos hshift]
    field_simp [hcomparison]
  · rw [if_neg hshift, if_neg hshift]
    ring

end FibonacciRibbonKernel
