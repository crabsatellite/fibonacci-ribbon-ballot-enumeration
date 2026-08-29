import FibonacciRibbonKernel.SelbergMehtaIntegralIdentity
import FibonacciRibbonKernel.CatalanAsymptotic

namespace FibonacciRibbonKernel

open Filter Asymptotics
open scoped Classical Topology BigOperators

theorem gamma_nat_add_half_formula (index : ℕ) :
    Real.Gamma ((index : ℝ) + 1 / 2) =
      (index * 2).factorial * Real.sqrt Real.pi /
        ((4 : ℝ) ^ index * index.factorial) := by
  induction index with
  | zero =>
      norm_num [Real.Gamma_one_half_eq]
  | succ index ih =>
      rw [show (((index + 1 : ℕ) : ℝ)) + 1 / 2 =
          ((index : ℝ) + 1 / 2) + 1 by push_cast; ring]
      rw [Real.Gamma_add_one (by positivity)]
      rw [ih]
      rw [show (index + 1) * 2 = (index * 2 + 1) + 1 by omega]
      rw [Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
      ring

theorem centralBinomial_cast_formula (index : ℕ) :
    (Nat.centralBinom index : ℝ) =
      ((2 * index).factorial : ℝ) / (index.factorial : ℝ) ^ 2 := by
  rw [Nat.centralBinom_eq_two_mul_choose,
    Nat.cast_choose ℝ (by omega)]
  rw [show 2 * index - index = index by omega]
  ring

noncomputable def gammaHalfStepRatio (index : ℕ) : ℝ :=
  Real.sqrt (index : ℝ) * Real.Gamma (index : ℝ) /
    Real.Gamma ((index : ℝ) + 1 / 2)

theorem gammaHalfStepRatio_eq_central (index : ℕ)
    (hindex : 0 < index) :
    gammaHalfStepRatio index =
      centralBinomialLeadingTerm index / (Nat.centralBinom index : ℝ) := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hindex.ne'
  have hgammaNat : Real.Gamma ((predecessor + 1 : ℕ) : ℝ) =
      predecessor.factorial := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Real.Gamma_nat_eq_factorial predecessor
  have hgammaHalf := gamma_nat_add_half_formula (predecessor + 1)
  have hcentral := centralBinomial_cast_formula (predecessor + 1)
  have hfactorial : (predecessor.factorial : ℝ) ≠ 0 := by positivity
  have hfactorialSucc : ((predecessor + 1).factorial : ℝ) ≠ 0 := by
    positivity
  have hdouble : (((2 * (predecessor + 1)).factorial : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hsqrtIndex : Real.sqrt ((predecessor + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrtProduct :
      Real.sqrt (Real.pi * ((predecessor + 1 : ℕ) : ℝ)) =
        Real.sqrt Real.pi * Real.sqrt ((predecessor + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi)]
  have hsquare' :
      Real.sqrt ((predecessor : ℝ) + 1) ^ 2 =
        (predecessor : ℝ) + 1 := by
    rw [Real.sq_sqrt]
    positivity
  unfold gammaHalfStepRatio centralBinomialLeadingTerm
  rw [hgammaNat, hgammaHalf, hcentral, hsqrtProduct]
  rw [Nat.factorial_succ]
  push_cast
  field_simp [hfactorial, hfactorialSucc, hdouble,
    hsqrtIndex, hsqrtPi]
  rw [hsquare']
  rw [Nat.mul_comm (predecessor + 1) 2]

theorem tendsto_gammaHalfStepRatio :
    Tendsto gammaHalfStepRatio atTop (nhds 1) := by
  have hcentralNe : ∀ᶠ index : ℕ in atTop,
      (Nat.centralBinom index : ℝ) ≠ 0 :=
    Filter.Eventually.of_forall fun index => by
      exact_mod_cast Nat.centralBinom_ne_zero index
  have hratio := (isEquivalent_iff_tendsto_one hcentralNe).mp
    centralBinomial_isEquivalent_leading.symm
  apply hratio.congr'
  filter_upwards [eventually_ge_atTop 1] with index hindex
  exact (gammaHalfStepRatio_eq_central index hindex).symm

noncomputable def gammaHalfStepRatioReciprocal (index : ℕ) : ℝ :=
  Real.sqrt (index : ℝ) * Real.Gamma ((index : ℝ) + 1 / 2) /
    Real.Gamma ((index : ℝ) + 1)

theorem gammaHalfStepRatioReciprocal_eq_inv (index : ℕ)
    (hindex : 0 < index) :
    gammaHalfStepRatioReciprocal index =
      (gammaHalfStepRatio index)⁻¹ := by
  have hindexReal : (index : ℝ) ≠ 0 := by positivity
  have hgamma : Real.Gamma (index : ℝ) ≠ 0 := by positivity
  have hgammaHalf : Real.Gamma ((index : ℝ) + 1 / 2) ≠ 0 := by
    positivity
  have hsqrt : Real.sqrt (index : ℝ) ≠ 0 := by positivity
  unfold gammaHalfStepRatioReciprocal gammaHalfStepRatio
  rw [Real.Gamma_add_one hindexReal]
  field_simp [hindexReal, hgamma, hgammaHalf, hsqrt]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ index)]

theorem tendsto_gammaHalfStepRatioReciprocal :
    Tendsto gammaHalfStepRatioReciprocal atTop (nhds 1) := by
  have hinverse := tendsto_gammaHalfStepRatio.inv₀ one_ne_zero
  norm_num at hinverse
  apply hinverse.congr'
  filter_upwards [eventually_ge_atTop 1] with index hindex
  exact (gammaHalfStepRatioReciprocal_eq_inv index hindex).symm

noncomputable def gammaHalfOffsetValue (offset index : ℕ) : ℝ :=
  ((index + 2 : ℕ) : ℝ) + (offset : ℝ) / 2

noncomputable def gammaHalfOffsetRatio (offset index : ℕ) : ℝ :=
  Real.sqrt (gammaHalfOffsetValue offset index) *
      Real.Gamma (gammaHalfOffsetValue offset index) /
    Real.Gamma (gammaHalfOffsetValue offset index + 1 / 2)

theorem tendsto_gammaHalfOffsetRatio (offset : ℕ) :
    Tendsto (gammaHalfOffsetRatio offset) atTop (nhds 1) := by
  obtain ⟨half, hoffset | hoffset⟩ := offset.even_or_odd'
  · subst offset
    have hbase := tendsto_gammaHalfStepRatio.comp
      (tendsto_add_atTop_nat (2 + 2 * half / 2))
    apply hbase.congr'
    filter_upwards with index
    unfold gammaHalfOffsetRatio gammaHalfOffsetValue gammaHalfStepRatio
    push_cast
    norm_num
    congr 3 <;> ring
  · subst offset
    let shifted : ℕ → ℕ := fun index => index + 2 + half
    have hshifted : Tendsto shifted atTop atTop := by
      simpa [shifted, Nat.add_assoc] using
        tendsto_add_atTop_nat (2 + half)
    have hreciprocal := tendsto_gammaHalfStepRatioReciprocal.comp hshifted
    have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)).comp
      hshifted
    have hsqrtBase : Tendsto (fun index =>
        Real.sqrt (1 + (1 / 2 : ℝ) / (shifted index : ℝ)))
        atTop (nhds 1) := by
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      have hadd := hone.add hsmall
      have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hadd
      change Tendsto ((fun value : ℝ => Real.sqrt value) ∘
        fun index => 1 + (1 / 2 : ℝ) / (shifted index : ℝ))
        atTop (nhds 1)
      simpa only [Function.comp_apply, add_zero, Real.sqrt_one] using hsqrt
    have hproduct := hsqrtBase.mul hreciprocal
    norm_num at hproduct
    apply hproduct.congr'
    filter_upwards with index
    have hshiftPos : 0 < shifted index := by
      dsimp only [shifted]
      omega
    have hshiftReal : (shifted index : ℝ) ≠ 0 := by positivity
    have hgamma : Real.Gamma (shifted index : ℝ) ≠ 0 := by positivity
    have hgammaHalf :
        Real.Gamma ((shifted index : ℝ) + 1 / 2) ≠ 0 := by positivity
    have hsqrtShift : Real.sqrt (shifted index : ℝ) ≠ 0 := by positivity
    unfold gammaHalfOffsetRatio gammaHalfOffsetValue
    unfold gammaHalfStepRatioReciprocal
    dsimp only [shifted]
    push_cast
    rw [show (2 * (half : ℝ) + 1) / 2 =
      (half : ℝ) + 1 / 2 by ring]
    have hargument : (index : ℝ) + 2 + ((half : ℝ) + 1 / 2) =
        (index : ℝ) + 2 + half + 1 / 2 := by ring
    rw [hargument]
    rw [show (index : ℝ) + 2 + half + 1 / 2 + 1 / 2 =
      (index : ℝ) + 2 + half + 1 by ring]
    have hgammaSucc : Real.Gamma ((index : ℝ) + 2 + half + 1) =
        ((index : ℝ) + 2 + half) *
          Real.Gamma ((index : ℝ) + 2 + half) := by
      rw [Real.Gamma_add_one]
      positivity
    rw [hgammaSucc]
    have hsqrtProduct :
        Real.sqrt (1 + (1 / 2 : ℝ) /
            ((index : ℝ) + 2 + half)) *
          Real.sqrt ((index : ℝ) + 2 + half) =
        Real.sqrt ((index : ℝ) + 2 + half + 1 / 2) := by
      rw [← Real.sqrt_mul (by positivity :
        (0 : ℝ) ≤ 1 + (1 / 2 : ℝ) / ((index : ℝ) + 2 + half))]
      congr 1
      field_simp
    rw [← hsqrtProduct]
    field_simp [hshiftReal, hgamma, hgammaHalf, hsqrtShift]

noncomputable def gammaNatShiftRatio
    (offset shift index : ℕ) : ℝ :=
  gammaHalfOffsetValue offset index ^ shift *
      Real.Gamma (gammaHalfOffsetValue offset index) /
    Real.Gamma (gammaHalfOffsetValue offset index + shift)

theorem tendsto_offset_div_offset_add
    (offset : ℝ) (shift : ℕ) :
    Tendsto (fun index : ℕ =>
      ((index : ℝ) + offset) /
        ((index : ℝ) + offset + shift)) atTop (nhds 1) := by
  have hnumZero := tendsto_const_div_atTop_nhds_zero_nat offset
  have hdenZero := tendsto_const_div_atTop_nhds_zero_nat
    (offset + shift)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hnum := hone.add hnumZero
  have hden := hone.add hdenZero
  have hdiv := hnum.div hden (by norm_num : (1 : ℝ) + 0 ≠ 0)
  norm_num at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  change (1 + offset / (index : ℝ)) /
      (1 + (offset + shift) / (index : ℝ)) =
    ((index : ℝ) + offset) / ((index : ℝ) + offset + shift)
  field_simp [hindexReal]
  ring

theorem tendsto_offset_div_offset_add_real
    (offset shift : ℝ) :
    Tendsto (fun index : ℕ =>
      ((index : ℝ) + offset) /
        ((index : ℝ) + offset + shift)) atTop (nhds 1) := by
  have hnumZero := tendsto_const_div_atTop_nhds_zero_nat offset
  have hdenZero := tendsto_const_div_atTop_nhds_zero_nat
    (offset + shift)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hnum := hone.add hnumZero
  have hden := hone.add hdenZero
  have hdiv := hnum.div hden (by norm_num : (1 : ℝ) + 0 ≠ 0)
  norm_num at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_ne_atTop 0] with index hindex
  have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  change (1 + offset / (index : ℝ)) /
      (1 + (offset + shift) / (index : ℝ)) =
    ((index : ℝ) + offset) / ((index : ℝ) + offset + shift)
  field_simp [hindexReal]
  ring

theorem gammaNatShiftRatio_succ
    (offset shift index : ℕ) :
    gammaNatShiftRatio offset (shift + 1) index =
      gammaNatShiftRatio offset shift index *
        (gammaHalfOffsetValue offset index /
          (gammaHalfOffsetValue offset index + shift)) := by
  let value := gammaHalfOffsetValue offset index
  have hvalue : 0 < value := by
    unfold value gammaHalfOffsetValue
    positivity
  have hgamma : Real.Gamma value ≠ 0 := by positivity
  have hgammaShift : Real.Gamma (value + shift) ≠ 0 := by positivity
  have hstep : Real.Gamma (value + (shift + 1 : ℕ)) =
      (value + shift) * Real.Gamma (value + shift) := by
    rw [show value + ((shift + 1 : ℕ) : ℝ) =
      (value + shift) + 1 by push_cast; ring]
    rw [Real.Gamma_add_one]
    positivity
  unfold gammaNatShiftRatio
  dsimp only [value] at hstep hvalue hgamma hgammaShift ⊢
  rw [hstep, pow_succ]
  field_simp [hgamma, hgammaShift]

theorem tendsto_gammaNatShiftRatio (offset shift : ℕ) :
    Tendsto (gammaNatShiftRatio offset shift) atTop (nhds 1) := by
  induction shift with
  | zero =>
      have heq : gammaNatShiftRatio offset 0 = fun _ => 1 := by
        funext index
        unfold gammaNatShiftRatio
        have hgamma : Real.Gamma (gammaHalfOffsetValue offset index) ≠ 0 := by
          exact (Real.Gamma_pos_of_pos (by
            unfold gammaHalfOffsetValue
            positivity)).ne'
        simp [hgamma]
      rw [heq]
      exact tendsto_const_nhds
  | succ shift ih =>
      have hratio := tendsto_offset_div_offset_add
        (2 + (offset : ℝ) / 2) shift
      have hproduct := ih.mul hratio
      norm_num at hproduct
      apply hproduct.congr'
      filter_upwards with index
      rw [gammaNatShiftRatio_succ]
      unfold gammaHalfOffsetValue
      push_cast
      ring

noncomputable def gammaHalfShiftRatio
    (offset halfShift index : ℕ) : ℝ :=
  gammaHalfOffsetValue offset index ^ ((halfShift : ℝ) / 2) *
      Real.Gamma (gammaHalfOffsetValue offset index) /
    Real.Gamma (gammaHalfOffsetValue offset index +
      (halfShift : ℝ) / 2)

theorem gammaHalfShiftRatio_even (offset shift index : ℕ) :
    gammaHalfShiftRatio offset (2 * shift) index =
      gammaNatShiftRatio offset shift index := by
  unfold gammaHalfShiftRatio gammaNatShiftRatio
  rw [show (((2 * shift : ℕ) : ℝ)) / 2 = (shift : ℝ) by
    push_cast; ring]
  rw [Real.rpow_natCast]

theorem gammaHalfShiftRatio_odd (offset shift index : ℕ) :
    gammaHalfShiftRatio offset (2 * shift + 1) index =
      gammaNatShiftRatio offset shift index *
        Real.sqrt (gammaHalfOffsetValue offset index /
          gammaHalfOffsetValue (offset + 2 * shift) index) *
        gammaHalfOffsetRatio (offset + 2 * shift) index := by
  let value := gammaHalfOffsetValue offset index
  let shifted := gammaHalfOffsetValue (offset + 2 * shift) index
  have hvalue : 0 < value := by
    unfold value gammaHalfOffsetValue
    positivity
  have hshifted : 0 < shifted := by
    unfold shifted gammaHalfOffsetValue
    positivity
  have hshiftedEq : shifted = value + shift := by
    unfold shifted value gammaHalfOffsetValue
    push_cast
    ring
  have hgamma : Real.Gamma value ≠ 0 := by positivity
  have hgammaShifted : Real.Gamma shifted ≠ 0 := by positivity
  have hgammaHalf : Real.Gamma (shifted + 1 / 2) ≠ 0 := by positivity
  have hsqrtValue : Real.sqrt value ≠ 0 := by positivity
  have hsqrtShifted : Real.sqrt shifted ≠ 0 := by positivity
  have hsqrtRatio :
      Real.sqrt (value / shifted) * Real.sqrt shifted =
        Real.sqrt value := by
    rw [← Real.sqrt_mul (div_nonneg hvalue.le hshifted.le)]
    congr 1
    field_simp [hshifted.ne']
  have hpower : value ^ ((((2 * shift + 1 : ℕ) : ℝ)) / 2) =
      value ^ shift * Real.sqrt value := by
    rw [show (((2 * shift + 1 : ℕ) : ℝ)) / 2 =
      (shift : ℝ) + 1 / 2 by push_cast; ring]
    rw [Real.rpow_add hvalue, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow]
  change value ^ ((((2 * shift + 1 : ℕ) : ℝ)) / 2) *
        Real.Gamma value /
        Real.Gamma (value + (((2 * shift + 1 : ℕ) : ℝ)) / 2) =
    (value ^ shift * Real.Gamma value /
        Real.Gamma (value + shift)) *
      Real.sqrt (value / shifted) *
      (Real.sqrt shifted * Real.Gamma shifted /
        Real.Gamma (shifted + 1 / 2))
  rw [hpower]
  rw [show (((2 * shift + 1 : ℕ) : ℝ)) / 2 =
    (shift : ℝ) + 1 / 2 by push_cast; ring]
  rw [hshiftedEq]
  have hsqrtRatio' :
      Real.sqrt (value / (value + shift)) *
          Real.sqrt (value + shift) = Real.sqrt value := by
    simpa only [hshiftedEq] using hsqrtRatio
  rw [← hsqrtRatio']
  field_simp [hgamma, hgammaShifted, hgammaHalf,
    hsqrtValue, hsqrtShifted]
  ring

theorem tendsto_gammaHalfShiftRatio (offset halfShift : ℕ) :
    Tendsto (gammaHalfShiftRatio offset halfShift) atTop (nhds 1) := by
  obtain ⟨shift, hshift | hshift⟩ := halfShift.even_or_odd'
  · subst halfShift
    have hbase := tendsto_gammaNatShiftRatio offset shift
    apply hbase.congr'
    filter_upwards with index
    exact (gammaHalfShiftRatio_even offset shift index).symm
  · subst halfShift
    have hnat := tendsto_gammaNatShiftRatio offset shift
    have hratio := tendsto_offset_div_offset_add
      (2 + (offset : ℝ) / 2) shift
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
    have hhalf := tendsto_gammaHalfOffsetRatio (offset + 2 * shift)
    have hproduct := (hnat.mul hsqrt).mul hhalf
    norm_num at hproduct
    apply hproduct.congr'
    filter_upwards with index
    rw [gammaHalfShiftRatio_odd]
    unfold gammaHalfOffsetValue
    push_cast
    congr 2
    congr 1
    ring

end FibonacciRibbonKernel
