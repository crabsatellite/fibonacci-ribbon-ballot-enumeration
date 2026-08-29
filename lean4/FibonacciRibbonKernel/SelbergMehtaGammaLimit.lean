import FibonacciRibbonKernel.GammaHalfRatioAsymptotic

namespace FibonacciRibbonKernel

open Filter Asymptotics
open scoped Classical Topology BigOperators

theorem mehtaPairCount_add_dimension (dimension : ℕ) :
    dimension + mehtaPairCount dimension =
      Finset.univ.sum (fun index : Fin dimension =>
        dimension - index.val) := by
  unfold mehtaPairCount
  have hdimension : dimension = ∑ _index : Fin dimension, 1 := by
    simp
  calc
    dimension + mehtaPairCount dimension =
        (∑ _index : Fin dimension, 1) +
          mehtaPairCount dimension :=
      congrArg (fun value => value + mehtaPairCount dimension) hdimension
    _ =
        (∑ _index : Fin dimension, 1) +
          ∑ first : Fin dimension, (Finset.Ioi first).card := by
            rfl
    _ = ∑ index : Fin dimension,
        (1 + (Finset.Ioi index).card) := by
          rw [Finset.sum_add_distrib]
    _ = Finset.univ.sum (fun index : Fin dimension =>
        dimension - index.val) := by
      apply Finset.sum_congr rfl
      intro index hindex
      rw [Fin.card_Ioi]
      omega

noncomputable def selbergMehtaLocalFactor
    (dimension : ℕ) (term : Fin dimension) (index : ℕ) : ℝ :=
  let alpha : ℝ := (index + 2 : ℕ)
  let shifted : ℝ := (2 * alpha + (term.val : ℝ)) / 2
  (4 : ℝ) ^ (index + 1) *
    selbergMehtaScale index ^ (dimension - term.val) *
      (Real.Gamma shifted ^ 2 /
        Real.Gamma (2 * alpha +
          ((dimension + term.val - 1 : ℕ) : ℝ) / 2))

noncomputable def selbergMehtaLocalConstant
    (dimension : ℕ) (term : Fin dimension) : ℝ :=
  (2 : ℝ) ^ ((dimension : ℝ) - 2 * term.val - 1 / 2) *
    Real.sqrt Real.pi

noncomputable def selbergMehtaLocalCorrection
    (dimension : ℕ) (term : Fin dimension) (index : ℕ) : ℝ :=
  ((((index + 2 : ℕ) : ℝ) /
      (((index + 2 : ℕ) : ℝ) + (term.val : ℝ) / 2)) ^
    (((dimension - term.val : ℕ) : ℝ) / 2))

theorem tendsto_selbergMehtaLocalCorrection
    (dimension : ℕ) (term : Fin dimension) :
    Tendsto (selbergMehtaLocalCorrection dimension term)
      atTop (nhds 1) := by
  have hratio := tendsto_offset_div_offset_add_real
    2 ((term.val : ℝ) / 2)
  have hpower := hratio.rpow_const
    (p := (((dimension - term.val : ℕ) : ℝ) / 2)) (Or.inl one_ne_zero)
  norm_num at hpower
  convert hpower using 1
  funext index
  unfold selbergMehtaLocalCorrection
  push_cast
  rw [Nat.cast_sub (Nat.le_of_lt term.isLt)]

noncomputable def selbergMehtaElementaryFactor
    (dimension : ℕ) (term : Fin dimension) (index : ℕ) : ℝ :=
  let alpha : ℝ := (index + 2 : ℕ)
  let shifted : ℝ := alpha + (term.val : ℝ) / 2
  let halfShift : ℕ := dimension - term.val - 1
  (4 : ℝ) ^ (index + 1) *
      selbergMehtaScale index ^ (dimension - term.val) *
      (2 : ℝ) ^ (1 - 2 * shifted) /
    (Real.sqrt shifted *
      (2 * shifted) ^ ((halfShift : ℝ) / 2))

theorem selbergMehtaElementaryFactor_eq
    (dimension : ℕ) (term : Fin dimension) (index : ℕ) :
    selbergMehtaElementaryFactor dimension term index =
      (2 : ℝ) ^ ((dimension : ℝ) - 2 * term.val - 1 / 2) *
        selbergMehtaLocalCorrection dimension term index := by
  let alpha : ℝ := (index + 2 : ℕ)
  let shifted : ℝ := alpha + (term.val : ℝ) / 2
  let halfShift : ℕ := dimension - term.val - 1
  have halpha : 0 < alpha := by unfold alpha; positivity
  have hshifted : 0 < shifted := by unfold shifted; positivity
  have hdimension : dimension = halfShift + term.val + 1 := by
    unfold halfShift
    omega
  have htail : dimension - term.val = halfShift + 1 := by
    unfold halfShift
    omega
  unfold selbergMehtaElementaryFactor selbergMehtaLocalCorrection
  dsimp only [alpha, shifted, halfShift] at halpha hshifted hdimension htail ⊢
  rw [htail]
  have hcorrectionPos : 0 <
      ((((index + 2 : ℕ) : ℝ) /
          (((index + 2 : ℕ) : ℝ) + (term.val : ℝ) / 2)) ^
        (((halfShift + 1 : ℕ) : ℝ) / 2)) :=
    Real.rpow_pos_of_pos (div_pos halpha hshifted) _
  have hfourPos : 0 < (4 : ℝ) ^ (index + 1) := by positivity
  have hscalePowPos : 0 < selbergMehtaScale index ^ (halfShift + 1) :=
    pow_pos (selbergMehtaScale_pos index) _
  have htwoPowPos : 0 < (2 : ℝ) ^
      (1 - 2 * (((index + 2 : ℕ) : ℝ) + (term.val : ℝ) / 2)) :=
    Real.rpow_pos_of_pos two_pos _
  have hsqrtPos : 0 < Real.sqrt
      (((index + 2 : ℕ) : ℝ) + (term.val : ℝ) / 2) := by positivity
  have hshiftPowPos : 0 <
      (2 * (((index + 2 : ℕ) : ℝ) + (term.val : ℝ) / 2)) ^
        (((halfShift : ℕ) : ℝ) / 2) :=
    Real.rpow_pos_of_pos (mul_pos two_pos hshifted) _
  have hnumeratorPos : 0 <
      (4 : ℝ) ^ (index + 1) *
        selbergMehtaScale index ^ (halfShift + 1) *
        (2 : ℝ) ^
          (1 - 2 * (((index + 2 : ℕ) : ℝ) + (term.val : ℝ) / 2)) :=
    mul_pos (mul_pos hfourPos hscalePowPos) htwoPowPos
  have hdenominatorPos : 0 <
      Real.sqrt (((index + 2 : ℕ) : ℝ) + (term.val : ℝ) / 2) *
        (2 * (((index + 2 : ℕ) : ℝ) + (term.val : ℝ) / 2)) ^
          (((halfShift : ℕ) : ℝ) / 2) :=
    mul_pos hsqrtPos hshiftPowPos
  apply Real.log_injOn_pos (div_pos hnumeratorPos hdenominatorPos)
    (mul_pos (Real.rpow_pos_of_pos two_pos _) hcorrectionPos)
  rw [Real.log_div hnumeratorPos.ne' hdenominatorPos.ne']
  rw [Real.log_mul (mul_pos hfourPos hscalePowPos).ne' htwoPowPos.ne']
  rw [Real.log_mul hfourPos.ne' hscalePowPos.ne']
  rw [Real.log_mul hsqrtPos.ne' hshiftPowPos.ne']
  rw [Real.log_pow, Real.log_pow]
  rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
  rw [Real.log_sqrt hshifted.le]
  rw [Real.log_mul (by positivity) (by positivity)]
  conv_rhs =>
    rw [Real.log_mul (by positivity) hcorrectionPos.ne']
    rw [Real.log_rpow two_pos]
    rw [Real.log_rpow (div_pos halpha hshifted)]
    rw [Real.log_div halpha.ne' hshifted.ne']
  rw [show selbergMehtaScale index =
    Real.sqrt (8 * ((index + 2 : ℕ) : ℝ)) by rfl]
  rw [Real.log_sqrt (by positivity :
    (0 : ℝ) ≤ 8 * ((index + 2 : ℕ) : ℝ))]
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogEight : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [show Real.log (8 * ((index + 2 : ℕ) : ℝ)) =
      Real.log 8 + Real.log ((index + 2 : ℕ) : ℝ) by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity)]]
  rw [hlogFour, hlogEight]
  push_cast
  have hdimensionReal : (dimension : ℝ) =
      (halfShift : ℝ) + term.val + 1 := by
    exact_mod_cast hdimension
  rw [hdimensionReal]
  ring

theorem selbergMehtaLocalFactor_eq_ratios
    (dimension : ℕ) (term : Fin dimension) (index : ℕ) :
    selbergMehtaLocalFactor dimension term index =
      selbergMehtaElementaryFactor dimension term index *
        Real.sqrt Real.pi *
        gammaHalfOffsetRatio term.val index *
        gammaHalfShiftRatio (2 * term.val)
          (dimension - term.val - 1) (2 * index + 2) := by
  let alpha : ℝ := (index + 2 : ℕ)
  let shifted : ℝ := (2 * alpha + (term.val : ℝ)) / 2
  let halfShift : ℕ := dimension - term.val - 1
  let doubled : ℝ := 2 * shifted
  have halpha : 0 < alpha := by unfold alpha; positivity
  have hshifted : 0 < shifted := by unfold shifted; positivity
  have hdoubled : 0 < doubled := by unfold doubled; positivity
  have hdimension : dimension = halfShift + term.val + 1 := by
    unfold halfShift
    omega
  have hdoubledValue :
      gammaHalfOffsetValue (2 * term.val) (2 * index + 2) = doubled := by
    unfold gammaHalfOffsetValue doubled shifted alpha
    push_cast
    ring
  have hshiftedValue : gammaHalfOffsetValue term.val index = shifted := by
    unfold gammaHalfOffsetValue shifted alpha
    ring
  have hdenominator :
      2 * alpha + ((dimension + term.val - 1 : ℕ) : ℝ) / 2 =
        doubled + (halfShift : ℝ) / 2 := by
    have hnat : dimension + term.val - 1 =
        2 * term.val + halfShift := by omega
    rw [hnat]
    unfold doubled shifted
    push_cast
    ring
  have hgamma : Real.Gamma shifted ≠ 0 := by positivity
  have hgammaHalf : Real.Gamma (shifted + 1 / 2) ≠ 0 := by positivity
  have hgammaDouble : Real.Gamma doubled ≠ 0 := by positivity
  have hgammaDenominator :
      Real.Gamma (doubled + (halfShift : ℝ) / 2) ≠ 0 := by positivity
  have hsqrtShifted : Real.sqrt shifted ≠ 0 := by positivity
  have hdoublePower : doubled ^ ((halfShift : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hdoubled _).ne'
  have hduplication := Real.Gamma_mul_Gamma_add_half shifted
  unfold selbergMehtaLocalFactor selbergMehtaElementaryFactor
  unfold gammaHalfOffsetRatio gammaHalfShiftRatio
  dsimp only [alpha, shifted, halfShift, doubled] at halpha hshifted hdoubled hdimension hdoubledValue hshiftedValue hdenominator hgamma hgammaHalf hgammaDouble hgammaDenominator hsqrtShifted hdoublePower hduplication ⊢
  rw [hshiftedValue, hdoubledValue, hdenominator]
  field_simp [hgamma, hgammaHalf, hgammaDouble,
    hgammaDenominator, hsqrtShifted, hdoublePower]
  have hcurrent :
      Real.Gamma ((2 * ((index + 2 : ℕ) : ℝ) + (term.val : ℝ)) / 2) *
          Real.Gamma ((2 * ((index + 2 : ℕ) : ℝ) +
            (term.val : ℝ) + 1) / 2) =
        (2 : ℝ) ^ (1 - (2 * ((index + 2 : ℕ) : ℝ) +
            (term.val : ℝ))) * Real.sqrt Real.pi *
          Real.Gamma (2 * ((index + 2 : ℕ) : ℝ) + (term.val : ℝ)) := by
    convert hduplication using 1 <;> ring
  have hscaledCurrent := congrArg (fun value : ℝ =>
    selbergMehtaScale index ^ (dimension - term.val) * value) hcurrent
  ring_nf at hscaledCurrent ⊢
  exact hscaledCurrent

theorem selbergMehtaLocalFactor_eq_asymptoticProduct
    (dimension : ℕ) (term : Fin dimension) (index : ℕ) :
    selbergMehtaLocalFactor dimension term index =
      selbergMehtaLocalConstant dimension term *
        selbergMehtaLocalCorrection dimension term index *
        gammaHalfOffsetRatio term.val index *
        gammaHalfShiftRatio (2 * term.val)
          (dimension - term.val - 1) (2 * index + 2) := by
  rw [selbergMehtaLocalFactor_eq_ratios]
  rw [selbergMehtaElementaryFactor_eq]
  unfold selbergMehtaLocalConstant
  ring

theorem tendsto_two_mul_add_two_atTop :
    Tendsto (fun index : ℕ => 2 * index + 2) atTop atTop := by
  rw [tendsto_atTop]
  intro bound
  exact eventually_atTop.2 ⟨bound, fun index hindex => by omega⟩

theorem tendsto_selbergMehtaLocalFactor
    (dimension : ℕ) (term : Fin dimension) :
    Tendsto (selbergMehtaLocalFactor dimension term)
      atTop (nhds (selbergMehtaLocalConstant dimension term)) := by
  have hcorrection := tendsto_selbergMehtaLocalCorrection dimension term
  have hhalf := tendsto_gammaHalfOffsetRatio term.val
  have hshift := (tendsto_gammaHalfShiftRatio
    (2 * term.val) (dimension - term.val - 1)).comp
      tendsto_two_mul_add_two_atTop
  have hconstant : Tendsto
      (fun _ : ℕ => selbergMehtaLocalConstant dimension term)
      atTop (nhds (selbergMehtaLocalConstant dimension term)) :=
    tendsto_const_nhds
  have hproduct := (((hconstant.mul hcorrection).mul hhalf).mul hshift)
  norm_num at hproduct
  apply hproduct.congr'
  filter_upwards with index
  exact (selbergMehtaLocalFactor_eq_asymptoticProduct
    dimension term index).symm

theorem sum_selbergMehtaLocalExponents (dimension : ℕ) :
    (∑ term : Fin dimension,
      ((dimension : ℝ) - 2 * term.val - 1 / 2)) =
      (dimension : ℝ) / 2 := by
  induction dimension with
  | zero => simp
  | succ dimension ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [show (∑ term : Fin dimension,
          (((dimension + 1 : ℕ) : ℝ) - 2 * term.val - 1 / 2)) =
        (∑ term : Fin dimension,
          ((dimension : ℝ) - 2 * term.val - 1 / 2)) + dimension by
        calc
          _ = ∑ term : Fin dimension,
              (((dimension : ℝ) - 2 * term.val - 1 / 2) + 1) := by
            apply Finset.sum_congr rfl
            intro term hterm
            push_cast
            ring
          _ = (∑ term : Fin dimension,
              ((dimension : ℝ) - 2 * term.val - 1 / 2)) +
              ∑ _term : Fin dimension, (1 : ℝ) :=
            Finset.sum_add_distrib
          _ = _ := by simp]
      rw [ih]
      push_cast
      ring

theorem prod_selbergMehtaLocalConstant (dimension : ℕ) :
    (∏ term : Fin dimension,
      selbergMehtaLocalConstant dimension term) =
      Real.sqrt (2 * Real.pi) ^ dimension := by
  unfold selbergMehtaLocalConstant
  rw [Finset.prod_mul_distrib]
  rw [← Real.rpow_sum_of_pos two_pos
    (fun term : Fin dimension =>
      (dimension : ℝ) - 2 * term.val - 1 / 2) Finset.univ]
  rw [sum_selbergMehtaLocalExponents]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.rpow_div_two_eq_sqrt (dimension : ℝ) (by norm_num)]
  rw [Real.rpow_natCast]
  rw [← mul_pow]
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

noncomputable def expectedMehtaIntegralByDimension (dimension : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi) ^ dimension *
    mehtaGammaProduct dimension / (dimension.factorial : ℝ)

theorem normalizedExpectedSelberg_factorization
    (dimension index : ℕ) :
    selbergMehtaNormalization dimension index *
        expectedOrderedSelbergHalfIntegral dimension
          ((index + 2 : ℕ) : ℝ) ((index + 2 : ℕ) : ℝ) =
      (∏ term : Fin dimension,
        (selbergMehtaLocalFactor dimension term index *
          (Real.Gamma (1 + ((term.val + 1 : ℕ) : ℝ) / 2) /
            Real.Gamma (3 / 2)))) /
        (dimension.factorial : ℝ) := by
  unfold selbergMehtaNormalization expectedOrderedSelbergHalfIntegral
  unfold selbergHalfGammaProduct selbergMehtaLocalFactor
  rw [Finset.prod_range]
  have hfour :
      (4 : ℝ) ^ ((index + 1) * dimension) =
        ∏ _term : Fin dimension, (4 : ℝ) ^ (index + 1) := by
    simp [← pow_mul]
  have hscale :
      selbergMehtaScale index ^
          (dimension + mehtaPairCount dimension) =
        ∏ term : Fin dimension,
          selbergMehtaScale index ^ (dimension - term.val) := by
    rw [mehtaPairCount_add_dimension]
    symm
    exact Finset.prod_pow_eq_pow_sum
      (Finset.univ : Finset (Fin dimension))
      (fun term => dimension - term.val)
      (selbergMehtaScale index)
  rw [hfour, hscale]
  rw [← Finset.prod_mul_distrib]
  rw [← mul_div_assoc]
  rw [← Finset.prod_mul_distrib]
  apply congrArg (fun value : ℝ => value / (dimension.factorial : ℝ))
  apply Finset.prod_congr rfl
  intro term hterm
  dsimp
  push_cast
  ring

theorem tendsto_normalizedExpectedSelberg_explicit
    (dimension : ℕ) :
    Tendsto (fun index =>
      selbergMehtaNormalization dimension index *
        expectedOrderedSelbergHalfIntegral dimension
          ((index + 2 : ℕ) : ℝ) ((index + 2 : ℕ) : ℝ))
      atTop (nhds (expectedMehtaIntegralByDimension dimension)) := by
  have hproduct : Tendsto (fun index =>
      ∏ term : Fin dimension,
        (selbergMehtaLocalFactor dimension term index *
          (Real.Gamma (1 + ((term.val + 1 : ℕ) : ℝ) / 2) /
            Real.Gamma (3 / 2)))) atTop
      (nhds (∏ term : Fin dimension,
        (selbergMehtaLocalConstant dimension term *
          (Real.Gamma (1 + ((term.val + 1 : ℕ) : ℝ) / 2) /
            Real.Gamma (3 / 2))))) := by
    apply tendsto_finsetProd Finset.univ
    intro term hterm
    exact (tendsto_selbergMehtaLocalFactor dimension term).mul_const _
  have hdivide := hproduct.div_const (dimension.factorial : ℝ)
  have hlimitEq :
      ((∏ term : Fin dimension,
        (selbergMehtaLocalConstant dimension term *
          (Real.Gamma (1 + ((term.val + 1 : ℕ) : ℝ) / 2) /
            Real.Gamma (3 / 2)))) /
        (dimension.factorial : ℝ)) =
      expectedMehtaIntegralByDimension dimension := by
    unfold expectedMehtaIntegralByDimension mehtaGammaProduct
    rw [Finset.prod_range]
    rw [Finset.prod_mul_distrib]
    rw [prod_selbergMehtaLocalConstant]
  rw [hlimitEq] at hdivide
  apply hdivide.congr'
  filter_upwards with index
  exact (normalizedExpectedSelberg_factorization dimension index).symm

end FibonacciRibbonKernel
