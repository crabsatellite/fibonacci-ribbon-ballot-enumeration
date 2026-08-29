import FibonacciRibbonKernel.HeightFourCatalan
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast

namespace FibonacciRibbonKernel

open Filter Asymptotics

/-- The exact comparison term used by Mathlib's kernel proof of Stirling's
formula. -/
noncomputable def stirlingComparison (index : ℕ) : ℝ :=
  Real.sqrt (2 * (index : ℝ) * Real.pi) *
    ((index : ℝ) / Real.exp 1) ^ index

noncomputable def centralBinomialStirlingComparison (index : ℕ) : ℝ :=
  stirlingComparison (2 * index) / stirlingComparison index ^ 2

noncomputable def catalanStirlingComparison (index : ℕ) : ℝ :=
  centralBinomialStirlingComparison index / (index + 1 : ℝ)

noncomputable def centralBinomialLeadingTerm (index : ℕ) : ℝ :=
  (4 : ℝ) ^ index / Real.sqrt (Real.pi * (index : ℝ))

noncomputable def catalanLeadingTerm (index : ℕ) : ℝ :=
  centralBinomialLeadingTerm index / (index : ℝ)

noncomputable def heightFourRegevLeadingTerm (index : ℕ) : ℝ :=
  (32 / Real.pi) * (4 : ℝ) ^ index / (index : ℝ) ^ 3

noncomputable def heightFourEvenRatio (index : ℕ) : ℝ :=
  (index : ℝ) / (index + 1 : ℝ)

noncomputable def heightFourOddRatio (index : ℕ) : ℝ :=
  (2 * index + 1 : ℝ) / (2 * (index + 1 : ℝ))

theorem tendsto_two_mul_nat_atTop :
    Tendsto (fun index : ℕ => 2 * index) atTop atTop := by
  rw [tendsto_atTop]
  intro bound
  exact eventually_atTop.2 ⟨bound, fun index hindex => by omega⟩

theorem factorial_isEquivalent_stirlingComparison :
    (fun index : ℕ => (index.factorial : ℝ)) ~[atTop]
      stirlingComparison := by
  exact Stirling.factorial_isEquivalent_stirling

theorem centralBinomial_isEquivalent_stirlingComparison :
    (fun index : ℕ => (Nat.centralBinom index : ℝ)) ~[atTop]
      centralBinomialStirlingComparison := by
  have hexact : Filter.EventuallyEq atTop
      (fun index : ℕ => (Nat.centralBinom index : ℝ))
        (fun index : ℕ =>
          (Nat.factorial (2 * index) : ℝ) /
            (Nat.factorial index : ℝ) ^ 2) := by
    filter_upwards with index
    rw [Nat.centralBinom_eq_two_mul_choose,
      Nat.cast_choose ℝ (by omega)]
    rw [show 2 * index - index = index by omega]
    ring
  have htwice := factorial_isEquivalent_stirlingComparison.comp_tendsto
    tendsto_two_mul_nat_atTop
  exact hexact.isEquivalent.trans
    (htwice.div (factorial_isEquivalent_stirlingComparison.pow 2))

theorem centralBinomialStirlingComparison_eq_leading
    (index : ℕ) (hindex : index ≠ 0) :
    centralBinomialStirlingComparison index =
      centralBinomialLeadingTerm index := by
  have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  have hindexPos : (0 : ℝ) < index := by positivity
  have hexp : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hratio : (index : ℝ) / Real.exp 1 ≠ 0 := div_ne_zero hindexReal hexp
  have hstirling : stirlingComparison index ≠ 0 := by
    unfold stirlingComparison
    positivity
  have hsqrt : Real.sqrt (Real.pi * (index : ℝ)) ≠ 0 := by
    positivity
  have htwoPower :
      (2 : ℝ) ^ (2 * index) = (4 : ℝ) ^ index := by
    rw [pow_mul]
    norm_num
  have hratioPower :
      ((index : ℝ) / Real.exp 1) ^ (2 * index) =
        (((index : ℝ) / Real.exp 1) ^ index) ^ 2 := by
    rw [show 2 * index = index * 2 by omega, pow_mul]
  have hpower :
      (((2 * index : ℕ) : ℝ) / Real.exp 1) ^ (2 * index) =
        (4 : ℝ) ^ index *
          (((index : ℝ) / Real.exp 1) ^ index) ^ 2 := by
    push_cast
    rw [show (2 : ℝ) * index / Real.exp 1 =
      2 * ((index : ℝ) / Real.exp 1) by ring, mul_pow,
      htwoPower, hratioPower]
  have hsqrtNumerator :
      Real.sqrt (2 * ((2 * index : ℕ) : ℝ) * Real.pi) =
        2 * Real.sqrt (Real.pi * (index : ℝ)) := by
    push_cast
    calc
      Real.sqrt (2 * (2 * (index : ℝ)) * Real.pi) =
          Real.sqrt (4 * (Real.pi * (index : ℝ))) := by ring_nf
      _ = Real.sqrt 4 * Real.sqrt (Real.pi * (index : ℝ)) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt (Real.pi * (index : ℝ)) := by norm_num
  have hsqrtSquare :
      Real.sqrt (Real.pi * (index : ℝ)) ^ 2 =
        Real.pi * (index : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtDenominator' :
      Real.sqrt (Real.pi * (index : ℝ) * 2) ^ 2 =
        Real.pi * (index : ℝ) * 2 :=
    Real.sq_sqrt (by positivity)
  unfold centralBinomialStirlingComparison centralBinomialLeadingTerm
  field_simp [hstirling, hsqrt]
  unfold stirlingComparison
  rw [hpower, hsqrtNumerator]
  ring_nf
  rw [hsqrtDenominator', hsqrtSquare]
  ring

theorem centralBinomialStirlingComparison_isEquivalent_leading :
    centralBinomialStirlingComparison ~[atTop]
      centralBinomialLeadingTerm := by
  apply Filter.EventuallyEq.isEquivalent
  filter_upwards [eventually_ne_atTop 0] with index hindex
  exact centralBinomialStirlingComparison_eq_leading index hindex

theorem centralBinomial_isEquivalent_leading :
    (fun index : ℕ => (Nat.centralBinom index : ℝ)) ~[atTop]
      centralBinomialLeadingTerm :=
  centralBinomial_isEquivalent_stirlingComparison.trans
    centralBinomialStirlingComparison_isEquivalent_leading

theorem natCast_add_one_isEquivalent_natCast :
    (fun index : ℕ => (index + 1 : ℝ)) ~[atTop]
      (fun index : ℕ => (index : ℝ)) := by
  have hne : ∀ᶠ index : ℕ in atTop, (index : ℝ) ≠ 0 := by
    exact eventually_atTop.2 ⟨1, fun index hindex => by positivity⟩
  rw [isEquivalent_iff_tendsto_one hne]
  have hinverse := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  norm_num at hinverse
  change Tendsto (fun index : ℕ =>
    (index + 1 : ℝ) / (index : ℝ)) atTop (nhds 1)
  simpa only [Nat.cast_add, Nat.cast_one] using hinverse

theorem catalan_isEquivalent_stirlingComparison :
    (fun index : ℕ => (catalan index : ℝ)) ~[atTop]
      catalanStirlingComparison := by
  have hexact : Filter.EventuallyEq atTop
      (fun index : ℕ => (catalan index : ℝ))
        (fun index : ℕ =>
          (Nat.centralBinom index : ℝ) / (index + 1 : ℝ)) := by
    filter_upwards with index
    have hcat := succ_mul_catalan_eq_centralBinom index
    have hcatReal :
        (index + 1 : ℝ) * (catalan index : ℝ) =
          (Nat.centralBinom index : ℝ) := by
      exact_mod_cast hcat
    rw [eq_div_iff (by positivity)]
    simpa [mul_comm] using hcatReal
  exact hexact.isEquivalent.trans
    (centralBinomial_isEquivalent_stirlingComparison.div IsEquivalent.refl)

theorem catalan_isEquivalent_leading :
    (fun index : ℕ => (catalan index : ℝ)) ~[atTop]
      catalanLeadingTerm := by
  exact catalan_isEquivalent_stirlingComparison.trans
    (centralBinomialStirlingComparison_isEquivalent_leading.div
      natCast_add_one_isEquivalent_natCast)

theorem heightFourEvenRatio_tendsto_one :
    Tendsto heightFourEvenRatio atTop (nhds 1) := by
  change Tendsto (fun index : ℕ =>
    (index : ℝ) / (index + 1 : ℝ)) atTop (nhds 1)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_natCast_div_add_atTop (1 : ℝ))

theorem heightFourEvenRatio_mul_sqrt_tendsto_one :
    Tendsto (fun index =>
      heightFourEvenRatio index * Real.sqrt (heightFourEvenRatio index))
      atTop (nhds 1) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    heightFourEvenRatio_tendsto_one
  norm_num at hsqrt
  convert heightFourEvenRatio_tendsto_one.mul hsqrt using 1
  all_goals norm_num

theorem heightFourOddRatio_tendsto_one :
    Tendsto heightFourOddRatio atTop (nhds 1) := by
  have hlimit := tendsto_add_mul_div_add_mul_atTop_nhds
    (1 : ℝ) 2 2 (by norm_num : (2 : ℝ) ≠ 0)
  change Tendsto (fun index : ℕ =>
    (2 * (index : ℝ) + 1) / (2 * ((index : ℝ) + 1)))
      atTop (nhds 1)
  convert hlimit using 1
  all_goals norm_num
  all_goals ring_nf

theorem catalanLeading_even_ratio_identity
    (index : ℕ) (hindex : index ≠ 0) :
    catalanLeadingTerm index * catalanLeadingTerm (index + 1) /
        heightFourRegevLeadingTerm (2 * index) =
      heightFourEvenRatio index * Real.sqrt (heightFourEvenRatio index) := by
  have hindexReal : (index : ℝ) ≠ 0 := by exact_mod_cast hindex
  have hsuccReal : (index + 1 : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrtIndex : Real.sqrt (Real.pi * (index : ℝ)) ≠ 0 := by positivity
  have hsqrtSucc : Real.sqrt (Real.pi * (index + 1 : ℝ)) ≠ 0 := by positivity
  have hsqrtRatio : Real.sqrt (heightFourEvenRatio index) ≠ 0 := by
    unfold heightFourEvenRatio
    positivity
  have hpow : (4 : ℝ) ^ (2 * index) = ((4 : ℝ) ^ index) ^ 2 := by
    rw [show 2 * index = index * 2 by omega, pow_mul]
  have hsqrtIndexSq :
      Real.sqrt (Real.pi * (index : ℝ)) ^ 2 =
        Real.pi * (index : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtSuccSq :
      Real.sqrt (Real.pi * (index + 1 : ℝ)) ^ 2 =
        Real.pi * (index + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtRatioSq :
      Real.sqrt (heightFourEvenRatio index) ^ 2 =
        heightFourEvenRatio index :=
    Real.sq_sqrt (by
      unfold heightFourEvenRatio
      positivity)
  have hsqrtBridge :
      Real.sqrt (Real.pi * (index : ℝ)) *
          Real.sqrt (Real.pi * (index + 1 : ℝ)) *
          Real.sqrt (heightFourEvenRatio index) =
        Real.pi * (index : ℝ) := by
    have hleftNonneg : 0 ≤
        Real.sqrt (Real.pi * (index : ℝ)) *
          Real.sqrt (Real.pi * (index + 1 : ℝ)) *
          Real.sqrt (heightFourEvenRatio index) := by positivity
    have hrightNonneg : 0 ≤ Real.pi * (index : ℝ) := by positivity
    have hsquare :
        (Real.sqrt (Real.pi * (index : ℝ)) *
            Real.sqrt (Real.pi * (index + 1 : ℝ)) *
            Real.sqrt (heightFourEvenRatio index)) ^ 2 =
          (Real.pi * (index : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, hsqrtIndexSq, hsqrtSuccSq,
        hsqrtRatioSq]
      unfold heightFourEvenRatio
      field_simp
    nlinarith
  unfold heightFourEvenRatio at hsqrtBridge
  unfold catalanLeadingTerm centralBinomialLeadingTerm
  unfold heightFourRegevLeadingTerm heightFourEvenRatio
  rw [hpow]
  push_cast
  field_simp
  rw [pow_succ]
  rw [show (2 : ℝ) ^ 3 = 8 by norm_num]
  linear_combination -32 * (4 : ℝ) ^ index * hsqrtBridge

theorem catalanLeading_odd_ratio_identity
    (index : ℕ) :
    catalanLeadingTerm (index + 1) ^ 2 /
        heightFourRegevLeadingTerm (2 * index + 1) =
      heightFourOddRatio index ^ 3 := by
  have hsuccReal : (index + 1 : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrtSucc : Real.sqrt (Real.pi * (index + 1 : ℝ)) ≠ 0 := by positivity
  have hsqrtSuccSq :
      Real.sqrt (Real.pi * (index + 1 : ℝ)) ^ 2 =
        Real.pi * (index + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hpow :
      (4 : ℝ) ^ (2 * index + 1) =
        4 * ((4 : ℝ) ^ index) ^ 2 := by
    rw [show 2 * index + 1 = index + index + 1 by omega,
      pow_succ, pow_add]
    ring
  unfold catalanLeadingTerm centralBinomialLeadingTerm
  unfold heightFourRegevLeadingTerm heightFourOddRatio
  rw [hpow]
  push_cast
  field_simp
  rw [hsqrtSuccSq]
  ring

theorem catalanLeading_even_product_isEquivalent :
    (fun index => catalanLeadingTerm index * catalanLeadingTerm (index + 1))
      ~[atTop] (fun index => heightFourRegevLeadingTerm (2 * index)) := by
  have hne : ∀ᶠ index : ℕ in atTop,
      heightFourRegevLeadingTerm (2 * index) ≠ 0 := by
    exact eventually_atTop.2 ⟨1, fun index hindex => by
      unfold heightFourRegevLeadingTerm
      positivity⟩
  rw [isEquivalent_iff_tendsto_one hne]
  exact heightFourEvenRatio_mul_sqrt_tendsto_one.congr'
    (eventually_atTop.2 ⟨1, fun index hindex =>
      (catalanLeading_even_ratio_identity index (by omega)).symm⟩)

theorem catalanLeading_odd_square_isEquivalent :
    (fun index => catalanLeadingTerm (index + 1) ^ 2)
      ~[atTop] (fun index => heightFourRegevLeadingTerm (2 * index + 1)) := by
  have hne : ∀ᶠ index : ℕ in atTop,
      heightFourRegevLeadingTerm (2 * index + 1) ≠ 0 := by
    filter_upwards with index
    unfold heightFourRegevLeadingTerm
    positivity
  rw [isEquivalent_iff_tendsto_one hne]
  have hlimit : Tendsto (fun index => heightFourOddRatio index ^ 3)
      atTop (nhds 1) := by
    simpa only [one_pow] using heightFourOddRatio_tendsto_one.pow 3
  exact hlimit.congr'
    (Filter.Eventually.of_forall fun index =>
      (catalanLeading_odd_ratio_identity index).symm)

theorem heightFourTableau_even_isEquivalent_regev :
    (fun index : ℕ => (heightFourTableauCount (2 * index) : ℝ))
      ~[atTop] (fun index => heightFourRegevLeadingTerm (2 * index)) := by
  have hshift := catalan_isEquivalent_leading.comp_tendsto
    (tendsto_add_atTop_nat 1)
  have hexact : Filter.EventuallyEq atTop
      (fun index : ℕ => (heightFourTableauCount (2 * index) : ℝ))
      (fun index : ℕ =>
        (catalan index : ℝ) * (catalan (index + 1) : ℝ)) := by
    filter_upwards with index
    exact_mod_cast heightFourTableauCount_even_catalan index
  exact hexact.isEquivalent.trans
    ((catalan_isEquivalent_leading.mul hshift).trans
      catalanLeading_even_product_isEquivalent)

theorem heightFourTableau_odd_isEquivalent_regev :
    (fun index : ℕ => (heightFourTableauCount (2 * index + 1) : ℝ))
      ~[atTop] (fun index => heightFourRegevLeadingTerm (2 * index + 1)) := by
  have hshift := catalan_isEquivalent_leading.comp_tendsto
    (tendsto_add_atTop_nat 1)
  have hexact : Filter.EventuallyEq atTop
      (fun index : ℕ => (heightFourTableauCount (2 * index + 1) : ℝ))
      (fun index : ℕ => (catalan (index + 1) : ℝ) ^ 2) := by
    filter_upwards with index
    exact_mod_cast heightFourTableauCount_odd_catalan index
  exact hexact.isEquivalent.trans
    ((hshift.pow 2).trans catalanLeading_odd_square_isEquivalent)

theorem tendsto_of_even_odd
    {target : Type*} [TopologicalSpace target]
    {function : ℕ → target} {limit : target}
    (heven : Tendsto (fun index => function (2 * index)) atTop (nhds limit))
    (hodd : Tendsto (fun index => function (2 * index + 1)) atTop (nhds limit)) :
    Tendsto function atTop (nhds limit) := by
  rw [tendsto_def] at heven hodd ⊢
  intro neighborhood hneighborhood
  obtain ⟨evenBound, hevenBound⟩ :=
    eventually_atTop.1 (heven neighborhood hneighborhood)
  obtain ⟨oddBound, hoddBound⟩ :=
    eventually_atTop.1 (hodd neighborhood hneighborhood)
  refine eventually_atTop.2
    ⟨2 * max evenBound oddBound + 1, ?_⟩
  intro index hindex
  obtain ⟨half, rfl | rfl⟩ := Nat.even_or_odd' index
  · apply hevenBound
    omega
  · apply hoddBound
    omega

/-- The exact Regev leading asymptotic for the first nontrivial manuscript
case, derived from the kernel Catalan formulas and Stirling's theorem. -/
theorem heightFourTableau_isEquivalent_regev :
    (fun index : ℕ => (heightFourTableauCount index : ℝ))
      ~[atTop] heightFourRegevLeadingTerm := by
  have hden : ∀ᶠ index : ℕ in atTop,
      heightFourRegevLeadingTerm index ≠ 0 := by
    exact eventually_atTop.2 ⟨1, fun index hindex => by
      unfold heightFourRegevLeadingTerm
      positivity⟩
  rw [isEquivalent_iff_tendsto_one hden]
  apply tendsto_of_even_odd
  · have hdenEven : ∀ᶠ index : ℕ in atTop,
        heightFourRegevLeadingTerm (2 * index) ≠ 0 := by
      exact eventually_atTop.2 ⟨1, fun index hindex => by
        unfold heightFourRegevLeadingTerm
        positivity⟩
    change Tendsto (fun index : ℕ =>
      (heightFourTableauCount (2 * index) : ℝ) /
        heightFourRegevLeadingTerm (2 * index)) atTop (nhds 1)
    have hratio := (isEquivalent_iff_tendsto_one hdenEven).mp
      heightFourTableau_even_isEquivalent_regev
    change Tendsto (fun index : ℕ =>
      (heightFourTableauCount (2 * index) : ℝ) /
        heightFourRegevLeadingTerm (2 * index)) atTop (nhds 1) at hratio
    exact hratio
  · have hdenOdd : ∀ᶠ index : ℕ in atTop,
        heightFourRegevLeadingTerm (2 * index + 1) ≠ 0 := by
      filter_upwards with index
      unfold heightFourRegevLeadingTerm
      positivity
    change Tendsto (fun index : ℕ =>
      (heightFourTableauCount (2 * index + 1) : ℝ) /
        heightFourRegevLeadingTerm (2 * index + 1)) atTop (nhds 1)
    have hratio := (isEquivalent_iff_tendsto_one hdenOdd).mp
      heightFourTableau_odd_isEquivalent_regev
    change Tendsto (fun index : ℕ =>
      (heightFourTableauCount (2 * index + 1) : ℝ) /
        heightFourRegevLeadingTerm (2 * index + 1)) atTop (nhds 1) at hratio
    exact hratio

end FibonacciRibbonKernel
