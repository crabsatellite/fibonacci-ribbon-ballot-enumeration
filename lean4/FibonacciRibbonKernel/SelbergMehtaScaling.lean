import FibonacciRibbonKernel.MehtaGaussianDomination
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical Topology BigOperators

noncomputable def selbergMehtaScalarWeight (index : ℕ)
    (value : ℝ) : ℝ :=
  (1 - value ^ 2 / (2 * ((index + 2 : ℕ) : ℝ))) ^ (index + 1)

def selbergMehtaScalarDomain (index : ℕ) (value : ℝ) : Prop :=
  value ^ 2 < 2 * ((index + 2 : ℕ) : ℝ)

theorem selbergMehtaScalarWeight_nonneg
    (index : ℕ) {value : ℝ}
    (hvalue : selbergMehtaScalarDomain index value) :
    0 ≤ selbergMehtaScalarWeight index value := by
  unfold selbergMehtaScalarWeight selbergMehtaScalarDomain at *
  apply pow_nonneg
  have hdenominator : 0 < 2 * ((index + 2 : ℕ) : ℝ) := by positivity
  rw [sub_nonneg, div_le_one hdenominator]
  exact hvalue.le

theorem selbergMehtaScalarWeight_le_gaussian
    (index : ℕ) {value : ℝ}
    (hvalue : selbergMehtaScalarDomain index value) :
    selbergMehtaScalarWeight index value ≤
      Real.exp (-(1 / 4 : ℝ) * value ^ 2) := by
  let denominator : ℝ := 2 * ((index + 2 : ℕ) : ℝ)
  let exponent : ℕ := index + 1
  let scaled : ℝ := ((exponent : ℕ) : ℝ) * value ^ 2 / denominator
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hexponent : 0 < exponent := by
    dsimp only [exponent]
    omega
  have hscaledLe : scaled ≤ exponent := by
    dsimp only [scaled]
    rw [div_le_iff₀ hdenominator]
    have hdomain : value ^ 2 ≤ denominator := hvalue.le
    nlinarith
  have hbound := Real.one_sub_div_pow_le_exp_neg
    (n := exponent) (t := scaled) hscaledLe
  have hbase : 1 - scaled / exponent =
      1 - value ^ 2 / denominator := by
    dsimp only [scaled]
    have hexponentReal : ((exponent : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hexponentReal]
  rw [hbase] at hbound
  have hscaledLower : (1 / 4 : ℝ) * value ^ 2 ≤ scaled := by
    dsimp only [scaled, denominator, exponent]
    have hdenominator' : 0 < (2 : ℝ) * ((index + 2 : ℕ) : ℝ) := by
      positivity
    rw [le_div_iff₀ hdenominator']
    push_cast
    nlinarith [sq_nonneg value]
  have hexp : Real.exp (-scaled) ≤
      Real.exp (-(1 / 4 : ℝ) * value ^ 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact hbound.trans hexp

theorem tendsto_selbergMehtaScalarWeight (value : ℝ) :
    Tendsto (fun index => selbergMehtaScalarWeight index value)
      atTop (nhds (Real.exp (-(1 / 2 : ℝ) * value ^ 2))) := by
  let g : ℕ → ℝ := fun n =>
    -value ^ 2 / (2 * ((n + 1 : ℕ) : ℝ))
  have hratio : Tendsto (fun n : ℕ =>
      (n : ℝ) / (n + 1 : ℝ)) atTop (nhds 1) := by
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hg : Tendsto (fun n : ℕ => (n : ℝ) * g n)
      atTop (nhds (-(1 / 2 : ℝ) * value ^ 2)) := by
    have hmul := hratio.const_mul (-(1 / 2 : ℝ) * value ^ 2)
    convert hmul using 1
    · funext n
      dsimp only [g]
      have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp [hn1]
    · ring
  have hlimit := Real.tendsto_one_add_pow_exp_of_tendsto hg
  have hshift := hlimit.comp (tendsto_add_atTop_nat 1)
  convert hshift using 1
  funext index
  unfold selbergMehtaScalarWeight
  dsimp only [g]
  congr 1
  push_cast
  ring

def selbergMehtaScaledDomain (dimension index : ℕ) :
    Set (Fin dimension → ℝ) :=
  {coordinates | ∀ coordinate,
      selbergMehtaScalarDomain index (coordinates coordinate)} ∩
    standardMehtaChamber dimension

noncomputable def selbergMehtaRescaledIntegrand
    (dimension index : ℕ) : (Fin dimension → ℝ) → ℝ :=
  (selbergMehtaScaledDomain dimension index).indicator fun coordinates =>
    (∏ coordinate, selbergMehtaScalarWeight index
      (coordinates coordinate)) *
      standardMehtaVandermonde dimension coordinates

noncomputable def standardMehtaChamberRestricted (dimension : ℕ) :
    (Fin dimension → ℝ) → ℝ :=
  (standardMehtaChamber dimension).indicator
    (standardMehtaIntegrand dimension)

theorem selbergMehtaScaledDomain_measurableSet
    (dimension index : ℕ) :
    MeasurableSet (selbergMehtaScaledDomain dimension index) := by
  unfold selbergMehtaScaledDomain selbergMehtaScalarDomain
  apply MeasurableSet.inter
  · have hrepresentation :
        {coordinates : Fin dimension → ℝ |
          ∀ coordinate, coordinates coordinate ^ 2 <
            2 * ((index + 2 : ℕ) : ℝ)} =
        ⋂ coordinate : Fin dimension,
          {coordinates : Fin dimension → ℝ |
            coordinates coordinate ^ 2 <
              2 * ((index + 2 : ℕ) : ℝ)} := by
      ext coordinates
      simp
    rw [hrepresentation]
    apply MeasurableSet.iInter
    intro coordinate
    have hcoordinate : Measurable
        (fun coordinates : Fin dimension → ℝ =>
          coordinates coordinate) := measurable_pi_apply coordinate
    exact measurableSet_lt (hcoordinate.pow measurable_const)
      measurable_const
  · exact (standardMehtaChamber_isClosed dimension).measurableSet

theorem aestronglyMeasurable_selbergMehtaRescaledIntegrand
    (dimension index : ℕ) :
    AEStronglyMeasurable
      (selbergMehtaRescaledIntegrand dimension index) := by
  unfold selbergMehtaRescaledIntegrand
  apply AEStronglyMeasurable.indicator
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · apply continuous_finsetProd Finset.univ
      intro coordinate hcoordinate
      unfold selbergMehtaScalarWeight
      fun_prop
    · exact continuous_standardMehtaVandermonde dimension
  · exact selbergMehtaScaledDomain_measurableSet dimension index

theorem norm_selbergMehtaRescaledIntegrand_le_dominating
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖selbergMehtaRescaledIntegrand dimension index coordinates‖ ≤
      mehtaLeibnizDominating dimension coordinates := by
  by_cases hcoordinates :
      coordinates ∈ selbergMehtaScaledDomain dimension index
  · rw [selbergMehtaRescaledIntegrand,
      Set.indicator_of_mem hcoordinates]
    have hweights :
        (∏ coordinate, selbergMehtaScalarWeight index
          (coordinates coordinate)) ≤
        ∏ coordinate,
          Real.exp (-(1 / 4 : ℝ) * coordinates coordinate ^ 2) := by
      apply Finset.prod_le_prod
      · intro coordinate hcoordinate
        exact selbergMehtaScalarWeight_nonneg index
          (hcoordinates.1 coordinate)
      · intro coordinate hcoordinate
        exact selbergMehtaScalarWeight_le_gaussian
          index (hcoordinates.1 coordinate)
    have hexponential :
        (∏ coordinate,
          Real.exp (-(1 / 4 : ℝ) * coordinates coordinate ^ 2)) =
        Real.exp (-(1 / 4 : ℝ) *
          ∑ coordinate, coordinates coordinate ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum]
    rw [hexponential] at hweights
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun coordinate hcoordinate =>
        selbergMehtaScalarWeight_nonneg index
          (hcoordinates.1 coordinate)),
      abs_of_nonneg (by
        unfold standardMehtaVandermonde
        exact Finset.prod_nonneg fun first hfirst =>
          Finset.prod_nonneg fun next hnext => abs_nonneg _)]
    exact (mul_le_mul_of_nonneg_right hweights (by
      unfold standardMehtaVandermonde
      exact Finset.prod_nonneg fun first hfirst =>
        Finset.prod_nonneg fun next hnext => abs_nonneg _)).trans
      (quarterGaussianVandermonde_le_dominating dimension coordinates)
  · rw [selbergMehtaRescaledIntegrand,
      Set.indicator_of_notMem hcoordinates, norm_zero]
    unfold mehtaLeibnizDominating mehtaLeibnizTerm
    exact Finset.sum_nonneg fun permutation hpermutation =>
      Finset.prod_nonneg fun coordinate hcoordinate =>
        mul_nonneg (pow_nonneg (abs_nonneg _) _)
          (Real.exp_pos _).le

theorem tendsto_selbergMehtaRescaledIntegrand
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      selbergMehtaRescaledIntegrand dimension index coordinates)
      atTop (nhds (standardMehtaChamberRestricted dimension coordinates)) := by
  by_cases hchamber : coordinates ∈ standardMehtaChamber dimension
  · have hscale : Tendsto (fun index : ℕ =>
        (2 : ℝ) * ((index + 2 : ℕ) : ℝ)) atTop atTop := by
      have hnat := tendsto_add_atTop_nat 2
      have hcast : Tendsto (fun index : ℕ =>
          ((index + 2 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_iff.mpr hnat
      exact Tendsto.const_mul_atTop (by norm_num) hcast
    have hevent : ∀ᶠ index : ℕ in atTop,
        ∀ coordinate : Fin dimension,
          selbergMehtaScalarDomain index (coordinates coordinate) := by
      rw [Filter.eventually_all]
      intro coordinate
      exact hscale.eventually (Ioi_mem_atTop (coordinates coordinate ^ 2))
    have hproduct : Tendsto (fun index =>
        ∏ coordinate, selbergMehtaScalarWeight index
          (coordinates coordinate)) atTop
        (nhds (Real.exp (-(1 / 2 : ℝ) *
          ∑ coordinate, coordinates coordinate ^ 2))) := by
      have hprod := tendsto_finsetProd Finset.univ fun coordinate hcoordinate =>
        tendsto_selbergMehtaScalarWeight (coordinates coordinate)
      convert hprod using 1
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum]
    have hlimit := hproduct.mul_const
      (standardMehtaVandermonde dimension coordinates)
    rw [standardMehtaChamberRestricted,
      Set.indicator_of_mem hchamber]
    unfold standardMehtaIntegrand standardMehtaGaussian
    have hgaussian :
        Real.exp (-(∑ row, coordinates row ^ 2 / 2)) =
          Real.exp (-(1 / 2 : ℝ) *
            ∑ row, coordinates row ^ 2) := by
      congr 1
      rw [← Finset.sum_div]
      ring
    rw [hgaussian]
    apply hlimit.congr'
    filter_upwards [hevent] with index hindex
    have hmem : coordinates ∈ selbergMehtaScaledDomain dimension index :=
      ⟨hindex, hchamber⟩
    rw [selbergMehtaRescaledIntegrand,
      Set.indicator_of_mem hmem]
  · have hzero : (fun index =>
        selbergMehtaRescaledIntegrand dimension index coordinates) =
        fun _ => 0 := by
      funext index
      rw [selbergMehtaRescaledIntegrand, Set.indicator_of_notMem]
      intro hscaled
      exact hchamber hscaled.2
    rw [hzero, standardMehtaChamberRestricted,
      Set.indicator_of_notMem hchamber]
    exact tendsto_const_nhds

theorem tendsto_integral_selbergMehtaRescaledIntegrand
    (dimension : ℕ) :
    Tendsto (fun index => ∫ coordinates,
      selbergMehtaRescaledIntegrand dimension index coordinates)
      atTop (nhds (standardMehtaChamberIntegral dimension)) := by
  have hdominated := tendsto_integral_of_dominated_convergence
    (mehtaLeibnizDominating dimension)
    (fun index => aestronglyMeasurable_selbergMehtaRescaledIntegrand
      dimension index)
    (integrable_mehtaLeibnizDominating dimension)
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_selbergMehtaRescaledIntegrand_le_dominating
        dimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_selbergMehtaRescaledIntegrand dimension coordinates)
  unfold standardMehtaChamberRestricted at hdominated
  rw [integral_indicator
    (standardMehtaChamber_isClosed dimension).measurableSet] at hdominated
  exact hdominated

noncomputable def selbergMehtaScale (index : ℕ) : ℝ :=
  Real.sqrt (8 * ((index + 2 : ℕ) : ℝ))

noncomputable def selbergMehtaAffine (dimension index : ℕ)
    (coordinates : Fin dimension → ℝ) : Fin dimension → ℝ :=
  fun coordinate => (1 / 2 : ℝ) +
    coordinates coordinate / selbergMehtaScale index

theorem selbergMehtaScale_pos (index : ℕ) :
    0 < selbergMehtaScale index := by
  unfold selbergMehtaScale
  positivity

theorem selbergMehtaScale_sq (index : ℕ) :
    selbergMehtaScale index ^ 2 =
      8 * ((index + 2 : ℕ) : ℝ) := by
  unfold selbergMehtaScale
  rw [Real.sq_sqrt]
  positivity

theorem selbergMehtaAffine_coordinate_mem_iff
    (index : ℕ) (value : ℝ) :
    (1 / 2 + value / selbergMehtaScale index) ∈ Set.Ioo (0 : ℝ) 1 ↔
      selbergMehtaScalarDomain index value := by
  let scale := selbergMehtaScale index
  have hscale : 0 < scale := selbergMehtaScale_pos index
  have hsquare : scale ^ 2 = 8 * ((index + 2 : ℕ) : ℝ) :=
    selbergMehtaScale_sq index
  have hfirst : scale * (1 / 2 + value / scale) = scale / 2 + value := by
    field_simp [hscale.ne']
  have hsecond : scale * (1 - (1 / 2 + value / scale)) =
      scale / 2 - value := by
    field_simp [hscale.ne']
    ring
  unfold selbergMehtaScalarDomain
  constructor
  · intro hvalue
    have hlower : 0 < scale / 2 + value := by
      rw [← hfirst]
      exact mul_pos hscale hvalue.1
    have hupper : 0 < scale / 2 - value := by
      rw [← hsecond]
      exact mul_pos hscale (sub_pos.mpr hvalue.2)
    nlinarith
  · intro hsquareValue
    have hlower : 0 < scale / 2 + value := by
      by_contra hnot
      have hle : value ≤ -scale / 2 := by linarith
      nlinarith
    have hupper : 0 < scale / 2 - value := by
      by_contra hnot
      have hle : scale / 2 ≤ value := by linarith
      nlinarith
    constructor
    · have hpositive : 0 < scale *
          (1 / 2 + value / scale) := by
        rw [hfirst]
        exact hlower
      exact (mul_pos_iff_of_pos_left hscale).mp hpositive
    · have hpositive : 0 < scale *
          (1 - (1 / 2 + value / scale)) := by
        rw [hsecond]
        exact hupper
      have := (mul_pos_iff_of_pos_left hscale).mp hpositive
      linarith

theorem selbergMehtaAffine_antitone_iff
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    Antitone (selbergMehtaAffine dimension index coordinates) ↔
      Antitone coordinates := by
  have hscale := selbergMehtaScale_pos index
  constructor
  · intro h first next hle
    have hvalue := h hle
    unfold selbergMehtaAffine at hvalue
    have hdiv : coordinates next / selbergMehtaScale index ≤
        coordinates first / selbergMehtaScale index := by linarith
    exact (div_le_div_iff_of_pos_right hscale).mp hdiv
  · intro h first next hle
    unfold selbergMehtaAffine
    have hvalue := h hle
    have hdiv := (div_le_div_iff_of_pos_right hscale).mpr hvalue
    linarith

theorem selbergMehtaAffine_mem_ordered_iff_scaled
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    selbergMehtaAffine dimension index coordinates ∈
        orderedSelbergDomain dimension ↔
      coordinates ∈ selbergMehtaScaledDomain dimension index := by
  unfold orderedSelbergDomain selbergUnitBox
  unfold selbergMehtaScaledDomain
  simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · rintro ⟨hbox, hchamber⟩
    constructor
    · intro coordinate
      exact (selbergMehtaAffine_coordinate_mem_iff
        index (coordinates coordinate)).mp (hbox coordinate)
    · exact (selbergMehtaAffine_antitone_iff
        dimension index coordinates).mp hchamber
  · rintro ⟨hbox, hchamber⟩
    constructor
    · intro coordinate
      exact (selbergMehtaAffine_coordinate_mem_iff
        index (coordinates coordinate)).mpr (hbox coordinate)
    · exact (selbergMehtaAffine_antitone_iff
        dimension index coordinates).mpr hchamber

def mehtaPairCount (dimension : ℕ) : ℕ :=
  ∑ first : Fin dimension, (Finset.Ioi first).card

noncomputable def selbergMehtaNormalization
    (dimension index : ℕ) : ℝ :=
  (4 : ℝ) ^ ((index + 1) * dimension) *
    selbergMehtaScale index ^ (dimension + mehtaPairCount dimension)

theorem selbergHalfWeight_affine_eq
    (index : ℕ) {value : ℝ}
    (hvalue : selbergMehtaScalarDomain index value) :
    selbergHalfWeight ((index + 2 : ℕ) : ℝ)
        ((index + 2 : ℕ) : ℝ)
        (1 / 2 + value / selbergMehtaScale index) =
      (1 / 4 : ℝ) ^ (index + 1) *
        selbergMehtaScalarWeight index value := by
  let scale := selbergMehtaScale index
  let affine := 1 / 2 + value / scale
  have haffine : affine ∈ Set.Ioo (0 : ℝ) 1 :=
    (selbergMehtaAffine_coordinate_mem_iff index value).mpr hvalue
  have hscale : 0 < scale := selbergMehtaScale_pos index
  have hsquare : scale ^ 2 = 8 * ((index + 2 : ℕ) : ℝ) :=
    selbergMehtaScale_sq index
  have hexponent : (((index + 2 : ℕ) : ℝ) - 1) =
      ((index + 1 : ℕ) : ℝ) := by push_cast; ring
  have hproduct : affine * (1 - affine) =
      (1 / 4 : ℝ) *
        (1 - value ^ 2 / (2 * ((index + 2 : ℕ) : ℝ))) := by
    dsimp only [affine, scale]
    have hscaleNe : selbergMehtaScale index ≠ 0 := hscale.ne'
    field_simp [hscaleNe]
    nlinarith
  unfold selbergHalfWeight selbergMehtaScalarWeight
  change affine ^ ((((index + 2 : ℕ) : ℝ)) - 1) *
      (1 - affine) ^ ((((index + 2 : ℕ) : ℝ)) - 1) = _
  rw [hexponent, Real.rpow_natCast, Real.rpow_natCast]
  rw [← mul_pow, hproduct, mul_pow]

theorem standardMehtaVandermonde_affine
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    standardMehtaVandermonde dimension
        (selbergMehtaAffine dimension index coordinates) =
      (selbergMehtaScale index)⁻¹ ^ mehtaPairCount dimension *
        standardMehtaVandermonde dimension coordinates := by
  have hscale : 0 < selbergMehtaScale index :=
    selbergMehtaScale_pos index
  have hfactor (first next : Fin dimension) :
      |selbergMehtaAffine dimension index coordinates first -
          selbergMehtaAffine dimension index coordinates next| =
        (selbergMehtaScale index)⁻¹ *
          |coordinates first - coordinates next| := by
    unfold selbergMehtaAffine
    have hscaleNe := hscale.ne'
    rw [show (1 / 2 + coordinates first / selbergMehtaScale index) -
        (1 / 2 + coordinates next / selbergMehtaScale index) =
      (coordinates first - coordinates next) /
        selbergMehtaScale index by field_simp [hscaleNe]; ring]
    rw [abs_div, abs_of_pos hscale]
    field_simp [hscaleNe]
  unfold standardMehtaVandermonde
  simp_rw [hfactor]
  simp_rw [Finset.prod_mul_distrib]
  congr 1
  · simp only [Finset.prod_const]
    simpa [mehtaPairCount] using
      Finset.prod_pow_eq_pow_sum
        (Finset.univ : Finset (Fin dimension))
        (fun first => (Finset.Ioi first).card)
        (selbergMehtaScale index)⁻¹

theorem selbergHalfIntegrand_affine_eq
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ)
    (hcoordinates : coordinates ∈
      selbergMehtaScaledDomain dimension index) :
    selbergHalfIntegrand dimension ((index + 2 : ℕ) : ℝ)
        ((index + 2 : ℕ) : ℝ)
        (selbergMehtaAffine dimension index coordinates) =
      (1 / 4 : ℝ) ^ ((index + 1) * dimension) *
        (selbergMehtaScale index)⁻¹ ^ mehtaPairCount dimension *
          ((∏ coordinate, selbergMehtaScalarWeight index
            (coordinates coordinate)) *
            standardMehtaVandermonde dimension coordinates) := by
  unfold selbergHalfIntegrand
  rw [show (∏ row,
      selbergHalfWeight ((index + 2 : ℕ) : ℝ)
        ((index + 2 : ℕ) : ℝ)
        (selbergMehtaAffine dimension index coordinates row)) =
    ∏ row, (1 / 4 : ℝ) ^ (index + 1) *
      selbergMehtaScalarWeight index (coordinates row) by
    apply Finset.prod_congr rfl
    intro row hrow
    exact selbergHalfWeight_affine_eq index (hcoordinates.1 row)]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  rw [standardMehtaVandermonde_affine]
  ring

end FibonacciRibbonKernel
