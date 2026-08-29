import FibonacciRibbonKernel.FibonacciMiddleIntegral

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable def allMinusScaledWeight
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  ∏ coordinate,
    (1 - Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))

noncomputable def allMinusLocalRescaledIntegrand
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  (positiveLocalScaledDomain dimension index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        normalizedFibonacciCosineKernel coordinates index *
        allMinusScaledWeight dimension index coordinates)
    coordinates

theorem allMinusScaledWeight_nonneg
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    0 ≤ allMinusScaledWeight dimension index coordinates := by
  unfold allMinusScaledWeight
  apply Finset.prod_nonneg
  intro coordinate _hcoordinate
  linarith [Real.cos_le_one
    (coordinates coordinate / Real.sqrt (index + 1 : ℝ))]

theorem allMinusScaledWeight_le_two_pow
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    allMinusScaledWeight dimension index coordinates ≤ (2 : ℝ) ^ dimension := by
  unfold allMinusScaledWeight
  calc
    (∏ coordinate : Fin dimension,
        (1 - Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) ≤
      ∏ _coordinate : Fin dimension, (2 : ℝ) := by
        apply Finset.prod_le_prod
        · intro coordinate _hcoordinate
          linarith [Real.cos_le_one
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ))]
        · intro coordinate _hcoordinate
          linarith [Real.neg_one_le_cos
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ))]
    _ = (2 : ℝ) ^ dimension := by simp

theorem tendsto_allMinusScaledWeight
    {dimension : ℕ} (hdimension : 0 < dimension)
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index => allMinusScaledWeight dimension index coordinates)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ))
      atTop atTop := by
    have hcast : Tendsto (fun index : ℕ => (index + 1 : ℝ)) atTop atTop := by
      have hbase := tendsto_natCast_atTop_atTop (R := ℝ)
      have hshift := hbase.comp (tendsto_add_atTop_nat 1)
      apply hshift.congr'
      filter_upwards with index
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    exact Real.tendsto_sqrt_atTop.comp hcast
  have hcoordinate : ∀ coordinate : Fin dimension,
      Tendsto (fun index : ℕ =>
        1 - Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))
        atTop (nhds 0) := by
    intro coordinate
    have hconstant : Tendsto (fun _ : ℕ => coordinates coordinate)
        atTop (nhds (coordinates coordinate)) := tendsto_const_nhds
    have hzero := hconstant.div_atTop hsqrt
    have hcos := Real.continuous_cos.continuousAt.tendsto.comp hzero
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hone.sub hcos
  unfold allMinusScaledWeight
  have hprod := tendsto_finsetProd (Finset.univ : Finset (Fin dimension))
    (fun coordinate _hcoordinate => hcoordinate coordinate)
  simpa [Finset.prod_const, zero_pow hdimension.ne'] using hprod

theorem continuous_allMinusScaledWeight (dimension index : ℕ) :
    Continuous (allMinusScaledWeight dimension index) := by
  unfold allMinusScaledWeight
  apply continuous_finsetProd
  intro coordinate _hcoordinate
  exact continuous_const.sub <|
    Real.continuous_cos.comp <|
      (continuous_apply coordinate).div_const _

theorem aestronglyMeasurable_allMinusLocalRescaledIntegrand
    (dimension index : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    AEStronglyMeasurable
      (allMinusLocalRescaledIntegrand dimension index) := by
  unfold allMinusLocalRescaledIntegrand
  exact (((continuous_const.mul
      (continuous_normalizedFibonacciCosineKernel
        dimension index hdimension)).mul
      (continuous_allMinusScaledWeight dimension index)).stronglyMeasurable.indicator
        (measurableSet_positiveLocalScaledDomain dimension index)).aestronglyMeasurable

theorem tendsto_allMinusLocalRescaledIntegrand
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      allMinusLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds 0) := by
  have hdimensionPos : 0 < dimension := by
    by_contra hzero
    have : dimension = 0 := Nat.eq_zero_of_not_pos hzero
    subst dimension
    norm_num at hdimension
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain
      hdimension coordinates horthant
    have hkernel := tendsto_normalizedFibonacciCosineKernel
      hdimension coordinates
    have hweight := tendsto_allMinusScaledWeight hdimensionPos coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    simpa only [mul_zero] using hproduct.congr' (by
      filter_upwards [hlocal] with index hindex
      rw [allMinusLocalRescaledIntegrand, indicator_of_mem hindex])
  · have hnot : ∃ coordinate : Fin dimension, coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _hcoordinate => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveLocalScaledDomain dimension index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    have hzero : (fun index : ℕ =>
        allMinusLocalRescaledIntegrand dimension index coordinates) =
        fun _ => 0 := by
      funext index
      rw [allMinusLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)]
    rw [hzero]
    exact tendsto_const_nhds

theorem norm_allMinusLocalRescaledIntegrand_le
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖allMinusLocalRescaledIntegrand dimension index coordinates‖ ≤
      allPlusLocalDominating dimension coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [allMinusLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      norm_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by positivity) _),
      Real.norm_eq_abs,
      abs_of_nonneg (normalizedFibonacciCosineKernel_nonneg
        hdimension coordinates
        ((cosineScaleMidpoint_gt_two hdimension).trans_le hdomain.2)),
      Real.norm_eq_abs,
      abs_of_nonneg (allMinusScaledWeight_nonneg dimension index coordinates)]
    have hcube := hdomain.1
    have hcoordinate : ∀ coordinate,
        |coordinates coordinate| ≤
          Real.pi * Real.sqrt (index + 1 : ℝ) := by
      intro coordinate
      have hmem := hcube coordinate (Set.mem_univ coordinate)
      rw [abs_of_pos hmem.1]
      exact hmem.2
    have hkernel := normalizedFibonacciCosineKernel_le_local_gaussian
      hdimension coordinates hcoordinate hdomain.2
    have hweight := allMinusScaledWeight_le_two_pow
      dimension index coordinates
    have hkernelNonneg := normalizedFibonacciCosineKernel_nonneg
      hdimension coordinates
      ((cosineScaleMidpoint_gt_two hdimension).trans_le hdomain.2)
    have hweightNonneg := allMinusScaledWeight_nonneg
      dimension index coordinates
    unfold allPlusLocalDominating allPlusGaussianCoefficient
    have hproduct := mul_le_mul hkernel hweight hweightNonneg
      (by positivity)
    calc
      (1 / Real.pi) ^ dimension *
          normalizedFibonacciCosineKernel coordinates index *
          allMinusScaledWeight dimension index coordinates =
        (1 / Real.pi) ^ dimension *
          (normalizedFibonacciCosineKernel coordinates index *
            allMinusScaledWeight dimension index coordinates) := by ring
      _ ≤ (1 / Real.pi) ^ dimension *
          ((Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
              Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4)) *
            Real.exp
              (-(4 / (Real.pi ^ 2 *
                Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
                  ∑ coordinate, coordinates coordinate ^ 2) *
            2 ^ dimension) :=
        mul_le_mul_of_nonneg_left hproduct (by positivity)
      _ = ((1 / Real.pi) ^ dimension *
            (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
              Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4)) *
            2 ^ dimension) *
          ∏ coordinate,
            Real.exp
              (-(4 / (Real.pi ^ 2 *
                Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
                  coordinates coordinate ^ 2) := by
        have hexponent :
            -(4 / (Real.pi ^ 2 *
                Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
                  (∑ coordinate, coordinates coordinate ^ 2) =
              ∑ coordinate,
                -(4 / (Real.pi ^ 2 *
                  Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
                    coordinates coordinate ^ 2 := by
          rw [Finset.mul_sum]
        rw [← Real.exp_sum, ← hexponent]
        ring
  · rw [allMinusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold allPlusLocalDominating
    positivity

theorem tendsto_integral_allMinusLocalRescaledIntegrand
    (dimension : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    Tendsto
      (fun index => ∫ coordinates,
        allMinusLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds 0) := by
  simpa using tendsto_integral_of_dominated_convergence
    (allPlusLocalDominating dimension)
    (fun index =>
      aestronglyMeasurable_allMinusLocalRescaledIntegrand
        dimension index hdimension)
    (integrable_allPlusLocalDominating dimension hdimension)
    (fun index => Filter.Eventually.of_forall fun coordinates =>
      norm_allMinusLocalRescaledIntegrand_le hdimension index coordinates)
    (Filter.Eventually.of_forall fun coordinates =>
      tendsto_allMinusLocalRescaledIntegrand hdimension coordinates)

end FibonacciRibbonKernel
