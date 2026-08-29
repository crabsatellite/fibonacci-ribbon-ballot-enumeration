import FibonacciRibbonKernel.CoordinateScalingJacobian
import FibonacciRibbonKernel.FibonacciKernelLocalDomination

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable def allPlusScaledWeight
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  ∏ coordinate,
    (1 + Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))

def positiveOrthant {dimension : ℕ} : Set (Fin dimension → ℝ) :=
  Set.univ.pi fun _ : Fin dimension => Set.Ioi (0 : ℝ)

noncomputable def positiveScaledCube
    (dimension index : ℕ) : Set (Fin dimension → ℝ) :=
  Set.univ.pi fun _ : Fin dimension =>
    Set.Ioc (0 : ℝ) (Real.pi * Real.sqrt (index + 1 : ℝ))

noncomputable def positiveLocalScaledDomain
    (dimension index : ℕ) : Set (Fin dimension → ℝ) :=
  positiveScaledCube dimension index ∩
    {coordinates | cosineScaleMidpoint dimension ≤
      cosineSumScale coordinates index}

noncomputable def allPlusLocalRescaledIntegrand
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  (positiveLocalScaledDomain dimension index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        normalizedFibonacciCosineKernel coordinates index *
        allPlusScaledWeight dimension index coordinates)
    coordinates

noncomputable def allPlusLocalLimitIntegrand
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  positiveOrthant.indicator
    (fun coordinates =>
      (2 / Real.pi) ^ dimension *
        Real.exp
          ((-∑ coordinate, coordinates coordinate ^ 2) /
            Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)))
    coordinates

noncomputable def allPlusGaussianCoefficient (dimension : ℕ) : ℝ :=
  4 / (Real.pi ^ 2 *
    Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))

noncomputable def allPlusLocalDominating
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  ((1 / Real.pi) ^ dimension *
      (Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) /
        Real.sqrt (cosineScaleMidpoint dimension ^ 2 - 4)) *
      2 ^ dimension) *
    ∏ coordinate,
      Real.exp (-(allPlusGaussianCoefficient dimension) *
        coordinates coordinate ^ 2)

theorem allPlusGaussianCoefficient_pos
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ)) :
    0 < allPlusGaussianCoefficient dimension := by
  unfold allPlusGaussianCoefficient
  have hroot : 0 < Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4) := by
    apply Real.sqrt_pos.2
    nlinarith
  positivity

theorem allPlusScaledWeight_nonneg
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    0 ≤ allPlusScaledWeight dimension index coordinates := by
  unfold allPlusScaledWeight
  apply Finset.prod_nonneg
  intro coordinate _hcoordinate
  linarith [Real.neg_one_le_cos
    (coordinates coordinate / Real.sqrt (index + 1 : ℝ))]

theorem allPlusScaledWeight_le_two_pow
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    allPlusScaledWeight dimension index coordinates ≤ (2 : ℝ) ^ dimension := by
  unfold allPlusScaledWeight
  calc
    (∏ coordinate : Fin dimension,
        (1 + Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) ≤
      ∏ _coordinate : Fin dimension, (2 : ℝ) := by
        apply Finset.prod_le_prod
        · intro coordinate _hcoordinate
          linarith [Real.neg_one_le_cos
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ))]
        · intro coordinate _hcoordinate
          linarith [Real.cos_le_one
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ))]
    _ = (2 : ℝ) ^ dimension := by simp

theorem tendsto_allPlusScaledWeight
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index => allPlusScaledWeight dimension index coordinates)
      atTop (nhds ((2 : ℝ) ^ dimension)) := by
  have hsqrt : Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ))
      atTop atTop := by
    have hcast : Tendsto (fun index : ℕ => (index + 1 : ℝ)) atTop atTop := by
      have hbase := tendsto_natCast_atTop_atTop (R := ℝ)
      have hshift := hbase.comp (tendsto_add_atTop_nat 1)
      apply hshift.congr'
      filter_upwards with index
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have hraw := Real.tendsto_sqrt_atTop.comp hcast
    apply hraw.congr'
    filter_upwards with index
    rfl
  have hcoordinate : ∀ coordinate : Fin dimension,
      Tendsto (fun index : ℕ =>
        1 + Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))
        atTop (nhds 2) := by
    intro coordinate
    have hconstant : Tendsto (fun _ : ℕ => coordinates coordinate)
        atTop (nhds (coordinates coordinate)) := tendsto_const_nhds
    have hzero := hconstant.div_atTop hsqrt
    have hcosRaw := Real.continuous_cos.continuousAt.tendsto.comp hzero
    rw [Real.cos_zero] at hcosRaw
    have hcos : Tendsto (fun index : ℕ =>
        Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))
        atTop (nhds 1) := by
      apply hcosRaw.congr'
      filter_upwards with index
      rfl
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [one_add_one_eq_two] using hone.add hcos
  unfold allPlusScaledWeight
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    using tendsto_finsetProd (Finset.univ : Finset (Fin dimension))
      (fun coordinate _hcoordinate => hcoordinate coordinate)

theorem integrable_allPlusLocalDominating
    (dimension : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    Integrable (allPlusLocalDominating dimension) := by
  unfold allPlusLocalDominating
  rw [volume_pi]
  have hcoordinate : ∀ _coordinate : Fin dimension,
      Integrable (fun value : ℝ =>
        Real.exp (-(allPlusGaussianCoefficient dimension) * value ^ 2)) := by
    intro coordinate
    exact integrable_exp_neg_mul_sq (allPlusGaussianCoefficient_pos hdimension)
  exact (Integrable.fintype_prod hcoordinate).const_mul _

theorem continuous_fibonacciScaleKernel (power : ℕ) :
    Continuous (fun scale : ℝ => fibonacciScaleKernel scale power) := by
  induction power using Nat.twoStepInduction with
  | zero => simpa [fibonacciScaleKernel] using (continuous_const :
      Continuous (fun _ : ℝ => (1 : ℝ)))
  | one =>
      change Continuous (fun scale : ℝ => scale)
      fun_prop
  | more power hzero hone =>
      rw [show (fun scale : ℝ => fibonacciScaleKernel scale (power + 2)) =
          fun scale => scale * fibonacciScaleKernel scale (power + 1) -
            fibonacciScaleKernel scale power by
        funext scale
        rw [fibonacciScaleKernel_succ_succ]]
      exact (continuous_id.mul hone).sub hzero

theorem continuous_cosineSumScale
    (dimension index : ℕ) :
    Continuous (cosineSumScale (dimension := dimension) · index) := by
  unfold cosineSumScale
  fun_prop

theorem continuous_normalizedFibonacciCosineKernel
    (dimension index : ℕ) (_hdimension : 2 < (2 * dimension : ℝ)) :
    Continuous (normalizedFibonacciCosineKernel
      (dimension := dimension) · index) := by
  unfold normalizedFibonacciCosineKernel
  exact ((continuous_fibonacciScaleKernel index).comp
    (continuous_cosineSumScale dimension index)).div_const _

theorem continuous_allPlusScaledWeight (dimension index : ℕ) :
    Continuous (allPlusScaledWeight dimension index) := by
  unfold allPlusScaledWeight
  apply continuous_finsetProd
  intro coordinate _hcoordinate
  exact continuous_const.add <|
    Real.continuous_cos.comp <|
      (continuous_apply coordinate).div_const _

theorem measurableSet_positiveScaledCube (dimension index : ℕ) :
    MeasurableSet (positiveScaledCube dimension index) := by
  unfold positiveScaledCube
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem measurableSet_positiveLocalScaledDomain
    (dimension index : ℕ) :
    MeasurableSet (positiveLocalScaledDomain dimension index) := by
  unfold positiveLocalScaledDomain
  apply (measurableSet_positiveScaledCube dimension index).inter
  exact measurableSet_Ici.preimage
    (continuous_cosineSumScale dimension index).measurable

theorem aestronglyMeasurable_allPlusLocalRescaledIntegrand
    (dimension index : ℕ) (hdimension : 2 < (2 * dimension : ℝ)) :
    AEStronglyMeasurable (allPlusLocalRescaledIntegrand dimension index) := by
  unfold allPlusLocalRescaledIntegrand
  exact (((continuous_const.mul
      (continuous_normalizedFibonacciCosineKernel dimension index hdimension)).mul
        (continuous_allPlusScaledWeight dimension index)).stronglyMeasurable.indicator
          (measurableSet_positiveLocalScaledDomain dimension index)).aestronglyMeasurable

theorem eventually_mem_positiveScaledCube
    {dimension : ℕ} (coordinates : Fin dimension → ℝ)
    (hcoordinates : coordinates ∈ positiveOrthant) :
    ∀ᶠ index : ℕ in atTop,
      coordinates ∈ positiveScaledCube dimension index := by
  have hsqrt : Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ))
      atTop atTop := by
    have hcast : Tendsto (fun index : ℕ => (index + 1 : ℝ)) atTop atTop := by
      have hbase := tendsto_natCast_atTop_atTop (R := ℝ)
      have hshift := hbase.comp (tendsto_add_atTop_nat 1)
      apply hshift.congr'
      filter_upwards with index
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have hraw := Real.tendsto_sqrt_atTop.comp hcast
    apply hraw.congr'
    filter_upwards with index
    rfl
  have hbound : Tendsto
      (fun index : ℕ => Real.pi * Real.sqrt (index + 1 : ℝ))
      atTop atTop :=
    (tendsto_const_mul_atTop_of_pos Real.pi_pos).2 hsqrt
  unfold positiveScaledCube
  have hall : ∀ᶠ index : ℕ in atTop, ∀ coordinate : Fin dimension,
      coordinates coordinate ∈
        Set.Ioc (0 : ℝ) (Real.pi * Real.sqrt (index + 1 : ℝ)) := by
    rw [eventually_all]
    intro coordinate
    have hupper : ∀ᶠ index : ℕ in atTop,
        coordinates coordinate ≤ Real.pi * Real.sqrt (index + 1 : ℝ) :=
      (tendsto_atTop.1 hbound) (coordinates coordinate)
    filter_upwards [hupper] with index hindex
    have hpositive : 0 < coordinates coordinate :=
      hcoordinates coordinate (Set.mem_univ coordinate)
    exact ⟨hpositive, hindex⟩
  filter_upwards [hall] with index hindex
  intro coordinate _hcoordinate
  exact hindex coordinate

theorem eventually_mem_positiveLocalScaledDomain
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hcoordinates : coordinates ∈ positiveOrthant) :
    ∀ᶠ index : ℕ in atTop,
      coordinates ∈ positiveLocalScaledDomain dimension index := by
  have hcube := eventually_mem_positiveScaledCube coordinates hcoordinates
  have hscale := tendsto_cosineSumScale coordinates
  have hlocal : ∀ᶠ index : ℕ in atTop,
      cosineScaleMidpoint dimension ≤ cosineSumScale coordinates index :=
    ((tendsto_order.1 hscale).1 _
      (cosineScaleMidpoint_lt_base hdimension)).mono fun _ h => h.le
  filter_upwards [hcube, hlocal] with index hcubeIndex hlocalIndex
  exact ⟨hcubeIndex, hlocalIndex⟩

theorem tendsto_allPlusLocalRescaledIntegrand
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      allPlusLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds (allPlusLocalLimitIntegrand dimension coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveLocalScaledDomain
      hdimension coordinates horthant
    have hkernel := tendsto_normalizedFibonacciCosineKernel
      hdimension coordinates
    have hweight := tendsto_allPlusScaledWeight dimension coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    have hlimit :
        (1 / Real.pi) ^ dimension *
            Real.exp
              ((-∑ coordinate, coordinates coordinate ^ 2) /
                Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) *
            (2 : ℝ) ^ dimension =
          (2 / Real.pi) ^ dimension *
            Real.exp
              ((-∑ coordinate, coordinates coordinate ^ 2) /
                Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4)) := by
      rw [div_pow]
      ring
    rw [hlimit] at hproduct
    rw [allPlusLocalLimitIntegrand, Set.indicator_of_mem horthant]
    apply hproduct.congr'
    filter_upwards [hlocal] with index hindex
    rw [allPlusLocalRescaledIntegrand, Set.indicator_of_mem hindex]
  · have hnot : ∃ coordinate : Fin dimension, coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      apply horthant
      unfold positiveOrthant
      intro coordinate _hcoordinate
      exact hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveLocalScaledDomain dimension index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    have hzero : (fun index : ℕ =>
        allPlusLocalRescaledIntegrand dimension index coordinates) =
        fun _ => 0 := by
      funext index
      rw [allPlusLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)]
    rw [hzero, allPlusLocalLimitIntegrand,
      Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

theorem norm_allPlusLocalRescaledIntegrand_le
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (index : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖allPlusLocalRescaledIntegrand dimension index coordinates‖ ≤
      allPlusLocalDominating dimension coordinates := by
  by_cases hdomain : coordinates ∈ positiveLocalScaledDomain dimension index
  · rw [allPlusLocalRescaledIntegrand, Set.indicator_of_mem hdomain,
      Real.norm_eq_abs, abs_of_nonneg]
    · have hcube := hdomain.1
      have hcoordinate : ∀ coordinate,
          |coordinates coordinate| ≤
            Real.pi * Real.sqrt (index + 1 : ℝ) := by
        intro coordinate
        have hmem := hcube coordinate (Set.mem_univ coordinate)
        rw [abs_of_pos hmem.1]
        exact hmem.2
      have hkernel := normalizedFibonacciCosineKernel_le_local_gaussian
        hdimension coordinates hcoordinate hdomain.2
      have hweight := allPlusScaledWeight_le_two_pow
        dimension index coordinates
      have hkernelNonneg := normalizedFibonacciCosineKernel_nonneg
        hdimension coordinates
        ((cosineScaleMidpoint_gt_two hdimension).trans_le hdomain.2)
      have hweightNonneg := allPlusScaledWeight_nonneg
        dimension index coordinates
      unfold allPlusLocalDominating allPlusGaussianCoefficient
      have hproduct := mul_le_mul hkernel hweight hweightNonneg
        (by positivity)
      calc
        (1 / Real.pi) ^ dimension *
            normalizedFibonacciCosineKernel coordinates index *
            allPlusScaledWeight dimension index coordinates =
          (1 / Real.pi) ^ dimension *
            (normalizedFibonacciCosineKernel coordinates index *
              allPlusScaledWeight dimension index coordinates) := by ring
        _ ≤
          (1 / Real.pi) ^ dimension *
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
    · exact mul_nonneg
        (mul_nonneg (by positivity)
          (normalizedFibonacciCosineKernel_nonneg hdimension coordinates
            ((cosineScaleMidpoint_gt_two hdimension).trans_le hdomain.2)))
        (allPlusScaledWeight_nonneg dimension index coordinates)
  · rw [allPlusLocalRescaledIntegrand,
      Set.indicator_of_notMem hdomain, norm_zero]
    unfold allPlusLocalDominating
    positivity

end FibonacciRibbonKernel
