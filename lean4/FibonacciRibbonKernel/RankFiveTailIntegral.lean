import FibonacciRibbonKernel.RankFiveTailDecay

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def rankFivePositiveSpectralDomain : Set (Fin 2 → ℝ) :=
  {angles | oddCosineScaleMidpoint 2 ≤ oddCosineCubeScale angles}

noncomputable def rankFiveTailSpectralDomain : Set (Fin 2 → ℝ) :=
  {angles | oddCosineCubeScale angles < oddCosineScaleMidpoint 2}

noncomputable def rankFiveFullNormalizedIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  (1 / Real.pi) ^ 2 *
    (fibonacciScaleKernel (oddCosineCubeScale angles) index /
      (largeScalePreimage 5 ^ (index + 1) / Real.sqrt 21)) *
    oddWeylAngleWeight 2 angles

noncomputable def rankFiveLocalProductIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  rankFivePositiveSpectralDomain.indicator
    (rankFiveFullNormalizedIntegrand index) angles

noncomputable def rankFiveTailProductIntegrand
    (index : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  rankFiveTailSpectralDomain.indicator
    (rankFiveFullNormalizedIntegrand index) angles

noncomputable def rankFiveFullNormalizedIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFiveFullNormalizedIntegrand index angles
    ∂cosineCubeProductMeasure 2

noncomputable def rankFiveTailNormalizedIntegral (index : ℕ) : ℝ :=
  ∫ angles : Fin 2 → ℝ, rankFiveTailProductIntegrand index angles
    ∂cosineCubeProductMeasure 2

theorem oddWeylAngleWeight_two_le_four (angles : Fin 2 → ℝ) :
    oddWeylAngleWeight 2 angles ≤ 4 := by
  unfold oddWeylAngleWeight cosineVandermondeWeight
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]
  have hzero : Finset.Iio (0 : Fin 2) = ∅ := by decide
  have hone : Finset.Iio (1 : Fin 2) = {0} := by decide
  rw [hzero, hone]
  simp only [Finset.prod_empty, Finset.prod_singleton, one_mul]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]
  let left := Real.cos (angles 0)
  let right := Real.cos (angles 1)
  have hleftLower : -1 ≤ left := Real.neg_one_le_cos _
  have hleftUpper : left ≤ 1 := Real.cos_le_one _
  have hrightLower : -1 ≤ right := Real.neg_one_le_cos _
  have hrightUpper : right ≤ 1 := Real.cos_le_one _
  have hdiff : (right - left) ^ 2 ≤ 4 := by nlinarith
  have hleftFactor : 0 ≤ (1 - left) * (1 + left) := by nlinarith
  have hleftFactorLe : (1 - left) * (1 + left) ≤ 1 := by
    nlinarith [sq_nonneg left]
  have hrightFactor : 0 ≤ (1 - right) * (1 + right) := by nlinarith
  have hrightFactorLe : (1 - right) * (1 + right) ≤ 1 := by
    nlinarith [sq_nonneg right]
  have hcoordinateProduct :
      (1 - left) * (1 + left) * ((1 - right) * (1 + right)) ≤ 1 := by
    simpa only [mul_one] using
      mul_le_mul hleftFactorLe hrightFactorLe hrightFactor (by norm_num)
  have htotal := mul_le_mul hdiff hcoordinateProduct
    (mul_nonneg hleftFactor hrightFactor) (by norm_num : (0 : ℝ) ≤ 4)
  dsimp only [left, right] at *
  simpa [mul_assoc] using htotal

theorem oddWeylAngleWeight_two_nonneg (angles : Fin 2 → ℝ) :
    0 ≤ oddWeylAngleWeight 2 angles :=
  oddWeylAngleWeight_nonneg 2 angles

theorem abs_oddCosineCubeScale_le_midpoint_of_tail
    {angles : Fin 2 → ℝ} (hangles : angles ∈ rankFiveTailSpectralDomain) :
    |oddCosineCubeScale angles| ≤ 7 / 2 := by
  have hupper : oddCosineCubeScale angles < 7 / 2 := by
    change oddCosineCubeScale angles < oddCosineScaleMidpoint 2 at hangles
    norm_num [oddCosineScaleMidpoint] at hangles ⊢
    exact hangles
  have hlower : -(3 : ℝ) ≤ oddCosineCubeScale angles := by
    unfold oddCosineCubeScale cosineCubeScale
    have hzero := Real.neg_one_le_cos (angles 0)
    have hone := Real.neg_one_le_cos (angles 1)
    rw [show (∑ coordinate : Fin 2, Real.cos (angles coordinate)) =
      Real.cos (angles 0) + Real.cos (angles 1) by
      rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
      simp]
    linarith
  rw [abs_le]
  constructor <;> norm_num at * <;> linarith

theorem abs_rankFiveNormalizedKernel_le_tail
    {index : ℕ} {scale : ℝ} (hscale : |scale| ≤ 7 / 2) :
    |fibonacciScaleKernel scale index /
        (largeScalePreimage 5 ^ (index + 1) / Real.sqrt 21)| ≤
      Real.sqrt 21 * rankFiveTailGrowthRatio ^ (index + 1) := by
  let gamma := absoluteKernelGrowth (7 / 2 : ℝ)
  let alpha := largeScalePreimage 5
  have hkernel : |fibonacciScaleKernel scale index| ≤ gamma ^ index :=
    abs_fibonacciScaleKernel_le_growth_pow (by norm_num) hscale index
  have hgammaOne : 1 ≤ gamma := by
    exact (show (1 : ℝ) ≤ 7 / 2 by norm_num).trans
      (absoluteKernelGrowth_ge_bound (by norm_num))
  have halphaPos : 0 < alpha := largeScalePreimage_pos (by norm_num)
  have hrootPos : 0 < Real.sqrt (21 : ℝ) := by positivity
  have hdenomPos : 0 < alpha ^ (index + 1) / Real.sqrt 21 :=
    div_pos (pow_pos halphaPos _) hrootPos
  rw [abs_div, abs_of_pos hdenomPos]
  calc
    |fibonacciScaleKernel scale index| /
        (alpha ^ (index + 1) / Real.sqrt 21) =
      (|fibonacciScaleKernel scale index| * Real.sqrt 21) /
        alpha ^ (index + 1) := by field_simp
    _ ≤ (gamma ^ index * Real.sqrt 21) / alpha ^ (index + 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkernel hrootPos.le)
        (pow_nonneg halphaPos.le _)
    _ ≤ (gamma ^ (index + 1) * Real.sqrt 21) /
        alpha ^ (index + 1) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg halphaPos.le _)
      apply mul_le_mul_of_nonneg_right _ hrootPos.le
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg (by positivity) _) hgammaOne
    _ = Real.sqrt 21 * (gamma / alpha) ^ (index + 1) := by
      rw [div_pow]
      ring
    _ = _ := by rfl

theorem norm_rankFiveTailProductIntegrand_le
    (index : ℕ) (angles : Fin 2 → ℝ) :
    ‖rankFiveTailProductIntegrand index angles‖ ≤
      ((1 / Real.pi) ^ 2 * Real.sqrt 21 * 4) *
        rankFiveTailGrowthRatio ^ (index + 1) := by
  by_cases htail : angles ∈ rankFiveTailSpectralDomain
  · rw [rankFiveTailProductIntegrand, Set.indicator_of_mem htail,
      rankFiveFullNormalizedIntegrand, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
      abs_of_nonneg (oddWeylAngleWeight_two_nonneg angles)]
    have hkernel := abs_rankFiveNormalizedKernel_le_tail (index := index)
      (abs_oddCosineCubeScale_le_midpoint_of_tail htail)
    have hweight := oddWeylAngleWeight_two_le_four angles
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left hkernel (pow_nonneg (by positivity) _))
      hweight (oddWeylAngleWeight_two_nonneg angles)
      (mul_nonneg (pow_nonneg (by positivity) _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg rankFiveTailGrowthRatio_pos.le _)))).trans_eq (by ring)
  · rw [rankFiveTailProductIntegrand, Set.indicator_of_notMem htail, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _) (Real.sqrt_nonneg _))
        (by norm_num))
      (pow_nonneg rankFiveTailGrowthRatio_pos.le _)

theorem norm_rankFiveTailNormalizedIntegral_le (index : ℕ) :
    ‖rankFiveTailNormalizedIntegral index‖ ≤
      (((1 / Real.pi) ^ 2 * Real.sqrt 21 * 4) *
        rankFiveTailGrowthRatio ^ (index + 1)) *
          (cosineCubeProductMeasure 2).real Set.univ := by
  unfold rankFiveTailNormalizedIntegral
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall
      (norm_rankFiveTailProductIntegrand_le index))

theorem tendsto_rankFiveTailNormalizedIntegral :
    Tendsto (fun index : ℕ =>
      (index + 1 : ℝ) ^ 5 * rankFiveTailNormalizedIntegral index)
      atTop (nhds 0) := by
  let constant : ℝ := ((1 / Real.pi) ^ 2 * Real.sqrt 21 * 4) *
    (cosineCubeProductMeasure 2).real Set.univ
  apply squeeze_zero_norm
    (a := fun index : ℕ =>
      ((index + 1 : ℝ) ^ 5 *
        rankFiveTailGrowthRatio ^ (index + 1)) * constant)
  · intro index
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by positivity) _)]
    have hbound := norm_rankFiveTailNormalizedIntegral_le index
    exact (mul_le_mul_of_nonneg_left hbound (pow_nonneg (by positivity) _)).trans_eq
      (by ring)
  · simpa using tendsto_rankFiveTailPolynomialGeometric.mul_const constant

end FibonacciRibbonKernel
