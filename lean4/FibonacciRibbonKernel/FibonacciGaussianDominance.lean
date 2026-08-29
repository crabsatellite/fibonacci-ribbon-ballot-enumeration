import FibonacciRibbonKernel.LogGrowthConcavity

namespace FibonacciRibbonKernel

open scoped BigOperators

theorem largeScalePreimage_ratio_le_exp_tangent_of_le
    {scale base : ℝ} (hscale : 2 < scale) (hbase : scale ≤ base) :
    largeScalePreimage scale / largeScalePreimage base ≤
      Real.exp ((scale - base) / Real.sqrt (base ^ 2 - 4)) := by
  rcases hbase.eq_or_lt with heq | hlt
  · subst scale
    rw [sub_self, zero_div, Real.exp_zero, div_self]
    exact (largeScalePreimage_pos hscale.le).ne'
  · exact largeScalePreimage_ratio_le_exp_tangent hscale hlt

theorem largeScalePreimage_cosine_ratio_pow_le_gaussian
    {dimension index : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hcoordinates : ∀ coordinate,
      |coordinates coordinate| ≤ Real.pi * Real.sqrt (index + 1 : ℝ))
    (hscale : 2 < cosineSumScale coordinates index) :
    (largeScalePreimage (cosineSumScale coordinates index) /
        largeScalePreimage (2 * dimension : ℝ)) ^ (index + 1) ≤
      Real.exp
        (-(4 / (Real.pi ^ 2 *
          Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) *
            ∑ coordinate, coordinates coordinate ^ 2) := by
  let base : ℝ := 2 * dimension
  let current : ℝ := cosineSumScale coordinates index
  let root : ℝ := Real.sqrt (base ^ 2 - 4)
  let normalization : ℝ := index + 1
  let squares : ℝ := ∑ coordinate, coordinates coordinate ^ 2
  have hrootPos : 0 < root := by
    dsimp only [root, base]
    apply Real.sqrt_pos.2
    nlinarith
  have hnormalizationPos : 0 < normalization := by
    dsimp only [normalization]
    positivity
  have hsquaresNonneg : 0 ≤ squares := by
    dsimp only [squares]
    positivity
  have hdeficit := cosineSumScale_le_quadratic coordinates hcoordinates
  have hcurrentLe : current ≤ base := by
    dsimp only [current, base]
    have hsubNonneg :
        0 ≤ (4 / (Real.pi ^ 2 * (index + 1 : ℝ))) *
          ∑ coordinate, coordinates coordinate ^ 2 := by positivity
    linarith
  have hratio := largeScalePreimage_ratio_le_exp_tangent_of_le
    hscale hcurrentLe
  have hratioNonneg : 0 ≤
      largeScalePreimage current / largeScalePreimage base :=
    (div_pos (largeScalePreimage_pos hscale.le)
      (largeScalePreimage_pos hdimension.le)).le
  have hpow := pow_le_pow_left₀ hratioNonneg hratio (index + 1)
  have hscaledDeficit :
      normalization * (current - base) / root ≤
        -(4 / (Real.pi ^ 2 * root)) * squares := by
    have hraw : current - base ≤
        -(4 / (Real.pi ^ 2 * normalization)) * squares := by
      dsimp only [current, base, normalization, squares]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hraw hnormalizationPos.le
    have hdivide := div_le_div_of_nonneg_right hmul hrootPos.le
    field_simp [hnormalizationPos.ne', hrootPos.ne'] at hdivide ⊢
    exact hdivide
  calc
    (largeScalePreimage current / largeScalePreimage base) ^ (index + 1) ≤
        Real.exp ((current - base) / root) ^ (index + 1) := hpow
    _ = Real.exp (normalization * (current - base) / root) := by
      rw [← Real.exp_nat_mul]
      dsimp only [normalization]
      push_cast
      congr 1
      ring
    _ ≤ Real.exp (-(4 / (Real.pi ^ 2 * root)) * squares) :=
      Real.exp_le_exp.mpr hscaledDeficit

end FibonacciRibbonKernel
