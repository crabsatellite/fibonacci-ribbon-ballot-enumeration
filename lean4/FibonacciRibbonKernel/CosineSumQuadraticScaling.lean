import FibonacciRibbonKernel.VariableMicroscopicScaling

namespace FibonacciRibbonKernel

open Filter
open scoped BigOperators

noncomputable def cosineSumScale
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) (index : ℕ) : ℝ :=
  2 * ∑ coordinate,
    Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ))

noncomputable def cosineSumDisplacement
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) (index : ℕ) : ℝ :=
  (index + 1 : ℝ) *
    (cosineSumScale coordinates index - 2 * dimension)

theorem tendsto_cosineSumDisplacement
    {dimension : ℕ} (coordinates : Fin dimension → ℝ) :
    Tendsto (cosineSumDisplacement coordinates) atTop
      (nhds (-∑ coordinate, coordinates coordinate ^ 2)) := by
  have hcoordinate : ∀ coordinate : Fin dimension,
      Tendsto
        (fun index : ℕ =>
          2 * ((index + 1 : ℝ) *
            (Real.cos (coordinates coordinate /
              Real.sqrt (index + 1 : ℝ)) - 1)))
        atTop (nhds (-(coordinates coordinate ^ 2))) := by
    intro coordinate
    have hbase := tendsto_cos_sqrt_quadratic (coordinates coordinate)
    have hscaled := hbase.const_mul 2
    have hlimit : (2 : ℝ) * (-(coordinates coordinate ^ 2) / 2) =
        -(coordinates coordinate ^ 2) := by ring
    rw [hlimit] at hscaled
    exact hscaled
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin dimension))
    (fun coordinate _hcoordinate => hcoordinate coordinate)
  have hsum' : Tendsto
      (fun index : ℕ => ∑ coordinate,
        2 * ((index + 1 : ℝ) *
          (Real.cos (coordinates coordinate /
            Real.sqrt (index + 1 : ℝ)) - 1)))
      atTop (nhds (-∑ coordinate, coordinates coordinate ^ 2)) := by
    rw [← Finset.sum_neg_distrib]
    exact hsum
  apply hsum'.congr'
  filter_upwards with index
  unfold cosineSumDisplacement cosineSumScale
  change (∑ coordinate : Fin dimension,
      2 * ((index + 1 : ℝ) *
        (Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) - 1))) =
    (index + 1 : ℝ) *
      (2 * ∑ coordinate : Fin dimension,
        Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) -
        2 * (dimension : ℝ))
  calc
    (∑ coordinate : Fin dimension,
        2 * ((index + 1 : ℝ) *
          (Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) - 1))) =
      2 * (index + 1 : ℝ) *
        ∑ coordinate : Fin dimension,
          (Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ)) - 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro coordinate _hcoordinate
        ring
    _ = 2 * (index + 1 : ℝ) *
        ((∑ coordinate : Fin dimension,
            Real.cos (coordinates coordinate / Real.sqrt (index + 1 : ℝ))) -
          ∑ _coordinate : Fin dimension, (1 : ℝ)) := by
        rw [Finset.sum_sub_distrib]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

theorem tendsto_log_largeScalePreimage_cosineSum
    {dimension : ℕ} (hdimension : 2 < (2 * dimension : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (Real.log (largeScalePreimage (cosineSumScale coordinates index)) -
            Real.log (largeScalePreimage (2 * dimension : ℝ))))
      atTop
      (nhds ((-∑ coordinate, coordinates coordinate ^ 2) /
        Real.sqrt ((2 * dimension : ℝ) ^ 2 - 4))) := by
  have h := tendsto_log_largeScalePreimage_variable_microscopic
    hdimension (tendsto_cosineSumDisplacement coordinates)
  have hscale : ∀ index : ℕ,
      cosineSumScale coordinates index =
        (2 * dimension : ℝ) +
          cosineSumDisplacement coordinates index / (index + 1 : ℝ) := by
    intro index
    unfold cosineSumDisplacement
    have hdenominator : (index + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  apply h.congr'
  filter_upwards with index
  rw [hscale]

end FibonacciRibbonKernel
