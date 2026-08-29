import FibonacciRibbonKernel.OddFibonacciPointwise

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def oddCosineScaleMidpoint (dimension : ℕ) : ℝ :=
  ((2 * dimension + 1 : ℝ) + 2) / 2

noncomputable def positiveOddLocalScaledDomain
    (dimension index : ℕ) : Set (Fin dimension → ℝ) :=
  positiveScaledCube dimension index ∩
    {coordinates | oddCosineScaleMidpoint dimension ≤
      oddCosineSumScale coordinates index}

noncomputable def oddWeylLocalRescaledIntegrand
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  (positiveOddLocalScaledDomain dimension index).indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        normalizedOddFibonacciKernel coordinates index *
        oddScaledWeylWeight dimension index coordinates)
    coordinates

noncomputable def oddWeylLocalLimitIntegrand
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  positiveOrthant.indicator
    (fun coordinates =>
      (1 / Real.pi) ^ dimension *
        Real.exp
          ((-∑ coordinate, coordinates coordinate ^ 2) /
            Real.sqrt ((2 * dimension + 1 : ℝ) ^ 2 - 4)) *
        oddLimitWeylWeight dimension coordinates)
    coordinates

theorem oddCosineScaleMidpoint_lt_base
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ)) :
    oddCosineScaleMidpoint dimension < (2 * dimension + 1 : ℝ) := by
  unfold oddCosineScaleMidpoint
  linarith

theorem eventually_mem_positiveOddLocalScaledDomain
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ)
    (hcoordinates : coordinates ∈ positiveOrthant) :
    ∀ᶠ index : ℕ in atTop,
      coordinates ∈ positiveOddLocalScaledDomain dimension index := by
  have hcube := eventually_mem_positiveScaledCube coordinates hcoordinates
  have hscale := tendsto_oddCosineSumScale coordinates
  have hlocal : ∀ᶠ index : ℕ in atTop,
      oddCosineScaleMidpoint dimension ≤
        oddCosineSumScale coordinates index :=
    ((tendsto_order.1 hscale).1 _
      (oddCosineScaleMidpoint_lt_base hdimension)).mono fun _ h => h.le
  filter_upwards [hcube, hlocal] with index hcubeIndex hlocalIndex
  exact ⟨hcubeIndex, hlocalIndex⟩

theorem tendsto_oddWeylLocalRescaledIntegrand
    {dimension : ℕ} (hdimension : 2 < (2 * dimension + 1 : ℝ))
    (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index =>
      oddWeylLocalRescaledIntegrand dimension index coordinates)
      atTop (nhds (oddWeylLocalLimitIntegrand dimension coordinates)) := by
  by_cases horthant : coordinates ∈ positiveOrthant
  · have hlocal := eventually_mem_positiveOddLocalScaledDomain
      hdimension coordinates horthant
    have hkernel := tendsto_normalizedOddFibonacciKernel
      hdimension coordinates
    have hweight := tendsto_oddScaledWeylWeight dimension coordinates
    have hconstant : Tendsto (fun _ : ℕ => (1 / Real.pi) ^ dimension)
        atTop (nhds ((1 / Real.pi) ^ dimension)) := tendsto_const_nhds
    have hproduct := (hconstant.mul hkernel).mul hweight
    rw [oddWeylLocalLimitIntegrand, Set.indicator_of_mem horthant]
    apply hproduct.congr'
    filter_upwards [hlocal] with index hindex
    rw [oddWeylLocalRescaledIntegrand, Set.indicator_of_mem hindex]
  · have hdimensionPos : 0 < dimension := by
      by_contra hzero
      have : dimension = 0 := Nat.eq_zero_of_not_pos hzero
      subst dimension
      norm_num at hdimension
    have hnot : ∃ coordinate : Fin dimension,
        coordinates coordinate ≤ 0 := by
      by_contra hnone
      push Not at hnone
      exact horthant fun coordinate _hcoordinate => hnone coordinate
    obtain ⟨coordinate, hcoordinate⟩ := hnot
    have houtside : ∀ index : ℕ,
        coordinates ∉ positiveOddLocalScaledDomain dimension index := by
      intro index hdomain
      have hcube := hdomain.1 coordinate (Set.mem_univ coordinate)
      linarith [hcube.1]
    have hzero : (fun index : ℕ =>
        oddWeylLocalRescaledIntegrand dimension index coordinates) =
        fun _ => 0 := by
      funext index
      rw [oddWeylLocalRescaledIntegrand,
        Set.indicator_of_notMem (houtside index)]
    rw [hzero, oddWeylLocalLimitIntegrand,
      Set.indicator_of_notMem horthant]
    exact tendsto_const_nhds

end FibonacciRibbonKernel
