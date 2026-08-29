import FibonacciRibbonKernel.RegevGeneralLocal

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

noncomputable def regevPositiveVandermonde
    (rank : ℕ) (coordinates : Fin rank → ℝ) : ℝ :=
  ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
    max (tracelessExtend coordinates row -
      tracelessExtend coordinates next) 0

noncomputable def regevChamberExtension
    (rank : ℕ) (coordinates : Fin rank → ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
    regevGaussianKernel rank coordinates *
    regevPositiveVandermonde rank coordinates

theorem continuous_regevPositiveVandermonde (rank : ℕ) :
    Continuous (regevPositiveVandermonde rank) := by
  unfold regevPositiveVandermonde
  apply continuous_finsetProd Finset.univ
  intro row hrow
  apply continuous_finsetProd (Finset.Ioi row)
  intro next hnext
  exact ((continuous_tracelessExtend_apply row).sub
    (continuous_tracelessExtend_apply next)).max continuous_const

theorem continuous_regevChamberExtension (rank : ℕ) :
    Continuous (regevChamberExtension rank) := by
  unfold regevChamberExtension
  exact (continuous_const.mul (continuous_regevGaussianKernel rank)).mul
    (continuous_regevPositiveVandermonde rank)

theorem regevPositiveVandermonde_eq_vandermonde_of_mem
    {rank : ℕ} {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∈ regevChamber rank) :
    regevPositiveVandermonde rank coordinates =
      regevVandermonde rank coordinates := by
  unfold regevPositiveVandermonde regevVandermonde
  apply Finset.prod_congr rfl
  intro row hrow
  apply Finset.prod_congr rfl
  intro next hnext
  rw [max_eq_left]
  have horder := (regevChamber_mem_iff coordinates).1 hcoordinates
    row next (Finset.mem_Ioi.mp hnext).le
  linarith

theorem regevPositiveVandermonde_eq_zero_of_not_mem
    {rank : ℕ} {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∉ regevChamber rank) :
    regevPositiveVandermonde rank coordinates = 0 := by
  rw [regevChamber_mem_iff] at hcoordinates
  push Not at hcoordinates
  obtain ⟨row, next, hrowNext, hviolation⟩ := hcoordinates
  have hstrict : row < next := hrowNext.lt_of_ne (by
    intro heq
    subst next
    exact (lt_irrefl _ hviolation))
  unfold regevPositiveVandermonde
  apply Finset.prod_eq_zero (Finset.mem_univ row)
  apply Finset.prod_eq_zero (Finset.mem_Ioi.mpr hstrict)
  rw [max_eq_right]
  linarith

theorem regevChamberExtension_eq_local_of_mem
    {rank : ℕ} {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∈ regevChamber rank) :
    regevChamberExtension rank coordinates =
      regevLocalIntegrand rank coordinates := by
  unfold regevChamberExtension regevLocalIntegrand
  rw [regevPositiveVandermonde_eq_vandermonde_of_mem hcoordinates]

theorem regevChamberExtension_eq_zero_of_not_mem
    {rank : ℕ} {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∉ regevChamber rank) :
    regevChamberExtension rank coordinates = 0 := by
  unfold regevChamberExtension
  rw [regevPositiveVandermonde_eq_zero_of_not_mem hcoordinates]
  ring

theorem regevChamberExtension_eq_indicator (rank : ℕ) :
    regevChamberExtension rank =
      (regevChamber rank).indicator (regevLocalIntegrand rank) := by
  funext coordinates
  by_cases hcoordinates : coordinates ∈ regevChamber rank
  · rw [Set.indicator_of_mem hcoordinates]
    exact regevChamberExtension_eq_local_of_mem hcoordinates
  · rw [Set.indicator_of_notMem hcoordinates]
    exact regevChamberExtension_eq_zero_of_not_mem hcoordinates

theorem integrable_regevChamberExtension (rank : ℕ) :
    Integrable (regevChamberExtension rank) := by
  rw [regevChamberExtension_eq_indicator]
  exact (integrable_regevLocalIntegrand rank).integrableOn.integrable_indicator
    (regevChamber_isClosed rank).measurableSet

theorem integral_regevChamberExtension (rank : ℕ) :
    (∫ coordinates : Fin rank → ℝ,
      regevChamberExtension rank coordinates) =
      regevFullChamberIntegral rank := by
  rw [regevChamberExtension_eq_indicator]
  rw [integral_indicator (regevChamber_isClosed rank).measurableSet]
  rfl

end FibonacciRibbonKernel
